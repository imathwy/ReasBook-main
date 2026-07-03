import Mathlib
import StacksProject_2024.Chap11.Lemma_11_4_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

namespace CSA

section

variable {k : Type u} [Field k]
variable (A : CSA.{u, w} k)
variable (k' : Type v) [Field k'] [Algebra k k']

/-
Domain-style sampling for Lemma 11.4.9:
- primary domain: scalar extension of finite-dimensional central simple algebras along field
  extensions;
- sampled owner declarations:
  `CSA`,
  `Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct`,
  `Algebra.IsCentral.center_eq_bot`,
  `isSimpleRing_tensorProduct_of_finite_central_left_factor`;
- best owner abstraction: the source-facing object is the base-changed algebra
  `A.baseChange k' : CSA k'`; the tensor product `k' ⊗[k] A` is the canonical carrier, while
  centrality and simplicity are derived owner data rather than a separate wrapper;
- primitive data: a central simple algebra `A : CSA k` and a field extension `k'/k`;
- derived API: the induced `k'`-centrality and simplicity instances on `k' ⊗[k] A`, packaged by
  `CSA.mk`.

Source/core/bridge triage:
- `source-facing`: scalar extension of a central simple `k`-algebra to a `k'`-algebra;
- `core/canonical`: the owner object `CSA k'` with carrier `k' ⊗[k] A`;
- `bridge/view`: the tensor-product centralizer computation identifying the center with the image of
  the left factor. -/

private theorem map_bot_range_eq_includeLeft_range :
    (Algebra.TensorProduct.map (AlgHom.id k k') (⊥ : Subalgebra k A).val).range =
      (includeLeft : k' →ₐ[k] k' ⊗[k] A).range := by
  rw [Algebra.TensorProduct.map_range]
  have hbot :
      ((includeRight : A →ₐ[k] k' ⊗[k] A).comp (⊥ : Subalgebra k A).val).range =
        (⊥ : Subalgebra k (k' ⊗[k] A)) := by
    rw [AlgHom.range_comp, Subalgebra.range_val, Algebra.map_bot]
  rw [hbot, sup_bot_eq]
  simp

private instance : Algebra.IsCentral k' (k' ⊗[k] A) := by
  refine ⟨fun x hx ↦ ?_⟩
  have hx' :
      x ∈ Subalgebra.centralizer k
        (includeRight : A →ₐ[k] k' ⊗[k] A).range := by
    rw [Subalgebra.mem_centralizer_iff]
    rw [Subalgebra.mem_center_iff] at hx
    intro y _
    exact hx y
  have hx'' :
      x ∈ (Algebra.TensorProduct.map (AlgHom.id k k') (Subalgebra.center k A).val).range := by
    rwa [Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct k k' A] at hx'
  have hx''' : x ∈ (includeLeft : k' →ₐ[k] k' ⊗[k] A).range := by
    rw [Algebra.IsCentral.center_eq_bot, map_bot_range_eq_includeLeft_range A k'] at hx''
    exact hx''
  rcases hx''' with ⟨y, rfl⟩
  exact Subalgebra.algebraMap_mem (⊥ : Subalgebra k' (k' ⊗[k] A)) y

private instance : IsSimpleRing (k' ⊗[k] A) := by
  exact IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.comm k A k').toRingEquiv
    isSimpleRing_tensorProduct_of_finite_central_left_factor

/-- Lemma 11.4.9: scalar extension of a finite central simple `k`-algebra along a field extension,
packaged as the canonical owner object `CSA k'`. -/
noncomputable def baseChange : CSA k' :=
  CSA.mk (AlgCat.of k' (k' ⊗[k] A))

end

end CSA
