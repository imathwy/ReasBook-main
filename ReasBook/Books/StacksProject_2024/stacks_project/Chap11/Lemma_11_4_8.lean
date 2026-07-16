import Mathlib
import StacksProject_2024.stacks_project.Chap11.Lemma_11_4_7

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 11.4.8:
- primary domain: finite-dimensional central simple algebras over a field and the tensor product of
  their representative algebras;
- sampled owner declarations:
  `CSA`,
  `BrauerGroup`,
  `isSimpleRing_tensorProduct_of_finite_central_left_factor`;
- best owner abstraction: this item is `source-facing`, and its public owner should be the
  representative-level object `CSA.tensorProduct`; the ambient `CSA k` structure is the
  `core/canonical` owner, while the later Brauer-group multiplication is a downstream
  `bridge/view` built from this representative tensor product;
- primitive data: only the tensor-product algebra `A ⊗[k] B` together with the canonical proofs
  that it is central and simple over `k`;
- derived API: the packaged owner `CSA.tensorProduct`, which downstream files use to define
  multiplication on Brauer classes.

The raw instances on `A ⊗[k] B` are implementation details for constructing the owner object; they
should not remain part of the public API surface. -/

open scoped TensorProduct
open Algebra Algebra.TensorProduct Subalgebra

universe u v w

section

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k) (B : CSA.{u, w} k)

private theorem map_bot_range_eq_includeRight_range :
    (map (⊥ : Subalgebra k A).val (AlgHom.id k B)).range =
      (includeRight : B →ₐ[k] A ⊗[k] B).range := by
  rw [Algebra.TensorProduct.map_range, AlgHom.range_comp, Subalgebra.range_val,
    Algebra.map_bot, bot_sup_eq]
  simp

private instance instIsCentralTensorProduct : Algebra.IsCentral k (A ⊗[k] B) where
  out x hx := by
    rw [Subalgebra.mem_center_iff] at hx
    have hxL : x ∈ centralizer k ((includeLeft : A →ₐ[k] A ⊗[k] B).range : Set (A ⊗[k] B)) := by
      intro y hy
      exact hx y
    rw [centralizer_coe_range_includeLeft_eq_center_tensorProduct,
      Algebra.IsCentral.center_eq_bot, map_bot_range_eq_includeRight_range] at hxL
    rcases hxL with ⟨b, rfl⟩
    have hb : b ∈ center k B := by
      rw [Subalgebra.mem_center_iff]
      intro b'
      apply (includeRight : B →ₐ[k] A ⊗[k] B).injective
      simpa using hx (includeRight b')
    rw [Algebra.IsCentral.mem_center_iff] at hb
    rcases hb with ⟨r, rfl⟩
    exact ⟨r, by simp⟩

private instance instIsSimpleRingTensorProduct : IsSimpleRing (A ⊗[k] B) :=
  isSimpleRing_tensorProduct_of_finite_central_left_factor

namespace CSA

/-- Lemma 11.4.8: the tensor product of finite central simple `k`-algebras over `k`, packaged as
a canonical object of `CSA k`. -/
def tensorProduct : CSA.{u, max v w} k where
  toAlgCat := AlgCat.of k (A ⊗[k] B)

end CSA

end
