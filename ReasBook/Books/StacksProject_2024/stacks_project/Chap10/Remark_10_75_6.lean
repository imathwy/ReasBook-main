import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_75_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ModuleCat.MonoidalCategory

universe u

section

variable {R : Type u} [CommRing R]

/-- In degree `0`, the diagonal component of the symmetry from Lemma `10.75.5` identifies,
via the canonical degree-`0` comparisons with tensor product in the two variables, with the usual
tensor-product braiding on `M ⊗[R] M`. -/
theorem tor_zero_self_flip_via_tensor_braiding (M : ModuleCat R) :
    ((tensorLeft M).leftDerivedZeroIsoSelf.inv.app M) ≫
        ((tor_flip_iso (ModuleCat R) 0).app M).hom.app M ≫
        (tensorRight M).fromLeftDerivedZero.app M =
      (β_ M M).hom := sorry

end

section

variable {k : Type u} [Field k]

private theorem rankTwoTensor_swap_ne :
    (TensorProduct.tmul k ((1 : k), 0) ((0 : k), 1) : TensorProduct k (k × k) (k × k)) ≠
      TensorProduct.tmul k ((0 : k), 1) ((1 : k), 0) := by
  intro h
  let fst : (k × k) →ₗ[k] k := LinearMap.fst k k k
  let snd : (k × k) →ₗ[k] k := LinearMap.snd k k k
  have h' := congr_arg
    ((TensorProduct.map fst snd) :
      TensorProduct k (k × k) (k × k) →ₗ[k] TensorProduct k k k) h
  simp [fst, snd] at h'

/-- For the free rank-`2` module over a field, the diagonal symmetry on `Tor₀` is not the
identity. -/
theorem tor_zero_self_flip_not_identity_on_free_rankTwo :
    ((tensorLeft (ModuleCat.of k (k × k))).leftDerivedZeroIsoSelf.inv.app (ModuleCat.of k (k × k)))
        ≫
        ((tor_flip_iso (ModuleCat k) 0).app (ModuleCat.of k (k × k))).hom.app
          (ModuleCat.of k (k × k))
        ≫
        (tensorRight (ModuleCat.of k (k × k))).fromLeftDerivedZero.app (ModuleCat.of k (k × k)) ≠
      𝟙 ((ModuleCat.of k (k × k)) ⊗ (ModuleCat.of k (k × k))) := by
  let M : ModuleCat k := ModuleCat.of k (k × k)
  rw [tor_zero_self_flip_via_tensor_braiding M]
  intro hβ
  have hxy := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp hβ)
    (TensorProduct.tmul k ((1 : k), 0) ((0 : k), 1))
  have hswap :
      TensorProduct.tmul k ((0 : k), 1) ((1 : k), 0) =
        (TensorProduct.tmul k ((1 : k), 0) ((0 : k), 1) : TensorProduct k (k × k) (k × k)) := by
    simpa [M] using hxy
  exact rankTwoTensor_swap_ne hswap.symm

/-- Remark 10.75.6: the canonical endomorphism of `Tor_i^R(M, M)` coming from the symmetry of
Lemma `10.75.5` is generally not the identity after the canonical degree-`0` identifications with
tensor product; this already fails in degree `0`. -/
theorem tor_zero_self_flip_not_universally_identity :
    ¬ ∀ M : ModuleCat k,
      ((tensorLeft M).leftDerivedZeroIsoSelf.inv.app M) ≫
          ((tor_flip_iso (ModuleCat k) 0).app M).hom.app M ≫
          (tensorRight M).fromLeftDerivedZero.app M =
        𝟙 (M ⊗ M) := by
  intro h
  exact tor_zero_self_flip_not_identity_on_free_rankTwo (h (ModuleCat.of k (k × k)))

end
