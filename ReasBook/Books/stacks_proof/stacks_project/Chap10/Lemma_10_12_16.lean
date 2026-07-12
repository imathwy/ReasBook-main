import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open LocalizedModule

universe u v w

noncomputable section

section

variable {R : Type u} [CommSemiring R] (S : Submonoid R)
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

/- Lemma 10.12.16 is a `bridge/view` item. Its owner abstractions are
`IsLocalizedModule.linearEquiv`, applied to the canonical localization map on tensor products, and
`IsLocalization.moduleTensorEquiv`, which identifies tensoring over `Localization S` with tensoring
over `R` for localized modules. The source-facing equivalence below is their canonical composite. -/
/-- Lemma 10.12.16: localizing a tensor product is canonically equivalent to the tensor product of
the localized modules over `Localization S`. -/
@[stacks 00DL]
def localizedTensorProductLinearEquiv :
    LocalizedModule S M ⊗[Localization S] LocalizedModule S N ≃ₗ[Localization S]
      LocalizedModule S (M ⊗[R] N) :=
  let tensorMap := TensorProduct.map (mkLinearMap S M) (mkLinearMap S N)
  IsLocalization.moduleTensorEquiv S (Localization S) (LocalizedModule S M) (LocalizedModule S N) ≪≫ₗ
    (IsLocalizedModule.linearEquiv S tensorMap
      (mkLinearMap S (M ⊗[R] N))).extendScalarsOfIsLocalization S (Localization S)

/-- The canonical localization-tensor equivalence sends a simple tensor of localized elements to
the localization of the corresponding tensor with multiplied denominator. -/
theorem localizedTensorProductLinearEquiv_apply_mk_tmul_mk
    (m : M) (n : N) (s t : S) :
    localizedTensorProductLinearEquiv S
      (mk m s ⊗ₜ[Localization S] mk n t) =
        mk (m ⊗ₜ[R] n) (s * t) := by
  let tensorMap := TensorProduct.map (mkLinearMap S M) (mkLinearMap S N)
  rw [show mk m s = Localization.mk (1 : R) s • mk m (1 : S) by
    simpa using (mk_smul_mk (1 : R) m s (1 : S)).symm]
  rw [show mk n t = Localization.mk (1 : R) t • mk n (1 : S) by
    simpa using (mk_smul_mk (1 : R) n t (1 : S)).symm]
  rw [TensorProduct.smul_tmul_smul, map_smul]
  change (Localization.mk (1 : R) s * Localization.mk (1 : R) t) •
      localizedTensorProductLinearEquiv S (mk m (1 : S) ⊗ₜ[Localization S] mk n (1 : S)) = _
  have hbase :
      localizedTensorProductLinearEquiv S (mk m (1 : S) ⊗ₜ[Localization S] mk n (1 : S)) =
        mk (m ⊗ₜ[R] n) (1 : S) := by
    change (IsLocalizedModule.linearEquiv S tensorMap (mkLinearMap S (M ⊗[R] N)))
        (mk m (1 : S) ⊗ₜ[R] mk n (1 : S)) = _
    simpa [localizedTensorProductLinearEquiv, tensorMap] using
      IsLocalizedModule.linearEquiv_apply S tensorMap
        (mkLinearMap S (M ⊗[R] N)) (m ⊗ₜ[R] n)
  rw [hbase]
  have hmul :
      Localization.mk (1 : R) s * Localization.mk (1 : R) t = Localization.mk (1 : R) (s * t) := by
    simp [Localization.mk_mul]
  rw [hmul]
  simpa using (mk_smul_mk (1 : R) (m ⊗ₜ[R] n) (s * t) (1 : S))

end
