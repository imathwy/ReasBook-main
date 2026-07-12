import Mathlib
import StacksProject_2024.Chap10.Proposition_10_89_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x y

namespace Module

section

open scoped TensorProduct
open TensorProduct.AlgebraTensorModule

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

private theorem piRightHom_restrictScalars_factor
    {A : Type x} (Q : A → Type y) [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)] :
    (LinearEquiv.piCongrRight fun a ↦ cancelBaseChange R S S M (Q a)).toLinearMap ∘ₗ
        TensorProduct.piRightHom S S M (fun a ↦ S ⊗[R] Q a) ∘ₗ
        lTensor S M (TensorProduct.piRightHom R S S Q) ∘ₗ
        (cancelBaseChange R S S M ((a : A) → Q a)).symm.toLinearMap =
      TensorProduct.piRightHom R S M Q := by
  ext m q a
  simp

private theorem piRightHom_restrictScalars_injective
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    {A : Type x} (Q : A → Type y) [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)]
    [MittagLeffler R S] [Module.Flat S M] [MittagLeffler S M] :
    Function.Injective (TensorProduct.piRightHom R R M Q) := by
  let eDom := cancelBaseChange R S S M ((a : A) → Q a)
  let eCod := LinearEquiv.piCongrRight fun a ↦ cancelBaseChange R S S M (Q a)
  have hCriterionS :
      MittagLeffler R S ↔
        ∀ (A : Type x) (Q : A → Type y) [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)],
          Function.Injective (TensorProduct.piRightHom R R S Q) :=
    mittagLeffler_iff_tensorProduct_piRight_injective
  have hS :
      Function.Injective (TensorProduct.piRightHom R S S Q) := by
    simpa using hCriterionS.1 (inferInstance : MittagLeffler R S) A Q
  have hTensor :
      Function.Injective (lTensor S M (TensorProduct.piRightHom R S S Q)) := by
    simpa using
      Module.Flat.lTensor_preserves_injective_linearMap (TensorProduct.piRightHom R S S Q) hS
  have hCriterionM :
      MittagLeffler S M ↔
        ∀ (A : Type x) (Q : A → Type (max v y)) [∀ a, AddCommGroup (Q a)]
          [∀ a, Module S (Q a)],
          Function.Injective (TensorProduct.piRightHom S S M Q) :=
    mittagLeffler_iff_tensorProduct_piRight_injective
  have hM :
      Function.Injective (TensorProduct.piRightHom S S M (fun a ↦ S ⊗[R] Q a)) := by
    simpa using hCriterionM.1 (inferInstance : MittagLeffler S M) A (fun a ↦ S ⊗[R] Q a)
  have hComp :
      Function.Injective
        (eCod.toLinearMap ∘ₗ
          TensorProduct.piRightHom S S M (fun a ↦ S ⊗[R] Q a) ∘ₗ
          lTensor S M (TensorProduct.piRightHom R S S Q) ∘ₗ
          eDom.symm.toLinearMap) :=
    eCod.injective.comp <| hM.comp <| hTensor.comp eDom.symm.injective
  have hRS : Function.Injective (TensorProduct.piRightHom R S M Q) := by
    rw [← piRightHom_restrictScalars_factor Q]
    simpa [eDom, eCod] using hComp
  simpa using hRS

-- Proof sketch: by Proposition `10.89.5`, it is enough to test injectivity of the canonical map
-- `M ⊗[R] ∏ Q_α → ∏ (M ⊗[R] Q_α)` for every family of `R`-modules. Rewrite this map as the
-- composite obtained by first tensoring the injective map
-- `S ⊗[R] ∏ Q_α → ∏ (S ⊗[R] Q_α)` with the `S`-flat module `M`, and then applying the injective
-- `S`-Mittag-Leffler map for the family `α ↦ S ⊗[R] Q_α`.
/-- Lemma 10.89.11: if `S` is a Mittag-Leffler `R`-module and `M` is flat and Mittag-Leffler as
an `S`-module, then `M` is Mittag-Leffler as an `R`-module. -/
@[stacks 05CT]
theorem mittagLeffler_restrictScalars_of_mittagLeffler_of_flat [MittagLeffler R S]
    [Module.Flat S M] [MittagLeffler S M] :
    MittagLeffler R M := by
  have hCriterion :
      MittagLeffler R M ↔
        ∀ (A : Type w) (Q : A → Type w) [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)],
          Function.Injective (TensorProduct.piRightHom R R M Q) :=
    mittagLeffler_iff_tensorProduct_piRight_injective
  refine hCriterion.2 ?_
  intro (A : Type w) (Q : A → Type w) _ _
  exact piRightHom_restrictScalars_injective R S M Q

end

end Module
