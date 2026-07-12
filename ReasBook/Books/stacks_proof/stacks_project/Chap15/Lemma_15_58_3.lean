import StacksProject_2024.Chap15.Lemma_15_58_3_Owner
import Mathlib.Tactic.StacksAttribute

-- Public wrapper import for the canonical owner file of Lemma 15.58.3.

noncomputable section

universe u

open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable [Preadditive (ModuleCat R)] [HasZeroObject (ModuleCat R)]
variable [MonoidalCategory (ModuleCat R)]
variable [SymmetricCategory (ModuleCat R)]
variable [MonoidalPreadditive (ModuleCat R)]
variable [HasColimits (ModuleCat R)]
variable [HasBinaryBiproducts (ModuleCat R)]
variable [(curriedTensor (ModuleCat R)).Additive]
variable [∀ X : ModuleCat R,
  ((curriedTensor (ModuleCat R)).obj X).Additive]
variable [∀ (K L : CochainComplex (ModuleCat R) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (ModuleCat R))]
variable [∀ G₁ G₂ : GradedObject ℤ (ModuleCat R), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (ModuleCat R),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (ModuleCat R),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (ModuleCat R),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [∀ X : ModuleCat R,
  PreservesColimit (Functor.empty.{0} (ModuleCat R)) ((curriedTensor (ModuleCat R)).obj X)]
variable [∀ X : ModuleCat R,
  PreservesColimit (Functor.empty.{0} (ModuleCat R)) ((curriedTensor (ModuleCat R)).flip.obj X)]

/-- Lemma 15.58.3: the imported generic owner instance specializes to the homotopy category of
cochain complexes of `R`-modules. -/
@[stacks 0GWP]
abbrev moduleCat_homotopyCategory_symmetricCategory :
    SymmetricCategory (HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ)) := inferInstance

end

end CategoryTheory
