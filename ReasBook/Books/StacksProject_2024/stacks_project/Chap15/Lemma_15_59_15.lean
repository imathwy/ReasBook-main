import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import StacksProject_2024.stacks_project.Chap15.Definition_15_59_13
import StacksProject_2024.stacks_project.Chap15.Lemma_15_59_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable [Preadditive (ModuleCat R)] [HasZeroObject (ModuleCat R)]
variable [MonoidalCategory (ModuleCat R)] [SymmetricCategory (ModuleCat R)]
variable [(curriedTensor (ModuleCat R)).Additive]
variable [∀ X : ModuleCat R, ((curriedTensor (ModuleCat R)).obj X).Additive]
variable [∀ G₁ G₂ : GradedObject ℤ (ModuleCat R), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (ModuleCat R), GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (ModuleCat R), GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (ModuleCat R), GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [∀ X : ModuleCat R,
  PreservesColimit (Functor.empty.{0} (ModuleCat R)) ((curriedTensor (ModuleCat R)).obj X)]
variable [∀ X : ModuleCat R,
  PreservesColimit (Functor.empty.{0} (ModuleCat R)) ((curriedTensor (ModuleCat R)).flip.obj X)]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for derived tensor associativity:
- primary domain: localized monoidal structures on homotopy and derived categories of module
  complexes;
- sampled owner declarations: `Localization.Monoidal.associator` in mathlib's localized monoidal
  API, `MonoidalCategory.tensorRightTensor`, `tensoringRightIsoDerivedTensorProduct` from Lemma
  `15.59.14`, and the ambient monoidal associator `α_`;
- layer: this file remains a `source-facing` bridge for the textbook associativity isomorphism on
  derived tensor products. The owner abstraction for associativity lives in the ambient monoidal
  coherence API, so this file should not duplicate generic inverse-identity lemmas. -/

/-- The functorial comparison identifying two successive derived tensor functors with tensoring by
the derived tensor product of the right factors. -/
noncomputable def derivedTensorProductTensorIso
    (L M : DMod) :
    derivedTensorProduct L ⋙ derivedTensorProduct M ≅
      derivedTensorProduct (L ⊗[R]^L M) :=
  Functor.isoWhiskerRight (tensoringRightIsoDerivedTensorProduct L).symm
      (derivedTensorProduct M) ≪≫
    Functor.isoWhiskerLeft ((tensoringRight DMod).obj L)
      (tensoringRightIsoDerivedTensorProduct M).symm ≪≫
      (tensorRightTensor L M).symm ≪≫
        (tensoringRight DMod).mapIso
          (derivedCategory_tensorObj_iso_derivedTensorProduct L M) ≪≫
          tensoringRightIsoDerivedTensorProduct (L ⊗[R]^L M)

/-- Lemma 15.59.15: for complexes `K^•`, `L^•`, and `M^•` of `R`-modules, there is a canonical
associativity isomorphism
`(K^• \otimes_R^{\mathbf L} L^•) \otimes_R^{\mathbf L} M^• \cong
K^• \otimes_R^{\mathbf L} (L^• \otimes_R^{\mathbf L} M^•)`,
functorial in all three complexes. -/
noncomputable def derivedTensorProduct_associator
    (K L M : DMod) :
    ((K ⊗[R]^L L) ⊗[R]^L M) ≅ (K ⊗[R]^L (L ⊗[R]^L M)) :=
  (derivedTensorProductTensorIso L M).app K

end

end CategoryTheory
