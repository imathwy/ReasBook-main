import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.ComparisonFullFaithfulness
import Mathlib.Tactic.StacksAttribute

universe u v

namespace CategoryTheory

open Bicategory
open BasedFunctor
open FibredCategoryMor
open InducedCategory.Hom
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section

/-- Helper for Lemma 8.8.1: a direct comparison morphism between two stackifications is fully
faithful once one compares the Hom-presheaf triangle for `G₁`, `H`, and `G₂`. -/
-- TODO: rewrite the Hom-presheaf triangle with `fibredMorphismPresheafMap_comp`, transport
-- across the compatible isomorphism `α`, use the new source-image wrapper to isolate the
-- cancellation step, and then cancel the two stackification maps because the Hom-presheaves of
-- stacks are already sheaves.
theorem comparison_stackification_fullyFaithful
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    (G₂ : X ⟶ Y₂)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    (hG₂ : FibredCategoryMor.IsStackification G₂)
    (H : Y₁ ⟶ Y₂)
    (α : (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H ≅ G₂) :
    Nonempty (InducedCategory.Hom.toBasedFunctor H).FullyFaithful := by
  -- Full faithfulness reduces to the Hom-presheaf isomorphism criterion: every fiberwise
  -- comparison map for `H` between arbitrary objects of `Y₁` is an isomorphism.
  exact
    stack_morphism_fullyFaithful_of_fibredMorphismPresheafMap_isIso (J := J) H
      (fun {U} x y ↦
        comparison_stackification_presheafMap_isIso (J := J) G₁ G₂ hG₁ hG₂ H α x y)

/-- Helper for Lemma 8.8.1: an isomorphism of stack morphisms induces the corresponding
isomorphism of underlying based functors over the base category. -/
noncomputable abbrev stack_morphism_basedFunctorIsoOfOwnerIso
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    {H K : Y₁ ⟶ Y₂}
    (η : H ≅ K) :
    InducedCategory.Hom.toBasedFunctor H ≅
      InducedCategory.Hom.toBasedFunctor K :=
  -- Push `η` through the stack hom-category inclusion to an owner iso of fibred-category
  -- morphisms, then forget that owner iso to the based-functor level.
  FibredCategoryMor.basedFunctorIsoOfOwnerIso
    (Functor.mapIso ((stackOverSubTwoCategory J).hom Y₁ Y₂).inclusion η)

/-- Helper for Lemma 8.8.1: any compatible comparison morphism between two stackifications is an
equivalence over the base. The direct comparison route only needs full faithfulness plus local
essential surjectivity, matching the source proof. -/
theorem comparison_stackification_isEquivalenceOverBase
    {X : FibredCategoryOver C} {Y₁ Y₂ : StackOver J}
    (G₁ : X ⟶ Y₁)
    (G₂ : X ⟶ Y₂)
    (hG₁ : FibredCategoryMor.IsStackification G₁)
    (hG₂ : FibredCategoryMor.IsStackification G₂)
    (H : Y₁ ⟶ Y₂)
    (α : (stackification_comparison_precompose_functor (J := J) (G := G₁)).obj H ≅ G₂) :
    IsEquivalenceOverBase H := by
  -- A direct comparison morphism is fully faithful (Hom-presheaf criterion) and locally
  -- essentially surjective on objects, hence an equivalence over the base.
  exact
    stack_morphism_isEquivalenceOverBase_of_fullyFaithful_of_locallyEssentiallySurjective
      (J := J) H
      (comparison_stackification_fullyFaithful (J := J) G₁ G₂ hG₁ hG₂ H α)
      (comparison_stack_morphism_locallyEssentiallySurjectiveOnObjects
        (J := J) G₁ G₂ hG₂ H α)

end

end CategoryTheory
