import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.Frontier
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.TransitionLaws
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.TransitionPullHomCollapsed
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.ThreeFactorBridge
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.ExplicitMiddleBridge
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.ExplicitMiddleRestricted
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.ExplicitMiddleRestrictedComponents
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.TransitionHomCompReduction

universe u v uX vX

namespace CategoryTheory

open Bicategory
open FibredCategoryMor
open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace FibredCategoryMor
namespace DescentCompletionObject

/-- The reduced three-factor owner bridge implies the transition-level restriction law. -/
theorem projectionDescentTotalCoverTransitionComponentPullHomLaw_of_threeFactor
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hthree :
      projectionDescentTotalCoverTransitionComponentThreeFactorPullHomLaw (J := J) hSheaf D) :
    projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D := by
  intro Y' Y g A B a b h ga gb hga hgb
  rw [projectionDescentTotalCoverTransitionComponent_pullHom_collapsed]
  rw [projectionDescentTotalCoverTransitionComponent_collapsed]
  exact hthree g a b h ga gb hga hgb

/-- The narrowed explicit-middle owner bridge implies the transition-level restriction law. -/
theorem projectionDescentTotalCoverTransitionComponentPullHomLaw_of_explicitMiddle
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hmiddle :
      projectionDescentTotalCoverExplicitMiddlePullHomLaw (J := J) hSheaf D) :
    projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D :=
  projectionDescentTotalCoverTransitionComponentPullHomLaw_of_threeFactor
    (J := J) hSheaf D
    (projectionDescentTotalCoverTransitionComponentThreeFactorPullHomLaw_of_explicitMiddle
      (J := J) hSheaf D hmiddle)

/-- The restricted explicit middle component law implies the transition-level restriction law. -/
theorem projectionDescentTotalCoverTransitionComponentPullHomLaw_of_restrictedComponent
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hrestricted :
      projectionDescentTotalCoverExplicitMiddleRestrictedComponentLaw (J := J) hSheaf D) :
    projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D :=
  projectionDescentTotalCoverTransitionComponentPullHomLaw_of_explicitMiddle
    (J := J) hSheaf D
    (projectionDescentTotalCoverExplicitMiddlePullHomLaw_of_restrictedComponent
      (J := J) hSheaf D hrestricted)

/-- The remaining threefold-composite component expansion is enough for the transition-level
restriction law.  This keeps the canonical-owner component bridge isolated while allowing the
source stage 3.13 pipeline to continue under that single explicit obligation. -/
theorem projectionDescentTotalCoverTransitionComponentPullHomLaw_of_restrictedComposite
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hcomposite :
      projectionDescentExplicitOuterFiberHomForTotalCoverRestrictedCompositeComponentLaw
        (J := J) hSheaf D) :
    projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D :=
  projectionDescentTotalCoverTransitionComponentPullHomLaw_of_restrictedComponent
    (J := J) hSheaf D
    (projectionDescentTotalCoverExplicitMiddleRestrictedComponentLaw_of_restrictedComposite
      (J := J) hSheaf D hcomposite)

/-- Source stage 3.13 frontier after discharging the transition pullback law through the
restricted-composite component reduction.

The remaining fields are closer to the source proof:
* expand the restricted old outer component through the explicit pullback owners;
* prove that the total-cover glued object realizes the original outer descent datum.
-/
structure ProjectionDescentTotalCoverReducedFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) where
  /-- Component expansion for the restricted explicit outer transition. -/
  transitionRestrictedComposite :
    projectionDescentExplicitOuterFiberHomForTotalCoverRestrictedCompositeComponentLaw
      (J := J) hSheaf D
  /-- The glued total-cover object realizes the original outer descent datum. -/
  realizes :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    let hPull :=
      projectionDescentTotalCoverTransitionComponentPullHomLaw_of_restrictedComposite
        (J := J) hSheaf D transitionRestrictedComposite
    let hComp :=
      projectionDescentTotalCoverTransitionComponentHomCompLaw_of_explicit
        (J := J) hSheaf D
        (projectionDescentTotalCoverExplicitTransitionComponentHomCompLaw_of_outer
          (J := J) hSheaf D)
    ((canonicalFiberPseudofunctor P).toDescentData
        (fun I : S.Arrow => I.f)).obj
      (projectionFiberObject (J := J) hSheaf
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D
          hPull hComp)) ≅ D

namespace ProjectionDescentTotalCoverReducedFrontier

/-- The reduced stage 3.13 frontier supplies the full total-cover frontier expected by the
existing descent-effectivity interface. -/
noncomputable def toTotalCoverFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    (H : ProjectionDescentTotalCoverReducedFrontier (J := J) hSheaf D) :
    ProjectionDescentTotalCoverFrontier (J := J) hSheaf D where
  transitionPullHom :=
    projectionDescentTotalCoverTransitionComponentPullHomLaw_of_restrictedComposite
      (J := J) hSheaf D H.transitionRestrictedComposite
  transitionHomComp :=
    projectionDescentTotalCoverTransitionComponentHomCompLaw_of_explicit
      (J := J) hSheaf D
      (projectionDescentTotalCoverExplicitTransitionComponentHomCompLaw_of_outer
        (J := J) hSheaf D)
  realizes := H.realizes

end ProjectionDescentTotalCoverReducedFrontier

/-- Source stage 3.13 frontier for all coverwise descent data, with the transition pullback law
kept at the reduced restricted-composite component surface. -/
structure ProjectionFunctorCoverwiseReducedDescentEffectiveFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X) where
  /-- Apply the reduced total-cover construction to every coverwise descent datum. -/
  reducedTotalCover :
    ∀ (U : C) (S : J.Cover U)
      (D : ProjectionDescentDatum (J := J) hSheaf S),
      ProjectionDescentTotalCoverReducedFrontier (J := J) hSheaf D

namespace ProjectionFunctorCoverwiseReducedDescentEffectiveFrontier

/-- The reduced coverwise frontier supplies the full coverwise descent-effectivity frontier. -/
noncomputable def toTotalCoverFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    (H : ProjectionFunctorCoverwiseReducedDescentEffectiveFrontier (J := J) hSheaf) :
    ProjectionFunctorCoverwiseDescentEffectiveFrontier (J := J) hSheaf where
  totalCover := fun U S D =>
    (H.reducedTotalCover U S D).toTotalCoverFrontier

end ProjectionFunctorCoverwiseReducedDescentEffectiveFrontier

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
