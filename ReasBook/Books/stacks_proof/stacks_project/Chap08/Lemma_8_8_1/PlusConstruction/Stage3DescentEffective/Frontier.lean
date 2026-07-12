import StacksProject_2024.Chap08.Lemma_8_8_1.HomSheaf
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.GluedDatum

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

/-- Source stage 3.13 glued object built from the total-cover transition laws.

This is the formal version of constructing
`X := ({U_ai -> U}, x_ai, rho_(ai)(bj))` once the two source calculations for `rho`
have been supplied. -/
noncomputable def projectionDescentTotalCoverGluedObjectOfTransitionLaws
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hpull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hcomp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D) :
    DescentCompletionObject (J := J) X :=
  projectionDescentTotalCoverGluedObjectOfLaws (J := J) hSheaf D
    (projectionDescentTotalCoverGluedDatumPullHomLaw_of_transitionComponent
      (J := J) hSheaf D hpull)
    (projectionDescentTotalCoverGluedDatumHomCompLaw_of_transitionComponent
      (J := J) hSheaf D hcomp)

/-- Source stage 3.13 frontier for one coverwise descent datum.

The first two fields are exactly the remaining transition calculations for
`rho_(ai)(bj)`.  The last field is the final comparison with the original outer descent datum
`(X_a, Theta_ab)`: the total-cover glued object realizes it under the canonical descent functor.
-/
structure ProjectionDescentTotalCoverFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) where
  /-- Restriction compatibility of the total-cover transition components. -/
  transitionPullHom :
    projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D
  /-- Cocycle compatibility of the total-cover transition components. -/
  transitionHomComp :
    projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D
  /-- The glued total-cover object realizes the original outer descent datum. -/
  realizes :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    ((canonicalFiberPseudofunctor P).toDescentData
        (fun I : S.Arrow => I.f)).obj
      (projectionFiberObject (J := J) hSheaf
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D transitionPullHom transitionHomComp)) ≅ D

namespace ProjectionDescentTotalCoverFrontier

/-- The glued object attached to a one-datum stage 3.13 frontier. -/
noncomputable def gluedObject
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    (H : ProjectionDescentTotalCoverFrontier (J := J) hSheaf D) :
    DescentCompletionObject (J := J) X :=
  projectionDescentTotalCoverGluedObjectOfTransitionLaws
    (J := J) hSheaf D H.transitionPullHom H.transitionHomComp

@[simp]
theorem gluedObject_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X}
    {U : C} {S : J.Cover U}
    {D : ProjectionDescentDatum (J := J) hSheaf S}
    (H : ProjectionDescentTotalCoverFrontier (J := J) hSheaf D) :
    H.gluedObject.base = U :=
  rfl

end ProjectionDescentTotalCoverFrontier

/-- Source stage 3.13 frontier for all coverwise descent data of the completed projection. -/
structure ProjectionFunctorCoverwiseDescentEffectiveFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X) where
  /-- Apply the total-cover construction to every coverwise descent datum. -/
  totalCover :
    ∀ (U : C) (S : J.Cover U)
      (D : ProjectionDescentDatum (J := J) hSheaf S),
      ProjectionDescentTotalCoverFrontier (J := J) hSheaf D

/-- A completed source stage 3.13 total-cover frontier gives coverwise descent effectivity for
the descent-completion projection. -/
theorem projectionFunctorCoverwiseDescentEffective_of_totalCoverFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (H : ProjectionFunctorCoverwiseDescentEffectiveFrontier (J := J) hSheaf) :
    projectionFunctorCoverwiseDescentEffective (J := J) hSheaf := by
  intro U S
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  refine Functor.EssSurj.mk ?_
  intro D
  let HD := H.totalCover U S D
  exact ⟨projectionFiberObject (J := J) hSheaf HD.gluedObject, ⟨HD.realizes⟩⟩

/-- Source-order stage 3 builder: after the Hom-sheaf input for descent-completion morphism
composition and source stage 3.12 are available, the total-cover stage 3.13 frontier supplies the
full `Stage3Frontier`. -/
noncomputable def Stage3Frontier.ofTotalCoverFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    (hHom : projectionFunctorHomPresheavesAreSheaves (J := J) hSheaf)
    (Htotal : ProjectionFunctorCoverwiseDescentEffectiveFrontier (J := J) hSheaf) :
    Stage3Frontier (J := J) X where
  homSheaves := hSheaf
  projectionHomSheaves := hHom
  projectionDescentEffective :=
    projectionFunctorCoverwiseDescentEffective_of_totalCoverFrontier (J := J) hSheaf Htotal

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
