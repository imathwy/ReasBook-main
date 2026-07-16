import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationMiddleRestricted

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

/-- Source stage 3.13 component-expansion obligation for the restricted realization middle.

The canonical-owner calculation already proves the fiber-level equality
`eA.hom ≫ g^*theta_ba,ji ≫ eB.inv = theta'_ba,ji`.  The remaining source-faithful owner step is
to identify the component of the left-hand threefold composite with the explicit expression
"source overlap, old restricted component, target overlap" used in the realization construction.
-/
def projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInnerRestrictedCompositeComponentLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) : Prop :=
  ∀ ⦃Y' Y : C⦄ (g : Y' ⟶ Y)
    ⦃A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow⦄
    (I : S.Arrow)
    (a : Y ⟶ A.Y)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : Y ⟶ K.Y)
    (h : a ≫ A.f = k ≫ K.f ≫ I.f)
    (ga : Y' ⟶ A.Y) (gk : Y' ⟶ K.Y)
    (hga : g ≫ a = ga) (hgk : g ≫ k = gk),
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    let IA := projectionDescentTotalCoverOuter (J := J) hSheaf D A
    let OA := projectionDescentDatumObject (J := J) hSheaf D IA
    let OB := projectionDescentDatumObject (J := J) hSheaf D I
    let fA := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a
    let fB := k ≫ K.f
    let fA' := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga
    let fB' := gk ≫ K.f
    let hfA : g ≫ fA = fA' := by
      simp [fA, fA', projectionDescentTotalCoverOuterMap, ← hga, Category.assoc]
    let hfB : g ≫ fB = fB' := by
      simp [fB, fB', ← hgk, Category.assoc]
    let eA := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OA fA g fA' hfA
    let eB := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OB fB g fB' hfB
    let αold :=
      projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
        (J := J) hSheaf D A I a K k h
    let β :=
      eA.hom ≫ ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map αold ≫ eB.inv
    β.1.components.toHomOver.family
        (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
        (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk)
        (𝟙 Y') (𝟙 Y')
        (by
          have hbase : β.1.base = 𝟙 Y' := by
            letI : P.IsHomLift (𝟙 Y') β.1 := β.2
            have hfac := IsHomLift.fac' P (𝟙 Y') β.1
            simpa [P, projectionFunctor, explicitPullbackFiberObject] using hfac
          rw [hbase]
          dsimp [projectionDescentTotalCoverExplicitPullbackArrow,
            projectionDescentDatumExplicitPullbackArrow]
          calc
            𝟙 Y' ≫ 𝟙 Y' ≫ 𝟙 Y' = 𝟙 Y' ≫ 𝟙 Y' := by rw [Category.id_comp]
            _ = 𝟙 Y' ≫ 𝟙 Y' := rfl) =
      projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInnerOldRestrictedComponent
        (J := J) hSheaf D A I g a K k h ga gk hga hgk

set_option maxHeartbeats 1000000 in
/-- The explicit restricted-component owner law implies the threefold composite component
expansion for the realization middle `Lambda_a`.

The canonical-owner restriction theorem identifies the threefold composite with the rebuilt
explicit owner, and the restricted-component law identifies that rebuilt component with the
source-text old restricted expression. -/
theorem projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInnerRestrictedCompositeComponentLaw_of_restrictedComponent
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hrestricted :
      projectionDescentRealizationExplicitMiddleRestrictedComponentLaw
        (J := J) hSheaf D) :
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInnerRestrictedCompositeComponentLaw
      (J := J) hSheaf D := by
  intro Y' Y g A I a K k h ga gk hga hgk
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let hsmall : ga ≫ A.f = gk ≫ K.f ≫ I.f := by
    calc
      ga ≫ A.f = g ≫ a ≫ A.f := by rw [← hga]; simp [Category.assoc]
      _ = g ≫ (k ≫ K.f ≫ I.f) := by
        simpa [Category.assoc] using congrArg (fun q => g ≫ q) h
      _ = gk ≫ K.f ≫ I.f := by rw [← hgk]; simp [Category.assoc]
  let IA := projectionDescentTotalCoverOuter (J := J) hSheaf D A
  let OA := projectionDescentDatumObject (J := J) hSheaf D IA
  let OB := projectionDescentDatumObject (J := J) hSheaf D I
  let fA := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a
  let fB := k ≫ K.f
  let fA' := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga
  let fB' := gk ≫ K.f
  let hfA : g ≫ fA = fA' := by
    simp [fA, fA', projectionDescentTotalCoverOuterMap, ← hga, Category.assoc]
  let hfB : g ≫ fB = fB' := by
    simp [fB, fB', ← hgk, Category.assoc]
  let eA := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OA fA g fA' hfA
  let eB := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OB fB g fB' hfB
  let αold :=
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
      (J := J) hSheaf D A I a K k h
  let αnew :=
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
      (J := J) hSheaf D A I ga K gk hsmall
  have hFiber :
      eA.hom ≫ ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map αold ≫
          eB.inv =
        αnew := by
    simpa [P, IA, OA, OB, fA, fB, fA', fB', hfA, hfB, eA, eB, αold, αnew,
      hsmall] using
      projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_restrict
        (J := J) hSheaf D A I g a K k h ga gk hga hgk
  let compOf (β :
      explicitPullbackFiberObject (J := J) hSheaf OA fA' ⟶
        explicitPullbackFiberObject (J := J) hSheaf OB fB') :
      (projectionDescentDatumLocalObject (J := J) hSheaf D IA).restrictedLocalObject
          (DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
            (projectionDescentDatumLocalObject (J := J) hSheaf D IA) fA'
            (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga))
          (𝟙 Y') ⟶
        (projectionDescentDatumLocalObject (J := J) hSheaf D I).restrictedLocalObject
          (DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
            (projectionDescentDatumLocalObject (J := J) hSheaf D I) fB'
            (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk))
          (𝟙 Y') :=
    β.1.components.toHomOver.family
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
      (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk)
      (𝟙 Y') (𝟙 Y')
      (by
        have hbase : β.1.base = 𝟙 Y' := by
          letI : P.IsHomLift (𝟙 Y') β.1 := β.2
          have hfac := IsHomLift.fac' P (𝟙 Y') β.1
          simpa [P, projectionFunctor, explicitPullbackFiberObject] using hfac
        rw [hbase]
        dsimp [projectionDescentTotalCoverExplicitPullbackArrow,
          projectionDescentDatumExplicitPullbackArrow]
        calc
          𝟙 Y' ≫ 𝟙 Y' ≫ 𝟙 Y' = 𝟙 Y' ≫ 𝟙 Y' := by rw [Category.id_comp]
          _ = 𝟙 Y' ≫ 𝟙 Y' := rfl)
  have hcomponent := congrArg compOf hFiber
  have hright :
      compOf αnew =
        (let α :=
          projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
            (J := J) hSheaf D A I ga K gk hsmall
        α.1.components.toHomOver.family
          (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
          (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk)
          (𝟙 Y') (𝟙 Y')
          (by
            have hbase :
                α.1.base = 𝟙 Y' :=
              projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
                (J := J) hSheaf D A I ga K gk hsmall
            rw [hbase]
            dsimp [projectionDescentTotalCoverExplicitPullbackArrow,
              projectionDescentDatumExplicitPullbackArrow]
            calc
              𝟙 Y' ≫ 𝟙 Y' ≫ 𝟙 Y' = 𝟙 Y' ≫ 𝟙 Y' := by rw [Category.id_comp]
              _ = 𝟙 Y' ≫ 𝟙 Y' := rfl)) := by
    dsimp [compOf, αnew]
  have hres :
      projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInnerOldRestrictedComponent
          (J := J) hSheaf D A I g a K k h ga gk hga hgk =
        (let α :=
          projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
            (J := J) hSheaf D A I ga K gk hsmall
        α.1.components.toHomOver.family
          (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
          (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk)
          (𝟙 Y') (𝟙 Y')
          (by
            have hbase :
                α.1.base = 𝟙 Y' :=
              projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
                (J := J) hSheaf D A I ga K gk hsmall
            rw [hbase]
            dsimp [projectionDescentTotalCoverExplicitPullbackArrow,
              projectionDescentDatumExplicitPullbackArrow]
            calc
              𝟙 Y' ≫ 𝟙 Y' ≫ 𝟙 Y' = 𝟙 Y' ≫ 𝟙 Y' := by rw [Category.id_comp]
              _ = 𝟙 Y' ≫ 𝟙 Y' := rfl)) := by
    simpa [projectionDescentRealizationExplicitMiddleRestrictedComponentLaw,
      hsmall] using hrestricted g I a K k h ga gk hga hgk
  exact (hcomponent.trans hright).trans hres.symm

/-- Once the remaining threefold-composite component expansion is supplied, the canonical
fiber-level restriction theorem gives the realization restricted explicit middle component law. -/
theorem projectionDescentRealizationExplicitMiddleRestrictedComponentLaw_of_restrictedComposite
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hcomposite :
      projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInnerRestrictedCompositeComponentLaw
        (J := J) hSheaf D) :
    projectionDescentRealizationExplicitMiddleRestrictedComponentLaw (J := J) hSheaf D := by
  intro Y' Y g A I a K k h ga gk hga hgk
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let hsmall : ga ≫ A.f = gk ≫ K.f ≫ I.f := by
    calc
      ga ≫ A.f = g ≫ a ≫ A.f := by rw [← hga]; simp [Category.assoc]
      _ = g ≫ (k ≫ K.f ≫ I.f) := by
        simpa [Category.assoc] using congrArg (fun q => g ≫ q) h
      _ = gk ≫ K.f ≫ I.f := by rw [← hgk]; simp [Category.assoc]
  let IA := projectionDescentTotalCoverOuter (J := J) hSheaf D A
  let OA := projectionDescentDatumObject (J := J) hSheaf D IA
  let OB := projectionDescentDatumObject (J := J) hSheaf D I
  let fA := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a
  let fB := k ≫ K.f
  let fA' := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga
  let fB' := gk ≫ K.f
  let hfA : g ≫ fA = fA' := by
    simp [fA, fA', projectionDescentTotalCoverOuterMap, ← hga, Category.assoc]
  let hfB : g ≫ fB = fB' := by
    simp [fB, fB', ← hgk, Category.assoc]
  let eA := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OA fA g fA' hfA
  let eB := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OB fB g fB' hfB
  let αold :=
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
      (J := J) hSheaf D A I a K k h
  let αnew :=
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
      (J := J) hSheaf D A I ga K gk hsmall
  have hFiber :
      eA.hom ≫ ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map αold ≫
          eB.inv =
        αnew := by
    simpa [P, IA, OA, OB, fA, fB, fA', fB', hfA, hfB, eA, eB, αold, αnew,
      hsmall] using
      projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_restrict
        (J := J) hSheaf D A I g a K k h ga gk hga hgk
  let compOf (β :
      explicitPullbackFiberObject (J := J) hSheaf OA fA' ⟶
        explicitPullbackFiberObject (J := J) hSheaf OB fB') :
      (projectionDescentDatumLocalObject (J := J) hSheaf D IA).restrictedLocalObject
          (DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
            (projectionDescentDatumLocalObject (J := J) hSheaf D IA) fA'
            (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga))
          (𝟙 Y') ⟶
        (projectionDescentDatumLocalObject (J := J) hSheaf D I).restrictedLocalObject
          (DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
            (projectionDescentDatumLocalObject (J := J) hSheaf D I) fB'
            (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk))
          (𝟙 Y') :=
    β.1.components.toHomOver.family
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
      (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk)
      (𝟙 Y') (𝟙 Y')
      (by
        have hbase : β.1.base = 𝟙 Y' := by
          letI : P.IsHomLift (𝟙 Y') β.1 := β.2
          have hfac := IsHomLift.fac' P (𝟙 Y') β.1
          simpa [P, projectionFunctor, explicitPullbackFiberObject] using hfac
        rw [hbase]
        dsimp [projectionDescentTotalCoverExplicitPullbackArrow,
          projectionDescentDatumExplicitPullbackArrow]
        calc
          𝟙 Y' ≫ 𝟙 Y' ≫ 𝟙 Y' = 𝟙 Y' ≫ 𝟙 Y' := by rw [Category.id_comp]
          _ = 𝟙 Y' ≫ 𝟙 Y' := rfl)
  have hcomponent := congrArg compOf hFiber
  have hleft :
      compOf
          (eA.hom ≫ ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map αold ≫
            eB.inv) =
        projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInnerOldRestrictedComponent
          (J := J) hSheaf D A I g a K k h ga gk hga hgk := by
    simpa [
      projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInnerRestrictedCompositeComponentLaw,
      compOf, P, IA, OA, OB, fA, fB, fA', fB', hfA, hfB, eA, eB, αold] using
      hcomposite g I a K k h ga gk hga hgk
  have hright :
      compOf αnew =
        (let α :=
          projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
            (J := J) hSheaf D A I ga K gk hsmall
        α.1.components.toHomOver.family
          (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
          (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk)
          (𝟙 Y') (𝟙 Y')
          (by
            have hbase :
                α.1.base = 𝟙 Y' :=
              projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
                (J := J) hSheaf D A I ga K gk hsmall
            rw [hbase]
            dsimp [projectionDescentTotalCoverExplicitPullbackArrow,
              projectionDescentDatumExplicitPullbackArrow]
            calc
              𝟙 Y' ≫ 𝟙 Y' ≫ 𝟙 Y' = 𝟙 Y' ≫ 𝟙 Y' := by rw [Category.id_comp]
              _ = 𝟙 Y' ≫ 𝟙 Y' := rfl)) := by
    dsimp [compOf, αnew]
  simpa [hsmall] using hleft.symm.trans (hcomponent.trans hright)

/-- The restricted-composite component frontier implies the realization explicit middle law. -/
theorem projectionDescentRealizationExplicitMiddlePullHomLaw_of_restrictedComposite
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hcomposite :
      projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInnerRestrictedCompositeComponentLaw
        (J := J) hSheaf D) :
    projectionDescentRealizationExplicitMiddlePullHomLaw (J := J) hSheaf D :=
  projectionDescentRealizationExplicitMiddlePullHomLaw_of_restrictedComponent
    (J := J) hSheaf D
    (projectionDescentRealizationExplicitMiddleRestrictedComponentLaw_of_restrictedComposite
      (J := J) hSheaf D hcomposite)

/-- The restricted-composite component frontier implies the lower-level realization restriction
law for `Lambda_a` components. -/
theorem projectionDescentRealizationComponentFromTotalCoverToDatumInnerPullHomLaw_of_restrictedComposite
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hcomposite :
      projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInnerRestrictedCompositeComponentLaw
        (J := J) hSheaf D) :
    projectionDescentRealizationComponentFromTotalCoverToDatumInnerPullHomLaw
      (J := J) hSheaf D :=
  projectionDescentRealizationComponentFromTotalCoverToDatumInnerPullHomLaw_of_explicitMiddle
    (J := J) hSheaf D
    (projectionDescentRealizationExplicitMiddlePullHomLaw_of_restrictedComposite
      (J := J) hSheaf D hcomposite)

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
