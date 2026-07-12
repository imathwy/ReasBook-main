import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationLocalInverseMiddleRestricted

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

/-- Source stage 3.13 component-expansion obligation for the restricted inverse-realization
middle.

The canonical-owner calculation already proves the fiber-level equality
`eB.hom ≫ g^*theta_ab,ij ≫ eA.inv = theta'_ab,ij`.  The remaining source-faithful owner step is
to identify the component of the left-hand threefold composite with the explicit expression
"source overlap, old restricted component, target overlap" used in the inverse realization
construction. -/
def projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCoverRestrictedCompositeComponentLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) : Prop :=
  ∀ ⦃Y' Y : C⦄ (g : Y' ⟶ Y)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : Y ⟶ K.Y)
    ⦃A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow⦄
    (a : Y ⟶ A.Y)
    (h : k ≫ K.f ≫ I.f = a ≫ A.f)
    (gk : Y' ⟶ K.Y) (ga : Y' ⟶ A.Y)
    (hgk : g ≫ k = gk) (hga : g ≫ a = ga),
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    let IA := projectionDescentTotalCoverOuter (J := J) hSheaf D A
    let OB := projectionDescentDatumObject (J := J) hSheaf D I
    let OA := projectionDescentDatumObject (J := J) hSheaf D IA
    let fB := k ≫ K.f
    let fA := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a
    let fB' := gk ≫ K.f
    let fA' := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga
    let hfB : g ≫ fB = fB' := by
      simp [fB, fB', ← hgk, Category.assoc]
    let hfA : g ≫ fA = fA' := by
      simp [fA, fA', projectionDescentTotalCoverOuterMap, ← hga, Category.assoc]
    let eB := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OB fB g fB' hfB
    let eA := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OA fA g fA' hfA
    let αold :=
      projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
        (J := J) hSheaf D I K k A a h
    let β :=
      eB.hom ≫ ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map αold ≫
        eA.inv
    β.1.components.toHomOver.family
        (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk)
        (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
        (𝟙 Y') (𝟙 Y')
        (by
          have hbase : β.1.base = 𝟙 Y' := by
            letI : P.IsHomLift (𝟙 Y') β.1 := β.2
            have hfac := IsHomLift.fac' P (𝟙 Y') β.1
            simpa [P, projectionFunctor, explicitPullbackFiberObject] using hfac
          rw [hbase]
          dsimp [projectionDescentDatumExplicitPullbackArrow,
            projectionDescentTotalCoverExplicitPullbackArrow]
          calc
            𝟙 Y' ≫ 𝟙 Y' ≫ 𝟙 Y' = 𝟙 Y' ≫ 𝟙 Y' := by rw [Category.id_comp]
            _ = 𝟙 Y' ≫ 𝟙 Y' := rfl) =
      projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCoverOldRestrictedComponent
        (J := J) hSheaf D I K g k A a h gk ga hgk hga

set_option maxHeartbeats 1000000 in
/-- The explicit restricted-component owner law implies the threefold composite component
expansion for the inverse-realization middle.

This is the converse reduction to
`projectionDescentRealizationInverseExplicitMiddleRestrictedComponentLaw_of_restrictedComposite`:
the canonical-owner restriction theorem gives equality of the full threefold composite with the
rebuilt explicit owner, and the restricted-component law identifies that rebuilt component with
the source-text old restricted expression. -/
theorem projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCoverRestrictedCompositeComponentLaw_of_restrictedComponent
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hrestricted :
      projectionDescentRealizationInverseExplicitMiddleRestrictedComponentLaw
        (J := J) hSheaf D) :
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCoverRestrictedCompositeComponentLaw
      (J := J) hSheaf D := by
  intro Y' Y g I K k A a h gk ga hgk hga
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let hsmall : gk ≫ K.f ≫ I.f = ga ≫ A.f := by
    calc
      gk ≫ K.f ≫ I.f = g ≫ k ≫ K.f ≫ I.f := by
        rw [← hgk]
        simp [Category.assoc]
      _ = g ≫ (a ≫ A.f) := by
        simpa [Category.assoc] using congrArg (fun q => g ≫ q) h
      _ = ga ≫ A.f := by rw [← hga]; simp [Category.assoc]
  let IA := projectionDescentTotalCoverOuter (J := J) hSheaf D A
  let OB := projectionDescentDatumObject (J := J) hSheaf D I
  let OA := projectionDescentDatumObject (J := J) hSheaf D IA
  let fB := k ≫ K.f
  let fA := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a
  let fB' := gk ≫ K.f
  let fA' := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga
  let hfB : g ≫ fB = fB' := by
    simp [fB, fB', ← hgk, Category.assoc]
  let hfA : g ≫ fA = fA' := by
    simp [fA, fA', projectionDescentTotalCoverOuterMap, ← hga, Category.assoc]
  let eB := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OB fB g fB' hfB
  let eA := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OA fA g fA' hfA
  let αold :=
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
      (J := J) hSheaf D I K k A a h
  let αnew :=
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
      (J := J) hSheaf D I K gk A ga hsmall
  have hFiber :
      eB.hom ≫ ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map αold ≫
          eA.inv =
        αnew := by
    simpa [P, IA, OB, OA, fB, fA, fB', fA', hfB, hfA, eB, eA, αold, αnew,
      hsmall] using
      projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_restrict
        (J := J) hSheaf D I K g k A a h gk ga hgk hga
  let compOf (β :
      explicitPullbackFiberObject (J := J) hSheaf OB fB' ⟶
        explicitPullbackFiberObject (J := J) hSheaf OA fA') :
      (projectionDescentDatumLocalObject (J := J) hSheaf D I).restrictedLocalObject
          (DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
            (projectionDescentDatumLocalObject (J := J) hSheaf D I) fB'
            (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk))
          (𝟙 Y') ⟶
        (projectionDescentDatumLocalObject (J := J) hSheaf D IA).restrictedLocalObject
          (DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
            (projectionDescentDatumLocalObject (J := J) hSheaf D IA) fA'
            (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga))
          (𝟙 Y') :=
    β.1.components.toHomOver.family
      (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
      (𝟙 Y') (𝟙 Y')
      (by
        have hbase : β.1.base = 𝟙 Y' := by
          letI : P.IsHomLift (𝟙 Y') β.1 := β.2
          have hfac := IsHomLift.fac' P (𝟙 Y') β.1
          simpa [P, projectionFunctor, explicitPullbackFiberObject] using hfac
        rw [hbase]
        dsimp [projectionDescentDatumExplicitPullbackArrow,
          projectionDescentTotalCoverExplicitPullbackArrow]
        calc
          𝟙 Y' ≫ 𝟙 Y' ≫ 𝟙 Y' = 𝟙 Y' ≫ 𝟙 Y' := by rw [Category.id_comp]
          _ = 𝟙 Y' ≫ 𝟙 Y' := rfl)
  have hcomponent := congrArg compOf hFiber
  have hright :
      compOf αnew =
        (let α :=
          projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
            (J := J) hSheaf D I K gk A ga hsmall
        α.1.components.toHomOver.family
          (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk)
          (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
          (𝟙 Y') (𝟙 Y')
          (by
            have hbase :
                α.1.base = 𝟙 Y' :=
              projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_base
                (J := J) hSheaf D I K gk A ga hsmall
            rw [hbase]
            dsimp [projectionDescentDatumExplicitPullbackArrow,
              projectionDescentTotalCoverExplicitPullbackArrow]
            calc
              𝟙 Y' ≫ 𝟙 Y' ≫ 𝟙 Y' = 𝟙 Y' ≫ 𝟙 Y' := by rw [Category.id_comp]
              _ = 𝟙 Y' ≫ 𝟙 Y' := rfl)) := by
    dsimp [compOf, αnew]
  have hres :
      projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCoverOldRestrictedComponent
          (J := J) hSheaf D I K g k A a h gk ga hgk hga =
        (let α :=
          projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
            (J := J) hSheaf D I K gk A ga hsmall
        α.1.components.toHomOver.family
          (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk)
          (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
          (𝟙 Y') (𝟙 Y')
          (by
            have hbase :
                α.1.base = 𝟙 Y' :=
              projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_base
                (J := J) hSheaf D I K gk A ga hsmall
            rw [hbase]
            dsimp [projectionDescentDatumExplicitPullbackArrow,
              projectionDescentTotalCoverExplicitPullbackArrow]
            calc
              𝟙 Y' ≫ 𝟙 Y' ≫ 𝟙 Y' = 𝟙 Y' ≫ 𝟙 Y' := by rw [Category.id_comp]
              _ = 𝟙 Y' ≫ 𝟙 Y' := rfl)) := by
    simpa [projectionDescentRealizationInverseExplicitMiddleRestrictedComponentLaw,
      hsmall] using hrestricted g I K k a h gk ga hgk hga
  exact (hcomponent.trans hright).trans hres.symm

/-- Once the remaining threefold-composite component expansion is supplied, the canonical
fiber-level restriction theorem gives the inverse-realization restricted explicit middle
component law. -/
theorem projectionDescentRealizationInverseExplicitMiddleRestrictedComponentLaw_of_restrictedComposite
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hcomposite :
      projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCoverRestrictedCompositeComponentLaw
        (J := J) hSheaf D) :
    projectionDescentRealizationInverseExplicitMiddleRestrictedComponentLaw
      (J := J) hSheaf D := by
  intro Y' Y g I K k A a h gk ga hgk hga
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let hsmall : gk ≫ K.f ≫ I.f = ga ≫ A.f := by
    calc
      gk ≫ K.f ≫ I.f = g ≫ k ≫ K.f ≫ I.f := by
        rw [← hgk]
        simp [Category.assoc]
      _ = g ≫ (a ≫ A.f) := by
        simpa [Category.assoc] using congrArg (fun q => g ≫ q) h
      _ = ga ≫ A.f := by rw [← hga]; simp [Category.assoc]
  let IA := projectionDescentTotalCoverOuter (J := J) hSheaf D A
  let OB := projectionDescentDatumObject (J := J) hSheaf D I
  let OA := projectionDescentDatumObject (J := J) hSheaf D IA
  let fB := k ≫ K.f
  let fA := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a
  let fB' := gk ≫ K.f
  let fA' := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga
  let hfB : g ≫ fB = fB' := by
    simp [fB, fB', ← hgk, Category.assoc]
  let hfA : g ≫ fA = fA' := by
    simp [fA, fA', projectionDescentTotalCoverOuterMap, ← hga, Category.assoc]
  let eB := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OB fB g fB' hfB
  let eA := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OA fA g fA' hfA
  let αold :=
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
      (J := J) hSheaf D I K k A a h
  let αnew :=
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
      (J := J) hSheaf D I K gk A ga hsmall
  have hFiber :
      eB.hom ≫ ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map αold ≫
          eA.inv =
        αnew := by
    simpa [P, IA, OB, OA, fB, fA, fB', fA', hfB, hfA, eB, eA, αold, αnew,
      hsmall] using
      projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_restrict
        (J := J) hSheaf D I K g k A a h gk ga hgk hga
  let compOf (β :
      explicitPullbackFiberObject (J := J) hSheaf OB fB' ⟶
        explicitPullbackFiberObject (J := J) hSheaf OA fA') :
      (projectionDescentDatumLocalObject (J := J) hSheaf D I).restrictedLocalObject
          (DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
            (projectionDescentDatumLocalObject (J := J) hSheaf D I) fB'
            (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk))
          (𝟙 Y') ⟶
        (projectionDescentDatumLocalObject (J := J) hSheaf D IA).restrictedLocalObject
          (DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
            (projectionDescentDatumLocalObject (J := J) hSheaf D IA) fA'
            (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga))
          (𝟙 Y') :=
    β.1.components.toHomOver.family
      (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
      (𝟙 Y') (𝟙 Y')
      (by
        have hbase : β.1.base = 𝟙 Y' := by
          letI : P.IsHomLift (𝟙 Y') β.1 := β.2
          have hfac := IsHomLift.fac' P (𝟙 Y') β.1
          simpa [P, projectionFunctor, explicitPullbackFiberObject] using hfac
        rw [hbase]
        dsimp [projectionDescentDatumExplicitPullbackArrow,
          projectionDescentTotalCoverExplicitPullbackArrow]
        calc
          𝟙 Y' ≫ 𝟙 Y' ≫ 𝟙 Y' = 𝟙 Y' ≫ 𝟙 Y' := by rw [Category.id_comp]
          _ = 𝟙 Y' ≫ 𝟙 Y' := rfl)
  have hcomponent := congrArg compOf hFiber
  have hleft :
      compOf
          (eB.hom ≫ ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map αold ≫
            eA.inv) =
        projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCoverOldRestrictedComponent
          (J := J) hSheaf D I K g k A a h gk ga hgk hga := by
    simpa [
      projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCoverRestrictedCompositeComponentLaw,
      compOf, P, IA, OB, OA, fB, fA, fB', fA', hfB, hfA, eB, eA, αold] using
      hcomposite g I K k a h gk ga hgk hga
  have hright :
      compOf αnew =
        (let α :=
          projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
            (J := J) hSheaf D I K gk A ga hsmall
        α.1.components.toHomOver.family
          (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk)
          (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
          (𝟙 Y') (𝟙 Y')
          (by
            have hbase :
                α.1.base = 𝟙 Y' :=
              projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_base
                (J := J) hSheaf D I K gk A ga hsmall
            rw [hbase]
            dsimp [projectionDescentDatumExplicitPullbackArrow,
              projectionDescentTotalCoverExplicitPullbackArrow]
            calc
              𝟙 Y' ≫ 𝟙 Y' ≫ 𝟙 Y' = 𝟙 Y' ≫ 𝟙 Y' := by rw [Category.id_comp]
              _ = 𝟙 Y' ≫ 𝟙 Y' := rfl)) := by
    dsimp [compOf, αnew]
  simpa [hsmall] using hleft.symm.trans (hcomponent.trans hright)

/-- The restricted-composite component frontier implies the inverse-realization explicit middle
law. -/
theorem projectionDescentRealizationInverseExplicitMiddlePullHomLaw_of_restrictedComposite
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hcomposite :
      projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCoverRestrictedCompositeComponentLaw
        (J := J) hSheaf D) :
    projectionDescentRealizationInverseExplicitMiddlePullHomLaw (J := J) hSheaf D :=
  projectionDescentRealizationInverseExplicitMiddlePullHomLaw_of_restrictedComponent
    (J := J) hSheaf D
    (projectionDescentRealizationInverseExplicitMiddleRestrictedComponentLaw_of_restrictedComposite
      (J := J) hSheaf D hcomposite)

/-- The restricted-composite component frontier implies the lower-level realization restriction
law for `Lambda_a^{-1}` components. -/
theorem projectionDescentRealizationInverseComponentFromDatumInnerToTotalCoverPullHomLaw_of_restrictedComposite
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hcomposite :
      projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCoverRestrictedCompositeComponentLaw
        (J := J) hSheaf D) :
    projectionDescentRealizationInverseComponentFromDatumInnerToTotalCoverPullHomLaw
      (J := J) hSheaf D :=
  projectionDescentRealizationInverseComponentFromDatumInnerToTotalCoverPullHomLaw_of_explicitMiddle
    (J := J) hSheaf D
    (projectionDescentRealizationInverseExplicitMiddlePullHomLaw_of_restrictedComposite
      (J := J) hSheaf D hcomposite)

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
