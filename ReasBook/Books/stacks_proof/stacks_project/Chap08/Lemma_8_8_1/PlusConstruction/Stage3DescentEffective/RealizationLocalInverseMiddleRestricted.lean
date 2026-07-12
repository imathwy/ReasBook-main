import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationLocalInverseMiddleRestrictedCanonical

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

/-- The old explicit outer component used in `Lambda_a^{-1}`, evaluated at the cover arrows
obtained by restricting the old explicit pullback covers along `g`, and transported to the
directly rebuilt `Knew`/`IAnew` owners. -/
noncomputable def projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCoverOldRestrictedComponent
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (g : Y' ⟶ Y)
    (k : Y ⟶ K.Y)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : Y ⟶ A.Y)
    (h : k ≫ K.f ≫ I.f = a ≫ A.f)
    (gk : Y' ⟶ K.Y) (ga : Y' ⟶ A.Y)
    (hgk : g ≫ k = gk) (hga : g ≫ a = ga) :
    let DB := projectionDescentDatumLocalObject (J := J) hSheaf D I
    let DA :=
      projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
    let Knew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      DB (gk ≫ K.f)
      (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk)
    let IAnew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
    DB.restrictedLocalObject Knew (𝟙 Y') ⟶
      DA.restrictedLocalObject IAnew (𝟙 Y') := by
  letI := category (J := J) hSheaf
  let DB := projectionDescentDatumLocalObject (J := J) hSheaf D I
  let DA :=
    projectionDescentDatumLocalObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
  let Knew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DB (gk ≫ K.f)
    (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk)
  let IAnew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
  let Kres :=
    projectionDescentDatumExplicitPullbackArrowAlong
      (J := J) hSheaf D I K g k gk hgk
  let IAres :=
    projectionDescentTotalCoverExplicitPullbackArrowAlong
      (J := J) hSheaf D A g a ga hga
  let KresBase := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DB (k ≫ K.f) Kres
  let IAresBase := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a) IAres
  let α :=
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
      (J := J) hSheaf D I K k A a h
  let sourceCast :
      DB.restrictedLocalObject Knew (𝟙 Y') ⟶
        DB.restrictedLocalObject KresBase (𝟙 Y') :=
    (DB.overlapIso (I₁ := Knew) (I₂ := KresBase) (𝟙 Y') (𝟙 Y') (by
      dsimp [Knew, KresBase, Kres, projectionDescentDatumExplicitPullbackArrowAlong,
        projectionDescentDatumExplicitPullbackArrow,
        DescentCompletionObjectOver.pullbackCoverBaseArrow]
      rw [← hgk]
      simp [Category.assoc])).hom
  let targetCast :
      DA.restrictedLocalObject IAresBase (𝟙 Y') ⟶
        DA.restrictedLocalObject IAnew (𝟙 Y') :=
    (DA.overlapIso (I₁ := IAresBase) (I₂ := IAnew) (𝟙 Y') (𝟙 Y') (by
      dsimp [IAnew, IAresBase, IAres, projectionDescentTotalCoverExplicitPullbackArrowAlong,
        projectionDescentTotalCoverExplicitPullbackArrow,
        DescentCompletionObjectOver.pullbackCoverBaseArrow, projectionDescentTotalCoverOuterMap]
      rw [← hga]
      simp [Category.assoc])).hom
  exact sourceCast ≫
    α.1.components.toHomOver.family Kres IAres (𝟙 Y') (𝟙 Y')
      (by
        have hbase :
            α.1.base = 𝟙 Y :=
          projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_base
            (J := J) hSheaf D I K k A a h
        rw [hbase]
        dsimp [Kres, IAres, projectionDescentDatumExplicitPullbackArrowAlong,
          projectionDescentTotalCoverExplicitPullbackArrowAlong]
        calc
          𝟙 Y' ≫ g ≫ 𝟙 Y = (𝟙 Y' ≫ g) ≫ 𝟙 Y := by
            rw [← Category.assoc]
          _ = 𝟙 Y' ≫ g := Category.comp_id _) ≫
    targetCast

/-- The remaining component owner-identification after the old-cover compatibility square:
the old inverse-realization outer component evaluated on the restricted old explicit-cover
arrows agrees with the component rebuilt directly over `(gk, ga)`. -/
def projectionDescentRealizationInverseExplicitMiddleRestrictedComponentLaw
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
    let hsmall : gk ≫ K.f ≫ I.f = ga ≫ A.f := by
      calc
        gk ≫ K.f ≫ I.f = g ≫ k ≫ K.f ≫ I.f := by
          rw [← hgk]
          simp [Category.assoc]
        _ = g ≫ (a ≫ A.f) := by
          simpa [Category.assoc] using congrArg (fun q => g ≫ q) h
        _ = ga ≫ A.f := by rw [← hga]; simp [Category.assoc]
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
            _ = 𝟙 Y' ≫ 𝟙 Y' := rfl))

/-- The restricted-component owner bridge plus the ordinary compatibility square for the old
explicit pullback covers gives the inverse-realization explicit middle pullback law. -/
theorem projectionDescentRealizationInverseExplicitMiddlePullHomLaw_of_restrictedComponent
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hrestricted :
      projectionDescentRealizationInverseExplicitMiddleRestrictedComponentLaw (J := J)
        hSheaf D) :
    projectionDescentRealizationInverseExplicitMiddlePullHomLaw (J := J) hSheaf D := by
  intro Y' Y g I K k A a h gk ga hgk hga
  letI := category (J := J) hSheaf
  let hsmall : gk ≫ K.f ≫ I.f = ga ≫ A.f := by
    calc
      gk ≫ K.f ≫ I.f = g ≫ k ≫ K.f ≫ I.f := by
        rw [← hgk]
        simp [Category.assoc]
      _ = g ≫ (a ≫ A.f) := by
        simpa [Category.assoc] using congrArg (fun q => g ≫ q) h
      _ = ga ≫ A.f := by rw [← hga]; simp [Category.assoc]
  let DB := projectionDescentDatumLocalObject (J := J) hSheaf D I
  let DA :=
    projectionDescentDatumLocalObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
  let KoldArrow :=
    projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k
  let IAoldArrow :=
    projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a
  let Kres :=
    projectionDescentDatumExplicitPullbackArrowAlong
      (J := J) hSheaf D I K g k gk hgk
  let IAres :=
    projectionDescentTotalCoverExplicitPullbackArrowAlong
      (J := J) hSheaf D A g a ga hga
  let Kold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DB (k ≫ K.f) KoldArrow
  let IAold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a) IAoldArrow
  let KresBase := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DB (k ≫ K.f) Kres
  let IAresBase := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a) IAres
  let Knew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DB (gk ≫ K.f)
    (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk)
  let IAnew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
  let hKoldNew : g ≫ Kold.f = 𝟙 Y' ≫ Knew.f := by
    dsimp [Kold, Knew, KoldArrow, DB, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentDatumExplicitPullbackArrow]
    rw [← hgk]
    simp [Category.assoc]
  let hKnewRes : 𝟙 Y' ≫ Knew.f = 𝟙 Y' ≫ KresBase.f := by
    dsimp [Knew, KresBase, Kres, projectionDescentDatumExplicitPullbackArrowAlong,
      projectionDescentDatumExplicitPullbackArrow,
      DB, DescentCompletionObjectOver.pullbackCoverBaseArrow]
    rw [← hgk]
    simp [Category.assoc]
  let hKoldRes : g ≫ Kold.f = 𝟙 Y' ≫ KresBase.f := hKoldNew.trans hKnewRes
  let hAoldNew : g ≫ IAold.f = 𝟙 Y' ≫ IAnew.f := by
    dsimp [IAold, IAnew, IAoldArrow, DA, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentTotalCoverOuterMap]
    rw [← hga]
    simp [Category.assoc]
  let hAresNew : 𝟙 Y' ≫ IAresBase.f = 𝟙 Y' ≫ IAnew.f := by
    dsimp [IAnew, IAresBase, IAres, projectionDescentTotalCoverExplicitPullbackArrowAlong,
      projectionDescentTotalCoverExplicitPullbackArrow,
      DescentCompletionObjectOver.pullbackCoverBaseArrow, projectionDescentTotalCoverOuterMap]
    rw [← hga]
    simp [Category.assoc]
  let hAoldRes : g ≫ IAold.f = 𝟙 Y' ≫ IAresBase.f := hAoldNew.trans hAresNew.symm
  let hKpb : g ≫ KoldArrow.f = 𝟙 Y' ≫ Kres.f := by
    dsimp [KoldArrow, Kres, projectionDescentDatumExplicitPullbackArrow,
      projectionDescentDatumExplicitPullbackArrowAlong]
    exact (Category.comp_id g).trans (Category.id_comp g).symm
  let hApb : g ≫ IAoldArrow.f = 𝟙 Y' ≫ IAres.f := by
    dsimp [IAoldArrow, IAres, projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentTotalCoverExplicitPullbackArrowAlong]
    exact (Category.comp_id g).trans (Category.id_comp g).symm
  let αold :=
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
      (J := J) hSheaf D I K k A a h
  let αnew :=
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
      (J := J) hSheaf D I K gk A ga hsmall
  let midOld :=
    αold.1.components.toHomOver.family KoldArrow IAoldArrow g g
      (by
        have hbase :
            αold.1.base = 𝟙 Y :=
          projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_base
            (J := J) hSheaf D I K k A a h
        rw [hbase]
        dsimp [KoldArrow, IAoldArrow, projectionDescentDatumExplicitPullbackArrow,
          projectionDescentTotalCoverExplicitPullbackArrow]
        exact (Category.assoc g (𝟙 Y) (𝟙 Y)).symm.trans
          (Category.comp_id (g ≫ 𝟙 Y)))
  let restrictedCore :=
    αold.1.components.toHomOver.family Kres IAres (𝟙 Y') (𝟙 Y')
      (by
        have hbase :
            αold.1.base = 𝟙 Y :=
          projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_base
            (J := J) hSheaf D I K k A a h
        rw [hbase]
        dsimp [Kres, IAres, projectionDescentDatumExplicitPullbackArrowAlong,
          projectionDescentTotalCoverExplicitPullbackArrowAlong]
        calc
          𝟙 Y' ≫ g ≫ 𝟙 Y = (𝟙 Y' ≫ g) ≫ 𝟙 Y := by
            rw [← Category.assoc]
          _ = 𝟙 Y' ≫ g := Category.comp_id _)
  let midNew :=
    αnew.1.components.toHomOver.family
      (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
      (𝟙 Y') (𝟙 Y')
      (by
        have hbase :
            αnew.1.base = 𝟙 Y' :=
          projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_base
            (J := J) hSheaf D I K gk A ga hsmall
        rw [hbase]
        dsimp [projectionDescentDatumExplicitPullbackArrow,
          projectionDescentTotalCoverExplicitPullbackArrow]
        calc
          𝟙 Y' ≫ 𝟙 Y' ≫ 𝟙 Y' = 𝟙 Y' ≫ 𝟙 Y' := by rw [Category.id_comp]
          _ = 𝟙 Y' ≫ 𝟙 Y' := rfl)
  let sourceOldNew := (DB.overlapIso (I₁ := Kold) (I₂ := Knew) g (𝟙 Y') hKoldNew).hom
  let sourceNewRes := (DB.overlapIso (I₁ := Knew) (I₂ := KresBase)
    (𝟙 Y') (𝟙 Y') hKnewRes).hom
  let sourceOldRes := (DB.overlapIso (I₁ := Kold) (I₂ := KresBase)
    g (𝟙 Y') hKoldRes).hom
  let targetOldRes := (DA.overlapIso (I₁ := IAold) (I₂ := IAresBase)
    g (𝟙 Y') hAoldRes).hom
  let targetResNew := (DA.overlapIso (I₁ := IAresBase) (I₂ := IAnew)
    (𝟙 Y') (𝟙 Y') hAresNew).hom
  let targetOldNew := (DA.overlapIso (I₁ := IAold) (I₂ := IAnew)
    g (𝟙 Y') hAoldNew).hom
  have hsourcePull :
      ((DescentCompletionObjectOver.pullback (J := J) DB
        (k ≫ K.f)).overlapIso
          (I₁ := KoldArrow) (I₂ := Kres) g (𝟙 Y') hKpb).hom =
        sourceOldRes := by
    simpa [sourceOldRes, hKoldRes, Kold, KresBase, KoldArrow, Kres] using
      DescentCompletionObjectOver.pullback_overlapIso_hom (J := J) DB
        (k ≫ K.f) KoldArrow Kres g (𝟙 Y') hKpb
  have htargetPull :
      ((DescentCompletionObjectOver.pullback (J := J) DA
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)).overlapIso
          (I₁ := IAoldArrow) (I₂ := IAres) g (𝟙 Y') hApb).hom =
        targetOldRes := by
    simpa [targetOldRes, hAoldRes, IAold, IAresBase, IAoldArrow, IAres] using
      DescentCompletionObjectOver.pullback_overlapIso_hom (J := J) DA
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
        IAoldArrow IAres g (𝟙 Y') hApb
  have hcompatPull :
      ((DescentCompletionObjectOver.pullback (J := J) DB
        (k ≫ K.f)).overlapIso
          (I₁ := KoldArrow) (I₂ := Kres) g (𝟙 Y') hKpb).hom ≫
        restrictedCore =
      midOld ≫
        ((DescentCompletionObjectOver.pullback (J := J) DA
          (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)).overlapIso
            (I₁ := IAoldArrow) (I₂ := IAres) g (𝟙 Y') hApb).hom := by
    simpa [midOld, restrictedCore, hKpb, hApb] using
      αold.1.components.toHomOver.compatible
        KoldArrow Kres IAoldArrow IAres
        g (𝟙 Y') g (𝟙 Y')
        hKpb hApb
        (by
          have hbase :
              αold.1.base = 𝟙 Y :=
            projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_base
              (J := J) hSheaf D I K k A a h
          rw [hbase]
          dsimp [KoldArrow, IAoldArrow, projectionDescentDatumExplicitPullbackArrow,
            projectionDescentTotalCoverExplicitPullbackArrow]
          exact (Category.assoc g (𝟙 Y) (𝟙 Y)).symm.trans
            (Category.comp_id (g ≫ 𝟙 Y)))
        (by
          have hbase :
              αold.1.base = 𝟙 Y :=
            projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_base
              (J := J) hSheaf D I K k A a h
          rw [hbase]
          dsimp [Kres, IAres, projectionDescentDatumExplicitPullbackArrowAlong,
            projectionDescentTotalCoverExplicitPullbackArrowAlong]
          calc
            𝟙 Y' ≫ g ≫ 𝟙 Y = (𝟙 Y' ≫ g) ≫ 𝟙 Y := by
              rw [← Category.assoc]
            _ = 𝟙 Y' ≫ g := Category.comp_id _)
  have hcompat : sourceOldRes ≫ restrictedCore = midOld ≫ targetOldRes := by
    simpa [hsourcePull, htargetPull] using hcompatPull
  have hsourceComp : sourceOldNew ≫ sourceNewRes = sourceOldRes := by
    simpa [sourceOldNew, sourceNewRes, sourceOldRes, hKoldNew, hKnewRes, hKoldRes] using
      DescentCompletionObjectOver.overlapIso_hom_comp (J := J) DB
        (I₁ := Kold) (I₂ := Knew) (I₃ := KresBase)
        g (𝟙 Y') (𝟙 Y') hKoldNew hKnewRes
  have htargetComp : targetOldRes ≫ targetResNew = targetOldNew := by
    simpa [targetOldRes, targetResNew, targetOldNew, hAoldRes, hAresNew, hAoldNew] using
      DescentCompletionObjectOver.overlapIso_hom_comp (J := J) DA
        (I₁ := IAold) (I₂ := IAresBase) (I₃ := IAnew)
        g (𝟙 Y') (𝟙 Y') hAoldRes hAresNew
  have hresEq : (sourceNewRes ≫ restrictedCore) ≫ targetResNew = midNew := by
    simpa [projectionDescentRealizationInverseExplicitMiddleRestrictedComponentLaw,
      projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCoverOldRestrictedComponent,
      hsmall, DB, DA, Knew, IAnew, Kres, IAres, KresBase, IAresBase,
      αold, αnew, sourceNewRes, targetResNew, restrictedCore, midNew] using
      hrestricted g I K k a h gk ga hgk hga
  change midOld ≫ targetOldNew = sourceOldNew ≫ midNew
  rw [← hresEq]
  calc
    midOld ≫ targetOldNew =
        midOld ≫ (targetOldRes ≫ targetResNew) := by
          exact congrArg (fun q => midOld ≫ q) htargetComp.symm
    _ = (midOld ≫ targetOldRes) ≫ targetResNew := by
      rw [Category.assoc]
    _ = (sourceOldRes ≫ restrictedCore) ≫ targetResNew := by
      exact congrArg (fun q => q ≫ targetResNew) hcompat.symm
    _ = ((sourceOldNew ≫ sourceNewRes) ≫ restrictedCore) ≫ targetResNew := by
      exact congrArg (fun q => (q ≫ restrictedCore) ≫ targetResNew) hsourceComp.symm
    _ = sourceOldNew ≫ ((sourceNewRes ≫ restrictedCore) ≫ targetResNew) := by
      simp [Category.assoc]

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
