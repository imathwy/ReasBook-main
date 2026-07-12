import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.ExplicitMiddleBridge
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.ExplicitMiddleRestrictedCore

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

/-- The restricted-component owner bridge plus the ordinary compatibility square for the old
explicit pullback covers gives the explicit middle pullback law. -/
theorem projectionDescentTotalCoverExplicitMiddlePullHomLaw_of_restrictedComponent
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hrestricted :
      projectionDescentTotalCoverExplicitMiddleRestrictedComponentLaw (J := J) hSheaf D) :
    projectionDescentTotalCoverExplicitMiddlePullHomLaw (J := J) hSheaf D := by
  intro Y' Y g A B a b h ga gb hga hgb
  letI := category (J := J) hSheaf
  let hsmall : ga ≫ A.f = gb ≫ B.f := by
    calc
      ga ≫ A.f = g ≫ a ≫ A.f := by rw [← hga]; simp [Category.assoc]
      _ = g ≫ b ≫ B.f := by
        simpa [Category.assoc] using congrArg (fun q => g ≫ q) h
      _ = gb ≫ B.f := by rw [← hgb]; simp [Category.assoc]
  let DA :=
    projectionDescentDatumLocalObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
  let DB :=
    projectionDescentDatumLocalObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D B)
  let IAoldArrow :=
    projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a
  let IBoldArrow :=
    projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B b
  let IAres :=
    projectionDescentTotalCoverExplicitPullbackArrowAlong
      (J := J) hSheaf D A g a ga hga
  let IBres :=
    projectionDescentTotalCoverExplicitPullbackArrowAlong
      (J := J) hSheaf D B g b gb hgb
  let IAold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a) IAoldArrow
  let IBold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DB (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b) IBoldArrow
  let IAresBase := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a) IAres
  let IBresBase := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DB (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b) IBres
  let IAnew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
  let IBnew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DB (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B gb)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B gb)
  let hAoldNew : g ≫ IAold.f = 𝟙 Y' ≫ IAnew.f := by
    dsimp [IAold, IAnew, IAoldArrow, DA, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentTotalCoverOuterMap]
    rw [← hga]
    simp [Category.assoc]
  let hAnewRes : 𝟙 Y' ≫ IAnew.f = 𝟙 Y' ≫ IAresBase.f := by
    dsimp [IAnew, IAresBase, IAres, projectionDescentTotalCoverExplicitPullbackArrowAlong,
      projectionDescentTotalCoverExplicitPullbackArrow,
      DescentCompletionObjectOver.pullbackCoverBaseArrow, projectionDescentTotalCoverOuterMap]
    rw [← hga]
    simp [Category.assoc]
  let hAoldRes : g ≫ IAold.f = 𝟙 Y' ≫ IAresBase.f := hAoldNew.trans hAnewRes
  let hBoldRes : g ≫ IBold.f = 𝟙 Y' ≫ IBresBase.f := by
    dsimp [IBold, IBresBase, IBoldArrow, IBres,
      projectionDescentTotalCoverExplicitPullbackArrowAlong,
      projectionDescentTotalCoverExplicitPullbackArrow,
      DB, DescentCompletionObjectOver.pullbackCoverBaseArrow, projectionDescentTotalCoverOuterMap]
    simp
  let hBresNew : 𝟙 Y' ≫ IBresBase.f = 𝟙 Y' ≫ IBnew.f := by
    dsimp [IBnew, IBresBase, IBres, projectionDescentTotalCoverExplicitPullbackArrowAlong,
      projectionDescentTotalCoverExplicitPullbackArrow,
      DB, DescentCompletionObjectOver.pullbackCoverBaseArrow, projectionDescentTotalCoverOuterMap]
    rw [← hgb]
    simp [Category.assoc]
  let hBoldNew : g ≫ IBold.f = 𝟙 Y' ≫ IBnew.f := hBoldRes.trans hBresNew
  let hApb : g ≫ IAoldArrow.f = 𝟙 Y' ≫ IAres.f := by
    dsimp [IAoldArrow, IAres, projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentTotalCoverExplicitPullbackArrowAlong]
    exact (Category.comp_id g).trans (Category.id_comp g).symm
  let hBpb : g ≫ IBoldArrow.f = 𝟙 Y' ≫ IBres.f := by
    dsimp [IBoldArrow, IBres, projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentTotalCoverExplicitPullbackArrowAlong]
    exact (Category.comp_id g).trans (Category.id_comp g).symm
  let αold :=
    projectionDescentExplicitOuterFiberHomForTotalCover (J := J)
      hSheaf D A B a b h
  let αnew :=
    projectionDescentExplicitOuterFiberHomForTotalCover (J := J)
      hSheaf D A B ga gb hsmall
  let midOld :=
    αold.1.components.toHomOver.family IAoldArrow IBoldArrow g g
      (by
        have hbase :
            αold.1.base = 𝟙 Y :=
          projectionDescentExplicitOuterFiberHomForTotalCover_base
            (J := J) hSheaf D A B a b h
        rw [hbase]
        dsimp [IAoldArrow, IBoldArrow, projectionDescentTotalCoverExplicitPullbackArrow]
        exact (Category.assoc g (𝟙 Y) (𝟙 Y)).symm.trans
          (Category.comp_id (g ≫ 𝟙 Y)))
  let restrictedCore :=
    αold.1.components.toHomOver.family IAres IBres (𝟙 Y') (𝟙 Y')
      (by
        have hbase :
            αold.1.base = 𝟙 Y :=
          projectionDescentExplicitOuterFiberHomForTotalCover_base
            (J := J) hSheaf D A B a b h
        rw [hbase]
        dsimp [IAres, IBres, projectionDescentTotalCoverExplicitPullbackArrowAlong]
        calc
          𝟙 Y' ≫ g ≫ 𝟙 Y = (𝟙 Y' ≫ g) ≫ 𝟙 Y := by
            rw [← Category.assoc]
          _ = 𝟙 Y' ≫ g := Category.comp_id _)
  let midNew :=
    αnew.1.components.toHomOver.family
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B gb)
      (𝟙 Y') (𝟙 Y')
      (by
        have hbase :
            αnew.1.base = 𝟙 Y' :=
          projectionDescentExplicitOuterFiberHomForTotalCover_base
            (J := J) hSheaf D A B ga gb hsmall
        rw [hbase]
        dsimp [projectionDescentTotalCoverExplicitPullbackArrow]
        calc
          𝟙 Y' ≫ 𝟙 Y' ≫ 𝟙 Y' = 𝟙 Y' ≫ 𝟙 Y' := by rw [Category.id_comp]
          _ = 𝟙 Y' ≫ 𝟙 Y' := rfl)
  let sourceOldNew := (DA.overlapIso (I₁ := IAold) (I₂ := IAnew) g (𝟙 Y') hAoldNew).hom
  let sourceNewRes := (DA.overlapIso (I₁ := IAnew) (I₂ := IAresBase)
    (𝟙 Y') (𝟙 Y') hAnewRes).hom
  let sourceOldRes := (DA.overlapIso (I₁ := IAold) (I₂ := IAresBase)
    g (𝟙 Y') hAoldRes).hom
  let targetOldRes := (DB.overlapIso (I₁ := IBold) (I₂ := IBresBase)
    g (𝟙 Y') hBoldRes).hom
  let targetResNew := (DB.overlapIso (I₁ := IBresBase) (I₂ := IBnew)
    (𝟙 Y') (𝟙 Y') hBresNew).hom
  let targetOldNew := (DB.overlapIso (I₁ := IBold) (I₂ := IBnew)
    g (𝟙 Y') hBoldNew).hom
  have hsourcePull :
      ((DescentCompletionObjectOver.pullback (J := J) DA
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)).overlapIso
          (I₁ := IAoldArrow) (I₂ := IAres) g (𝟙 Y') hApb).hom =
        sourceOldRes := by
    simpa [sourceOldRes, hAoldRes, IAold, IAresBase, IAoldArrow, IAres] using
      DescentCompletionObjectOver.pullback_overlapIso_hom (J := J) DA
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
        IAoldArrow IAres g (𝟙 Y') hApb
  have htargetPull :
      ((DescentCompletionObjectOver.pullback (J := J) DB
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b)).overlapIso
          (I₁ := IBoldArrow) (I₂ := IBres) g (𝟙 Y') hBpb).hom =
        targetOldRes := by
    simpa [targetOldRes, hBoldRes, IBold, IBresBase, IBoldArrow, IBres] using
      DescentCompletionObjectOver.pullback_overlapIso_hom (J := J) DB
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b)
        IBoldArrow IBres g (𝟙 Y') hBpb
  have hcompatPull :
      ((DescentCompletionObjectOver.pullback (J := J) DA
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)).overlapIso
          (I₁ := IAoldArrow) (I₂ := IAres) g (𝟙 Y') hApb).hom ≫
        restrictedCore =
      midOld ≫
        ((DescentCompletionObjectOver.pullback (J := J) DB
          (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b)).overlapIso
            (I₁ := IBoldArrow) (I₂ := IBres) g (𝟙 Y') hBpb).hom := by
    simpa [midOld, restrictedCore, hApb, hBpb] using
      αold.1.components.toHomOver.compatible
        IAoldArrow IAres IBoldArrow IBres
        g (𝟙 Y') g (𝟙 Y')
        hApb hBpb
        (by
          have hbase :
              αold.1.base = 𝟙 Y :=
            projectionDescentExplicitOuterFiberHomForTotalCover_base
              (J := J) hSheaf D A B a b h
          rw [hbase]
          dsimp [IAoldArrow, IBoldArrow, projectionDescentTotalCoverExplicitPullbackArrow]
          exact (Category.assoc g (𝟙 Y) (𝟙 Y)).symm.trans
            (Category.comp_id (g ≫ 𝟙 Y)))
        (by
          have hbase :
              αold.1.base = 𝟙 Y :=
            projectionDescentExplicitOuterFiberHomForTotalCover_base
              (J := J) hSheaf D A B a b h
          rw [hbase]
          dsimp [IAres, IBres, projectionDescentTotalCoverExplicitPullbackArrowAlong]
          calc
            𝟙 Y' ≫ g ≫ 𝟙 Y = (𝟙 Y' ≫ g) ≫ 𝟙 Y := by
              rw [← Category.assoc]
            _ = 𝟙 Y' ≫ g := Category.comp_id _)
  have hcompat : sourceOldRes ≫ restrictedCore = midOld ≫ targetOldRes := by
    simpa [hsourcePull, htargetPull] using hcompatPull
  have hsourceComp : sourceOldNew ≫ sourceNewRes = sourceOldRes := by
    simpa [sourceOldNew, sourceNewRes, sourceOldRes, hAoldNew, hAnewRes, hAoldRes] using
      DescentCompletionObjectOver.overlapIso_hom_comp (J := J) DA
        (I₁ := IAold) (I₂ := IAnew) (I₃ := IAresBase)
        g (𝟙 Y') (𝟙 Y') hAoldNew hAnewRes
  have htargetComp : targetOldRes ≫ targetResNew = targetOldNew := by
    simpa [targetOldRes, targetResNew, targetOldNew, hBoldRes, hBresNew, hBoldNew] using
      DescentCompletionObjectOver.overlapIso_hom_comp (J := J) DB
        (I₁ := IBold) (I₂ := IBresBase) (I₃ := IBnew)
        g (𝟙 Y') (𝟙 Y') hBoldRes hBresNew
  have hresEq : (sourceNewRes ≫ restrictedCore) ≫ targetResNew = midNew := by
    simpa [projectionDescentTotalCoverExplicitMiddleRestrictedComponentLaw,
      projectionDescentExplicitOuterFiberHomForTotalCoverOldRestrictedComponent,
      hsmall, DA, DB, IAnew, IBnew, IAres, IBres, IAresBase, IBresBase,
      αold, αnew, sourceNewRes, targetResNew, restrictedCore, midNew] using
      hrestricted g a b h ga gb hga hgb
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
