import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.ThreeFactorBridge

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

/-- Source stage 3.13 middle owner bridge for the explicit outer component.

This is the narrowed remaining coherence statement after the source and target local-restriction
factors have been collapsed.  It says that the explicit outer component for `(a,b)`, restricted
along `g`, agrees with the explicit outer component rebuilt directly for `(ga,gb)`, after the
source and target explicit pullback cover owners are compared by the descent-completion overlap
maps. -/
def projectionDescentTotalCoverExplicitMiddlePullHomLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) : Prop :=
  ∀ ⦃Y' Y : C⦄ (g : Y' ⟶ Y)
    ⦃A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow⦄
    (a : Y ⟶ A.Y) (b : Y ⟶ B.Y)
    (h : a ≫ A.f = b ≫ B.f)
    (ga : Y' ⟶ A.Y) (gb : Y' ⟶ B.Y)
    (hga : g ≫ a = ga) (hgb : g ≫ b = gb),
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
    let IAold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
    let IBold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      DB (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B b)
    let IAnew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
    let IBnew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      DB (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B gb)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B gb)
    let hAoldNew : g ≫ IAold.f = 𝟙 Y' ≫ IAnew.f := by
      dsimp [IAold, IAnew, DA, DescentCompletionObjectOver.pullbackCoverBaseArrow,
        projectionDescentTotalCoverExplicitPullbackArrow,
        projectionDescentTotalCoverOuterMap]
      rw [← hga]
      simp [Category.assoc]
    let hBoldNew : g ≫ IBold.f = 𝟙 Y' ≫ IBnew.f := by
      dsimp [IBold, IBnew, DB, DescentCompletionObjectOver.pullbackCoverBaseArrow,
        projectionDescentTotalCoverExplicitPullbackArrow,
        projectionDescentTotalCoverOuterMap]
      rw [← hgb]
      simp [Category.assoc]
    (let α :=
      projectionDescentExplicitOuterFiberHomForTotalCover (J := J)
        hSheaf D A B a b h
    α.1.components.toHomOver.family
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B b)
      g g
      (by
        have hbase :
            α.1.base = 𝟙 Y :=
          projectionDescentExplicitOuterFiberHomForTotalCover_base
            (J := J) hSheaf D A B a b h
        rw [hbase]
        dsimp [projectionDescentTotalCoverExplicitPullbackArrow]
        exact (Category.assoc g (𝟙 Y) (𝟙 Y)).symm.trans
          (Category.comp_id (g ≫ 𝟙 Y)))) ≫
        (DB.overlapIso (I₁ := IBold) (I₂ := IBnew) g (𝟙 Y') hBoldNew).hom =
      (DA.overlapIso (I₁ := IAold) (I₂ := IAnew) g (𝟙 Y') hAoldNew).hom ≫
        (let α :=
          projectionDescentExplicitOuterFiberHomForTotalCover (J := J)
            hSheaf D A B ga gb hsmall
        α.1.components.toHomOver.family
          (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
          (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B gb)
          (𝟙 Y') (𝟙 Y')
          (by
            have hbase :
                α.1.base = 𝟙 Y' :=
              projectionDescentExplicitOuterFiberHomForTotalCover_base
                (J := J) hSheaf D A B ga gb hsmall
            rw [hbase]
            dsimp [projectionDescentTotalCoverExplicitPullbackArrow]
            calc
              𝟙 Y' ≫ 𝟙 Y' ≫ 𝟙 Y' = 𝟙 Y' ≫ 𝟙 Y' := by rw [Category.id_comp]
              _ = 𝟙 Y' ≫ 𝟙 Y' := rfl))

/-- The middle explicit-owner square implies the three-factor transition bridge. -/
theorem projectionDescentTotalCoverTransitionComponentThreeFactorPullHomLaw_of_explicitMiddle
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hmiddle :
      projectionDescentTotalCoverExplicitMiddlePullHomLaw (J := J) hSheaf D) :
    projectionDescentTotalCoverTransitionComponentThreeFactorPullHomLaw (J := J) hSheaf D := by
  intro Y' Y g A B a b h ga gb hga hgb
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
  let IAinner := projectionDescentTotalCoverInner (J := J) hSheaf D A
  let IBinner := projectionDescentTotalCoverInner (J := J) hSheaf D B
  let IAold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
  let IBold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DB (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B b)
  let IAnew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
  let IBnew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DB (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B gb)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B gb)
  let hAold : ga ≫ IAinner.f = g ≫ IAold.f := by
    let IAa := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a
    let h₁₂ : ga ≫ IAinner.f = g ≫ IAa.f := by
      dsimp [IAa, projectionDescentTotalCoverRefinedInner]
      rw [← hga]
      exact Category.assoc g a IAinner.f
    let h₂₃ : g ≫ IAa.f = g ≫ IAold.f := by
      dsimp [IAa, IAold, DA, DescentCompletionObjectOver.pullbackCoverBaseArrow,
        projectionDescentTotalCoverExplicitPullbackArrow,
        projectionDescentTotalCoverRefinedInner, projectionDescentTotalCoverOuterMap]
      simpa only [Category.assoc] using
        (congrArg (fun q => g ≫ q)
          (Category.id_comp
            (a ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D A).f))).symm
    exact h₁₂.trans h₂₃
  let hBold : g ≫ IBold.f = gb ≫ IBinner.f := by
    let IBb := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D B b
    let h₁₂ : g ≫ IBold.f = g ≫ IBb.f := by
      dsimp [IBb, IBold, DB, DescentCompletionObjectOver.pullbackCoverBaseArrow,
        projectionDescentTotalCoverExplicitPullbackArrow,
        projectionDescentTotalCoverRefinedInner, projectionDescentTotalCoverOuterMap]
      simpa only [Category.assoc] using
        congrArg (fun q => g ≫ q)
          (Category.id_comp
            (b ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D B).f))
    let h₂₃ : g ≫ IBb.f = gb ≫ IBinner.f := by
      dsimp [IBb, projectionDescentTotalCoverRefinedInner]
      rw [← hgb]
      exact (Category.assoc g b IBinner.f).symm
    exact h₁₂.trans h₂₃
  let hAnew : ga ≫ IAinner.f = 𝟙 Y' ≫ IAnew.f := by
    dsimp [IAinner, IAnew, DA, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentTotalCoverOuterMap]
    simp
  let hBnew : 𝟙 Y' ≫ IBnew.f = gb ≫ IBinner.f := by
    dsimp [IBinner, IBnew, DB, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentTotalCoverOuterMap]
    simp
  let hAoldNew : g ≫ IAold.f = 𝟙 Y' ≫ IAnew.f := by
    dsimp [IAold, IAnew, DA, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentTotalCoverOuterMap]
    rw [← hga]
    simp [Category.assoc]
  let hBoldNew : g ≫ IBold.f = 𝟙 Y' ≫ IBnew.f := by
    dsimp [IBold, IBnew, DB, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentTotalCoverOuterMap]
    rw [← hgb]
    simp [Category.assoc]
  let lOld :=
    (DA.overlapIso (I₁ := IAinner) (I₂ := IAold) ga g hAold).hom
  let lOldNew :=
    (DA.overlapIso (I₁ := IAold) (I₂ := IAnew) g (𝟙 Y') hAoldNew).hom
  let lNew :=
    (DA.overlapIso (I₁ := IAinner) (I₂ := IAnew) ga (𝟙 Y') hAnew).hom
  let rOldNew :=
    (DB.overlapIso (I₁ := IBold) (I₂ := IBnew) g (𝟙 Y') hBoldNew).hom
  let rNew :=
    (DB.overlapIso (I₁ := IBnew) (I₂ := IBinner) (𝟙 Y') gb hBnew).hom
  let rOld :=
    (DB.overlapIso (I₁ := IBold) (I₂ := IBinner) g gb hBold).hom
  let midOld :=
    (let α :=
      projectionDescentExplicitOuterFiberHomForTotalCover (J := J)
        hSheaf D A B a b h
    α.1.components.toHomOver.family
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B b)
      g g
      (by
        have hbase :
            α.1.base = 𝟙 Y :=
          projectionDescentExplicitOuterFiberHomForTotalCover_base
            (J := J) hSheaf D A B a b h
        rw [hbase]
        dsimp [projectionDescentTotalCoverExplicitPullbackArrow]
        exact (Category.assoc g (𝟙 Y) (𝟙 Y)).symm.trans
          (Category.comp_id (g ≫ 𝟙 Y))))
  let midNew :=
    (let α :=
      projectionDescentExplicitOuterFiberHomForTotalCover (J := J)
        hSheaf D A B ga gb hsmall
    α.1.components.toHomOver.family
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B gb)
      (𝟙 Y') (𝟙 Y')
      (by
        have hbase :
            α.1.base = 𝟙 Y' :=
          projectionDescentExplicitOuterFiberHomForTotalCover_base
            (J := J) hSheaf D A B ga gb hsmall
        rw [hbase]
        dsimp [projectionDescentTotalCoverExplicitPullbackArrow]
        calc
          𝟙 Y' ≫ 𝟙 Y' ≫ 𝟙 Y' = 𝟙 Y' ≫ 𝟙 Y' := by rw [Category.id_comp]
          _ = 𝟙 Y' ≫ 𝟙 Y' := rfl))
  have hleft : lOld ≫ lOldNew = lNew := by
    simpa [lOld, lOldNew, lNew, hAold, hAoldNew, hAnew] using
      DescentCompletionObjectOver.overlapIso_hom_comp (J := J) DA
        (I₁ := IAinner) (I₂ := IAold) (I₃ := IAnew)
        ga g (𝟙 Y') hAold hAoldNew
  have hright : rOldNew ≫ rNew = rOld := by
    simpa [rOldNew, rNew, rOld, hBoldNew, hBnew, hBold] using
      DescentCompletionObjectOver.overlapIso_hom_comp (J := J) DB
        (I₁ := IBold) (I₂ := IBnew) (I₃ := IBinner)
        g (𝟙 Y') gb hBoldNew hBnew
  have hmid : midOld ≫ rOldNew = lOldNew ≫ midNew := by
    simpa [projectionDescentTotalCoverExplicitMiddlePullHomLaw, hsmall, DA, DB, IAold,
      IBold, IAnew, IBnew, hAoldNew, hBoldNew, midOld, midNew, lOldNew, rOldNew] using
      hmiddle g a b h ga gb hga hgb
  change lOld ≫ midOld ≫ rOld = lNew ≫ midNew ≫ rNew
  calc
    lOld ≫ midOld ≫ rOld =
        lOld ≫ midOld ≫ (rOldNew ≫ rNew) := by
          exact congrArg (fun q => lOld ≫ midOld ≫ q) hright.symm
    _ = lOld ≫ (midOld ≫ rOldNew) ≫ rNew := by
      simp [Category.assoc]
    _ = lOld ≫ (lOldNew ≫ midNew) ≫ rNew := by
      exact congrArg (fun q => lOld ≫ q ≫ rNew) hmid
    _ = (lOld ≫ lOldNew) ≫ midNew ≫ rNew := by
      simp [Category.assoc]
    _ = lNew ≫ midNew ≫ rNew := by rw [hleft]

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
