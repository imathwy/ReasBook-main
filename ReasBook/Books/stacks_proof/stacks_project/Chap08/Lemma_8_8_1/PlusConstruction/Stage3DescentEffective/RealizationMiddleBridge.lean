import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationPullHomCollapsed

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

/-- Source stage 3.13 middle owner bridge for the explicit outer component used in
`Lambda_a`.

This is the realization-side analogue of
`projectionDescentTotalCoverExplicitMiddlePullHomLaw`.  It says that the explicit outer
component `theta_ba,ji` for `(a,k)`, restricted along `g`, agrees with the explicit outer
component rebuilt directly for `(ga,gk)`, after the source and target explicit pullback cover
owners are compared by the descent-completion overlap maps. -/
def projectionDescentRealizationExplicitMiddlePullHomLaw
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
    let hsmall : ga ≫ A.f = gk ≫ K.f ≫ I.f := by
      calc
        ga ≫ A.f = g ≫ a ≫ A.f := by rw [← hga]; simp [Category.assoc]
        _ = g ≫ (k ≫ K.f ≫ I.f) := by
          simpa [Category.assoc] using congrArg (fun q => g ≫ q) h
        _ = gk ≫ K.f ≫ I.f := by rw [← hgk]; simp [Category.assoc]
    let DA :=
      projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
    let DB := projectionDescentDatumLocalObject (J := J) hSheaf D I
    let IAold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
    let Kold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      DB (k ≫ K.f)
      (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k)
    let IAnew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
    let Knew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      DB (gk ≫ K.f)
      (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk)
    let hAoldNew : g ≫ IAold.f = 𝟙 Y' ≫ IAnew.f := by
      dsimp [IAold, IAnew, DA, DescentCompletionObjectOver.pullbackCoverBaseArrow,
        projectionDescentTotalCoverExplicitPullbackArrow,
        projectionDescentTotalCoverOuterMap]
      rw [← hga]
      simp [Category.assoc]
    let hKoldNew : g ≫ Kold.f = 𝟙 Y' ≫ Knew.f := by
      dsimp [Kold, Knew, DB, DescentCompletionObjectOver.pullbackCoverBaseArrow,
        projectionDescentDatumExplicitPullbackArrow]
      rw [← hgk]
      simp [Category.assoc]
    (let α :=
      projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner (J := J)
        hSheaf D A I a K k h
    α.1.components.toHomOver.family
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
      (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k)
      g g
      (by
        have hbase :
            α.1.base = 𝟙 Y :=
          projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
            (J := J) hSheaf D A I a K k h
        rw [hbase]
        dsimp [projectionDescentTotalCoverExplicitPullbackArrow,
          projectionDescentDatumExplicitPullbackArrow]
        exact (Category.assoc g (𝟙 Y) (𝟙 Y)).symm.trans
          (Category.comp_id (g ≫ 𝟙 Y)))) ≫
        (DB.overlapIso (I₁ := Kold) (I₂ := Knew) g (𝟙 Y') hKoldNew).hom =
      (DA.overlapIso (I₁ := IAold) (I₂ := IAnew) g (𝟙 Y') hAoldNew).hom ≫
        (let α :=
          projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner (J := J)
            hSheaf D A I ga K gk hsmall
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
              _ = 𝟙 Y' ≫ 𝟙 Y' := rfl))

/-- Lower-level source stage 3.13 restriction law for the realization component. -/
def projectionDescentRealizationComponentFromTotalCoverToDatumInnerPullHomLaw
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
    let hsmall : ga ≫ A.f = gk ≫ K.f ≫ I.f := by
      calc
        ga ≫ A.f = g ≫ a ≫ A.f := by rw [← hga]; simp [Category.assoc]
        _ = g ≫ (k ≫ K.f ≫ I.f) := by
          simpa [Category.assoc] using congrArg (fun q => g ≫ q) h
        _ = gk ≫ K.f ≫ I.f := by rw [← hgk]; simp [Category.assoc]
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentRealizationComponentFromTotalCoverToDatumInner
          (J := J) hSheaf D A I a K k h)
        g ga gk hga hgk =
      projectionDescentRealizationComponentFromTotalCoverToDatumInner
        (J := J) hSheaf D A I ga K gk hsmall

/-- The middle explicit-owner square implies the lower-level realization restriction law. -/
theorem projectionDescentRealizationComponentFromTotalCoverToDatumInnerPullHomLaw_of_explicitMiddle
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hmiddle :
      projectionDescentRealizationExplicitMiddlePullHomLaw (J := J) hSheaf D) :
    projectionDescentRealizationComponentFromTotalCoverToDatumInnerPullHomLaw
      (J := J) hSheaf D := by
  intro Y' Y g A I a K k h ga gk hga hgk
  let hsmall : ga ≫ A.f = gk ≫ K.f ≫ I.f := by
    calc
      ga ≫ A.f = g ≫ a ≫ A.f := by rw [← hga]; simp [Category.assoc]
      _ = g ≫ (k ≫ K.f ≫ I.f) := by
        simpa [Category.assoc] using congrArg (fun q => g ≫ q) h
      _ = gk ≫ K.f ≫ I.f := by rw [← hgk]; simp [Category.assoc]
  change
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentRealizationComponentFromTotalCoverToDatumInner
          (J := J) hSheaf D A I a K k h)
        g ga gk hga hgk =
      projectionDescentRealizationComponentFromTotalCoverToDatumInner
        (J := J) hSheaf D A I ga K gk hsmall
  let DA :=
    projectionDescentDatumLocalObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
  let DB := projectionDescentDatumLocalObject (J := J) hSheaf D I
  let IAinner := projectionDescentTotalCoverInner (J := J) hSheaf D A
  let IAold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
  let Kold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DB (k ≫ K.f)
    (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k)
  let IAnew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
  let Knew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DB (gk ≫ K.f)
    (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk)
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
  let hKold : g ≫ Kold.f = gk ≫ K.f := by
    let Kk := projectionDescentDatumRefinedInner (J := J) hSheaf D I K k
    let h₁₂ : g ≫ Kold.f = g ≫ Kk.f := by
      dsimp [Kk, Kold, DB, DescentCompletionObjectOver.pullbackCoverBaseArrow,
        projectionDescentDatumExplicitPullbackArrow,
        projectionDescentDatumRefinedInner]
      simpa only [Category.assoc] using
        congrArg (fun q => g ≫ q) (Category.id_comp (k ≫ K.f))
    let h₂₃ : g ≫ Kk.f = gk ≫ K.f := by
      dsimp [Kk, projectionDescentDatumRefinedInner]
      rw [← hgk]
      exact (Category.assoc g k K.f).symm
    exact h₁₂.trans h₂₃
  let hAnew : ga ≫ IAinner.f = 𝟙 Y' ≫ IAnew.f := by
    dsimp [IAinner, IAnew, DA, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentTotalCoverOuterMap]
    simp
  let hKnew : 𝟙 Y' ≫ Knew.f = gk ≫ K.f := by
    dsimp [Knew, DB, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentDatumExplicitPullbackArrow]
    simp
  let hAoldNew : g ≫ IAold.f = 𝟙 Y' ≫ IAnew.f := by
    dsimp [IAold, IAnew, DA, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentTotalCoverOuterMap]
    rw [← hga]
    simp [Category.assoc]
  let hKoldNew : g ≫ Kold.f = 𝟙 Y' ≫ Knew.f := by
    dsimp [Kold, Knew, DB, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentDatumExplicitPullbackArrow]
    rw [← hgk]
    simp [Category.assoc]
  let lOld := (DA.overlapIso (I₁ := IAinner) (I₂ := IAold) ga g hAold).hom
  let lOldNew := (DA.overlapIso (I₁ := IAold) (I₂ := IAnew) g (𝟙 Y') hAoldNew).hom
  let lNew := (DA.overlapIso (I₁ := IAinner) (I₂ := IAnew) ga (𝟙 Y') hAnew).hom
  let rOldNew := (DB.overlapIso (I₁ := Kold) (I₂ := Knew) g (𝟙 Y') hKoldNew).hom
  let rNew := (DB.overlapIso (I₁ := Knew) (I₂ := K) (𝟙 Y') gk hKnew).hom
  let rOld := (DB.overlapIso (I₁ := Kold) (I₂ := K) g gk hKold).hom
  let midOld :=
    (let α :=
      projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner (J := J)
        hSheaf D A I a K k h
    α.1.components.toHomOver.family
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
      (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k)
      g g
      (by
        have hbase :
            α.1.base = 𝟙 Y :=
          projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
            (J := J) hSheaf D A I a K k h
        rw [hbase]
        dsimp [projectionDescentTotalCoverExplicitPullbackArrow,
          projectionDescentDatumExplicitPullbackArrow]
        exact (Category.assoc g (𝟙 Y) (𝟙 Y)).symm.trans
          (Category.comp_id (g ≫ 𝟙 Y))))
  let midNew :=
    (let α :=
      projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner (J := J)
        hSheaf D A I ga K gk hsmall
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
          _ = 𝟙 Y' ≫ 𝟙 Y' := rfl))
  have hleft : lOld ≫ lOldNew = lNew := by
    simpa [lOld, lOldNew, lNew, hAold, hAoldNew, hAnew] using
      DescentCompletionObjectOver.overlapIso_hom_comp (J := J) DA
        (I₁ := IAinner) (I₂ := IAold) (I₃ := IAnew)
        ga g (𝟙 Y') hAold hAoldNew
  have hright : rOldNew ≫ rNew = rOld := by
    simpa [rOldNew, rNew, rOld, hKoldNew, hKnew, hKold] using
      DescentCompletionObjectOver.overlapIso_hom_comp (J := J) DB
        (I₁ := Kold) (I₂ := Knew) (I₃ := K)
        g (𝟙 Y') gk hKoldNew hKnew
  have hmid : midOld ≫ rOldNew = lOldNew ≫ midNew := by
    simpa [projectionDescentRealizationExplicitMiddlePullHomLaw, hsmall, DA, DB, IAold,
      Kold, IAnew, Knew, hAoldNew, hKoldNew, midOld, midNew, lOldNew, rOldNew] using
      hmiddle g I a K k h ga gk hga hgk
  rw [projectionDescentRealizationComponentFromTotalCoverToDatumInner_pullHom_collapsed]
  rw [projectionDescentRealizationComponentFromTotalCoverToDatumInner_collapsed]
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
