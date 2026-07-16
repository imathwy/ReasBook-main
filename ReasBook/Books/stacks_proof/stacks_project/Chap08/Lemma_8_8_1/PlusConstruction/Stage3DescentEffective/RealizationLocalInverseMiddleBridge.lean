import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationLocalInverseNaturality

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
`Lambda_a^{-1}`.

This is the inverse-realization analogue of
`projectionDescentRealizationExplicitMiddlePullHomLaw`. It keeps the source datum-inner owner
`(a,i)` and the target total-cover owner distinct, and compares the old explicit pullback owners
with the directly rebuilt owners after restriction. -/
def projectionDescentRealizationInverseExplicitMiddlePullHomLaw
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
    let DB := projectionDescentDatumLocalObject (J := J) hSheaf D I
    let DA :=
      projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
    let Kold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      DB (k ≫ K.f)
      (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k)
    let IAold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
    let Knew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      DB (gk ≫ K.f)
      (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk)
    let IAnew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
    let hKoldNew : g ≫ Kold.f = 𝟙 Y' ≫ Knew.f := by
      dsimp [Kold, Knew, DB, DescentCompletionObjectOver.pullbackCoverBaseArrow,
        projectionDescentDatumExplicitPullbackArrow]
      rw [← hgk]
      simp [Category.assoc]
    let hAoldNew : g ≫ IAold.f = 𝟙 Y' ≫ IAnew.f := by
      dsimp [IAold, IAnew, DA, DescentCompletionObjectOver.pullbackCoverBaseArrow,
        projectionDescentTotalCoverExplicitPullbackArrow,
        projectionDescentTotalCoverOuterMap]
      rw [← hga]
      simp [Category.assoc]
    (let α :=
      projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover (J := J)
        hSheaf D I K k A a h
    α.1.components.toHomOver.family
      (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
      g g
      (by
        have hbase :
            α.1.base = 𝟙 Y :=
          projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_base
            (J := J) hSheaf D I K k A a h
        rw [hbase]
        dsimp [projectionDescentDatumExplicitPullbackArrow,
          projectionDescentTotalCoverExplicitPullbackArrow]
        exact (Category.assoc g (𝟙 Y) (𝟙 Y)).symm.trans
          (Category.comp_id (g ≫ 𝟙 Y)))) ≫
        (DA.overlapIso (I₁ := IAold) (I₂ := IAnew) g (𝟙 Y') hAoldNew).hom =
      (DB.overlapIso (I₁ := Kold) (I₂ := Knew) g (𝟙 Y') hKoldNew).hom ≫
        (let α :=
          projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover (J := J)
            hSheaf D I K gk A ga hsmall
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

/-- Lower-level source stage 3.13 restriction law for the inverse realization component. -/
def projectionDescentRealizationInverseComponentFromDatumInnerToTotalCoverPullHomLaw
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
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover
          (J := J) hSheaf D I K k A a h)
        g gk ga hgk hga =
      projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover
        (J := J) hSheaf D I K gk A ga hsmall

/-- The middle explicit-owner square implies the lower-level inverse-realization restriction
law. -/
theorem projectionDescentRealizationInverseComponentFromDatumInnerToTotalCoverPullHomLaw_of_explicitMiddle
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hmiddle :
      projectionDescentRealizationInverseExplicitMiddlePullHomLaw (J := J) hSheaf D) :
    projectionDescentRealizationInverseComponentFromDatumInnerToTotalCoverPullHomLaw
      (J := J) hSheaf D := by
  intro Y' Y g I K k A a h gk ga hgk hga
  let hsmall : gk ≫ K.f ≫ I.f = ga ≫ A.f := by
    calc
      gk ≫ K.f ≫ I.f = g ≫ k ≫ K.f ≫ I.f := by
        rw [← hgk]
        simp [Category.assoc]
      _ = g ≫ (a ≫ A.f) := by
        simpa [Category.assoc] using congrArg (fun q => g ≫ q) h
      _ = ga ≫ A.f := by rw [← hga]; simp [Category.assoc]
  change
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover
          (J := J) hSheaf D I K k A a h)
        g gk ga hgk hga =
      projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover
        (J := J) hSheaf D I K gk A ga hsmall
  let DB := projectionDescentDatumLocalObject (J := J) hSheaf D I
  let DA :=
    projectionDescentDatumLocalObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
  let Kold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DB (k ≫ K.f)
    (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k)
  let IAinner := projectionDescentTotalCoverInner (J := J) hSheaf D A
  let IAold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
  let Knew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DB (gk ≫ K.f)
    (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk)
  let IAnew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
  let hKold : gk ≫ K.f = g ≫ Kold.f := by
    let Kk := projectionDescentDatumRefinedInner (J := J) hSheaf D I K k
    let h₁₂ : gk ≫ K.f = g ≫ Kk.f := by
      dsimp [Kk, projectionDescentDatumRefinedInner]
      rw [← hgk]
      exact Category.assoc g k K.f
    let h₂₃ : g ≫ Kk.f = g ≫ Kold.f := by
      dsimp [Kk, Kold, DB, DescentCompletionObjectOver.pullbackCoverBaseArrow,
        projectionDescentDatumExplicitPullbackArrow,
        projectionDescentDatumRefinedInner]
      simpa only [Category.assoc] using
        (congrArg (fun q => g ≫ q) (Category.id_comp (k ≫ K.f))).symm
    exact h₁₂.trans h₂₃
  let hAold : g ≫ IAold.f = ga ≫ IAinner.f := by
    let IAa := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a
    let h₁₂ : g ≫ IAold.f = g ≫ IAa.f := by
      dsimp [IAa, IAold, DA, DescentCompletionObjectOver.pullbackCoverBaseArrow,
        projectionDescentTotalCoverExplicitPullbackArrow,
        projectionDescentTotalCoverRefinedInner, projectionDescentTotalCoverOuterMap]
      simpa only [Category.assoc] using
        congrArg (fun q => g ≫ q)
          (Category.id_comp
            (a ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D A).f))
    let h₂₃ : g ≫ IAa.f = ga ≫ IAinner.f := by
      dsimp [IAa, projectionDescentTotalCoverRefinedInner, IAinner]
      rw [← hga]
      exact (Category.assoc g a IAinner.f).symm
    exact h₁₂.trans h₂₃
  let hKnew : gk ≫ K.f = 𝟙 Y' ≫ Knew.f := by
    dsimp [Knew, DB, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentDatumExplicitPullbackArrow]
    simp
  let hAnew : 𝟙 Y' ≫ IAnew.f = ga ≫ IAinner.f := by
    dsimp [IAinner, IAnew, DA, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentTotalCoverOuterMap]
    simp
  let hKoldNew : g ≫ Kold.f = 𝟙 Y' ≫ Knew.f := by
    dsimp [Kold, Knew, DB, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentDatumExplicitPullbackArrow]
    rw [← hgk]
    simp [Category.assoc]
  let hAoldNew : g ≫ IAold.f = 𝟙 Y' ≫ IAnew.f := by
    dsimp [IAold, IAnew, DA, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentTotalCoverOuterMap]
    rw [← hga]
    simp [Category.assoc]
  let lOld := (DB.overlapIso (I₁ := K) (I₂ := Kold) gk g hKold).hom
  let lOldNew := (DB.overlapIso (I₁ := Kold) (I₂ := Knew) g (𝟙 Y') hKoldNew).hom
  let lNew := (DB.overlapIso (I₁ := K) (I₂ := Knew) gk (𝟙 Y') hKnew).hom
  let rOldNew := (DA.overlapIso (I₁ := IAold) (I₂ := IAnew) g (𝟙 Y') hAoldNew).hom
  let rNew := (DA.overlapIso (I₁ := IAnew) (I₂ := IAinner) (𝟙 Y') ga hAnew).hom
  let rOld := (DA.overlapIso (I₁ := IAold) (I₂ := IAinner) g ga hAold).hom
  let midOld :=
    (let α :=
      projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover (J := J)
        hSheaf D I K k A a h
    α.1.components.toHomOver.family
      (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
      g g
      (by
        have hbase :
            α.1.base = 𝟙 Y :=
          projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_base
            (J := J) hSheaf D I K k A a h
        rw [hbase]
        dsimp [projectionDescentDatumExplicitPullbackArrow,
          projectionDescentTotalCoverExplicitPullbackArrow]
        exact (Category.assoc g (𝟙 Y) (𝟙 Y)).symm.trans
          (Category.comp_id (g ≫ 𝟙 Y))))
  let midNew :=
    (let α :=
      projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover (J := J)
        hSheaf D I K gk A ga hsmall
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
  have hleft : lOld ≫ lOldNew = lNew := by
    simpa [lOld, lOldNew, lNew, hKold, hKoldNew, hKnew] using
      DescentCompletionObjectOver.overlapIso_hom_comp (J := J) DB
        (I₁ := K) (I₂ := Kold) (I₃ := Knew)
        gk g (𝟙 Y') hKold hKoldNew
  have hright : rOldNew ≫ rNew = rOld := by
    simpa [rOldNew, rNew, rOld, hAoldNew, hAnew, hAold] using
      DescentCompletionObjectOver.overlapIso_hom_comp (J := J) DA
        (I₁ := IAold) (I₂ := IAnew) (I₃ := IAinner)
        g (𝟙 Y') ga hAoldNew hAnew
  have hmid : midOld ≫ rOldNew = lOldNew ≫ midNew := by
    simpa [projectionDescentRealizationInverseExplicitMiddlePullHomLaw, hsmall, DB, DA, Kold,
      IAold, Knew, IAnew, hKoldNew, hAoldNew, midOld, midNew, lOldNew, rOldNew] using
      hmiddle g I K k a h gk ga hgk hga
  rw [projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover_pullHom_collapsed]
  rw [projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover_collapsed]
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
