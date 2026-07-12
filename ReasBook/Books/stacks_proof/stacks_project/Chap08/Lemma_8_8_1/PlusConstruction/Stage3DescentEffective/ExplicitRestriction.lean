import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.PullHom

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

/-- Source stage 3.13 explicit-restriction owner bridge: after pulling back the inverse of the
explicit-pullback-cover comparison and then moving from the old explicit cover owner to the
directly rebuilt refined inner cover, the result is the direct refined-inner overlap.

This is the small coherence step behind the source proof's silent identification of the
restriction of the explicit pullback cover with the refined inner cover built after base change.
-/
theorem projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso_inv_pullHom_comp_refined
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (g : Y' ⟶ Y)
    (a : Y ⟶ A.Y) (ga : Y' ⟶ A.Y)
    (hga : g ≫ a = ga) :
    let D₀ :=
      projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso
          (J := J) hSheaf D A a).inv
        g g g (by exact Category.comp_id g) (by exact Category.comp_id g) ≫
      (D₀.overlapIso
        (I₁ := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
          D₀ (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
          (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a))
        (I₂ := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A ga)
        g (𝟙 Y')
        (by
          dsimp [D₀, DescentCompletionObjectOver.pullbackCoverBaseArrow,
            projectionDescentTotalCoverExplicitPullbackArrow,
            projectionDescentTotalCoverRefinedInner,
            projectionDescentTotalCoverOuterMap]
          rw [← hga]
          calc
            g ≫ 𝟙 Y ≫ a ≫
                (projectionDescentTotalCoverInner (J := J) hSheaf D A).f =
              g ≫ a ≫
                (projectionDescentTotalCoverInner (J := J) hSheaf D A).f := by simp
            _ = (g ≫ a) ≫
                (projectionDescentTotalCoverInner (J := J) hSheaf D A).f :=
              (Category.assoc g a
                (projectionDescentTotalCoverInner (J := J) hSheaf D A).f).symm
            _ = 𝟙 Y' ≫ (g ≫ a) ≫
                (projectionDescentTotalCoverInner (J := J) hSheaf D A).f := by simp)).hom =
      (D₀.overlapIso
        (I₁ := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a)
        (I₂ := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A ga)
        g (𝟙 Y')
        (by
          dsimp [D₀, projectionDescentTotalCoverRefinedInner]
          rw [← hga]
          calc
            g ≫ a ≫
                (projectionDescentTotalCoverInner (J := J) hSheaf D A).f =
              (g ≫ a) ≫
                (projectionDescentTotalCoverInner (J := J) hSheaf D A).f :=
              (Category.assoc g a
                (projectionDescentTotalCoverInner (J := J) hSheaf D A).f).symm
            _ = 𝟙 Y' ≫ (g ≫ a) ≫
                (projectionDescentTotalCoverInner (J := J) hSheaf D A).f := by simp)).hom := by
  dsimp only
  rw [projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso_inv_pullHom]
  let D₀ :=
    projectionDescentDatumLocalObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
  let Ia := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a
  let Iold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    D₀ (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
  let Iga := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A ga
  have hhead : g ≫ Ia.f = g ≫ Iold.f := by
    dsimp [Ia, Iold, D₀, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentTotalCoverRefinedInner, projectionDescentTotalCoverOuterMap]
    simpa only [Category.assoc] using
      (congrArg (fun q => g ≫ q)
        (Category.id_comp
          (a ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D A).f))).symm
  have htail : g ≫ Iold.f = 𝟙 Y' ≫ Iga.f := by
    dsimp [Iold, Iga, D₀, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentTotalCoverRefinedInner, projectionDescentTotalCoverOuterMap]
    rw [← hga]
    calc
      g ≫ 𝟙 Y ≫ a ≫
          (projectionDescentTotalCoverInner (J := J) hSheaf D A).f =
        g ≫ a ≫
          (projectionDescentTotalCoverInner (J := J) hSheaf D A).f := by simp
      _ = (g ≫ a) ≫
          (projectionDescentTotalCoverInner (J := J) hSheaf D A).f :=
        (Category.assoc g a
          (projectionDescentTotalCoverInner (J := J) hSheaf D A).f).symm
      _ = 𝟙 Y' ≫ (g ≫ a) ≫
          (projectionDescentTotalCoverInner (J := J) hSheaf D A).f := by simp
  have hcomp :=
    DescentCompletionObjectOver.overlapIso_hom_comp (J := J) D₀
      (I₁ := Ia) (I₂ := Iold) (I₃ := Iga) g g (𝟙 Y') hhead htail
  simpa [Ia, Iold, Iga, D₀] using hcomp

/-- Source stage 3.13 explicit-restriction owner bridge, source side: the first two factors in
the expanded restriction of `rho` compose to the single overlap from the original inner local
object to the restricted explicit-pullback-cover owner. -/
theorem projectionDescentTotalCoverLocalRestrictionIso_pullHom_comp_explicitPullbackArrowRestrictionIso_inv_pullHom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (g : Y' ⟶ Y)
    (a : Y ⟶ A.Y) (ga : Y' ⟶ A.Y)
    (hga : g ≫ a = ga) :
    let D₀ :=
      projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
    let Iinner := projectionDescentTotalCoverInner (J := J) hSheaf D A
    let Ia := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a
    let Iold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      D₀ (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
    let h₁₂ : ga ≫ Iinner.f = g ≫ Ia.f := by
      dsimp [Ia, projectionDescentTotalCoverRefinedInner]
      rw [← hga]
      exact Category.assoc g a Iinner.f
    let h₂₃ : g ≫ Ia.f = g ≫ Iold.f := by
      dsimp [Ia, Iold, D₀, DescentCompletionObjectOver.pullbackCoverBaseArrow,
        projectionDescentTotalCoverExplicitPullbackArrow,
        projectionDescentTotalCoverRefinedInner, projectionDescentTotalCoverOuterMap]
      simpa only [Category.assoc] using
        (congrArg (fun q => g ≫ q)
          (Category.id_comp
            (a ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D A).f))).symm
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D A a).hom
        g ga g hga (by simp) ≫
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso
          (J := J) hSheaf D A a).inv
        g g g (by exact Category.comp_id g) (by exact Category.comp_id g) =
      (D₀.overlapIso (I₁ := Iinner) (I₂ := Iold) ga g (h₁₂.trans h₂₃)).hom := by
  dsimp only
  rw [projectionDescentTotalCoverLocalRestrictionIso_pullHom]
  rw [projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso_inv_pullHom]
  let D₀ :=
    projectionDescentDatumLocalObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
  let Iinner := projectionDescentTotalCoverInner (J := J) hSheaf D A
  let Ia := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a
  let Iold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    D₀ (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
  let h₁₂ : ga ≫ Iinner.f = g ≫ Ia.f := by
    dsimp [Ia, projectionDescentTotalCoverRefinedInner]
    rw [← hga]
    exact Category.assoc g a Iinner.f
  let h₂₃ : g ≫ Ia.f = g ≫ Iold.f := by
    dsimp [Ia, Iold, D₀, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentTotalCoverRefinedInner, projectionDescentTotalCoverOuterMap]
    simpa only [Category.assoc] using
      (congrArg (fun q => g ≫ q)
        (Category.id_comp
          (a ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D A).f))).symm
  have hcomp :=
    DescentCompletionObjectOver.overlapIso_hom_comp (J := J) D₀
      (I₁ := Iinner) (I₂ := Ia) (I₃ := Iold) ga g g h₁₂ h₂₃
  simpa [D₀, Iinner, Ia, Iold, h₁₂, h₂₃] using hcomp

/-- Source stage 3.13 explicit-restriction owner bridge, target side: the last two factors in
the expanded restriction of `rho` compose to the single overlap from the restricted
explicit-pullback-cover owner to the original inner local object. -/
theorem projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso_pullHom_comp_localRestrictionIso_inv_pullHom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (g : Y' ⟶ Y)
    (a : Y ⟶ A.Y) (ga : Y' ⟶ A.Y)
    (hga : g ≫ a = ga) :
    let D₀ :=
      projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
    let Iinner := projectionDescentTotalCoverInner (J := J) hSheaf D A
    let Ia := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a
    let Iold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      D₀ (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
    let h₁₂ : g ≫ Iold.f = g ≫ Ia.f := by
      dsimp [Ia, Iold, D₀, DescentCompletionObjectOver.pullbackCoverBaseArrow,
        projectionDescentTotalCoverExplicitPullbackArrow,
        projectionDescentTotalCoverRefinedInner, projectionDescentTotalCoverOuterMap]
      simpa only [Category.assoc] using
        congrArg (fun q => g ≫ q)
          (Category.id_comp
            (a ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D A).f))
    let h₂₃ : g ≫ Ia.f = ga ≫ Iinner.f := by
      dsimp [Ia, projectionDescentTotalCoverRefinedInner]
      rw [← hga]
      exact (Category.assoc g a Iinner.f).symm
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso
          (J := J) hSheaf D A a).hom
        g g g (by exact Category.comp_id g) (by exact Category.comp_id g) ≫
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D A a).inv
        g g ga (by simp) hga =
      (D₀.overlapIso (I₁ := Iold) (I₂ := Iinner) g ga (h₁₂.trans h₂₃)).hom := by
  dsimp only
  rw [projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso_pullHom]
  rw [projectionDescentTotalCoverLocalRestrictionIso_inv_pullHom]
  let D₀ :=
    projectionDescentDatumLocalObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
  let Iinner := projectionDescentTotalCoverInner (J := J) hSheaf D A
  let Ia := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a
  let Iold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    D₀ (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
  let h₁₂ : g ≫ Iold.f = g ≫ Ia.f := by
    dsimp [Ia, Iold, D₀, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentTotalCoverRefinedInner, projectionDescentTotalCoverOuterMap]
    simpa only [Category.assoc] using
      congrArg (fun q => g ≫ q)
        (Category.id_comp
          (a ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D A).f))
  let h₂₃ : g ≫ Ia.f = ga ≫ Iinner.f := by
    dsimp [Ia, projectionDescentTotalCoverRefinedInner]
    rw [← hga]
    exact (Category.assoc g a Iinner.f).symm
  have hcomp :=
    DescentCompletionObjectOver.overlapIso_hom_comp (J := J) D₀
      (I₁ := Iold) (I₂ := Ia) (I₃ := Iinner) g g ga h₁₂ h₂₃
  simpa [D₀, Iinner, Ia, Iold, h₁₂, h₂₃] using hcomp

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
