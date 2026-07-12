import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.LocalRefinement

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

/-- Source stage 3.13 restricted explicit-cover arrow.

If `a : Y -> U_ai` gives the explicit pullback cover of the outer object over `Y`, and
`g : Y' -> Y`, then this is the same explicit cover member viewed as an arrow of the old pullback
cover over `Y`, with structural map `g`.  It is the formal version of restricting the old
explicit pullback cover along `g`. -/
noncomputable def projectionDescentTotalCoverExplicitPullbackArrowAlong
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (g : Y' ⟶ Y) (a : Y ⟶ A.Y) (ga : Y' ⟶ A.Y)
    (hga : g ≫ a = ga) :
    ((projectionDescentDatumLocalObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D A)).cover.pullback
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)).Arrow where
  Y := Y'
  f := g
  hf := by
    change ((projectionDescentDatumLocalObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D A)).cover : Sieve _).arrows
        (g ≫ projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
    rw [show g ≫ projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a =
        projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga by
      dsimp [projectionDescentTotalCoverOuterMap]
      rw [← hga]
      simp [Category.assoc]]
    simpa [projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentTotalCoverOuterMap, Category.assoc] using
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga).hf

@[simp]
theorem projectionDescentTotalCoverExplicitPullbackArrowAlong_Y
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (g : Y' ⟶ Y) (a : Y ⟶ A.Y) (ga : Y' ⟶ A.Y)
    (hga : g ≫ a = ga) :
    (projectionDescentTotalCoverExplicitPullbackArrowAlong
      (J := J) hSheaf D A g a ga hga).Y = Y' :=
  rfl

@[simp]
theorem projectionDescentTotalCoverExplicitPullbackArrowAlong_f
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (g : Y' ⟶ Y) (a : Y ⟶ A.Y) (ga : Y' ⟶ A.Y)
    (hga : g ≫ a = ga) :
    (projectionDescentTotalCoverExplicitPullbackArrowAlong
      (J := J) hSheaf D A g a ga hga).f = g :=
  rfl

/-- The base arrow of the restricted old explicit-cover member has the same base map as the
direct explicit-cover member built from `ga`. -/
theorem projectionDescentTotalCoverExplicitPullbackArrowAlong_base_f
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (g : Y' ⟶ Y) (a : Y ⟶ A.Y) (ga : Y' ⟶ A.Y)
    (hga : g ≫ a = ga) :
    (DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      (projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
      (projectionDescentTotalCoverExplicitPullbackArrowAlong
        (J := J) hSheaf D A g a ga hga)).f =
      projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga := by
  dsimp [projectionDescentTotalCoverExplicitPullbackArrowAlong,
    DescentCompletionObjectOver.pullbackCoverBaseArrow,
    projectionDescentTotalCoverOuterMap]
  rw [← hga]
  exact (Category.assoc g a
    (projectionDescentTotalCoverInner (J := J) hSheaf D A).f).symm

/-- As an arrow of the original local cover, the restricted old explicit-cover member is the
refined inner cover member built directly from `ga`. -/
theorem projectionDescentTotalCoverExplicitPullbackArrowAlong_base_eq
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (g : Y' ⟶ Y) (a : Y ⟶ A.Y) (ga : Y' ⟶ A.Y)
    (hga : g ≫ a = ga) :
    DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      (projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
      (projectionDescentTotalCoverExplicitPullbackArrowAlong
        (J := J) hSheaf D A g a ga hga) =
    projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A ga := by
  ext
  · rfl
  · dsimp [projectionDescentTotalCoverExplicitPullbackArrowAlong,
      projectionDescentTotalCoverRefinedInner, projectionDescentTotalCoverOuterMap,
      DescentCompletionObjectOver.pullbackCoverBaseArrow]
    rw [← hga]
    exact heq_of_eq ((Category.assoc g a
      (projectionDescentTotalCoverInner (J := J) hSheaf D A).f).symm)

/-- The restricted old explicit-cover member and the directly rebuilt explicit-cover member have
the same underlying base map in the original local descent object. -/
theorem projectionDescentTotalCoverExplicitPullbackArrowAlong_base_f_eq_direct
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (g : Y' ⟶ Y) (a : Y ⟶ A.Y) (ga : Y' ⟶ A.Y)
    (hga : g ≫ a = ga) :
    (DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      (projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
      (projectionDescentTotalCoverExplicitPullbackArrowAlong
        (J := J) hSheaf D A g a ga hga)).f =
    (DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      (projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)).f := by
  rw [projectionDescentTotalCoverExplicitPullbackArrowAlong_base_f]
  dsimp [projectionDescentTotalCoverExplicitPullbackArrow,
    DescentCompletionObjectOver.pullbackCoverBaseArrow,
    projectionDescentTotalCoverOuterMap]
  simp

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
