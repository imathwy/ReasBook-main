import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.TransitionComponent

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

/-- Source stage 3.13 pullback law for the local-refinement comparison
`x_ai|_Y ≅ x_(a,i,Y)|_Y`.  The target is intentionally the refinement already obtained from
`a : Y -> U_ai`, restricted further along `g`; the comparison with the refinement built directly
from `ga : Y' -> U_ai` is a separate cocycle/overlap step. -/
theorem projectionDescentTotalCoverLocalRestrictionIso_pullHom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (g : Y' ⟶ Y)
    (a : Y ⟶ A.Y) (ga : Y' ⟶ A.Y)
    (hga : g ≫ a = ga) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D A a).hom
        g ga g hga (by simp) =
      ((projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A)).overlapIso
        (I₁ := projectionDescentTotalCoverInner (J := J) hSheaf D A)
        (I₂ := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a)
        ga g
        (by
          dsimp [projectionDescentTotalCoverRefinedInner]
          rw [← hga]
          exact Category.assoc g a
            (projectionDescentTotalCoverInner (J := J) hSheaf D A).f)).hom := by
  dsimp [projectionDescentTotalCoverLocalRestrictionIso]
  simpa [projectionDescentTotalCoverRefinedInner, Category.assoc] using
    DescentCompletionObjectOver.HomOver.overlapIso_pullHom (J := J)
      (projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
      (projectionDescentTotalCoverInner (J := J) hSheaf D A)
      (projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a)
      a (𝟙 Y)
      (by simp [projectionDescentTotalCoverRefinedInner])
      g ga g hga (by simp)

/-- Source stage 3.13 owner bridge for local refinements: after pulling back the comparison
attached to `a : Y -> U_ai`, composing with the inner overlap from the old refinement to the
direct refinement attached to `ga : Y' -> U_ai` gives the comparison attached directly to `ga`.
-/
theorem projectionDescentTotalCoverLocalRestrictionIso_pullHom_comp_refined
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (g : Y' ⟶ Y)
    (a : Y ⟶ A.Y) (ga : Y' ⟶ A.Y)
    (hga : g ≫ a = ga) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D A a).hom
        g ga g hga (by simp) ≫
      ((projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A)).overlapIso
        (I₁ := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a)
        (I₂ := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A ga)
        g (𝟙 Y')
        (by
          dsimp [projectionDescentTotalCoverRefinedInner]
          rw [← hga]
          calc
            g ≫ a ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D A).f =
                (g ≫ a) ≫
                  (projectionDescentTotalCoverInner (J := J) hSheaf D A).f :=
              (Category.assoc g a
                (projectionDescentTotalCoverInner (J := J) hSheaf D A).f).symm
            _ =
                𝟙 Y' ≫ (g ≫ a) ≫
                  (projectionDescentTotalCoverInner (J := J) hSheaf D A).f := by simp)).hom =
      (projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D A ga).hom := by
  rw [projectionDescentTotalCoverLocalRestrictionIso_pullHom]
  dsimp [projectionDescentTotalCoverLocalRestrictionIso]
  simpa [projectionDescentTotalCoverRefinedInner, Category.assoc] using
    DescentCompletionObjectOver.overlapIso_hom_comp (J := J)
      (projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
      (I₁ := projectionDescentTotalCoverInner (J := J) hSheaf D A)
      (I₂ := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a)
      (I₃ := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A ga)
      ga g (𝟙 Y')
      (by
        dsimp [projectionDescentTotalCoverRefinedInner]
        rw [← hga]
        exact Category.assoc g a
          (projectionDescentTotalCoverInner (J := J) hSheaf D A).f)
      (by
        dsimp [projectionDescentTotalCoverRefinedInner]
        rw [← hga]
        calc
          g ≫ a ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D A).f =
              (g ≫ a) ≫
                (projectionDescentTotalCoverInner (J := J) hSheaf D A).f :=
            (Category.assoc g a
              (projectionDescentTotalCoverInner (J := J) hSheaf D A).f).symm
          _ =
              𝟙 Y' ≫ (g ≫ a) ≫
                (projectionDescentTotalCoverInner (J := J) hSheaf D A).f := by simp)

/-- Source stage 3.13 inverse pullback law for the local-refinement comparison. -/
theorem projectionDescentTotalCoverLocalRestrictionIso_inv_pullHom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (g : Y' ⟶ Y)
    (a : Y ⟶ A.Y) (ga : Y' ⟶ A.Y)
    (hga : g ≫ a = ga) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D A a).inv
        g g ga (by simp) hga =
      ((projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A)).overlapIso
        (I₁ := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a)
        (I₂ := projectionDescentTotalCoverInner (J := J) hSheaf D A)
        g ga
        (by
          dsimp [projectionDescentTotalCoverRefinedInner]
          rw [← hga]
          exact (Category.assoc g a
            (projectionDescentTotalCoverInner (J := J) hSheaf D A).f).symm)).hom := by
  dsimp [projectionDescentTotalCoverLocalRestrictionIso]
  simpa [projectionDescentTotalCoverRefinedInner,
    DescentCompletionObjectOver.overlapIso,
    DescentCompletionObjectOver.transitionIso, Category.assoc] using
    DescentCompletionObjectOver.HomOver.overlapIso_pullHom (J := J)
      (projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
      (projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a)
      (projectionDescentTotalCoverInner (J := J) hSheaf D A)
      (𝟙 Y) a
      (by simp [projectionDescentTotalCoverRefinedInner])
      g g ga (by simp) hga

/-- Source stage 3.13 pullback law for the explicit-pullback-cover comparison.  This is the
second owner bridge in `rho_(ai)(bj)`: restricting the comparison from the explicit pullback cover
back to the inner refined cover is the corresponding overlap map on the further restriction. -/
theorem projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso_pullHom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (g : Y' ⟶ Y)
    (a : Y ⟶ A.Y) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso
          (J := J) hSheaf D A a).hom
        g g g (by exact Category.comp_id g) (by exact Category.comp_id g) =
      ((projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A)).overlapIso
        (I₁ := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
          (projectionDescentDatumLocalObject (J := J) hSheaf D
            (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
          (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
          (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a))
        (I₂ := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a)
        g g
        (by
          dsimp [DescentCompletionObjectOver.pullbackCoverBaseArrow,
            projectionDescentTotalCoverExplicitPullbackArrow,
            projectionDescentTotalCoverRefinedInner,
            projectionDescentTotalCoverOuterMap]
          simpa only [Category.assoc] using
            congrArg (fun q => g ≫ q)
              (Category.id_comp
                (a ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D A).f)))).hom := by
  dsimp [projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso]
  simpa [projectionDescentTotalCoverExplicitPullbackArrow,
    projectionDescentTotalCoverRefinedInner,
    projectionDescentTotalCoverOuterMap,
    DescentCompletionObjectOver.pullbackCoverBaseArrow, Category.assoc] using
    DescentCompletionObjectOver.HomOver.overlapIso_pullHom (J := J)
      (projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
      (DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
        (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a))
      (projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a)
      (𝟙 Y) (𝟙 Y)
      (by
        dsimp [DescentCompletionObjectOver.pullbackCoverBaseArrow,
          projectionDescentTotalCoverExplicitPullbackArrow,
          projectionDescentTotalCoverRefinedInner,
          projectionDescentTotalCoverOuterMap]
        simpa only [Category.assoc] using
          congrArg (fun q => 𝟙 Y ≫ q)
            (Category.id_comp
              (a ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D A).f)))
      g g g (by exact Category.comp_id g) (by exact Category.comp_id g)

/-- Source stage 3.13 pullback law for the inverse of the explicit-pullback-cover comparison.
It is the same overlap law as
`projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso_pullHom`, with the two owners
reversed. -/
theorem projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso_inv_pullHom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (g : Y' ⟶ Y)
    (a : Y ⟶ A.Y) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso
          (J := J) hSheaf D A a).inv
        g g g (by exact Category.comp_id g) (by exact Category.comp_id g) =
      ((projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A)).overlapIso
        (I₁ := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a)
        (I₂ := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
          (projectionDescentDatumLocalObject (J := J) hSheaf D
            (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
          (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
          (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a))
        g g
        (by
          dsimp [DescentCompletionObjectOver.pullbackCoverBaseArrow,
            projectionDescentTotalCoverExplicitPullbackArrow,
            projectionDescentTotalCoverRefinedInner,
            projectionDescentTotalCoverOuterMap]
          simpa only [Category.assoc] using
            (congrArg (fun q => g ≫ q)
              (Category.id_comp
                (a ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D A).f))).symm)).hom := by
  dsimp [projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso]
  simpa [projectionDescentTotalCoverExplicitPullbackArrow,
    projectionDescentTotalCoverRefinedInner,
    projectionDescentTotalCoverOuterMap,
    DescentCompletionObjectOver.pullbackCoverBaseArrow,
    DescentCompletionObjectOver.overlapIso,
    DescentCompletionObjectOver.transitionIso, Category.assoc] using
    DescentCompletionObjectOver.HomOver.overlapIso_pullHom (J := J)
      (projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
      (projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a)
      (DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
        (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a))
      (𝟙 Y) (𝟙 Y)
      (by
        dsimp [DescentCompletionObjectOver.pullbackCoverBaseArrow,
          projectionDescentTotalCoverExplicitPullbackArrow,
          projectionDescentTotalCoverRefinedInner,
          projectionDescentTotalCoverOuterMap]
        simpa only [Category.assoc] using
          (congrArg (fun q => 𝟙 Y ≫ q)
            (Category.id_comp
              (a ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D A).f))).symm)
      g g g (by exact Category.comp_id g) (by exact Category.comp_id g)

/-- Source stage 3.13 pullback law for the explicit component of one fixed outer transition
`Theta_ab`.  This is the `NaturalHomOver.naturality` field of the transported outer morphism,
specialized to the two explicit pullback-cover arrows.  It deliberately stays with the same
outer morphism owners; comparing these owners with the ones chosen after rebuilding the smaller
overlap is the remaining canonical-pullback coherence step. -/
theorem projectionDescentTotalCoverExplicitTransitionComponent_pullHom_sameOuter
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (g : Y' ⟶ Y)
    (a : Y ⟶ A.Y) (b : Y ⟶ B.Y)
    (h : a ≫ A.f = b ≫ B.f) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentTotalCoverExplicitTransitionComponent (J := J) hSheaf D A B a b h)
        g g g (by exact Category.comp_id g) (by exact Category.comp_id g) =
      letI := category (J := J) hSheaf
      let α :=
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
            (Category.comp_id (g ≫ 𝟙 Y))) := by
  letI := category (J := J) hSheaf
  let α :=
    projectionDescentExplicitOuterFiberHomForTotalCover (J := J)
      hSheaf D A B a b h
  have hbase :
      α.1.base = 𝟙 Y :=
    projectionDescentExplicitOuterFiberHomForTotalCover_base
      (J := J) hSheaf D A B a b h
  dsimp [projectionDescentTotalCoverExplicitTransitionComponent]
  simpa [α, hbase, projectionDescentTotalCoverExplicitPullbackArrow] using
    α.1.components.naturality
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B b)
      (𝟙 Y) (𝟙 Y)
      (by
        rw [hbase]
        dsimp [projectionDescentTotalCoverExplicitPullbackArrow]
        change 𝟙 Y ≫ 𝟙 Y ≫ 𝟙 Y = 𝟙 Y ≫ 𝟙 Y
        calc
          𝟙 Y ≫ 𝟙 Y ≫ 𝟙 Y = 𝟙 Y ≫ 𝟙 Y := by rw [Category.id_comp]
          _ = 𝟙 Y ≫ 𝟙 Y := rfl)
      g g g (by exact Category.comp_id g) (by exact Category.comp_id g)

/-- Source stage 3.13 pullback law for the outer transition `Theta_ab`, after specializing it to
members of the total cover `{U_ai -> U}`.  This isolates the part of the final `rho` restriction
law that comes directly from the outer descent datum. -/
theorem projectionDescentOuterFiberHomForTotalCover_pullHom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (g : Y' ⟶ Y)
    (a : Y ⟶ A.Y) (b : Y ⟶ B.Y)
    (h : a ≫ A.f = b ≫ B.f)
    (ga : Y' ⟶ A.Y) (gb : Y' ⟶ B.Y)
    (hga : g ≫ a = ga) (hgb : g ≫ b = gb) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor P)
        (projectionDescentOuterFiberHomForTotalCover (J := J) hSheaf D A B a b h)
        g
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga)
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B gb)
        (by
          simp [projectionDescentTotalCoverOuterMap, ← hga, Category.assoc])
        (by
          simp [projectionDescentTotalCoverOuterMap, ← hgb, Category.assoc]) =
      projectionDescentOuterFiberHomForTotalCover (J := J) hSheaf D A B ga gb
        (by
          calc
            ga ≫ A.f = g ≫ a ≫ A.f := by rw [← hga]; simp [Category.assoc]
            _ = g ≫ b ≫ B.f := by
              simpa [Category.assoc] using congrArg (fun q => g ≫ q) h
            _ = gb ≫ B.f := by rw [← hgb]; simp [Category.assoc]) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  dsimp [projectionDescentOuterFiberHomForTotalCover, projectionDescentOuterFiberHom]
  simpa [projectionDescentTotalCoverOuterMap, Category.assoc] using
    D.pullHom_hom g
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a ≫
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A).f)
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga ≫
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A).f)
      (by
        simp [projectionDescentTotalCoverOuterMap, ← hga, Category.assoc])
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b)
      rfl
      (projectionDescentTotalCoverOuterMap_fac (J := J) hSheaf D A B a b h).symm
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga)
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B gb)
      (by simp [projectionDescentTotalCoverOuterMap, ← hga, Category.assoc])
      (by simp [projectionDescentTotalCoverOuterMap, ← hgb, Category.assoc])

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
