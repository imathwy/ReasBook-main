import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationComponent

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

/-- Source stage 3.13 realization helper: pullback law for the target-side local refinement
comparison used in `Λ_a`. -/
theorem projectionDescentDatumLocalRestrictionIso_pullHom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (g : Y' ⟶ Y)
    (k : Y ⟶ K.Y) (gk : Y' ⟶ K.Y)
    (hgk : g ≫ k = gk) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentDatumLocalRestrictionIso (J := J) hSheaf D I K k).hom
        g gk g hgk (by simp) =
      ((projectionDescentDatumLocalObject (J := J) hSheaf D I).overlapIso
        (I₁ := K)
        (I₂ := projectionDescentDatumRefinedInner (J := J) hSheaf D I K k)
        gk g
        (by
          dsimp [projectionDescentDatumRefinedInner]
          rw [← hgk]
          exact Category.assoc g k K.f)).hom := by
  dsimp [projectionDescentDatumLocalRestrictionIso]
  simpa [projectionDescentDatumRefinedInner, Category.assoc] using
    DescentCompletionObjectOver.HomOver.overlapIso_pullHom (J := J)
      (projectionDescentDatumLocalObject (J := J) hSheaf D I)
      K
      (projectionDescentDatumRefinedInner (J := J) hSheaf D I K k)
      k (𝟙 Y)
      (by simp [projectionDescentDatumRefinedInner])
      g gk g hgk (by simp)

/-- After restriction, composing the old refined owner with the direct refined owner recovers the
target-side local-refinement comparison attached directly to the smaller map. -/
theorem projectionDescentDatumLocalRestrictionIso_pullHom_comp_refined
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (g : Y' ⟶ Y)
    (k : Y ⟶ K.Y) (gk : Y' ⟶ K.Y)
    (hgk : g ≫ k = gk) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentDatumLocalRestrictionIso (J := J) hSheaf D I K k).hom
        g gk g hgk (by simp) ≫
      ((projectionDescentDatumLocalObject (J := J) hSheaf D I).overlapIso
        (I₁ := projectionDescentDatumRefinedInner (J := J) hSheaf D I K k)
        (I₂ := projectionDescentDatumRefinedInner (J := J) hSheaf D I K gk)
        g (𝟙 Y')
        (by
          dsimp [projectionDescentDatumRefinedInner]
          rw [← hgk]
          calc
            g ≫ k ≫ K.f = (g ≫ k) ≫ K.f :=
              (Category.assoc g k K.f).symm
            _ = 𝟙 Y' ≫ (g ≫ k) ≫ K.f := by simp)).hom =
      (projectionDescentDatumLocalRestrictionIso (J := J) hSheaf D I K gk).hom := by
  rw [projectionDescentDatumLocalRestrictionIso_pullHom]
  dsimp [projectionDescentDatumLocalRestrictionIso]
  simpa [projectionDescentDatumRefinedInner, Category.assoc] using
    DescentCompletionObjectOver.overlapIso_hom_comp (J := J)
      (projectionDescentDatumLocalObject (J := J) hSheaf D I)
      (I₁ := K)
      (I₂ := projectionDescentDatumRefinedInner (J := J) hSheaf D I K k)
      (I₃ := projectionDescentDatumRefinedInner (J := J) hSheaf D I K gk)
      gk g (𝟙 Y')
      (by
        dsimp [projectionDescentDatumRefinedInner]
        rw [← hgk]
        exact Category.assoc g k K.f)
      (by
        dsimp [projectionDescentDatumRefinedInner]
        rw [← hgk]
        calc
          g ≫ k ≫ K.f = (g ≫ k) ≫ K.f :=
            (Category.assoc g k K.f).symm
          _ = 𝟙 Y' ≫ (g ≫ k) ≫ K.f := by simp)

/-- Pullback law for the inverse of the target-side local-refinement comparison. -/
theorem projectionDescentDatumLocalRestrictionIso_inv_pullHom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (g : Y' ⟶ Y)
    (k : Y ⟶ K.Y) (gk : Y' ⟶ K.Y)
    (hgk : g ≫ k = gk) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentDatumLocalRestrictionIso (J := J) hSheaf D I K k).inv
        g g gk (by simp) hgk =
      ((projectionDescentDatumLocalObject (J := J) hSheaf D I).overlapIso
        (I₁ := projectionDescentDatumRefinedInner (J := J) hSheaf D I K k)
        (I₂ := K)
        g gk
        (by
          dsimp [projectionDescentDatumRefinedInner]
          rw [← hgk]
          exact (Category.assoc g k K.f).symm)).hom := by
  dsimp [projectionDescentDatumLocalRestrictionIso]
  simpa [projectionDescentDatumRefinedInner,
    DescentCompletionObjectOver.overlapIso,
    DescentCompletionObjectOver.transitionIso, Category.assoc] using
    DescentCompletionObjectOver.HomOver.overlapIso_pullHom (J := J)
      (projectionDescentDatumLocalObject (J := J) hSheaf D I)
      (projectionDescentDatumRefinedInner (J := J) hSheaf D I K k)
      K
      (𝟙 Y) k
      (by simp [projectionDescentDatumRefinedInner])
      g g gk (by simp) hgk

/-- Pullback law for the explicit-pullback-cover comparison on the target side of `Λ_a`. -/
theorem projectionDescentDatumExplicitPullbackArrowRestrictionIso_pullHom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (g : Y' ⟶ Y)
    (k : Y ⟶ K.Y) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentDatumExplicitPullbackArrowRestrictionIso
          (J := J) hSheaf D I K k).hom
        g g g (by exact Category.comp_id g) (by exact Category.comp_id g) =
      ((projectionDescentDatumLocalObject (J := J) hSheaf D I).overlapIso
        (I₁ := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
          (projectionDescentDatumLocalObject (J := J) hSheaf D I)
          (k ≫ K.f)
          (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k))
        (I₂ := projectionDescentDatumRefinedInner (J := J) hSheaf D I K k)
        g g
        (by
          dsimp [DescentCompletionObjectOver.pullbackCoverBaseArrow,
            projectionDescentDatumExplicitPullbackArrow,
            projectionDescentDatumRefinedInner]
          simpa only [Category.assoc] using
            congrArg (fun q => g ≫ q) (Category.id_comp (k ≫ K.f)))).hom := by
  dsimp [projectionDescentDatumExplicitPullbackArrowRestrictionIso]
  simpa [projectionDescentDatumExplicitPullbackArrow,
    projectionDescentDatumRefinedInner,
    DescentCompletionObjectOver.pullbackCoverBaseArrow, Category.assoc] using
    DescentCompletionObjectOver.HomOver.overlapIso_pullHom (J := J)
      (projectionDescentDatumLocalObject (J := J) hSheaf D I)
      (DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D I)
        (k ≫ K.f)
        (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k))
      (projectionDescentDatumRefinedInner (J := J) hSheaf D I K k)
      (𝟙 Y) (𝟙 Y)
      (by
        dsimp [DescentCompletionObjectOver.pullbackCoverBaseArrow,
          projectionDescentDatumExplicitPullbackArrow,
          projectionDescentDatumRefinedInner]
        simpa only [Category.assoc] using
          congrArg (fun q => 𝟙 Y ≫ q) (Category.id_comp (k ≫ K.f)))
      g g g (by exact Category.comp_id g) (by exact Category.comp_id g)

/-- Pullback law for the inverse explicit-pullback-cover comparison on the target side of
`Λ_a`. -/
theorem projectionDescentDatumExplicitPullbackArrowRestrictionIso_inv_pullHom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (g : Y' ⟶ Y)
    (k : Y ⟶ K.Y) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentDatumExplicitPullbackArrowRestrictionIso
          (J := J) hSheaf D I K k).inv
        g g g (by exact Category.comp_id g) (by exact Category.comp_id g) =
      ((projectionDescentDatumLocalObject (J := J) hSheaf D I).overlapIso
        (I₁ := projectionDescentDatumRefinedInner (J := J) hSheaf D I K k)
        (I₂ := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
          (projectionDescentDatumLocalObject (J := J) hSheaf D I)
          (k ≫ K.f)
          (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k))
        g g
        (by
          dsimp [DescentCompletionObjectOver.pullbackCoverBaseArrow,
            projectionDescentDatumExplicitPullbackArrow,
            projectionDescentDatumRefinedInner]
          simpa only [Category.assoc] using
            (congrArg (fun q => g ≫ q) (Category.id_comp (k ≫ K.f))).symm)).hom := by
  dsimp [projectionDescentDatumExplicitPullbackArrowRestrictionIso]
  simpa [projectionDescentDatumExplicitPullbackArrow,
    projectionDescentDatumRefinedInner,
    DescentCompletionObjectOver.pullbackCoverBaseArrow,
    DescentCompletionObjectOver.overlapIso,
    DescentCompletionObjectOver.transitionIso, Category.assoc] using
    DescentCompletionObjectOver.HomOver.overlapIso_pullHom (J := J)
      (projectionDescentDatumLocalObject (J := J) hSheaf D I)
      (projectionDescentDatumRefinedInner (J := J) hSheaf D I K k)
      (DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D I)
        (k ≫ K.f)
        (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k))
      (𝟙 Y) (𝟙 Y)
      (by
        dsimp [DescentCompletionObjectOver.pullbackCoverBaseArrow,
          projectionDescentDatumExplicitPullbackArrow,
          projectionDescentDatumRefinedInner]
        simpa only [Category.assoc] using
          (congrArg (fun q => 𝟙 Y ≫ q) (Category.id_comp (k ≫ K.f))).symm)
      g g g (by exact Category.comp_id g) (by exact Category.comp_id g)

/-- Pullback law for the explicit component of the fixed outer transition used by the realization
map `Λ_a`.  This is the `NaturalHomOver.naturality` field of the transported outer morphism,
specialized to the source total-cover explicit pullback arrow and the target datum explicit
pullback arrow. -/
theorem projectionDescentExplicitTransitionComponentFromTotalCoverToDatumInner_pullHom_sameOuter
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (g : Y' ⟶ Y)
    (a : Y ⟶ A.Y)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : Y ⟶ K.Y)
    (h : a ≫ A.f = k ≫ K.f ≫ I.f) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentExplicitTransitionComponentFromTotalCoverToDatumInner
          (J := J) hSheaf D A I a K k h)
        g g g (by exact Category.comp_id g) (by exact Category.comp_id g) =
      letI := category (J := J) hSheaf
      let α :=
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
            (Category.comp_id (g ≫ 𝟙 Y))) := by
  letI := category (J := J) hSheaf
  let α :=
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner (J := J)
      hSheaf D A I a K k h
  have hbase :
      α.1.base = 𝟙 Y :=
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
      (J := J) hSheaf D A I a K k h
  dsimp [projectionDescentExplicitTransitionComponentFromTotalCoverToDatumInner]
  simpa [α, hbase, projectionDescentTotalCoverExplicitPullbackArrow,
    projectionDescentDatumExplicitPullbackArrow] using
    α.1.components.naturality
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
      (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k)
      (𝟙 Y) (𝟙 Y)
      (by
        rw [hbase]
        dsimp [projectionDescentTotalCoverExplicitPullbackArrow,
          projectionDescentDatumExplicitPullbackArrow]
        change 𝟙 Y ≫ 𝟙 Y ≫ 𝟙 Y = 𝟙 Y ≫ 𝟙 Y
        calc
          𝟙 Y ≫ 𝟙 Y ≫ 𝟙 Y = 𝟙 Y ≫ 𝟙 Y := by rw [Category.id_comp]
          _ = 𝟙 Y ≫ 𝟙 Y := rfl)
      g g g (by exact Category.comp_id g) (by exact Category.comp_id g)

/-- Pullback law for the canonical-pullback owner form of the outer transition used by the
realization map `Λ_a`.  This isolates the part coming directly from the outer descent datum `D`,
before the explicit-pullback owner bridges are applied. -/
theorem projectionDescentOuterFiberHomFromTotalCoverToDatumInner_pullHom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (g : Y' ⟶ Y)
    (a : Y ⟶ A.Y)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : Y ⟶ K.Y)
    (h : a ≫ A.f = k ≫ K.f ≫ I.f)
    (ga : Y' ⟶ A.Y) (gk : Y' ⟶ K.Y)
    (hga : g ≫ a = ga) (hgk : g ≫ k = gk) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor P)
        (projectionDescentOuterFiberHomFromTotalCoverToDatumInner
          (J := J) hSheaf D A I a K k h)
        g
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga)
        (gk ≫ K.f)
        (by
          simp [projectionDescentTotalCoverOuterMap, ← hga, Category.assoc])
        (by
          simp [← hgk, Category.assoc]) =
      projectionDescentOuterFiberHomFromTotalCoverToDatumInner
        (J := J) hSheaf D A I ga K gk
        (by
          calc
            ga ≫ A.f = g ≫ a ≫ A.f := by rw [← hga]; simp [Category.assoc]
            _ = g ≫ (k ≫ K.f ≫ I.f) := by
              simpa [Category.assoc] using congrArg (fun q => g ≫ q) h
            _ = gk ≫ K.f ≫ I.f := by rw [← hgk]; simp [Category.assoc]) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  dsimp [projectionDescentOuterFiberHomFromTotalCoverToDatumInner,
    projectionDescentOuterFiberHom]
  simpa [projectionDescentTotalCoverOuterMap, Category.assoc] using
    D.pullHom_hom g
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a ≫
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A).f)
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga ≫
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A).f)
      (by
        simp [projectionDescentTotalCoverOuterMap, ← hga, Category.assoc])
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
      (k ≫ K.f)
      rfl
      (by
        calc
          (k ≫ K.f) ≫ I.f = k ≫ K.f ≫ I.f := by simp [Category.assoc]
          _ = a ≫ A.f := h.symm
          _ =
              projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a ≫
                (projectionDescentTotalCoverOuter (J := J) hSheaf D A).f := by
            have hA :
                a ≫ ((projectionDescentTotalCoverInner (J := J) hSheaf D A).f ≫
                    (projectionDescentTotalCoverOuter (J := J) hSheaf D A).f) =
                  a ≫ A.f :=
              congrArg (fun q => a ≫ q)
                (projectionDescentTotalCover_fac (J := J) hSheaf D A)
            simpa [projectionDescentTotalCoverOuterMap, Category.assoc] using hA.symm)
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga)
      (gk ≫ K.f)
      (by simp [projectionDescentTotalCoverOuterMap, ← hga, Category.assoc])
      (by simp [← hgk, Category.assoc])

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
