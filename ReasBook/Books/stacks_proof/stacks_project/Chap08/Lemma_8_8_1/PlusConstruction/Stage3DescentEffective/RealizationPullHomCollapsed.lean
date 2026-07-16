import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationPullHom

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

set_option backward.isDefEq.respectTransparency false in
/-- Source stage 3.13 restriction law for the realization component
`Lambda_a,(b,j),i = rho_(b,j),(a,i)`, expanded into the five local factors obtained by
restricting the definition of the component.

This is the realization-side analogue of
`projectionDescentTotalCoverTransitionComponent_pullHom_expanded`.  It deliberately keeps the
middle component with the old explicit pullback owners; comparing those owners with the directly
rebuilt smaller-overlap owners is the remaining canonical-owner bridge. -/
theorem projectionDescentRealizationComponentFromTotalCoverToDatumInner_pullHom_expanded
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
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentRealizationComponentFromTotalCoverToDatumInner
          (J := J) hSheaf D A I a K k h)
        g ga gk hga hgk =
      ((projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A)).overlapIso
        (I₁ := projectionDescentTotalCoverInner (J := J) hSheaf D A)
        (I₂ := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a)
        ga g
        (by
          dsimp [projectionDescentTotalCoverRefinedInner]
          rw [← hga]
          exact Category.assoc g a
            (projectionDescentTotalCoverInner (J := J) hSheaf D A).f)).hom ≫
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
                (a ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D A).f))).symm)).hom ≫
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
            congrArg (fun q => g ≫ q) (Category.id_comp (k ≫ K.f)))).hom ≫
      ((projectionDescentDatumLocalObject (J := J) hSheaf D I).overlapIso
        (I₁ := projectionDescentDatumRefinedInner (J := J) hSheaf D I K k)
        (I₂ := K)
        g gk
        (by
          dsimp [projectionDescentDatumRefinedInner]
          rw [← hgk]
          exact (Category.assoc g k K.f).symm)).hom := by
  dsimp [projectionDescentRealizationComponentFromTotalCoverToDatumInner]
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp
    (F := canonicalFiberPseudofunctor X.p)
    (projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D A a).hom
    ((projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso (J := J) hSheaf D A a).inv ≫
      projectionDescentExplicitTransitionComponentFromTotalCoverToDatumInner
        (J := J) hSheaf D A I a K k h ≫
        (projectionDescentDatumExplicitPullbackArrowRestrictionIso (J := J)
          hSheaf D I K k).hom ≫
          (projectionDescentDatumLocalRestrictionIso (J := J) hSheaf D I K k).inv)
    g ga g gk hga (by exact Category.comp_id g) hgk]
  rw [projectionDescentTotalCoverLocalRestrictionIso_pullHom]
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp
    (F := canonicalFiberPseudofunctor X.p)
    (projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso
      (J := J) hSheaf D A a).inv
    (projectionDescentExplicitTransitionComponentFromTotalCoverToDatumInner
      (J := J) hSheaf D A I a K k h ≫
      (projectionDescentDatumExplicitPullbackArrowRestrictionIso (J := J)
        hSheaf D I K k).hom ≫
        (projectionDescentDatumLocalRestrictionIso (J := J) hSheaf D I K k).inv)
    g g g gk (by exact Category.comp_id g) (by exact Category.comp_id g) hgk]
  rw [projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso_inv_pullHom]
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp
    (F := canonicalFiberPseudofunctor X.p)
    (projectionDescentExplicitTransitionComponentFromTotalCoverToDatumInner
      (J := J) hSheaf D A I a K k h)
    ((projectionDescentDatumExplicitPullbackArrowRestrictionIso (J := J)
      hSheaf D I K k).hom ≫
      (projectionDescentDatumLocalRestrictionIso (J := J) hSheaf D I K k).inv)
    g g g gk (by exact Category.comp_id g) (by exact Category.comp_id g) hgk]
  rw [projectionDescentExplicitTransitionComponentFromTotalCoverToDatumInner_pullHom_sameOuter]
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp
    (F := canonicalFiberPseudofunctor X.p)
    (projectionDescentDatumExplicitPullbackArrowRestrictionIso (J := J)
      hSheaf D I K k).hom
    (projectionDescentDatumLocalRestrictionIso (J := J) hSheaf D I K k).inv
    g g g gk (by exact Category.comp_id g) (by exact Category.comp_id g) hgk]
  rw [projectionDescentDatumExplicitPullbackArrowRestrictionIso_pullHom]
  rw [projectionDescentDatumLocalRestrictionIso_inv_pullHom]

/-- Source stage 3.13 restriction law for the realization component, after collapsing the source
and target explicit-restriction pairs in the expanded formula.  The only remaining
non-definitional comparison is the outer `Theta` component between old explicit pullback owners
and the directly rebuilt owners. -/
theorem projectionDescentRealizationComponentFromTotalCoverToDatumInner_pullHom_collapsed
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
    let hA₁₂ : ga ≫ IAinner.f = g ≫ IAold.f := by
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
    let hK₁₂ : g ≫ Kold.f = gk ≫ K.f := by
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
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentRealizationComponentFromTotalCoverToDatumInner
          (J := J) hSheaf D A I a K k h)
        g ga gk hga hgk =
      (DA.overlapIso (I₁ := IAinner) (I₂ := IAold) ga g hA₁₂).hom ≫
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
        (DB.overlapIso (I₁ := Kold) (I₂ := K) g gk hK₁₂).hom := by
  rw [projectionDescentRealizationComponentFromTotalCoverToDatumInner_pullHom_expanded]
  dsimp only
  let DA :=
    projectionDescentDatumLocalObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
  let DB := projectionDescentDatumLocalObject (J := J) hSheaf D I
  let IAinner := projectionDescentTotalCoverInner (J := J) hSheaf D A
  let IAa := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a
  let Kk := projectionDescentDatumRefinedInner (J := J) hSheaf D I K k
  let IAold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
  let Kold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DB (k ≫ K.f)
    (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k)
  let hA₁₂ : ga ≫ IAinner.f = g ≫ IAa.f := by
    dsimp [IAa, projectionDescentTotalCoverRefinedInner]
    rw [← hga]
    exact Category.assoc g a IAinner.f
  let hA₂₃ : g ≫ IAa.f = g ≫ IAold.f := by
    dsimp [IAa, IAold, DA, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentTotalCoverRefinedInner, projectionDescentTotalCoverOuterMap]
    simpa only [Category.assoc] using
      (congrArg (fun q => g ≫ q)
        (Category.id_comp
          (a ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D A).f))).symm
  let hK₁₂ : g ≫ Kold.f = g ≫ Kk.f := by
    dsimp [Kk, Kold, DB, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentDatumExplicitPullbackArrow,
      projectionDescentDatumRefinedInner]
    simpa only [Category.assoc] using
      congrArg (fun q => g ≫ q) (Category.id_comp (k ≫ K.f))
  let hK₂₃ : g ≫ Kk.f = gk ≫ K.f := by
    dsimp [Kk, projectionDescentDatumRefinedInner]
    rw [← hgk]
    exact (Category.assoc g k K.f).symm
  have hleft :=
    DescentCompletionObjectOver.overlapIso_hom_comp (J := J) DA
      (I₁ := IAinner) (I₂ := IAa) (I₃ := IAold) ga g g hA₁₂ hA₂₃
  have hright :=
    DescentCompletionObjectOver.overlapIso_hom_comp (J := J) DB
      (I₁ := Kold) (I₂ := Kk) (I₃ := K) g g gk hK₁₂ hK₂₃
  rw [← Category.assoc]
  rw [hleft]
  let α :=
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner (J := J)
      hSheaf D A I a K k h
  let mid :=
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
          (Category.comp_id (g ≫ 𝟙 Y)))
  let l :=
    (DA.overlapIso (I₁ := IAinner) (I₂ := IAold) ga g (hA₁₂.trans hA₂₃)).hom
  let r₁ := (DB.overlapIso (I₁ := Kold) (I₂ := Kk) g g hK₁₂).hom
  let r₂ := (DB.overlapIso (I₁ := Kk) (I₂ := K) g gk hK₂₃).hom
  let r := (DB.overlapIso (I₁ := Kold) (I₂ := K) g gk (hK₁₂.trans hK₂₃)).hom
  have hright' : r₁ ≫ r₂ = r := by
    simpa [r₁, r₂, r] using hright
  change l ≫ mid ≫ r₁ ≫ r₂ = l ≫ mid ≫ r
  calc
    l ≫ mid ≫ r₁ ≫ r₂ = l ≫ mid ≫ (r₁ ≫ r₂) := rfl
    _ = l ≫ mid ≫ r := by
      exact congrArg (fun q => l ≫ mid ≫ q) hright'

/-- Source stage 3.13 realization component in the same three-factor collapsed normal form as
`projectionDescentRealizationComponentFromTotalCoverToDatumInner_pullHom_collapsed`.  This is the
`g = id` specialization used to compare a restricted old explicit owner with the directly rebuilt
owner at the smaller overlap. -/
theorem projectionDescentRealizationComponentFromTotalCoverToDatumInner_collapsed
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (a : Y ⟶ A.Y)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : Y ⟶ K.Y)
    (h : a ≫ A.f = k ≫ K.f ≫ I.f) :
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
    let hA₁₂ : a ≫ IAinner.f = 𝟙 Y ≫ IAold.f := by
      dsimp [IAinner, IAold, DA, DescentCompletionObjectOver.pullbackCoverBaseArrow,
        projectionDescentTotalCoverExplicitPullbackArrow,
        projectionDescentTotalCoverOuterMap]
      simp
    let hK₁₂ : 𝟙 Y ≫ Kold.f = k ≫ K.f := by
      dsimp [Kold, DB, DescentCompletionObjectOver.pullbackCoverBaseArrow,
        projectionDescentDatumExplicitPullbackArrow]
      simp
    projectionDescentRealizationComponentFromTotalCoverToDatumInner
        (J := J) hSheaf D A I a K k h =
      (DA.overlapIso (I₁ := IAinner) (I₂ := IAold) a (𝟙 Y) hA₁₂).hom ≫
        (let α :=
          projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner (J := J)
            hSheaf D A I a K k h
        α.1.components.toHomOver.family
          (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
          (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k)
          (𝟙 Y) (𝟙 Y)
          (by
            have hbase :
                α.1.base = 𝟙 Y :=
              projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
                (J := J) hSheaf D A I a K k h
            rw [hbase]
            dsimp [projectionDescentTotalCoverExplicitPullbackArrow,
              projectionDescentDatumExplicitPullbackArrow]
            calc
              𝟙 Y ≫ 𝟙 Y ≫ 𝟙 Y = 𝟙 Y ≫ 𝟙 Y := by rw [Category.id_comp]
              _ = 𝟙 Y ≫ 𝟙 Y := rfl)) ≫
        (DB.overlapIso (I₁ := Kold) (I₂ := K) (𝟙 Y) k hK₁₂).hom := by
  have hpull :=
    projectionDescentRealizationComponentFromTotalCoverToDatumInner_pullHom_collapsed
      (J := J) hSheaf D A I (𝟙 Y) a K k h a k
      (by simp) (by simp)
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_id] at hpull
  simpa [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Category.assoc] using hpull

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
