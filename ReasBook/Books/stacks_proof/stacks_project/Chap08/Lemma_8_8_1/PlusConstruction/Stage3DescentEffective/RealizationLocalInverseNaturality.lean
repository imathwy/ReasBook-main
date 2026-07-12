import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationLocalInverseCompatibility

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

/-- Pullback law for the explicit component of the fixed outer transition used by the inverse
realization map `Lambda_a^{-1}`.

This is the `NaturalHomOver.naturality` field of the transported outer morphism, specialized to
the source datum explicit pullback arrow and the target total-cover explicit pullback arrow. -/
theorem projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover_pullHom_sameOuter
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
    (h : k ≫ K.f ≫ I.f = a ≫ A.f) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover
          (J := J) hSheaf D I K k A a h)
        g g g (by exact Category.comp_id g) (by exact Category.comp_id g) =
      letI := category (J := J) hSheaf
      let α :=
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
            (Category.comp_id (g ≫ 𝟙 Y))) := by
  letI := category (J := J) hSheaf
  let α :=
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover (J := J)
      hSheaf D I K k A a h
  have hbase :
      α.1.base = 𝟙 Y :=
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_base
      (J := J) hSheaf D I K k A a h
  dsimp [projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover]
  simpa [α, hbase, projectionDescentDatumExplicitPullbackArrow,
    projectionDescentTotalCoverExplicitPullbackArrow] using
    α.1.components.naturality
      (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
      (𝟙 Y) (𝟙 Y)
      (by
        rw [hbase]
        dsimp [projectionDescentDatumExplicitPullbackArrow,
          projectionDescentTotalCoverExplicitPullbackArrow]
        change 𝟙 Y ≫ 𝟙 Y ≫ 𝟙 Y = 𝟙 Y ≫ 𝟙 Y
        calc
          𝟙 Y ≫ 𝟙 Y ≫ 𝟙 Y = 𝟙 Y ≫ 𝟙 Y := by rw [Category.id_comp]
          _ = 𝟙 Y ≫ 𝟙 Y := rfl)
      g g g (by exact Category.comp_id g) (by exact Category.comp_id g)

set_option backward.isDefEq.respectTransparency false in
/-- Source stage 3.13 restriction law for the inverse realization component
`Lambda_a^{-1}_{i,(b,j)} = rho_(a,i),(b,j)`, expanded into the five local factors obtained by
restricting the definition of the component.

The comparison with the directly rebuilt smaller-overlap component is the remaining
canonical-owner bridge, handled after this expanded normal form. -/
theorem projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover_pullHom_expanded
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
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover
          (J := J) hSheaf D I K k A a h)
        g gk ga hgk hga =
      ((projectionDescentDatumLocalObject (J := J) hSheaf D I).overlapIso
        (I₁ := K)
        (I₂ := projectionDescentDatumRefinedInner (J := J) hSheaf D I K k)
        gk g
        (by
          dsimp [projectionDescentDatumRefinedInner]
          rw [← hgk]
          exact Category.assoc g k K.f)).hom ≫
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
            (congrArg (fun q => g ≫ q) (Category.id_comp (k ≫ K.f))).symm)).hom ≫
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
                (a ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D A).f)))).hom ≫
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
  dsimp [projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover]
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp
    (F := canonicalFiberPseudofunctor X.p)
    (projectionDescentDatumLocalRestrictionIso (J := J) hSheaf D I K k).hom
    ((projectionDescentDatumExplicitPullbackArrowRestrictionIso
      (J := J) hSheaf D I K k).inv ≫
      projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover
        (J := J) hSheaf D I K k A a h ≫
        (projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso
          (J := J) hSheaf D A a).hom ≫
          (projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D A a).inv)
    g gk g ga hgk (by exact Category.comp_id g) hga]
  rw [projectionDescentDatumLocalRestrictionIso_pullHom]
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp
    (F := canonicalFiberPseudofunctor X.p)
    (projectionDescentDatumExplicitPullbackArrowRestrictionIso
      (J := J) hSheaf D I K k).inv
    (projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover
      (J := J) hSheaf D I K k A a h ≫
      (projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso
        (J := J) hSheaf D A a).hom ≫
        (projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D A a).inv)
    g g g ga (by exact Category.comp_id g) (by exact Category.comp_id g) hga]
  rw [projectionDescentDatumExplicitPullbackArrowRestrictionIso_inv_pullHom]
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp
    (F := canonicalFiberPseudofunctor X.p)
    (projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover
      (J := J) hSheaf D I K k A a h)
    ((projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso
      (J := J) hSheaf D A a).hom ≫
      (projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D A a).inv)
    g g g ga (by exact Category.comp_id g) (by exact Category.comp_id g) hga]
  rw [projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover_pullHom_sameOuter]
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp
    (F := canonicalFiberPseudofunctor X.p)
    (projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso
      (J := J) hSheaf D A a).hom
    (projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D A a).inv
    g g g ga (by exact Category.comp_id g) (by exact Category.comp_id g) hga]
  rw [projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso_pullHom]
  rw [projectionDescentTotalCoverLocalRestrictionIso_inv_pullHom]

/-- Source stage 3.13 restriction law for the inverse realization component, after collapsing the
source and target explicit-restriction pairs in the expanded formula.

The only remaining non-definitional comparison is the middle `Theta` component between old
explicit pullback owners and the directly rebuilt owners. -/
theorem projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover_pullHom_collapsed
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
    let Kold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      DB (k ≫ K.f)
      (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k)
    let IAinner := projectionDescentTotalCoverInner (J := J) hSheaf D A
    let IAold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
    let hK₁₂ : gk ≫ K.f = g ≫ Kold.f := by
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
    let hA₁₂ : g ≫ IAold.f = ga ≫ IAinner.f := by
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
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover
          (J := J) hSheaf D I K k A a h)
        g gk ga hgk hga =
      (DB.overlapIso (I₁ := K) (I₂ := Kold) gk g hK₁₂).hom ≫
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
        (DA.overlapIso (I₁ := IAold) (I₂ := IAinner) g ga hA₁₂).hom := by
  rw [projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover_pullHom_expanded]
  dsimp only
  let DB := projectionDescentDatumLocalObject (J := J) hSheaf D I
  let DA :=
    projectionDescentDatumLocalObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
  let Kk := projectionDescentDatumRefinedInner (J := J) hSheaf D I K k
  let Kold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DB (k ≫ K.f)
    (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k)
  let IAinner := projectionDescentTotalCoverInner (J := J) hSheaf D A
  let IAa := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a
  let IAold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
  let hK₁₂ : gk ≫ K.f = g ≫ Kk.f := by
    dsimp [Kk, projectionDescentDatumRefinedInner]
    rw [← hgk]
    exact Category.assoc g k K.f
  let hK₂₃ : g ≫ Kk.f = g ≫ Kold.f := by
    dsimp [Kk, Kold, DB, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentDatumExplicitPullbackArrow,
      projectionDescentDatumRefinedInner]
    simpa only [Category.assoc] using
      (congrArg (fun q => g ≫ q) (Category.id_comp (k ≫ K.f))).symm
  let hA₁₂ : g ≫ IAold.f = g ≫ IAa.f := by
    dsimp [IAa, IAold, DA, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentTotalCoverRefinedInner, projectionDescentTotalCoverOuterMap]
    simpa only [Category.assoc] using
      congrArg (fun q => g ≫ q)
        (Category.id_comp
          (a ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D A).f))
  let hA₂₃ : g ≫ IAa.f = ga ≫ IAinner.f := by
    dsimp [IAa, projectionDescentTotalCoverRefinedInner, IAinner]
    rw [← hga]
    exact (Category.assoc g a IAinner.f).symm
  have hleft :=
    DescentCompletionObjectOver.overlapIso_hom_comp (J := J) DB
      (I₁ := K) (I₂ := Kk) (I₃ := Kold)
      gk g g hK₁₂ hK₂₃
  have hright :=
    DescentCompletionObjectOver.overlapIso_hom_comp (J := J) DA
      (I₁ := IAold) (I₂ := IAa) (I₃ := IAinner)
      g g ga hA₁₂ hA₂₃
  let mid :=
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
  let l₁ := (DB.overlapIso (I₁ := K) (I₂ := Kk) gk g hK₁₂).hom
  let l₂ := (DB.overlapIso (I₁ := Kk) (I₂ := Kold) g g hK₂₃).hom
  let l := (DB.overlapIso (I₁ := K) (I₂ := Kold) gk g (hK₁₂.trans hK₂₃)).hom
  let r₁ := (DA.overlapIso (I₁ := IAold) (I₂ := IAa) g g hA₁₂).hom
  let r₂ := (DA.overlapIso (I₁ := IAa) (I₂ := IAinner) g ga hA₂₃).hom
  let r := (DA.overlapIso (I₁ := IAold) (I₂ := IAinner) g ga (hA₁₂.trans hA₂₃)).hom
  have hleft' : l₁ ≫ l₂ = l := by
    simpa [l₁, l₂, l] using hleft
  have hright' : r₁ ≫ r₂ = r := by
    simpa [r₁, r₂, r] using hright
  change l₁ ≫ l₂ ≫ mid ≫ r₁ ≫ r₂ = l ≫ mid ≫ r
  calc
    l₁ ≫ l₂ ≫ mid ≫ r₁ ≫ r₂ =
        (l₁ ≫ l₂) ≫ mid ≫ (r₁ ≫ r₂) := by simp [Category.assoc]
    _ = l ≫ mid ≫ (r₁ ≫ r₂) := by
      exact congrArg (fun q => q ≫ mid ≫ (r₁ ≫ r₂)) hleft'
    _ = l ≫ mid ≫ r := by
      exact congrArg (fun q => l ≫ mid ≫ q) hright'

/-- The inverse realization component in the same three-factor collapsed normal form as
`projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover_pullHom_collapsed`.
This is the `g = id` specialization used to compare a restricted old explicit owner with the
directly rebuilt owner at the smaller overlap. -/
theorem projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover_collapsed
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : Y ⟶ K.Y)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : Y ⟶ A.Y)
    (h : k ≫ K.f ≫ I.f = a ≫ A.f) :
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
    let hK₁₂ : k ≫ K.f = 𝟙 Y ≫ Kold.f := by
      dsimp [Kold, DB, DescentCompletionObjectOver.pullbackCoverBaseArrow,
        projectionDescentDatumExplicitPullbackArrow]
      simp
    let hA₁₂ : 𝟙 Y ≫ IAold.f = a ≫ IAinner.f := by
      dsimp [IAinner, IAold, DA, DescentCompletionObjectOver.pullbackCoverBaseArrow,
        projectionDescentTotalCoverExplicitPullbackArrow,
        projectionDescentTotalCoverOuterMap]
      simp
    projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover
        (J := J) hSheaf D I K k A a h =
      (DB.overlapIso (I₁ := K) (I₂ := Kold) k (𝟙 Y) hK₁₂).hom ≫
        (let α :=
          projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover (J := J)
            hSheaf D I K k A a h
        α.1.components.toHomOver.family
          (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k)
          (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
          (𝟙 Y) (𝟙 Y)
          (by
            have hbase :
                α.1.base = 𝟙 Y :=
              projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_base
                (J := J) hSheaf D I K k A a h
            rw [hbase]
            dsimp [projectionDescentDatumExplicitPullbackArrow,
              projectionDescentTotalCoverExplicitPullbackArrow]
            calc
              𝟙 Y ≫ 𝟙 Y ≫ 𝟙 Y = 𝟙 Y ≫ 𝟙 Y := by rw [Category.id_comp]
              _ = 𝟙 Y ≫ 𝟙 Y := rfl)) ≫
        (DA.overlapIso (I₁ := IAold) (I₂ := IAinner) (𝟙 Y) a hA₁₂).hom := by
  have hpull :=
    projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover_pullHom_collapsed
      (J := J) hSheaf D I K (𝟙 Y) k A a h k a
      (by simp) (by simp)
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_id] at hpull
  simpa [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Category.assoc] using hpull

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
