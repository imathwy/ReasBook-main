import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.ExplicitRestriction

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
/-- Source stage 3.13 restriction law for `rho`, expanded into the five local factors obtained
by restricting the definition of `rho_(ai)(bj)`.  The remaining comparison with the directly
rebuilt component at `(ga, gb)` is the canonical-owner coherence step. -/
theorem projectionDescentTotalCoverTransitionComponent_pullHom_expanded
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
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentTotalCoverTransitionComponent (J := J) hSheaf D A B a b h)
        g ga gb hga hgb =
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
      ((projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D B)).overlapIso
        (I₁ := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
          (projectionDescentDatumLocalObject (J := J) hSheaf D
            (projectionDescentTotalCoverOuter (J := J) hSheaf D B))
          (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b)
          (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B b))
        (I₂ := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D B b)
        g g
        (by
          dsimp [DescentCompletionObjectOver.pullbackCoverBaseArrow,
            projectionDescentTotalCoverExplicitPullbackArrow,
            projectionDescentTotalCoverRefinedInner,
            projectionDescentTotalCoverOuterMap]
          simpa only [Category.assoc] using
            congrArg (fun q => g ≫ q)
              (Category.id_comp
                (b ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D B).f)))).hom ≫
      ((projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D B)).overlapIso
        (I₁ := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D B b)
        (I₂ := projectionDescentTotalCoverInner (J := J) hSheaf D B)
        g gb
        (by
          dsimp [projectionDescentTotalCoverRefinedInner]
          rw [← hgb]
          exact (Category.assoc g b
            (projectionDescentTotalCoverInner (J := J) hSheaf D B).f).symm)).hom := by
  dsimp [projectionDescentTotalCoverTransitionComponent]
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp
    (F := canonicalFiberPseudofunctor X.p)
    (projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D A a).hom
    ((projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso (J := J) hSheaf D A a).inv ≫
      projectionDescentTotalCoverExplicitTransitionComponent (J := J) hSheaf D A B a b h ≫
        (projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso (J := J) hSheaf D B b).hom ≫
          (projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D B b).inv)
    g ga g gb hga (by exact Category.comp_id g) hgb]
  rw [projectionDescentTotalCoverLocalRestrictionIso_pullHom]
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp
    (F := canonicalFiberPseudofunctor X.p)
    (projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso (J := J) hSheaf D A a).inv
    (projectionDescentTotalCoverExplicitTransitionComponent (J := J) hSheaf D A B a b h ≫
      (projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso (J := J) hSheaf D B b).hom ≫
        (projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D B b).inv)
    g g g gb (by exact Category.comp_id g) (by exact Category.comp_id g) hgb]
  rw [projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso_inv_pullHom]
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp
    (F := canonicalFiberPseudofunctor X.p)
    (projectionDescentTotalCoverExplicitTransitionComponent (J := J) hSheaf D A B a b h)
    ((projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso (J := J) hSheaf D B b).hom ≫
      (projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D B b).inv)
    g g g gb (by exact Category.comp_id g) (by exact Category.comp_id g) hgb]
  rw [projectionDescentTotalCoverExplicitTransitionComponent_pullHom_sameOuter]
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp
    (F := canonicalFiberPseudofunctor X.p)
    (projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso (J := J) hSheaf D B b).hom
    (projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D B b).inv
    g g g gb (by exact Category.comp_id g) (by exact Category.comp_id g) hgb]
  rw [projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso_pullHom]
  rw [projectionDescentTotalCoverLocalRestrictionIso_inv_pullHom]

/-- Source stage 3.13 restriction law for `rho`, after collapsing the source and target
explicit-restriction pairs in the expanded formula.  The only remaining non-definitional
comparison is the outer `Theta` component between old explicit pullback owners and the directly
rebuilt owners. -/
theorem projectionDescentTotalCoverTransitionComponent_pullHom_collapsed
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
    let hB₁₂ : g ≫ IBold.f = gb ≫ IBinner.f := by
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
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor X.p)
        (projectionDescentTotalCoverTransitionComponent (J := J) hSheaf D A B a b h)
        g ga gb hga hgb =
      (DA.overlapIso (I₁ := IAinner) (I₂ := IAold) ga g hA₁₂).hom ≫
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
        (DB.overlapIso (I₁ := IBold) (I₂ := IBinner) g gb hB₁₂).hom := by
  rw [projectionDescentTotalCoverTransitionComponent_pullHom_expanded]
  dsimp only
  let DA :=
    projectionDescentDatumLocalObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
  let DB :=
    projectionDescentDatumLocalObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D B)
  let IAinner := projectionDescentTotalCoverInner (J := J) hSheaf D A
  let IBinner := projectionDescentTotalCoverInner (J := J) hSheaf D B
  let IAa := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a
  let IBb := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D B b
  let IAold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
  let IBold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DB (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B b)
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
  let hB₁₂ : g ≫ IBold.f = g ≫ IBb.f := by
    dsimp [IBb, IBold, DB, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentTotalCoverRefinedInner, projectionDescentTotalCoverOuterMap]
    simpa only [Category.assoc] using
      congrArg (fun q => g ≫ q)
        (Category.id_comp
          (b ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D B).f))
  let hB₂₃ : g ≫ IBb.f = gb ≫ IBinner.f := by
    dsimp [IBb, projectionDescentTotalCoverRefinedInner]
    rw [← hgb]
    exact (Category.assoc g b IBinner.f).symm
  have hleft :=
    DescentCompletionObjectOver.overlapIso_hom_comp (J := J) DA
      (I₁ := IAinner) (I₂ := IAa) (I₃ := IAold) ga g g hA₁₂ hA₂₃
  have hright :=
    DescentCompletionObjectOver.overlapIso_hom_comp (J := J) DB
      (I₁ := IBold) (I₂ := IBb) (I₃ := IBinner) g g gb hB₁₂ hB₂₃
  rw [← Category.assoc]
  rw [hleft]
  let α :=
    projectionDescentExplicitOuterFiberHomForTotalCover (J := J)
      hSheaf D A B a b h
  let mid :=
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
          (Category.comp_id (g ≫ 𝟙 Y)))
  let l :=
    (DA.overlapIso (I₁ := IAinner) (I₂ := IAold) ga g (hA₁₂.trans hA₂₃)).hom
  let r₁ :=
    (DB.overlapIso (I₁ := IBold) (I₂ := IBb) g g hB₁₂).hom
  let r₂ :=
    (DB.overlapIso (I₁ := IBb) (I₂ := IBinner) g gb hB₂₃).hom
  let r :=
    (DB.overlapIso (I₁ := IBold) (I₂ := IBinner) g gb (hB₁₂.trans hB₂₃)).hom
  have hright' : r₁ ≫ r₂ = r := by
    simpa [r₁, r₂, r] using hright
  change l ≫ mid ≫ r₁ ≫ r₂ = l ≫ mid ≫ r
  calc
    l ≫ mid ≫ r₁ ≫ r₂ = l ≫ mid ≫ (r₁ ≫ r₂) := rfl
    _ = l ≫ mid ≫ r := by
      exact congrArg (fun q => l ≫ mid ≫ q) hright'

/-- Source stage 3.13 transition component `rho_(ai)(bj)`, in the same three-factor collapsed
normal form as `projectionDescentTotalCoverTransitionComponent_pullHom_collapsed`.  This is the
`g = id` specialization used to compare a restricted old explicit owner with the directly rebuilt
owner at the smaller overlap. -/
theorem projectionDescentTotalCoverTransitionComponent_collapsed
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : Y ⟶ A.Y) (b : Y ⟶ B.Y)
    (h : a ≫ A.f = b ≫ B.f) :
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
    let hA₁₂ : a ≫ IAinner.f = 𝟙 Y ≫ IAold.f := by
      dsimp [IAinner, IAold, DA, DescentCompletionObjectOver.pullbackCoverBaseArrow,
        projectionDescentTotalCoverExplicitPullbackArrow,
        projectionDescentTotalCoverOuterMap]
      simp
    let hB₁₂ : 𝟙 Y ≫ IBold.f = b ≫ IBinner.f := by
      dsimp [IBinner, IBold, DB, DescentCompletionObjectOver.pullbackCoverBaseArrow,
        projectionDescentTotalCoverExplicitPullbackArrow,
        projectionDescentTotalCoverOuterMap]
      simp
    projectionDescentTotalCoverTransitionComponent (J := J) hSheaf D A B a b h =
      (DA.overlapIso (I₁ := IAinner) (I₂ := IAold) a (𝟙 Y) hA₁₂).hom ≫
        (let α :=
          projectionDescentExplicitOuterFiberHomForTotalCover (J := J)
            hSheaf D A B a b h
        α.1.components.toHomOver.family
          (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
          (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B b)
          (𝟙 Y) (𝟙 Y)
          (by
            have hbase :
                α.1.base = 𝟙 Y :=
              projectionDescentExplicitOuterFiberHomForTotalCover_base
                (J := J) hSheaf D A B a b h
            rw [hbase]
            dsimp [projectionDescentTotalCoverExplicitPullbackArrow]
            calc
              𝟙 Y ≫ 𝟙 Y ≫ 𝟙 Y = 𝟙 Y ≫ 𝟙 Y := by rw [Category.id_comp]
              _ = 𝟙 Y ≫ 𝟙 Y := rfl)) ≫
        (DB.overlapIso (I₁ := IBold) (I₂ := IBinner) (𝟙 Y) b hB₁₂).hom := by
  have hpull :=
    projectionDescentTotalCoverTransitionComponent_pullHom_collapsed
      (J := J) hSheaf D A B (𝟙 Y) a b h a b
      (by simp) (by simp)
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom_id] at hpull
  simpa [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Category.assoc] using hpull

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
