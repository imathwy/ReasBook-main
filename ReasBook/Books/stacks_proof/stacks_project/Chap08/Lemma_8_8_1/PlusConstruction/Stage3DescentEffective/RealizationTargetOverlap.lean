import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationTargetOverlapComponent
import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationPullHomCollapsed

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

/-- Target-side component transport for the explicit transition, with the final target owner
rebuilt directly over `k₂ ≫ K₂.f`.

This combines the old-owner compatibility square with the equality-transport comparison of the
explicit pullback target owner.  It is the component-level form of the source-text identity that
the same `rho_(b,j),(a,i)` is obtained after changing the target inner owner by an overlap. -/
theorem projectionDescentExplicitTransitionComponentFromTotalCoverToDatumInner_comp_targetOverlap
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (a : W ⟶ A.Y)
    (K₁ K₂ : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k₁ : W ⟶ K₁.Y) (k₂ : W ⟶ K₂.Y)
    (hK : k₁ ≫ K₁.f = k₂ ≫ K₂.f)
    (h₁ : a ≫ A.f = k₁ ≫ K₁.f ≫ I.f)
    (h₂ : a ≫ A.f = k₂ ≫ K₂.f ≫ I.f) :
    let DB := projectionDescentDatumLocalObject (J := J) hSheaf D I
    let IA := projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a
    let Karr₁ := projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K₁ k₁
    let Karr₂ := projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K₂ k₂
    let Karr₂old := projectionDescentDatumExplicitPullbackArrowOfEq
      (J := J) hSheaf D I K₁ K₂ k₁ k₂ hK
    let Kbase₁ := DescentCompletionObjectOver.pullbackCoverBaseArrow
      (J := J) DB (k₁ ≫ K₁.f) Karr₁
    let Kbase₂old := DescentCompletionObjectOver.pullbackCoverBaseArrow
      (J := J) DB (k₁ ≫ K₁.f) Karr₂old
    let Kbase₂ := DescentCompletionObjectOver.pullbackCoverBaseArrow
      (J := J) DB (k₂ ≫ K₂.f) Karr₂
    let hbase₁₂old : 𝟙 W ≫ Kbase₁.f = 𝟙 W ≫ Kbase₂old.f := by rfl
    let hbaseOld₂ : 𝟙 W ≫ Kbase₂old.f = 𝟙 W ≫ Kbase₂.f := by
      dsimp [Kbase₂old, Kbase₂, Karr₂old, Karr₂,
        projectionDescentDatumExplicitPullbackArrowOfEq, pullbackCoverArrowOfEq,
        projectionDescentDatumExplicitPullbackArrow,
        DescentCompletionObjectOver.pullbackCoverBaseArrow]
      simpa [Category.assoc] using hK
    let hbase₁₂ : 𝟙 W ≫ Kbase₁.f = 𝟙 W ≫ Kbase₂.f :=
      hbase₁₂old.trans hbaseOld₂
    (let α := projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
        (J := J) hSheaf D A I a K₁ k₁ h₁
    α.1.components.toHomOver.family IA Karr₁ (𝟙 W) (𝟙 W)
      (by
        have hα : α.1.base = 𝟙 W :=
          projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
            (J := J) hSheaf D A I a K₁ k₁ h₁
        rw [hα]
        dsimp [IA, Karr₁, projectionDescentTotalCoverExplicitPullbackArrow,
          projectionDescentDatumExplicitPullbackArrow]
        repeat rw [Category.id_comp]
        exact Category.comp_id (𝟙 W))) ≫
        (DB.overlapIso (I₁ := Kbase₁) (I₂ := Kbase₂)
          (𝟙 W) (𝟙 W) hbase₁₂).hom =
      (let α := projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
          (J := J) hSheaf D A I a K₂ k₂ h₂
      α.1.components.toHomOver.family IA Karr₂ (𝟙 W) (𝟙 W)
        (by
          have hα : α.1.base = 𝟙 W :=
            projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
              (J := J) hSheaf D A I a K₂ k₂ h₂
          rw [hα]
          dsimp [IA, Karr₂, projectionDescentTotalCoverExplicitPullbackArrow,
            projectionDescentDatumExplicitPullbackArrow]
          repeat rw [Category.id_comp]
          exact Category.comp_id (𝟙 W))) := by
  dsimp only
  let DB := projectionDescentDatumLocalObject (J := J) hSheaf D I
  let IA := projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a
  let Karr₁ := projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K₁ k₁
  let Karr₂ := projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K₂ k₂
  let Karr₂old := projectionDescentDatumExplicitPullbackArrowOfEq
    (J := J) hSheaf D I K₁ K₂ k₁ k₂ hK
  let Kbase₁ := DescentCompletionObjectOver.pullbackCoverBaseArrow
    (J := J) DB (k₁ ≫ K₁.f) Karr₁
  let Kbase₂old := DescentCompletionObjectOver.pullbackCoverBaseArrow
    (J := J) DB (k₁ ≫ K₁.f) Karr₂old
  let Kbase₂ := DescentCompletionObjectOver.pullbackCoverBaseArrow
    (J := J) DB (k₂ ≫ K₂.f) Karr₂
  let hbase₁₂old : 𝟙 W ≫ Kbase₁.f = 𝟙 W ≫ Kbase₂old.f := by rfl
  let hbaseOld₂ : 𝟙 W ≫ Kbase₂old.f = 𝟙 W ≫ Kbase₂.f := by
    dsimp [Kbase₂old, Kbase₂, Karr₂old, Karr₂,
      projectionDescentDatumExplicitPullbackArrowOfEq, pullbackCoverArrowOfEq,
      projectionDescentDatumExplicitPullbackArrow,
      DescentCompletionObjectOver.pullbackCoverBaseArrow]
    simpa [Category.assoc] using hK
  let hbase₁₂ : 𝟙 W ≫ Kbase₁.f = 𝟙 W ≫ Kbase₂.f :=
    hbase₁₂old.trans hbaseOld₂
  have hold :=
    projectionDescentExplicitTransitionComponentFromTotalCoverToDatumInner_comp_targetOverlap_oldOwner
      (J := J) hSheaf D A I a K₁ K₂ k₁ k₂ hK h₁
  have htransport :=
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase_component_congr_target_explicit
      (J := J) hSheaf D A I a (k₁ ≫ K₁.f) K₂ k₂ hK
      (by simpa [Category.assoc] using h₁) h₂
  have hover :=
    DescentCompletionObjectOver.overlapIso_hom_comp (J := J) DB
      (I₁ := Kbase₁) (I₂ := Kbase₂old) (I₃ := Kbase₂)
      (𝟙 W) (𝟙 W) (𝟙 W) hbase₁₂old hbaseOld₂
  rw [← hover]
  let α₁ := projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
    (J := J) hSheaf D A I a K₁ k₁ h₁
  let α₂ := projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
    (J := J) hSheaf D A I a K₂ k₂ h₂
  let mid₁ := α₁.1.components.toHomOver.family IA Karr₁ (𝟙 W) (𝟙 W)
    (by
      have hα : α₁.1.base = 𝟙 W :=
        projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
          (J := J) hSheaf D A I a K₁ k₁ h₁
      rw [hα]
      dsimp [IA, Karr₁, projectionDescentTotalCoverExplicitPullbackArrow,
        projectionDescentDatumExplicitPullbackArrow]
      repeat rw [Category.id_comp]
      exact Category.comp_id (𝟙 W))
  let midOld := α₁.1.components.toHomOver.family IA Karr₂old (𝟙 W) (𝟙 W)
    (by
      have hα : α₁.1.base = 𝟙 W :=
        projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
          (J := J) hSheaf D A I a K₁ k₁ h₁
      rw [hα]
      dsimp [IA, Karr₂old, projectionDescentTotalCoverExplicitPullbackArrow]
      repeat rw [Category.id_comp]
      rfl)
  let mid₂ := α₂.1.components.toHomOver.family IA Karr₂ (𝟙 W) (𝟙 W)
    (by
      have hα : α₂.1.base = 𝟙 W :=
        projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
          (J := J) hSheaf D A I a K₂ k₂ h₂
      rw [hα]
      dsimp [IA, Karr₂, projectionDescentTotalCoverExplicitPullbackArrow,
        projectionDescentDatumExplicitPullbackArrow]
      repeat rw [Category.id_comp]
      exact Category.comp_id (𝟙 W))
  let oldOverlap :=
    (DB.overlapIso (I₁ := Kbase₁) (I₂ := Kbase₂old)
      (𝟙 W) (𝟙 W) hbase₁₂old).hom
  let bridgeOverlap :=
    (DB.overlapIso (I₁ := Kbase₂old) (I₂ := Kbase₂)
      (𝟙 W) (𝟙 W) hbaseOld₂).hom
  have hold' : mid₁ ≫ oldOverlap = midOld := by
    simpa [mid₁, midOld, oldOverlap, α₁, DB, IA, Karr₁, Karr₂old, Kbase₁,
      Kbase₂old, hbase₁₂old] using hold
  have htransport' : midOld ≫ bridgeOverlap = mid₂ := by
    simpa [midOld, mid₂, bridgeOverlap, α₁, α₂, DB, IA, Karr₂old, Karr₂,
      Kbase₂old, Kbase₂, hbaseOld₂,
      projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_eq_base]
      using htransport
  change mid₁ ≫ (oldOverlap ≫ bridgeOverlap) = mid₂
  calc
    mid₁ ≫ (oldOverlap ≫ bridgeOverlap) =
        (mid₁ ≫ oldOverlap) ≫ bridgeOverlap := by rw [Category.assoc]
    _ = midOld ≫ bridgeOverlap := congrArg (fun q => q ≫ bridgeOverlap) hold'
    _ = mid₂ := htransport'

/-- Target-side overlap law for the owner-faithful realization component.

This is the isolated source-text target half of the compatibility square for `Lambda_a`: after
the target inner owner is changed by a datum overlap, the component is unchanged up to that
visible overlap.  The remaining proof should pass through the old-owner lemma and the explicit
target-transport law without treating either owner as definitionally equal. -/
def projectionDescentRealizationComponentFromTotalCoverToDatumInnerTargetOverlapLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (a : W ⟶ A.Y)
    (K₁ K₂ : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k₁ : W ⟶ K₁.Y) (k₂ : W ⟶ K₂.Y)
    (hK : k₁ ≫ K₁.f = k₂ ≫ K₂.f)
    (h₁ : a ≫ A.f = k₁ ≫ K₁.f ≫ I.f)
    (h₂ : a ≫ A.f = k₂ ≫ K₂.f ≫ I.f) : Prop :=
  let Target := projectionDescentDatumLocalObject (J := J) hSheaf D I
  projectionDescentRealizationComponentFromTotalCoverToDatumInner
      (J := J) hSheaf D A I a K₁ k₁ h₁ ≫
        (Target.overlapIso k₁ k₂ hK).hom =
    projectionDescentRealizationComponentFromTotalCoverToDatumInner
      (J := J) hSheaf D A I a K₂ k₂ h₂

/-- Target-overlap frontier for the realization compatibility proof.

The first field is the component-level equality transport for the explicit target owner.  The
second field is the source-text target overlap statement used together with the already proved
source-overlap theorem to discharge `projectionDescentRealizationComponentCompatibleLaw`. -/
structure ProjectionDescentRealizationTargetOverlapFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) where
  /-- Explicit component transport from the old target pullback owner to the direct owner. -/
  explicitTargetTransport :
    ∀ {W : C}
      (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
      (I : S.Arrow)
      (a : W ⟶ A.Y)
      (q : W ⟶ I.Y)
      (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
      (k : W ⟶ K.Y)
      (hq : q = k ≫ K.f)
      (h₁ : a ≫ A.f = q ≫ I.f)
      (h₂ : a ≫ A.f = k ≫ K.f ≫ I.f),
        projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase_component_congr_target_explicit_law
          (J := J) hSheaf D A I a q K k hq h₁ h₂
  /-- Target half of the source-text compatibility square for the actual realization component. -/
  targetOverlap :
    ∀ {W : C}
      (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
      (I : S.Arrow)
      (a : W ⟶ A.Y)
      (K₁ K₂ : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
      (k₁ : W ⟶ K₁.Y) (k₂ : W ⟶ K₂.Y)
      (hK : k₁ ≫ K₁.f = k₂ ≫ K₂.f)
      (h₁ : a ≫ A.f = k₁ ≫ K₁.f ≫ I.f)
      (h₂ : a ≫ A.f = k₂ ≫ K₂.f ≫ I.f),
        projectionDescentRealizationComponentFromTotalCoverToDatumInnerTargetOverlapLaw
          (J := J) hSheaf D A I a K₁ K₂ k₁ k₂ hK h₁ h₂

/-- Target-side overlap for the owner-faithful realization component `Λ_a`.

This is the target half of the source-text check
`Theta_ab ∘ Lambda_a = Lambda_b`: once the explicit transition component has been transported
between target owners, the two visible datum-overlap factors are compared by the cocycle law for
`overlapIso`. -/
theorem projectionDescentRealizationComponentFromTotalCoverToDatumInner_targetOverlap
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (a : W ⟶ A.Y)
    (K₁ K₂ : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k₁ : W ⟶ K₁.Y) (k₂ : W ⟶ K₂.Y)
    (hK : k₁ ≫ K₁.f = k₂ ≫ K₂.f)
    (h₁ : a ≫ A.f = k₁ ≫ K₁.f ≫ I.f)
    (h₂ : a ≫ A.f = k₂ ≫ K₂.f ≫ I.f) :
    projectionDescentRealizationComponentFromTotalCoverToDatumInnerTargetOverlapLaw
      (J := J) hSheaf D A I a K₁ K₂ k₁ k₂ hK h₁ h₂ := by
  unfold projectionDescentRealizationComponentFromTotalCoverToDatumInnerTargetOverlapLaw
  let DA :=
    projectionDescentDatumLocalObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
  let DB := projectionDescentDatumLocalObject (J := J) hSheaf D I
  let IAinner := projectionDescentTotalCoverInner (J := J) hSheaf D A
  let IAold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
  let Karr₁ := projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K₁ k₁
  let Karr₂ := projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K₂ k₂
  let Kbase₁ := DescentCompletionObjectOver.pullbackCoverBaseArrow
    (J := J) DB (k₁ ≫ K₁.f) Karr₁
  let Kbase₂ := DescentCompletionObjectOver.pullbackCoverBaseArrow
    (J := J) DB (k₂ ≫ K₂.f) Karr₂
  let hA₁₂ : a ≫ IAinner.f = 𝟙 W ≫ IAold.f := by
    dsimp [IAinner, IAold, DA, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentTotalCoverOuterMap]
    simp
  let hKbase₁ : 𝟙 W ≫ Kbase₁.f = k₁ ≫ K₁.f := by
    dsimp [Kbase₁, Karr₁, DB, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentDatumExplicitPullbackArrow]
    simp
  let hKbase₂ : 𝟙 W ≫ Kbase₂.f = k₂ ≫ K₂.f := by
    dsimp [Kbase₂, Karr₂, DB, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentDatumExplicitPullbackArrow]
    simp
  let hbase₁₂ : 𝟙 W ≫ Kbase₁.f = 𝟙 W ≫ Kbase₂.f :=
    hKbase₁.trans (hK.trans hKbase₂.symm)
  let leftSource := (DA.overlapIso (I₁ := IAinner) (I₂ := IAold)
    a (𝟙 W) hA₁₂).hom
  let α₁ := projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
    (J := J) hSheaf D A I a K₁ k₁ h₁
  let α₂ := projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
    (J := J) hSheaf D A I a K₂ k₂ h₂
  let mid₁ := α₁.1.components.toHomOver.family
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
    Karr₁ (𝟙 W) (𝟙 W)
    (by
      have hα : α₁.1.base = 𝟙 W :=
        projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
          (J := J) hSheaf D A I a K₁ k₁ h₁
      rw [hα]
      dsimp [Karr₁, projectionDescentTotalCoverExplicitPullbackArrow,
        projectionDescentDatumExplicitPullbackArrow]
      repeat rw [Category.id_comp]
      exact Category.comp_id (𝟙 W))
  let mid₂ := α₂.1.components.toHomOver.family
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
    Karr₂ (𝟙 W) (𝟙 W)
    (by
      have hα : α₂.1.base = 𝟙 W :=
        projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
          (J := J) hSheaf D A I a K₂ k₂ h₂
      rw [hα]
      dsimp [Karr₂, projectionDescentTotalCoverExplicitPullbackArrow,
        projectionDescentDatumExplicitPullbackArrow]
      repeat rw [Category.id_comp]
      exact Category.comp_id (𝟙 W))
  let r₁ := (DB.overlapIso (I₁ := Kbase₁) (I₂ := K₁)
    (𝟙 W) k₁ hKbase₁).hom
  let r₂ := (DB.overlapIso (I₁ := Kbase₂) (I₂ := K₂)
    (𝟙 W) k₂ hKbase₂).hom
  let targetOverlap := (DB.overlapIso (I₁ := K₁) (I₂ := K₂) k₁ k₂ hK).hom
  let baseOverlap := (DB.overlapIso (I₁ := Kbase₁) (I₂ := Kbase₂)
    (𝟙 W) (𝟙 W) hbase₁₂).hom
  have hcollapsed₁ :=
    projectionDescentRealizationComponentFromTotalCoverToDatumInner_collapsed
      (J := J) hSheaf D A I a K₁ k₁ h₁
  have hcollapsed₂ :=
    projectionDescentRealizationComponentFromTotalCoverToDatumInner_collapsed
      (J := J) hSheaf D A I a K₂ k₂ h₂
  rw [hcollapsed₁, hcollapsed₂]
  have hmid : mid₁ ≫ baseOverlap = mid₂ := by
    simpa [mid₁, mid₂, baseOverlap, α₁, α₂, DB, Karr₁, Karr₂, Kbase₁, Kbase₂,
      hKbase₁, hKbase₂, hbase₁₂]
      using
        projectionDescentExplicitTransitionComponentFromTotalCoverToDatumInner_comp_targetOverlap
          (J := J) hSheaf D A I a K₁ K₂ k₁ k₂ hK h₁ h₂
  have hright₁ :=
    DescentCompletionObjectOver.overlapIso_hom_comp (J := J) DB
      (I₁ := Kbase₁) (I₂ := K₁) (I₃ := K₂)
      (𝟙 W) k₁ k₂ hKbase₁ hK
  have hright₂ :=
    DescentCompletionObjectOver.overlapIso_hom_comp (J := J) DB
      (I₁ := Kbase₁) (I₂ := Kbase₂) (I₃ := K₂)
      (𝟙 W) (𝟙 W) k₂ hbase₁₂ hKbase₂
  have hright : r₁ ≫ targetOverlap = baseOverlap ≫ r₂ := by
    rw [hright₁, hright₂]
  change (leftSource ≫ mid₁ ≫ r₁) ≫ targetOverlap =
    leftSource ≫ mid₂ ≫ r₂
  calc
    (leftSource ≫ mid₁ ≫ r₁) ≫ targetOverlap =
        leftSource ≫ mid₁ ≫ (r₁ ≫ targetOverlap) := by simp [Category.assoc]
    _ = leftSource ≫ mid₁ ≫ (baseOverlap ≫ r₂) := by
      exact congrArg (fun q => leftSource ≫ mid₁ ≫ q) hright
    _ = leftSource ≫ (mid₁ ≫ baseOverlap) ≫ r₂ := by simp [Category.assoc]
    _ = leftSource ≫ mid₂ ≫ r₂ := by
      exact congrArg (fun q => leftSource ≫ q ≫ r₂) hmid

/-- The target-overlap frontier supplied by the source-faithful component lemmas. -/
noncomputable def projectionDescentRealizationTargetOverlapFrontier
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) :
    ProjectionDescentRealizationTargetOverlapFrontier (J := J) hSheaf D where
  explicitTargetTransport := by
    intro W A I a q K k hq h₁ h₂
    exact
      projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase_component_congr_target_explicit
        (J := J) hSheaf D A I a q K k hq h₁ h₂
  targetOverlap := by
    intro W A I a K₁ K₂ k₁ k₂ hK h₁ h₂
    exact
      projectionDescentRealizationComponentFromTotalCoverToDatumInner_targetOverlap
        (J := J) hSheaf D A I a K₁ K₂ k₁ k₂ hK h₁ h₂

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
