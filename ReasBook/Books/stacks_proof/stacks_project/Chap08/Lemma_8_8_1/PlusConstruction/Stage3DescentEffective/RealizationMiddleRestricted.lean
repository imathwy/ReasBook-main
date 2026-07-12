import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationMiddleBridge
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RestrictedExplicitArrow

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

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Source stage 3.13 canonical-owner restriction law for the transported outer component
`theta_ba,ji` used in the realization map `Lambda_a`.

Restricting the old explicit-owner component and then using the explicit pullback composition
bridges agrees with rebuilding the component directly on the smaller overlap.  This is the
realization-side analogue of
`projectionDescentExplicitOuterFiberHomForTotalCover_restrict`. -/
theorem projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_restrict
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
    let hsmall : ga ≫ A.f = gk ≫ K.f ≫ I.f := by
      calc
        ga ≫ A.f = g ≫ a ≫ A.f := by rw [← hga]; simp [Category.assoc]
        _ = g ≫ (k ≫ K.f ≫ I.f) := by
          simpa [Category.assoc] using congrArg (fun q => g ≫ q) h
        _ = gk ≫ K.f ≫ I.f := by rw [← hgk]; simp [Category.assoc]
    let OA := projectionDescentDatumObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
    let OB := projectionDescentDatumObject (J := J) hSheaf D I
    let fA := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a
    let fB := k ≫ K.f
    let fA' := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga
    let fB' := gk ≫ K.f
    let hfA : g ≫ fA = fA' := by
      simp [fA, fA', projectionDescentTotalCoverOuterMap, ← hga, Category.assoc]
    let hfB : g ≫ fB = fB' := by
      simp [fB, fB', ← hgk, Category.assoc]
    let eA := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OA fA g fA' hfA
    let eB := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OB fB g fB' hfB
    let αold :=
      projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
        (J := J) hSheaf D A I a K k h
    let αnew :=
      projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
        (J := J) hSheaf D A I ga K gk hsmall
    eA.hom ≫ ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map αold ≫
        eB.inv =
      αnew := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let hsmall : ga ≫ A.f = gk ≫ K.f ≫ I.f := by
    calc
      ga ≫ A.f = g ≫ a ≫ A.f := by rw [← hga]; simp [Category.assoc]
      _ = g ≫ (k ≫ K.f ≫ I.f) := by
        simpa [Category.assoc] using congrArg (fun q => g ≫ q) h
      _ = gk ≫ K.f ≫ I.f := by rw [← hgk]; simp [Category.assoc]
  let IA := projectionDescentTotalCoverOuter (J := J) hSheaf D A
  let OA := projectionDescentDatumObject (J := J) hSheaf D IA
  let OB := projectionDescentDatumObject (J := J) hSheaf D I
  let fA := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a
  let fB := k ≫ K.f
  let fA' := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga
  let fB' := gk ≫ K.f
  let hfA : g ≫ fA = fA' := by
    simp [fA, fA', projectionDescentTotalCoverOuterMap, ← hga, Category.assoc]
  let hfB : g ≫ fB = fB' := by
    simp [fB, fB', ← hgk, Category.assoc]
  let eA := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OA fA g fA' hfA
  let eB := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OB fB g fB' hfB
  let eOldA := projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D IA fA
  let eOldB := projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D I fB
  let eNewA := projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D IA fA'
  let eNewB := projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D I fB'
  let outerOld :=
    projectionDescentOuterFiberHomFromTotalCoverToDatumInner
      (J := J) hSheaf D A I a K k h
  let outerNew :=
    projectionDescentOuterFiberHomFromTotalCoverToDatumInner
      (J := J) hSheaf D A I ga K gk hsmall
  let κA := ((canonicalFiberPseudofunctor P).mapComp' fA.op.toLoc g.op.toLoc fA'.op.toLoc
      (comp_toLoc_eq fA g fA' hfA)).hom.toNatTrans.app (D.obj IA)
  let κB := ((canonicalFiberPseudofunctor P).mapComp' fB.op.toLoc g.op.toLoc fB'.op.toLoc
      (comp_toLoc_eq fB g fB' hfB)).inv.toNatTrans.app (D.obj I)
  have hA :
      eA.hom ≫ ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map eOldA.hom =
        eNewA.hom ≫ κA := by
    simpa [OA, eA, eOldA, eNewA, κA] using
      projectionDescentDatumPullbackIsoCanonicalOriginal_hom_naturality
        (J := J) hSheaf D IA fA g fA' hfA
  have hB :
      ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map eOldB.inv ≫ eB.inv =
        κB ≫ eNewB.inv := by
    simpa [OB, eB, eOldB, eNewB, κB] using
      projectionDescentDatumPullbackIsoCanonicalOriginal_inv_naturality
        (J := J) hSheaf D I fB g fB' hfB
  have hOuter :
      κA ≫ ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map outerOld ≫
        κB = outerNew := by
    simpa [κA, κB, outerOld, outerNew, fA, fB, fA', fB', hsmall,
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom] using
      projectionDescentOuterFiberHomFromTotalCoverToDatumInner_pullHom
        (J := J) hSheaf D A I g a K k h ga gk hga hgk
  dsimp [projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner]
  change eA.hom ≫
      ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map
        (eOldA.hom ≫ outerOld ≫ eOldB.inv) ≫ eB.inv =
    eNewA.hom ≫ outerNew ≫ eNewB.inv
  rw [Functor.map_comp, Functor.map_comp]
  calc
    eA.hom ≫
        (((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map eOldA.hom ≫
          ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map outerOld ≫
          ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map eOldB.inv) ≫
        eB.inv =
      (eA.hom ≫ ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map eOldA.hom) ≫
        ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map outerOld ≫
        (((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map eOldB.inv ≫ eB.inv) := by
        simp [Category.assoc]
    _ = (eNewA.hom ≫ κA) ≫
        ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map outerOld ≫
        (κB ≫ eNewB.inv) := by
        rw [hA, hB]
    _ = eNewA.hom ≫
        (κA ≫ ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map outerOld ≫
          κB) ≫ eNewB.inv := by
        simp [Category.assoc]
    _ = eNewA.hom ≫ outerNew ≫ eNewB.inv := by
        rw [hOuter]

/-- Target-side restricted explicit-cover arrow for the realization component.

If `k : Y -> U_ai` gives the explicit pullback cover of `X_a` over `Y`, and
`g : Y' -> Y`, this is the same explicit cover member viewed as an arrow of the old pullback
cover over `Y`, with structural map `g`. -/
noncomputable def projectionDescentDatumExplicitPullbackArrowAlong
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (g : Y' ⟶ Y) (k : Y ⟶ K.Y) (gk : Y' ⟶ K.Y)
    (hgk : g ≫ k = gk) :
    ((projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.pullback
        (k ≫ K.f)).Arrow where
  Y := Y'
  f := g
  hf := by
    change ((projectionDescentDatumLocalObject (J := J) hSheaf D I).cover : Sieve _).arrows
      (g ≫ k ≫ K.f)
    rw [show g ≫ k ≫ K.f = gk ≫ K.f by
      rw [← hgk]
      simp [Category.assoc]]
    simpa [projectionDescentDatumExplicitPullbackArrow, Category.assoc] using
      (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk).hf

@[simp]
theorem projectionDescentDatumExplicitPullbackArrowAlong_f
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y' Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (g : Y' ⟶ Y) (k : Y ⟶ K.Y) (gk : Y' ⟶ K.Y)
    (hgk : g ≫ k = gk) :
    (projectionDescentDatumExplicitPullbackArrowAlong
      (J := J) hSheaf D I K g k gk hgk).f = g :=
  rfl

/-- The old explicit outer component used in `Lambda_a`, evaluated at the cover arrows obtained
by restricting the old explicit pullback covers along `g`, and transported to the directly
rebuilt `IAnew`/`Knew` owners. -/
noncomputable def projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInnerOldRestrictedComponent
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
    let IAnew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
    let Knew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
      DB (gk ≫ K.f)
      (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk)
    DA.restrictedLocalObject IAnew (𝟙 Y') ⟶
      DB.restrictedLocalObject Knew (𝟙 Y') := by
  letI := category (J := J) hSheaf
  let DA :=
    projectionDescentDatumLocalObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
  let DB := projectionDescentDatumLocalObject (J := J) hSheaf D I
  let IAnew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
  let Knew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DB (gk ≫ K.f)
    (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk)
  let IAres :=
    projectionDescentTotalCoverExplicitPullbackArrowAlong
      (J := J) hSheaf D A g a ga hga
  let Kres :=
    projectionDescentDatumExplicitPullbackArrowAlong
      (J := J) hSheaf D I K g k gk hgk
  let IAresBase := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a) IAres
  let KresBase := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DB (k ≫ K.f) Kres
  let α :=
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
      (J := J) hSheaf D A I a K k h
  let sourceCast :
      DA.restrictedLocalObject IAnew (𝟙 Y') ⟶
        DA.restrictedLocalObject IAresBase (𝟙 Y') :=
    (DA.overlapIso (I₁ := IAnew) (I₂ := IAresBase) (𝟙 Y') (𝟙 Y') (by
      dsimp [IAnew, IAresBase, IAres, projectionDescentTotalCoverExplicitPullbackArrowAlong,
        projectionDescentTotalCoverExplicitPullbackArrow,
        DescentCompletionObjectOver.pullbackCoverBaseArrow, projectionDescentTotalCoverOuterMap]
      rw [← hga]
      simp [Category.assoc])).hom
  let targetCast :
      DB.restrictedLocalObject KresBase (𝟙 Y') ⟶
        DB.restrictedLocalObject Knew (𝟙 Y') :=
    (DB.overlapIso (I₁ := KresBase) (I₂ := Knew) (𝟙 Y') (𝟙 Y') (by
      dsimp [Knew, KresBase, Kres, projectionDescentDatumExplicitPullbackArrowAlong,
        projectionDescentDatumExplicitPullbackArrow,
        DescentCompletionObjectOver.pullbackCoverBaseArrow]
      rw [← hgk]
      simp [Category.assoc])).hom
  exact sourceCast ≫
    α.1.components.toHomOver.family IAres Kres (𝟙 Y') (𝟙 Y')
      (by
        have hbase :
            α.1.base = 𝟙 Y :=
          projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
            (J := J) hSheaf D A I a K k h
        rw [hbase]
        dsimp [IAres, Kres, projectionDescentTotalCoverExplicitPullbackArrowAlong,
          projectionDescentDatumExplicitPullbackArrowAlong]
        calc
          𝟙 Y' ≫ g ≫ 𝟙 Y = (𝟙 Y' ≫ g) ≫ 𝟙 Y := by
            rw [← Category.assoc]
          _ = 𝟙 Y' ≫ g := Category.comp_id _) ≫
    targetCast

/-- The remaining component owner-identification after the old-cover compatibility square:
the old realization outer component evaluated on the restricted old explicit-cover arrows agrees
with the component rebuilt directly over `(ga, gk)`. -/
def projectionDescentRealizationExplicitMiddleRestrictedComponentLaw
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
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInnerOldRestrictedComponent
        (J := J) hSheaf D A I g a K k h ga gk hga hgk =
      (let α :=
        projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
          (J := J) hSheaf D A I ga K gk hsmall
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

/-- The restricted-component owner bridge plus the ordinary compatibility square for the old
explicit pullback covers gives the realization explicit middle pullback law. -/
theorem projectionDescentRealizationExplicitMiddlePullHomLaw_of_restrictedComponent
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hrestricted :
      projectionDescentRealizationExplicitMiddleRestrictedComponentLaw (J := J) hSheaf D) :
    projectionDescentRealizationExplicitMiddlePullHomLaw (J := J) hSheaf D := by
  intro Y' Y g A I a K k h ga gk hga hgk
  letI := category (J := J) hSheaf
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
  let IAoldArrow :=
    projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a
  let KoldArrow :=
    projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k
  let IAres :=
    projectionDescentTotalCoverExplicitPullbackArrowAlong
      (J := J) hSheaf D A g a ga hga
  let Kres :=
    projectionDescentDatumExplicitPullbackArrowAlong
      (J := J) hSheaf D I K g k gk hgk
  let IAold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a) IAoldArrow
  let Kold := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DB (k ≫ K.f) KoldArrow
  let IAresBase := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a) IAres
  let KresBase := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DB (k ≫ K.f) Kres
  let IAnew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DA (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
  let Knew := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
    DB (gk ≫ K.f)
    (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk)
  let hAoldNew : g ≫ IAold.f = 𝟙 Y' ≫ IAnew.f := by
    dsimp [IAold, IAnew, IAoldArrow, DA, DescentCompletionObjectOver.pullbackCoverBaseArrow,
      projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentTotalCoverOuterMap]
    rw [← hga]
    simp [Category.assoc]
  let hAnewRes : 𝟙 Y' ≫ IAnew.f = 𝟙 Y' ≫ IAresBase.f := by
    dsimp [IAnew, IAresBase, IAres, projectionDescentTotalCoverExplicitPullbackArrowAlong,
      projectionDescentTotalCoverExplicitPullbackArrow,
      DescentCompletionObjectOver.pullbackCoverBaseArrow, projectionDescentTotalCoverOuterMap]
    rw [← hga]
    simp [Category.assoc]
  let hAoldRes : g ≫ IAold.f = 𝟙 Y' ≫ IAresBase.f := hAoldNew.trans hAnewRes
  let hKoldRes : g ≫ Kold.f = 𝟙 Y' ≫ KresBase.f := by
    dsimp [Kold, KresBase, KoldArrow, Kres, DB,
      projectionDescentDatumExplicitPullbackArrowAlong,
      projectionDescentDatumExplicitPullbackArrow,
      DescentCompletionObjectOver.pullbackCoverBaseArrow]
    simp
  let hKresNew : 𝟙 Y' ≫ KresBase.f = 𝟙 Y' ≫ Knew.f := by
    dsimp [Knew, KresBase, Kres, projectionDescentDatumExplicitPullbackArrowAlong,
      projectionDescentDatumExplicitPullbackArrow,
      DB, DescentCompletionObjectOver.pullbackCoverBaseArrow]
    rw [← hgk]
    simp [Category.assoc]
  let hKoldNew : g ≫ Kold.f = 𝟙 Y' ≫ Knew.f := hKoldRes.trans hKresNew
  let hApb : g ≫ IAoldArrow.f = 𝟙 Y' ≫ IAres.f := by
    dsimp [IAoldArrow, IAres, projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentTotalCoverExplicitPullbackArrowAlong]
    exact (Category.comp_id g).trans (Category.id_comp g).symm
  let hKpb : g ≫ KoldArrow.f = 𝟙 Y' ≫ Kres.f := by
    dsimp [KoldArrow, Kres, projectionDescentDatumExplicitPullbackArrow,
      projectionDescentDatumExplicitPullbackArrowAlong]
    exact (Category.comp_id g).trans (Category.id_comp g).symm
  let αold :=
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
      (J := J) hSheaf D A I a K k h
  let αnew :=
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
      (J := J) hSheaf D A I ga K gk hsmall
  let midOld :=
    αold.1.components.toHomOver.family IAoldArrow KoldArrow g g
      (by
        have hbase :
            αold.1.base = 𝟙 Y :=
          projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
            (J := J) hSheaf D A I a K k h
        rw [hbase]
        dsimp [IAoldArrow, KoldArrow, projectionDescentTotalCoverExplicitPullbackArrow,
          projectionDescentDatumExplicitPullbackArrow]
        exact (Category.assoc g (𝟙 Y) (𝟙 Y)).symm.trans
          (Category.comp_id (g ≫ 𝟙 Y)))
  let restrictedCore :=
    αold.1.components.toHomOver.family IAres Kres (𝟙 Y') (𝟙 Y')
      (by
        have hbase :
            αold.1.base = 𝟙 Y :=
          projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
            (J := J) hSheaf D A I a K k h
        rw [hbase]
        dsimp [IAres, Kres, projectionDescentTotalCoverExplicitPullbackArrowAlong,
          projectionDescentDatumExplicitPullbackArrowAlong]
        calc
          𝟙 Y' ≫ g ≫ 𝟙 Y = (𝟙 Y' ≫ g) ≫ 𝟙 Y := by
            rw [← Category.assoc]
          _ = 𝟙 Y' ≫ g := Category.comp_id _)
  let midNew :=
    αnew.1.components.toHomOver.family
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
      (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K gk)
      (𝟙 Y') (𝟙 Y')
      (by
        have hbase :
            αnew.1.base = 𝟙 Y' :=
          projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
            (J := J) hSheaf D A I ga K gk hsmall
        rw [hbase]
        dsimp [projectionDescentTotalCoverExplicitPullbackArrow,
          projectionDescentDatumExplicitPullbackArrow]
        calc
          𝟙 Y' ≫ 𝟙 Y' ≫ 𝟙 Y' = 𝟙 Y' ≫ 𝟙 Y' := by rw [Category.id_comp]
          _ = 𝟙 Y' ≫ 𝟙 Y' := rfl)
  let sourceOldNew := (DA.overlapIso (I₁ := IAold) (I₂ := IAnew) g (𝟙 Y') hAoldNew).hom
  let sourceNewRes := (DA.overlapIso (I₁ := IAnew) (I₂ := IAresBase)
    (𝟙 Y') (𝟙 Y') hAnewRes).hom
  let sourceOldRes := (DA.overlapIso (I₁ := IAold) (I₂ := IAresBase)
    g (𝟙 Y') hAoldRes).hom
  let targetOldRes := (DB.overlapIso (I₁ := Kold) (I₂ := KresBase)
    g (𝟙 Y') hKoldRes).hom
  let targetResNew := (DB.overlapIso (I₁ := KresBase) (I₂ := Knew)
    (𝟙 Y') (𝟙 Y') hKresNew).hom
  let targetOldNew := (DB.overlapIso (I₁ := Kold) (I₂ := Knew)
    g (𝟙 Y') hKoldNew).hom
  have hsourcePull :
      ((DescentCompletionObjectOver.pullback (J := J) DA
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)).overlapIso
          (I₁ := IAoldArrow) (I₂ := IAres) g (𝟙 Y') hApb).hom =
        sourceOldRes := by
    simpa [sourceOldRes, hAoldRes, IAold, IAresBase, IAoldArrow, IAres] using
      DescentCompletionObjectOver.pullback_overlapIso_hom (J := J) DA
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
        IAoldArrow IAres g (𝟙 Y') hApb
  have htargetPull :
      ((DescentCompletionObjectOver.pullback (J := J) DB
        (k ≫ K.f)).overlapIso
          (I₁ := KoldArrow) (I₂ := Kres) g (𝟙 Y') hKpb).hom =
        targetOldRes := by
    simpa [targetOldRes, hKoldRes, Kold, KresBase, KoldArrow, Kres] using
      DescentCompletionObjectOver.pullback_overlapIso_hom (J := J) DB
        (k ≫ K.f) KoldArrow Kres g (𝟙 Y') hKpb
  have hcompatPull :
      ((DescentCompletionObjectOver.pullback (J := J) DA
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)).overlapIso
          (I₁ := IAoldArrow) (I₂ := IAres) g (𝟙 Y') hApb).hom ≫
        restrictedCore =
      midOld ≫
        ((DescentCompletionObjectOver.pullback (J := J) DB
          (k ≫ K.f)).overlapIso
            (I₁ := KoldArrow) (I₂ := Kres) g (𝟙 Y') hKpb).hom := by
    simpa [midOld, restrictedCore, hApb, hKpb] using
      αold.1.components.toHomOver.compatible
        IAoldArrow IAres KoldArrow Kres
        g (𝟙 Y') g (𝟙 Y')
        hApb hKpb
        (by
          have hbase :
              αold.1.base = 𝟙 Y :=
            projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
              (J := J) hSheaf D A I a K k h
          rw [hbase]
          dsimp [IAoldArrow, KoldArrow, projectionDescentTotalCoverExplicitPullbackArrow,
            projectionDescentDatumExplicitPullbackArrow]
          exact (Category.assoc g (𝟙 Y) (𝟙 Y)).symm.trans
            (Category.comp_id (g ≫ 𝟙 Y)))
        (by
          have hbase :
              αold.1.base = 𝟙 Y :=
            projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
              (J := J) hSheaf D A I a K k h
          rw [hbase]
          dsimp [IAres, Kres, projectionDescentTotalCoverExplicitPullbackArrowAlong,
            projectionDescentDatumExplicitPullbackArrowAlong]
          calc
            𝟙 Y' ≫ g ≫ 𝟙 Y = (𝟙 Y' ≫ g) ≫ 𝟙 Y := by
              rw [← Category.assoc]
            _ = 𝟙 Y' ≫ g := Category.comp_id _)
  have hcompat : sourceOldRes ≫ restrictedCore = midOld ≫ targetOldRes := by
    simpa [hsourcePull, htargetPull] using hcompatPull
  have hsourceComp : sourceOldNew ≫ sourceNewRes = sourceOldRes := by
    simpa [sourceOldNew, sourceNewRes, sourceOldRes, hAoldNew, hAnewRes, hAoldRes] using
      DescentCompletionObjectOver.overlapIso_hom_comp (J := J) DA
        (I₁ := IAold) (I₂ := IAnew) (I₃ := IAresBase)
        g (𝟙 Y') (𝟙 Y') hAoldNew hAnewRes
  have htargetComp : targetOldRes ≫ targetResNew = targetOldNew := by
    simpa [targetOldRes, targetResNew, targetOldNew, hKoldRes, hKresNew, hKoldNew] using
      DescentCompletionObjectOver.overlapIso_hom_comp (J := J) DB
        (I₁ := Kold) (I₂ := KresBase) (I₃ := Knew)
        g (𝟙 Y') (𝟙 Y') hKoldRes hKresNew
  have hresEq : (sourceNewRes ≫ restrictedCore) ≫ targetResNew = midNew := by
    simpa [projectionDescentRealizationExplicitMiddleRestrictedComponentLaw,
      projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInnerOldRestrictedComponent,
      hsmall, DA, DB, IAnew, Knew, IAres, Kres, IAresBase, KresBase,
      αold, αnew, sourceNewRes, targetResNew, restrictedCore, midNew] using
      hrestricted g I a K k h ga gk hga hgk
  change midOld ≫ targetOldNew = sourceOldNew ≫ midNew
  rw [← hresEq]
  calc
    midOld ≫ targetOldNew =
        midOld ≫ (targetOldRes ≫ targetResNew) := by
          exact congrArg (fun q => midOld ≫ q) htargetComp.symm
    _ = (midOld ≫ targetOldRes) ≫ targetResNew := by
      rw [Category.assoc]
    _ = (sourceOldRes ≫ restrictedCore) ≫ targetResNew := by
      exact congrArg (fun q => q ≫ targetResNew) hcompat.symm
    _ = ((sourceOldNew ≫ sourceNewRes) ≫ restrictedCore) ≫ targetResNew := by
      exact congrArg (fun q => (q ≫ restrictedCore) ≫ targetResNew) hsourceComp.symm
    _ = sourceOldNew ≫ ((sourceNewRes ≫ restrictedCore) ≫ targetResNew) := by
      simp [Category.assoc]

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
