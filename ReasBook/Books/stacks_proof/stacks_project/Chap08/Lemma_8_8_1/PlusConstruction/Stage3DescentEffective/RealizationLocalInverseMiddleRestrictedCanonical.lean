import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationLocalInverseMiddleBridge

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

/-- Pullback law for the canonical-pullback owner form of the outer transition used by the
inverse realization map `Lambda_a^{-1}`.  This isolates the restriction law coming directly from
the outer descent datum `D`, before the explicit-pullback owner bridges are applied. -/
theorem projectionDescentOuterFiberHomFromDatumInnerToTotalCover_pullHom
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
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := canonicalFiberPseudofunctor P)
        (projectionDescentOuterFiberHomFromDatumInnerToTotalCover
          (J := J) hSheaf D I K k A a h)
        g
        (gk ≫ K.f)
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga)
        (by
          simp [← hgk, Category.assoc])
        (by
          simp [projectionDescentTotalCoverOuterMap, ← hga, Category.assoc]) =
      projectionDescentOuterFiberHomFromDatumInnerToTotalCover
        (J := J) hSheaf D I K gk A ga
        (by
          calc
            gk ≫ K.f ≫ I.f = g ≫ k ≫ K.f ≫ I.f := by
              rw [← hgk]
              simp [Category.assoc]
            _ = g ≫ (a ≫ A.f) := by
              simpa [Category.assoc] using congrArg (fun q => g ≫ q) h
            _ = ga ≫ A.f := by rw [← hga]; simp [Category.assoc]) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  dsimp [projectionDescentOuterFiberHomFromDatumInnerToTotalCover,
    projectionDescentOuterFiberHom]
  simpa [projectionDescentTotalCoverOuterMap, Category.assoc] using
    D.pullHom_hom g
      ((k ≫ K.f) ≫ I.f)
      ((gk ≫ K.f) ≫ I.f)
      (by
        rw [← hgk]
        simp [Category.assoc])
      (k ≫ K.f)
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
      rfl
      (by
        calc
          projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a ≫
              (projectionDescentTotalCoverOuter (J := J) hSheaf D A).f =
            a ≫ A.f := by
              have hA :
                  a ≫ ((projectionDescentTotalCoverInner (J := J) hSheaf D A).f ≫
                      (projectionDescentTotalCoverOuter (J := J) hSheaf D A).f) =
                    a ≫ A.f :=
                congrArg (fun q => a ≫ q)
                  (projectionDescentTotalCover_fac (J := J) hSheaf D A)
              simpa [projectionDescentTotalCoverOuterMap, Category.assoc] using hA
          _ = (k ≫ K.f) ≫ I.f := by simpa [Category.assoc] using h.symm)
      (gk ≫ K.f)
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga)
      (by simp [← hgk, Category.assoc])
      (by simp [projectionDescentTotalCoverOuterMap, ← hga, Category.assoc])

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Source stage 3.13 canonical-owner restriction law for the transported outer component
`theta_ab,ij` used in the inverse realization map `Lambda_a^{-1}`.

Restricting the old explicit-owner component and then using the explicit pullback composition
bridges agrees with rebuilding the component directly on the smaller overlap. -/
theorem projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_restrict
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
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    let hsmall : gk ≫ K.f ≫ I.f = ga ≫ A.f := by
      calc
        gk ≫ K.f ≫ I.f = g ≫ k ≫ K.f ≫ I.f := by
          rw [← hgk]
          simp [Category.assoc]
        _ = g ≫ (a ≫ A.f) := by
          simpa [Category.assoc] using congrArg (fun q => g ≫ q) h
        _ = ga ≫ A.f := by rw [← hga]; simp [Category.assoc]
    let OB := projectionDescentDatumObject (J := J) hSheaf D I
    let OA := projectionDescentDatumObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
    let fB := k ≫ K.f
    let fA := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a
    let fB' := gk ≫ K.f
    let fA' := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga
    let hfB : g ≫ fB = fB' := by
      simp [fB, fB', ← hgk, Category.assoc]
    let hfA : g ≫ fA = fA' := by
      simp [fA, fA', projectionDescentTotalCoverOuterMap, ← hga, Category.assoc]
    let eB := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OB fB g fB' hfB
    let eA := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OA fA g fA' hfA
    let αold :=
      projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
        (J := J) hSheaf D I K k A a h
    let αnew :=
      projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
        (J := J) hSheaf D I K gk A ga hsmall
    eB.hom ≫ ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map αold ≫
        eA.inv =
      αnew := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let hsmall : gk ≫ K.f ≫ I.f = ga ≫ A.f := by
    calc
      gk ≫ K.f ≫ I.f = g ≫ k ≫ K.f ≫ I.f := by
        rw [← hgk]
        simp [Category.assoc]
      _ = g ≫ (a ≫ A.f) := by
        simpa [Category.assoc] using congrArg (fun q => g ≫ q) h
      _ = ga ≫ A.f := by rw [← hga]; simp [Category.assoc]
  let IA := projectionDescentTotalCoverOuter (J := J) hSheaf D A
  let OB := projectionDescentDatumObject (J := J) hSheaf D I
  let OA := projectionDescentDatumObject (J := J) hSheaf D IA
  let fB := k ≫ K.f
  let fA := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a
  let fB' := gk ≫ K.f
  let fA' := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga
  let hfB : g ≫ fB = fB' := by
    simp [fB, fB', ← hgk, Category.assoc]
  let hfA : g ≫ fA = fA' := by
    simp [fA, fA', projectionDescentTotalCoverOuterMap, ← hga, Category.assoc]
  let eB := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OB fB g fB' hfB
  let eA := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OA fA g fA' hfA
  let eOldB := projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D I fB
  let eOldA := projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D IA fA
  let eNewB := projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D I fB'
  let eNewA := projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D IA fA'
  let outerOld :=
    projectionDescentOuterFiberHomFromDatumInnerToTotalCover
      (J := J) hSheaf D I K k A a h
  let outerNew :=
    projectionDescentOuterFiberHomFromDatumInnerToTotalCover
      (J := J) hSheaf D I K gk A ga hsmall
  let κB := ((canonicalFiberPseudofunctor P).mapComp' fB.op.toLoc g.op.toLoc fB'.op.toLoc
      (comp_toLoc_eq fB g fB' hfB)).hom.toNatTrans.app (D.obj I)
  let κA := ((canonicalFiberPseudofunctor P).mapComp' fA.op.toLoc g.op.toLoc fA'.op.toLoc
      (comp_toLoc_eq fA g fA' hfA)).inv.toNatTrans.app (D.obj IA)
  have hB :
      eB.hom ≫ ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map eOldB.hom =
        eNewB.hom ≫ κB := by
    simpa [OB, eB, eOldB, eNewB, κB] using
      projectionDescentDatumPullbackIsoCanonicalOriginal_hom_naturality
        (J := J) hSheaf D I fB g fB' hfB
  have hA :
      ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map eOldA.inv ≫ eA.inv =
        κA ≫ eNewA.inv := by
    simpa [OA, eA, eOldA, eNewA, κA] using
      projectionDescentDatumPullbackIsoCanonicalOriginal_inv_naturality
        (J := J) hSheaf D IA fA g fA' hfA
  have hOuter :
      κB ≫ ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map outerOld ≫
        κA = outerNew := by
    simpa [κB, κA, outerOld, outerNew, fB, fA, fB', fA', hsmall,
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom] using
      projectionDescentOuterFiberHomFromDatumInnerToTotalCover_pullHom
        (J := J) hSheaf D I K g k A a h gk ga hgk hga
  dsimp [projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover]
  change eB.hom ≫
      ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map
        (eOldB.hom ≫ outerOld ≫ eOldA.inv) ≫ eA.inv =
    eNewB.hom ≫ outerNew ≫ eNewA.inv
  rw [Functor.map_comp, Functor.map_comp]
  calc
    eB.hom ≫
        (((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map eOldB.hom ≫
          ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map outerOld ≫
          ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map eOldA.inv) ≫
        eA.inv =
      (eB.hom ≫ ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map eOldB.hom) ≫
        ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map outerOld ≫
        (((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map eOldA.inv ≫ eA.inv) := by
        simp [Category.assoc]
    _ = (eNewB.hom ≫ κB) ≫
        ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map outerOld ≫
        (κA ≫ eNewA.inv) := by
        rw [hB, hA]
    _ = eNewB.hom ≫
        (κB ≫ ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map outerOld ≫
          κA) ≫ eNewA.inv := by
        simp [Category.assoc]
    _ = eNewB.hom ≫ outerNew ≫ eNewA.inv := by
        rw [hOuter]

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
