import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.PullHom
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.ExplicitMiddleRestrictedCore

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
`Theta_ab`: restricting the old explicit-owner component and then using the explicit pullback
composition bridges agrees with rebuilding the component directly on the smaller overlap. -/
theorem projectionDescentExplicitOuterFiberHomForTotalCover_restrict
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
    let hsmall : ga ≫ A.f = gb ≫ B.f := by
      calc
        ga ≫ A.f = g ≫ a ≫ A.f := by rw [← hga]; simp [Category.assoc]
        _ = g ≫ b ≫ B.f := by
          simpa [Category.assoc] using congrArg (fun q => g ≫ q) h
        _ = gb ≫ B.f := by rw [← hgb]; simp [Category.assoc]
    let OA := projectionDescentDatumObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
    let OB := projectionDescentDatumObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D B)
    let fA := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a
    let fB := projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b
    let fA' := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga
    let fB' := projectionDescentTotalCoverOuterMap (J := J) hSheaf D B gb
    let hfA : g ≫ fA = fA' := by
      simp [fA, fA', projectionDescentTotalCoverOuterMap, ← hga, Category.assoc]
    let hfB : g ≫ fB = fB' := by
      simp [fB, fB', projectionDescentTotalCoverOuterMap, ← hgb, Category.assoc]
    let eA := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OA fA g fA' hfA
    let eB := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OB fB g fB' hfB
    let αold := projectionDescentExplicitOuterFiberHomForTotalCover (J := J) hSheaf D A B a b h
    let αnew := projectionDescentExplicitOuterFiberHomForTotalCover (J := J) hSheaf D A B ga gb hsmall
    eA.hom ≫ ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map αold ≫ eB.inv =
      αnew := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let hsmall : ga ≫ A.f = gb ≫ B.f := by
    calc
      ga ≫ A.f = g ≫ a ≫ A.f := by rw [← hga]; simp [Category.assoc]
      _ = g ≫ b ≫ B.f := by
        simpa [Category.assoc] using congrArg (fun q => g ≫ q) h
      _ = gb ≫ B.f := by rw [← hgb]; simp [Category.assoc]
  let IA := projectionDescentTotalCoverOuter (J := J) hSheaf D A
  let IB := projectionDescentTotalCoverOuter (J := J) hSheaf D B
  let OA := projectionDescentDatumObject (J := J) hSheaf D IA
  let OB := projectionDescentDatumObject (J := J) hSheaf D IB
  let fA := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a
  let fB := projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b
  let fA' := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga
  let fB' := projectionDescentTotalCoverOuterMap (J := J) hSheaf D B gb
  let hfA : g ≫ fA = fA' := by
    simp [fA, fA', projectionDescentTotalCoverOuterMap, ← hga, Category.assoc]
  let hfB : g ≫ fB = fB' := by
    simp [fB, fB', projectionDescentTotalCoverOuterMap, ← hgb, Category.assoc]
  let eA := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OA fA g fA' hfA
  let eB := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OB fB g fB' hfB
  let eOldA := projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D IA fA
  let eOldB := projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D IB fB
  let eNewA := projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D IA fA'
  let eNewB := projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D IB fB'
  let outerOld := projectionDescentOuterFiberHomForTotalCover (J := J) hSheaf D A B a b h
  let outerNew := projectionDescentOuterFiberHomForTotalCover (J := J) hSheaf D A B ga gb hsmall
  let κA := ((canonicalFiberPseudofunctor P).mapComp' fA.op.toLoc g.op.toLoc fA'.op.toLoc
      (comp_toLoc_eq fA g fA' hfA)).hom.toNatTrans.app (D.obj IA)
  let κB := ((canonicalFiberPseudofunctor P).mapComp' fB.op.toLoc g.op.toLoc fB'.op.toLoc
      (comp_toLoc_eq fB g fB' hfB)).inv.toNatTrans.app (D.obj IB)
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
        (J := J) hSheaf D IB fB g fB' hfB
  have hOuter :
      κA ≫ ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map outerOld ≫
        κB = outerNew := by
    simpa [κA, κB, outerOld, outerNew, fA, fB, fA', fB', hsmall,
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom] using
      projectionDescentOuterFiberHomForTotalCover_pullHom
        (J := J) hSheaf D A B g a b h ga gb hga hgb
  dsimp [projectionDescentExplicitOuterFiberHomForTotalCover]
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

/-- Source stage 3.13 component-expansion obligation for the restricted explicit middle.

The canonical-owner calculation already proves the fiber-level equality
`eA.hom ≫ g^*Theta_ab ≫ eB.inv = Theta_ab'`.  The remaining source-faithful owner step is to
identify the component of the left-hand threefold composite with the explicit expression
"source overlap, old restricted component, target overlap" used in the total-cover construction.
-/
def projectionDescentExplicitOuterFiberHomForTotalCoverRestrictedCompositeComponentLaw
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) : Prop :=
  ∀ ⦃Y' Y : C⦄ (g : Y' ⟶ Y)
    ⦃A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow⦄
    (a : Y ⟶ A.Y) (b : Y ⟶ B.Y)
    (h : a ≫ A.f = b ≫ B.f)
    (ga : Y' ⟶ A.Y) (gb : Y' ⟶ B.Y)
    (hga : g ≫ a = ga) (hgb : g ≫ b = gb),
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    let IA := projectionDescentTotalCoverOuter (J := J) hSheaf D A
    let IB := projectionDescentTotalCoverOuter (J := J) hSheaf D B
    let OA := projectionDescentDatumObject (J := J) hSheaf D IA
    let OB := projectionDescentDatumObject (J := J) hSheaf D IB
    let fA := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a
    let fB := projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b
    let fA' := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga
    let fB' := projectionDescentTotalCoverOuterMap (J := J) hSheaf D B gb
    let hfA : g ≫ fA = fA' := by
      simp [fA, fA', projectionDescentTotalCoverOuterMap, ← hga, Category.assoc]
    let hfB : g ≫ fB = fB' := by
      simp [fB, fB', projectionDescentTotalCoverOuterMap, ← hgb, Category.assoc]
    let eA := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OA fA g fA' hfA
    let eB := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OB fB g fB' hfB
    let αold :=
      projectionDescentExplicitOuterFiberHomForTotalCover (J := J) hSheaf D A B a b h
    let β :=
      eA.hom ≫ ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map αold ≫ eB.inv
    β.1.components.toHomOver.family
        (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
        (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B gb)
        (𝟙 Y') (𝟙 Y')
        (by
          have hbase : β.1.base = 𝟙 Y' := by
            letI : P.IsHomLift (𝟙 Y') β.1 := β.2
            have hfac := IsHomLift.fac' P (𝟙 Y') β.1
            simpa [P, projectionFunctor, explicitPullbackFiberObject] using hfac
          rw [hbase]
          dsimp [projectionDescentTotalCoverExplicitPullbackArrow]
          calc
            𝟙 Y' ≫ 𝟙 Y' ≫ 𝟙 Y' = 𝟙 Y' ≫ 𝟙 Y' := by rw [Category.id_comp]
            _ = 𝟙 Y' ≫ 𝟙 Y' := rfl) =
      projectionDescentExplicitOuterFiberHomForTotalCoverOldRestrictedComponent
        (J := J) hSheaf D A B g a b h ga gb hga hgb

set_option maxHeartbeats 1000000 in
/-- The explicit restricted-component owner law implies the threefold composite component
expansion for the total-cover transition middle.

The canonical-owner restriction theorem identifies the threefold composite with the rebuilt
explicit owner, and the restricted-component law identifies that rebuilt component with the
source-text old restricted expression. -/
theorem projectionDescentExplicitOuterFiberHomForTotalCoverRestrictedCompositeComponentLaw_of_restrictedComponent
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hrestricted :
      projectionDescentTotalCoverExplicitMiddleRestrictedComponentLaw
        (J := J) hSheaf D) :
    projectionDescentExplicitOuterFiberHomForTotalCoverRestrictedCompositeComponentLaw
      (J := J) hSheaf D := by
  intro Y' Y g A B a b h ga gb hga hgb
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let hsmall : ga ≫ A.f = gb ≫ B.f := by
    calc
      ga ≫ A.f = g ≫ a ≫ A.f := by rw [← hga]; simp [Category.assoc]
      _ = g ≫ b ≫ B.f := by
        simpa [Category.assoc] using congrArg (fun q => g ≫ q) h
      _ = gb ≫ B.f := by rw [← hgb]; simp [Category.assoc]
  let IA := projectionDescentTotalCoverOuter (J := J) hSheaf D A
  let IB := projectionDescentTotalCoverOuter (J := J) hSheaf D B
  let OA := projectionDescentDatumObject (J := J) hSheaf D IA
  let OB := projectionDescentDatumObject (J := J) hSheaf D IB
  let fA := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a
  let fB := projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b
  let fA' := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga
  let fB' := projectionDescentTotalCoverOuterMap (J := J) hSheaf D B gb
  let hfA : g ≫ fA = fA' := by
    simp [fA, fA', projectionDescentTotalCoverOuterMap, ← hga, Category.assoc]
  let hfB : g ≫ fB = fB' := by
    simp [fB, fB', projectionDescentTotalCoverOuterMap, ← hgb, Category.assoc]
  let eA := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OA fA g fA' hfA
  let eB := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OB fB g fB' hfB
  let αold :=
    projectionDescentExplicitOuterFiberHomForTotalCover (J := J) hSheaf D A B a b h
  let αnew :=
    projectionDescentExplicitOuterFiberHomForTotalCover (J := J) hSheaf D A B ga gb hsmall
  have hFiber :
      eA.hom ≫ ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map αold ≫
          eB.inv =
        αnew := by
    simpa [P, IA, IB, OA, OB, fA, fB, fA', fB', hfA, hfB, eA, eB, αold, αnew,
      hsmall] using
      projectionDescentExplicitOuterFiberHomForTotalCover_restrict
        (J := J) hSheaf D A B g a b h ga gb hga hgb
  let compOf (β :
      explicitPullbackFiberObject (J := J) hSheaf OA fA' ⟶
        explicitPullbackFiberObject (J := J) hSheaf OB fB') :
      (projectionDescentDatumLocalObject (J := J) hSheaf D IA).restrictedLocalObject
          (DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
            (projectionDescentDatumLocalObject (J := J) hSheaf D IA) fA'
            (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga))
          (𝟙 Y') ⟶
        (projectionDescentDatumLocalObject (J := J) hSheaf D IB).restrictedLocalObject
          (DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
            (projectionDescentDatumLocalObject (J := J) hSheaf D IB) fB'
            (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B gb))
          (𝟙 Y') :=
    β.1.components.toHomOver.family
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B gb)
      (𝟙 Y') (𝟙 Y')
      (by
        have hbase : β.1.base = 𝟙 Y' := by
          letI : P.IsHomLift (𝟙 Y') β.1 := β.2
          have hfac := IsHomLift.fac' P (𝟙 Y') β.1
          simpa [P, projectionFunctor, explicitPullbackFiberObject] using hfac
        rw [hbase]
        dsimp [projectionDescentTotalCoverExplicitPullbackArrow]
        calc
          𝟙 Y' ≫ 𝟙 Y' ≫ 𝟙 Y' = 𝟙 Y' ≫ 𝟙 Y' := by rw [Category.id_comp]
          _ = 𝟙 Y' ≫ 𝟙 Y' := rfl)
  have hcomponent := congrArg compOf hFiber
  have hright :
      compOf αnew =
        (let α :=
          projectionDescentExplicitOuterFiberHomForTotalCover (J := J)
            hSheaf D A B ga gb hsmall
        α.1.components.toHomOver.family
          (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
          (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B gb)
          (𝟙 Y') (𝟙 Y')
          (by
            have hbase :
                α.1.base = 𝟙 Y' :=
              projectionDescentExplicitOuterFiberHomForTotalCover_base
                (J := J) hSheaf D A B ga gb hsmall
            rw [hbase]
            dsimp [projectionDescentTotalCoverExplicitPullbackArrow]
            calc
              𝟙 Y' ≫ 𝟙 Y' ≫ 𝟙 Y' = 𝟙 Y' ≫ 𝟙 Y' := by rw [Category.id_comp]
              _ = 𝟙 Y' ≫ 𝟙 Y' := rfl)) := by
    dsimp [compOf, αnew]
  have hres :
      projectionDescentExplicitOuterFiberHomForTotalCoverOldRestrictedComponent
          (J := J) hSheaf D A B g a b h ga gb hga hgb =
        (let α :=
          projectionDescentExplicitOuterFiberHomForTotalCover (J := J)
            hSheaf D A B ga gb hsmall
        α.1.components.toHomOver.family
          (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
          (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B gb)
          (𝟙 Y') (𝟙 Y')
          (by
            have hbase :
                α.1.base = 𝟙 Y' :=
              projectionDescentExplicitOuterFiberHomForTotalCover_base
                (J := J) hSheaf D A B ga gb hsmall
            rw [hbase]
            dsimp [projectionDescentTotalCoverExplicitPullbackArrow]
            calc
              𝟙 Y' ≫ 𝟙 Y' ≫ 𝟙 Y' = 𝟙 Y' ≫ 𝟙 Y' := by rw [Category.id_comp]
              _ = 𝟙 Y' ≫ 𝟙 Y' := rfl)) := by
    simpa [projectionDescentTotalCoverExplicitMiddleRestrictedComponentLaw,
      hsmall] using hrestricted g a b h ga gb hga hgb
  exact (hcomponent.trans hright).trans hres.symm

/-- Once the remaining threefold-composite component expansion is supplied, the canonical
fiber-level restriction theorem gives the restricted explicit middle component law. -/
theorem projectionDescentTotalCoverExplicitMiddleRestrictedComponentLaw_of_restrictedComposite
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hcomposite :
      projectionDescentExplicitOuterFiberHomForTotalCoverRestrictedCompositeComponentLaw
        (J := J) hSheaf D) :
    projectionDescentTotalCoverExplicitMiddleRestrictedComponentLaw (J := J) hSheaf D := by
  intro Y' Y g A B a b h ga gb hga hgb
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let hsmall : ga ≫ A.f = gb ≫ B.f := by
    calc
      ga ≫ A.f = g ≫ a ≫ A.f := by rw [← hga]; simp [Category.assoc]
      _ = g ≫ b ≫ B.f := by
        simpa [Category.assoc] using congrArg (fun q => g ≫ q) h
      _ = gb ≫ B.f := by rw [← hgb]; simp [Category.assoc]
  let IA := projectionDescentTotalCoverOuter (J := J) hSheaf D A
  let IB := projectionDescentTotalCoverOuter (J := J) hSheaf D B
  let OA := projectionDescentDatumObject (J := J) hSheaf D IA
  let OB := projectionDescentDatumObject (J := J) hSheaf D IB
  let fA := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a
  let fB := projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b
  let fA' := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A ga
  let fB' := projectionDescentTotalCoverOuterMap (J := J) hSheaf D B gb
  let hfA : g ≫ fA = fA' := by
    simp [fA, fA', projectionDescentTotalCoverOuterMap, ← hga, Category.assoc]
  let hfB : g ≫ fB = fB' := by
    simp [fB, fB', projectionDescentTotalCoverOuterMap, ← hgb, Category.assoc]
  let eA := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OA fA g fA' hfA
  let eB := explicitPullbackFiberObjectCompIsoOfEq (J := J) hSheaf OB fB g fB' hfB
  let αold :=
    projectionDescentExplicitOuterFiberHomForTotalCover (J := J) hSheaf D A B a b h
  let αnew :=
    projectionDescentExplicitOuterFiberHomForTotalCover (J := J) hSheaf D A B ga gb hsmall
  have hFiber :
      eA.hom ≫ ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map αold ≫
          eB.inv =
        αnew := by
    simpa [P, IA, IB, OA, OB, fA, fB, fA', fB', hfA, hfB, eA, eB, αold, αnew,
      hsmall] using
      projectionDescentExplicitOuterFiberHomForTotalCover_restrict
        (J := J) hSheaf D A B g a b h ga gb hga hgb
  let compOf (β :
      explicitPullbackFiberObject (J := J) hSheaf OA fA' ⟶
        explicitPullbackFiberObject (J := J) hSheaf OB fB') :
      (projectionDescentDatumLocalObject (J := J) hSheaf D IA).restrictedLocalObject
          (DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
            (projectionDescentDatumLocalObject (J := J) hSheaf D IA) fA'
            (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga))
          (𝟙 Y') ⟶
        (projectionDescentDatumLocalObject (J := J) hSheaf D IB).restrictedLocalObject
          (DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
            (projectionDescentDatumLocalObject (J := J) hSheaf D IB) fB'
            (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B gb))
          (𝟙 Y') :=
    β.1.components.toHomOver.family
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B gb)
      (𝟙 Y') (𝟙 Y')
      (by
        have hbase : β.1.base = 𝟙 Y' := by
          letI : P.IsHomLift (𝟙 Y') β.1 := β.2
          have hfac := IsHomLift.fac' P (𝟙 Y') β.1
          simpa [P, projectionFunctor, explicitPullbackFiberObject] using hfac
        rw [hbase]
        dsimp [projectionDescentTotalCoverExplicitPullbackArrow]
        calc
          𝟙 Y' ≫ 𝟙 Y' ≫ 𝟙 Y' = 𝟙 Y' ≫ 𝟙 Y' := by rw [Category.id_comp]
          _ = 𝟙 Y' ≫ 𝟙 Y' := rfl)
  have hcomponent := congrArg compOf hFiber
  have hleft :
      compOf
          (eA.hom ≫ ((canonicalFiberPseudofunctor P).map g.op.toLoc).toFunctor.map αold ≫
            eB.inv) =
        projectionDescentExplicitOuterFiberHomForTotalCoverOldRestrictedComponent
          (J := J) hSheaf D A B g a b h ga gb hga hgb := by
    simpa [projectionDescentExplicitOuterFiberHomForTotalCoverRestrictedCompositeComponentLaw,
      compOf, P, IA, IB, OA, OB, fA, fB, fA', fB', hfA, hfB, eA, eB, αold] using
      hcomposite g a b h ga gb hga hgb
  have hright :
      compOf αnew =
        (let α :=
          projectionDescentExplicitOuterFiberHomForTotalCover (J := J)
            hSheaf D A B ga gb hsmall
        α.1.components.toHomOver.family
          (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A ga)
          (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B gb)
          (𝟙 Y') (𝟙 Y')
          (by
            have hbase :
                α.1.base = 𝟙 Y' :=
              projectionDescentExplicitOuterFiberHomForTotalCover_base
                (J := J) hSheaf D A B ga gb hsmall
            rw [hbase]
            dsimp [projectionDescentTotalCoverExplicitPullbackArrow]
            calc
              𝟙 Y' ≫ 𝟙 Y' ≫ 𝟙 Y' = 𝟙 Y' ≫ 𝟙 Y' := by rw [Category.id_comp]
              _ = 𝟙 Y' ≫ 𝟙 Y' := rfl)) := by
    dsimp [compOf, αnew]
  simpa [hsmall] using hleft.symm.trans (hcomponent.trans hright)

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
