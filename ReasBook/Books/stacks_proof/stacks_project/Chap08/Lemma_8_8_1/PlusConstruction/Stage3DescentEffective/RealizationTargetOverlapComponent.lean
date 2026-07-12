import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationComponent

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

/-- Transport an arrow of a pulled-back cover across an equality of base maps.

This isolates the purely cover-theoretic dependent transport used below; the transported arrow is
not definitionally identified with the original arrow. -/
noncomputable def pullbackCoverArrowOfEq
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {U W : C}
    (D : DescentCompletionObjectOver (J := J) X U)
    {q₁ q₂ : W ⟶ U} (h : q₁ = q₂)
    (K : (D.cover.pullback q₂).Arrow) :
    (D.cover.pullback q₁).Arrow where
  Y := K.Y
  f := K.f
  hf := by
    change (D.cover : Sieve _).arrows (K.f ≫ q₁)
    rw [h]
    exact K.hf

/-- Casting the transported pulled-back-cover arrow back along the same base equality recovers
the original arrow. -/
theorem pullbackCoverArrowOfEq_cast
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {U W : C}
    (D : DescentCompletionObjectOver (J := J) X U)
    {q₁ q₂ : W ⟶ U} (h : q₁ = q₂)
    (K : (D.cover.pullback q₂).Arrow) :
    cast (congrArg (fun q => (D.cover.pullback q).Arrow) h)
        (pullbackCoverArrowOfEq (J := J) D h K) =
      K := by
  cases h
  rfl

/-- Target-side owner bridge for `Λ_a`: if two target inner owners have the same composite
map to `T_a`, the second direct explicit pullback arrow may also be viewed as an arrow of the
first pullback cover.

This is only the cover-owner transport.  It deliberately does not identify the two pullback
objects definitionally. -/
noncomputable def projectionDescentDatumExplicitPullbackArrowOfEq
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K₁ K₂ : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k₁ : W ⟶ K₁.Y) (k₂ : W ⟶ K₂.Y)
    (hK : k₁ ≫ K₁.f = k₂ ≫ K₂.f) :
    ((projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.pullback
        (k₁ ≫ K₁.f)).Arrow :=
  pullbackCoverArrowOfEq (J := J)
    (projectionDescentDatumLocalObject (J := J) hSheaf D I) hK
    (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K₂ k₂)

/-- Casting the equality-transported target explicit pullback arrow along the equality of target
base maps recovers the directly rebuilt explicit arrow. -/
theorem projectionDescentDatumExplicitPullbackArrowOfEq_cast
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K₁ K₂ : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k₁ : W ⟶ K₁.Y) (k₂ : W ⟶ K₂.Y)
    (hK : k₁ ≫ K₁.f = k₂ ≫ K₂.f) :
    cast (congrArg
        (fun q => ((projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.pullback q).Arrow)
        hK)
        (projectionDescentDatumExplicitPullbackArrowOfEq (J := J)
          hSheaf D I K₁ K₂ k₁ k₂ hK) =
      projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K₂ k₂ := by
  exact pullbackCoverArrowOfEq_cast (J := J)
    (projectionDescentDatumLocalObject (J := J) hSheaf D I) hK
    (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K₂ k₂)

@[simp]
theorem projectionDescentDatumExplicitPullbackArrowOfEq_f
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K₁ K₂ : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k₁ : W ⟶ K₁.Y) (k₂ : W ⟶ K₂.Y)
    (hK : k₁ ≫ K₁.f = k₂ ≫ K₂.f) :
    (projectionDescentDatumExplicitPullbackArrowOfEq (J := J)
      hSheaf D I K₁ K₂ k₁ k₂ hK).f = 𝟙 W :=
  rfl

/-- After forgetting from the old pullback cover back to the datum cover, the equality-transported
target explicit arrow is exactly the refined inner owner built directly from `K₂, k₂`. -/
theorem projectionDescentDatumExplicitPullbackArrowOfEq_base_eq_refined
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K₁ K₂ : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k₁ : W ⟶ K₁.Y) (k₂ : W ⟶ K₂.Y)
    (hK : k₁ ≫ K₁.f = k₂ ≫ K₂.f) :
    DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D I)
        (k₁ ≫ K₁.f)
        (projectionDescentDatumExplicitPullbackArrowOfEq (J := J)
          hSheaf D I K₁ K₂ k₁ k₂ hK) =
      projectionDescentDatumRefinedInner (J := J) hSheaf D I K₂ k₂ := by
  ext
  · rfl
  · dsimp [projectionDescentDatumExplicitPullbackArrowOfEq, pullbackCoverArrowOfEq,
      projectionDescentDatumExplicitPullbackArrow, projectionDescentDatumRefinedInner,
      DescentCompletionObjectOver.pullbackCoverBaseArrow]
    exact heq_of_eq (by simpa using hK)

/-- The equality-transported target explicit arrow and the directly rebuilt target explicit arrow
have the same owner after forgetting both back to the original datum cover. -/
theorem projectionDescentDatumExplicitPullbackArrowOfEq_base_eq_direct
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K₁ K₂ : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k₁ : W ⟶ K₁.Y) (k₂ : W ⟶ K₂.Y)
    (hK : k₁ ≫ K₁.f = k₂ ≫ K₂.f) :
    DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D I)
        (k₁ ≫ K₁.f)
        (projectionDescentDatumExplicitPullbackArrowOfEq (J := J)
          hSheaf D I K₁ K₂ k₁ k₂ hK) =
      DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D I)
        (k₂ ≫ K₂.f)
        (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K₂ k₂) := by
  calc
    DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D I)
        (k₁ ≫ K₁.f)
        (projectionDescentDatumExplicitPullbackArrowOfEq (J := J)
          hSheaf D I K₁ K₂ k₁ k₂ hK) =
      projectionDescentDatumRefinedInner (J := J) hSheaf D I K₂ k₂ := by
        exact projectionDescentDatumExplicitPullbackArrowOfEq_base_eq_refined
          (J := J) hSheaf D I K₁ K₂ k₁ k₂ hK
    _ =
      DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D I)
        (k₂ ≫ K₂.f)
        (projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K₂ k₂) := by
        exact (projectionDescentDatumExplicitPullbackArrow_base
          (J := J) hSheaf D I K₂ k₂).symm

/-- Target-base form of the canonical outer transition used in `Λ_a`.

The source text only depends on the target map `q : W -> T_a`; the cover owner `(K, k)` is used
later to choose a component of the explicit pullback cover. -/
noncomputable def projectionDescentOuterFiberHomFromTotalCoverToDatumBase
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (a : W ⟶ A.Y)
    (q : W ⟶ I.Y)
    (h : a ≫ A.f = q ≫ I.f) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    ((canonicalFiberPseudofunctor P).map
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a).op.toLoc).toFunctor.obj
        (D.obj (projectionDescentTotalCoverOuter (J := J) hSheaf D A)) ⟶
      ((canonicalFiberPseudofunctor P).map q.op.toLoc).toFunctor.obj (D.obj I) :=
  projectionDescentOuterFiberHom (J := J) hSheaf D
    (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
    I
    (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
    q
    (by
      calc
        projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a ≫
            (projectionDescentTotalCoverOuter (J := J) hSheaf D A).f =
          a ≫ A.f := by
            have hA :
                a ≫ ((projectionDescentTotalCoverInner (J := J) hSheaf D A).f ≫
                    (projectionDescentTotalCoverOuter (J := J) hSheaf D A).f) =
                  a ≫ A.f :=
              congrArg (fun t => a ≫ t)
                (projectionDescentTotalCover_fac (J := J) hSheaf D A)
            simpa [projectionDescentTotalCoverOuterMap, Category.assoc] using hA
        _ = q ≫ I.f := h)

/-- Target-base form of the explicit-owner outer transition used in `Λ_a`. -/
noncomputable def projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (a : W ⟶ A.Y)
    (q : W ⟶ I.Y)
    (h : a ≫ A.f = q ≫ I.f) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    explicitPullbackFiberObject (J := J) hSheaf
        (projectionDescentDatumObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a) ⟶
      explicitPullbackFiberObject (J := J) hSheaf
        (projectionDescentDatumObject (J := J) hSheaf D I) q := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let eA :=
    projectionDescentDatumPullbackIsoCanonicalOriginal
      (J := J) hSheaf D (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
  let eB := projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D I q
  exact eA.hom ≫
    projectionDescentOuterFiberHomFromTotalCoverToDatumBase (J := J) hSheaf D A I a q h ≫
      eB.inv

/-- The existing owner-indexed explicit transition is the target-base transition specialized to
`q = k ≫ K.f`. -/
theorem projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_eq_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (a : W ⟶ A.Y)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y)
    (h : a ≫ A.f = k ≫ K.f ≫ I.f) :
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
      (J := J) hSheaf D A I a K k h =
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase
      (J := J) hSheaf D A I a (k ≫ K.f) (by simpa [Category.assoc] using h) := by
  dsimp [projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase,
    projectionDescentOuterFiberHomFromTotalCoverToDatumBase,
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner,
    projectionDescentOuterFiberHomFromTotalCoverToDatumInner]

/-- The target-base explicit transition respects equality transport of the target base map. -/
theorem projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase_congr_target
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (a : W ⟶ A.Y)
    (q₁ q₂ : W ⟶ I.Y)
    (hq : q₁ = q₂)
    (h₁ : a ≫ A.f = q₁ ≫ I.f)
    (h₂ : a ≫ A.f = q₂ ≫ I.f) :
    let OB := projectionDescentDatumObject (J := J) hSheaf D I
    let eTarget : explicitPullbackFiberObject (J := J) hSheaf OB q₁ ≅
        explicitPullbackFiberObject (J := J) hSheaf OB q₂ :=
      eqToIso (congrArg (fun q => explicitPullbackFiberObject (J := J) hSheaf OB q) hq)
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase
        (J := J) hSheaf D A I a q₁ h₁ ≫ eTarget.hom =
      projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase
        (J := J) hSheaf D A I a q₂ h₂ := by
  subst q₂
  have hp : h₁ = h₂ := Subsingleton.elim _ _
  subst hp
  simp

/-- The owner-indexed explicit transition respects equality transport of the target base map.
This is the morphism-level bridge needed before comparing explicit pullback-cover components. -/
theorem projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_congr_target
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
    let OB := projectionDescentDatumObject (J := J) hSheaf D I
    let eTarget : explicitPullbackFiberObject (J := J) hSheaf OB (k₁ ≫ K₁.f) ≅
        explicitPullbackFiberObject (J := J) hSheaf OB (k₂ ≫ K₂.f) :=
      eqToIso (congrArg (fun q => explicitPullbackFiberObject (J := J) hSheaf OB q) hK)
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
        (J := J) hSheaf D A I a K₁ k₁ h₁ ≫ eTarget.hom =
      projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
        (J := J) hSheaf D A I a K₂ k₂ h₂ := by
  rw [projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_eq_base]
  rw [projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_eq_base]
  simpa [Category.assoc] using
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase_congr_target
      (J := J) hSheaf D A I a (k₁ ≫ K₁.f) (k₂ ≫ K₂.f) hK
      (by simpa [Category.assoc] using h₁)
      (by simpa [Category.assoc] using h₂)

/-- Target-side half of the `Λ_a` compatibility square, with the second target owner kept as
an arrow of the first explicit target pullback cover.

This is the source-faithful owner step before the remaining equality transport from the
old pullback owner over `k₁ ≫ K₁.f` to the directly rebuilt owner over `k₂ ≫ K₂.f`.  It uses
only the ordinary `HomOver.compatible` square for the explicit outer morphism and then translates
the target overlap back from the pullback object to the datum object. -/
theorem projectionDescentExplicitTransitionComponentFromTotalCoverToDatumInner_comp_targetOverlap_oldOwner
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
    (h₁ : a ≫ A.f = k₁ ≫ K₁.f ≫ I.f) :
    let DB := projectionDescentDatumLocalObject (J := J) hSheaf D I
    let IA := projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a
    let Karr₁ := projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K₁ k₁
    let Karr₂old := projectionDescentDatumExplicitPullbackArrowOfEq
      (J := J) hSheaf D I K₁ K₂ k₁ k₂ hK
    let Kbase₁ := DescentCompletionObjectOver.pullbackCoverBaseArrow
      (J := J) DB (k₁ ≫ K₁.f) Karr₁
    let Kbase₂old := DescentCompletionObjectOver.pullbackCoverBaseArrow
      (J := J) DB (k₁ ≫ K₁.f) Karr₂old
    let hbase : 𝟙 W ≫ Kbase₁.f = 𝟙 W ≫ Kbase₂old.f := by rfl
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
        (DB.overlapIso (I₁ := Kbase₁) (I₂ := Kbase₂old)
          (𝟙 W) (𝟙 W) hbase).hom =
      (let α := projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
          (J := J) hSheaf D A I a K₁ k₁ h₁
      α.1.components.toHomOver.family IA Karr₂old (𝟙 W) (𝟙 W)
        (by
          have hα : α.1.base = 𝟙 W :=
            projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
              (J := J) hSheaf D A I a K₁ k₁ h₁
          rw [hα]
          dsimp [IA, Karr₂old, projectionDescentTotalCoverExplicitPullbackArrow]
          repeat rw [Category.id_comp]
          rfl)) := by
  dsimp only
  let DB := projectionDescentDatumLocalObject (J := J) hSheaf D I
  let IA := projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a
  let Karr₁ := projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K₁ k₁
  let Karr₂old := projectionDescentDatumExplicitPullbackArrowOfEq
    (J := J) hSheaf D I K₁ K₂ k₁ k₂ hK
  let Kbase₁ := DescentCompletionObjectOver.pullbackCoverBaseArrow
    (J := J) DB (k₁ ≫ K₁.f) Karr₁
  let Kbase₂old := DescentCompletionObjectOver.pullbackCoverBaseArrow
    (J := J) DB (k₁ ≫ K₁.f) Karr₂old
  let hbase : 𝟙 W ≫ Kbase₁.f = 𝟙 W ≫ Kbase₂old.f := by rfl
  let α := projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
    (J := J) hSheaf D A I a K₁ k₁ h₁
  have hα : α.1.base = 𝟙 W :=
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
      (J := J) hSheaf D A I a K₁ k₁ h₁
  let mid₁ := α.1.components.toHomOver.family IA Karr₁ (𝟙 W) (𝟙 W)
    (by
      rw [hα]
      dsimp [IA, Karr₁, projectionDescentTotalCoverExplicitPullbackArrow,
        projectionDescentDatumExplicitPullbackArrow]
      repeat rw [Category.id_comp]
      exact Category.comp_id (𝟙 W))
  let mid₂ := α.1.components.toHomOver.family IA Karr₂old (𝟙 W) (𝟙 W)
    (by
      rw [hα]
      dsimp [IA, Karr₂old, projectionDescentTotalCoverExplicitPullbackArrow]
      repeat rw [Category.id_comp]
      rfl)
  let hE : 𝟙 W ≫ Karr₁.f = 𝟙 W ≫ Karr₂old.f := by rfl
  have hcompat :=
    α.1.components.toHomOver.compatible IA IA Karr₁ Karr₂old
      (𝟙 W) (𝟙 W) (𝟙 W) (𝟙 W)
      (by rfl) hE
      (by
        rw [hα]
        dsimp [IA, Karr₁, projectionDescentTotalCoverExplicitPullbackArrow,
          projectionDescentDatumExplicitPullbackArrow]
        repeat rw [Category.id_comp]
        exact Category.comp_id (𝟙 W))
      (by
        rw [hα]
        dsimp [IA, Karr₂old, projectionDescentTotalCoverExplicitPullbackArrow]
        repeat rw [Category.id_comp]
        rfl)
  rw [DescentCompletionObjectOver.overlapIso_self_hom] at hcompat
  have hpullOverlap :
      ((DescentCompletionObjectOver.pullback (J := J) DB (k₁ ≫ K₁.f)).overlapIso
          (I₁ := Karr₁) (I₂ := Karr₂old) (𝟙 W) (𝟙 W) hE).hom =
        (DB.overlapIso (I₁ := Kbase₁) (I₂ := Kbase₂old)
          (𝟙 W) (𝟙 W) hbase).hom := by
    simpa [Kbase₁, Kbase₂old, hbase, Karr₁, Karr₂old] using
      DescentCompletionObjectOver.pullback_overlapIso_hom (J := J) DB (k₁ ≫ K₁.f)
        Karr₁ Karr₂old (𝟙 W) (𝟙 W) hE
  rw [← hpullOverlap]
  simpa [mid₁, mid₂, α, hα, IA, Karr₁, Karr₂old, hE] using hcompat.symm

/-- The equality proof supplied to a `HomOver.family` component is proof-irrelevant.

This avoids dependent rewrite through the full component expression when only the proof term of
the fibre-product condition changes. -/
theorem homOver_family_proof_irrel
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    {U V W : C}
    {D : DescentCompletionObjectOver (J := J) X U}
    {E : DescentCompletionObjectOver (J := J) X V}
    {f : U ⟶ V}
    (α : DescentCompletionObjectOver.HomOver (J := J) D E f)
    (I : D.cover.Arrow) (K : E.cover.Arrow)
    (i : W ⟶ I.Y) (k : W ⟶ K.Y)
    (h h' : i ≫ I.f ≫ f = k ≫ K.f) :
    α.family I K i k h = α.family I K i k h' := by
  have hp : h = h' := Subsingleton.elim _ _
  cases hp
  rfl

/-- The target-base explicit realization transition is vertical over `W`. -/
theorem projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (a : W ⟶ A.Y)
    (q : W ⟶ I.Y)
    (h : a ≫ A.f = q ≫ I.f) :
    letI := category (J := J) hSheaf
    (projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase
      (J := J) hSheaf D A I a q h).1.base = 𝟙 W := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let α :=
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase
      (J := J) hSheaf D A I a q h
  letI : P.IsHomLift (𝟙 W) α.1 := α.2
  have hfac := IsHomLift.fac' P (𝟙 W) α.1
  simpa [P, projectionFunctor, α] using hfac

/-- Component-level target transport for the target-base explicit outer morphism.

If the target base map is changed only by an equality `q₁ = q₂`, the component over the
transported pullback-cover arrow agrees with the directly rebuilt component after the visible
target overlap in the datum object. -/
def projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase_component_congr_target_law
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (a : W ⟶ A.Y)
    (q₁ q₂ : W ⟶ I.Y)
    (hq : q₁ = q₂)
    (h₁ : a ≫ A.f = q₁ ≫ I.f)
    (h₂ : a ≫ A.f = q₂ ≫ I.f)
    (K : ((projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.pullback q₂).Arrow)
    (κ : W ⟶ K.Y)
    (hκ : κ ≫ K.f = 𝟙 W) : Prop :=
    let DB := projectionDescentDatumLocalObject (J := J) hSheaf D I
    let IA := projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a
    let Kold := pullbackCoverArrowOfEq (J := J) DB hq K
    let KbaseOld := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) DB q₁ Kold
    let KbaseDirect := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) DB q₂ K
    let hbase : κ ≫ KbaseOld.f = κ ≫ KbaseDirect.f := by
      subst q₂
      rfl
    (let α :=
      projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase
        (J := J) hSheaf D A I a q₁ h₁
    α.1.components.toHomOver.family IA Kold (𝟙 W) κ
      (by
        have hα : α.1.base = 𝟙 W :=
          projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase_base
            (J := J) hSheaf D A I a q₁ h₁
        rw [hα]
        dsimp [IA, Kold, projectionDescentTotalCoverExplicitPullbackArrow,
          pullbackCoverArrowOfEq]
        calc
          𝟙 W ≫ 𝟙 W ≫ 𝟙 W = 𝟙 W ≫ 𝟙 W := by rw [Category.id_comp]
          _ = 𝟙 W := Category.comp_id (𝟙 W)
          _ = κ ≫ K.f := hκ.symm)) ≫
        (DB.overlapIso (I₁ := KbaseOld) (I₂ := KbaseDirect)
          κ κ hbase).hom =
      (let α :=
        projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase
          (J := J) hSheaf D A I a q₂ h₂
      α.1.components.toHomOver.family IA K (𝟙 W) κ
        (by
          have hα : α.1.base = 𝟙 W :=
            projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase_base
              (J := J) hSheaf D A I a q₂ h₂
          rw [hα]
          dsimp [IA, projectionDescentTotalCoverExplicitPullbackArrow]
          calc
            𝟙 W ≫ 𝟙 W ≫ 𝟙 W = 𝟙 W ≫ 𝟙 W := by rw [Category.id_comp]
            _ = 𝟙 W := Category.comp_id (𝟙 W)
            _ = κ ≫ K.f := hκ.symm))

/-- Component-level target transport for the actual explicit target owner used in `Λ_a`.

This is the `projectionDescentDatumExplicitPullbackArrow` specialization of
`projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase_component_congr_target_law`.
It avoids generalizing over arbitrary pullback-cover arrows, where the proof field of the arrow
creates unnecessary dependent-rewrite noise. -/
def projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase_component_congr_target_explicit_law
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (a : W ⟶ A.Y)
    (q : W ⟶ I.Y)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y)
    (hq : q = k ≫ K.f)
    (h₁ : a ≫ A.f = q ≫ I.f)
    (h₂ : a ≫ A.f = k ≫ K.f ≫ I.f) : Prop :=
    let DB := projectionDescentDatumLocalObject (J := J) hSheaf D I
    let IA := projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a
    let Kdirect := projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k
    let Kold := pullbackCoverArrowOfEq (J := J) DB hq Kdirect
    let KbaseOld := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) DB q Kold
    let KbaseDirect := DescentCompletionObjectOver.pullbackCoverBaseArrow
      (J := J) DB (k ≫ K.f) Kdirect
    let hbase : 𝟙 W ≫ KbaseOld.f = 𝟙 W ≫ KbaseDirect.f := by
      dsimp [KbaseOld, KbaseDirect, Kold, Kdirect,
        projectionDescentDatumExplicitPullbackArrow, pullbackCoverArrowOfEq,
        DescentCompletionObjectOver.pullbackCoverBaseArrow]
      simpa using hq
    (let α :=
      projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase
        (J := J) hSheaf D A I a q h₁
    α.1.components.toHomOver.family IA Kold (𝟙 W) (𝟙 W)
      (by
        have hα : α.1.base = 𝟙 W :=
          projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase_base
            (J := J) hSheaf D A I a q h₁
        rw [hα]
        dsimp [IA, Kold, Kdirect, projectionDescentTotalCoverExplicitPullbackArrow,
          projectionDescentDatumExplicitPullbackArrow, pullbackCoverArrowOfEq]
        change 𝟙 W ≫ 𝟙 W ≫ 𝟙 W = 𝟙 W ≫ 𝟙 W
        calc
          𝟙 W ≫ 𝟙 W ≫ 𝟙 W = 𝟙 W ≫ 𝟙 W := by rw [Category.id_comp]
          _ = 𝟙 W ≫ 𝟙 W := rfl)) ≫
        (DB.overlapIso (I₁ := KbaseOld) (I₂ := KbaseDirect)
          (𝟙 W) (𝟙 W) hbase).hom =
      (let α :=
        projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase
          (J := J) hSheaf D A I a (k ≫ K.f)
          (by simpa [Category.assoc] using h₂)
      α.1.components.toHomOver.family IA Kdirect (𝟙 W) (𝟙 W)
        (by
          have hα : α.1.base = 𝟙 W :=
            projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase_base
              (J := J) hSheaf D A I a (k ≫ K.f)
              (by simpa [Category.assoc] using h₂)
          rw [hα]
          dsimp [IA, Kdirect, projectionDescentTotalCoverExplicitPullbackArrow,
            projectionDescentDatumExplicitPullbackArrow]
          change 𝟙 W ≫ 𝟙 W ≫ 𝟙 W = 𝟙 W ≫ 𝟙 W
          calc
            𝟙 W ≫ 𝟙 W ≫ 𝟙 W = 𝟙 W ≫ 𝟙 W := by rw [Category.id_comp]
            _ = 𝟙 W ≫ 𝟙 W := rfl))

/-- The explicit component target-transport law holds. -/
theorem projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase_component_congr_target_explicit
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (a : W ⟶ A.Y)
    (q : W ⟶ I.Y)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y)
    (hq : q = k ≫ K.f)
    (h₁ : a ≫ A.f = q ≫ I.f)
    (h₂ : a ≫ A.f = k ≫ K.f ≫ I.f) :
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase_component_congr_target_explicit_law
      (J := J) hSheaf D A I a q K k hq h₁ h₂ := by
  subst q
  let h₂base : a ≫ A.f = (k ≫ K.f) ≫ I.f := by
    simpa [Category.assoc] using h₂
  have hp : h₁ = h₂base := Subsingleton.elim _ _
  cases hp
  unfold projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumBase_component_congr_target_explicit_law
  dsimp [pullbackCoverArrowOfEq, projectionDescentDatumExplicitPullbackArrow,
    DescentCompletionObjectOver.pullbackCoverBaseArrow]
  have hp' : h₁ = (by simpa [Category.assoc] using h₂) := Subsingleton.elim _ _
  cases hp'
  rw [DescentCompletionObjectOver.overlapIso_self_hom]
  erw [Category.comp_id]

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
