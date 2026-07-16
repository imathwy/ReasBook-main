import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationLocalInverse

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

/-- Source stage 3.13 inverse-realization cocycle, canonical-owner form.

This is the source-text identity
`rho_(a,i),(b,j) ≫ rho_(b,j),(c,k) = rho_(a,i),(c,k)` with the first
owner kept as the explicit datum-inner owner `(a,i)`.  It is the target-overlap half of
compatibility for the componentwise inverse of `Lambda_a`. -/
theorem projectionDescentOuterFiberHomFromDatumInnerToTotalCover_comp_forTotalCover
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : Y ⟶ K.Y)
    (A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : Y ⟶ A.Y) (b : Y ⟶ B.Y)
    (hka : k ≫ K.f ≫ I.f = a ≫ A.f)
    (hab : a ≫ A.f = b ≫ B.f) :
    letI := category (J := J) hSheaf
    projectionDescentOuterFiberHomFromDatumInnerToTotalCover
        (J := J) hSheaf D I K k A a hka ≫
      projectionDescentOuterFiberHomForTotalCover
        (J := J) hSheaf D A B a b hab =
    projectionDescentOuterFiberHomFromDatumInnerToTotalCover
      (J := J) hSheaf D I K k B b (hka.trans hab) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let IA := projectionDescentTotalCoverOuter (J := J) hSheaf D A
  let IB := projectionDescentTotalCoverOuter (J := J) hSheaf D B
  let fK := k ≫ K.f
  let fA := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a
  let fB := projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b
  let hKA : fK ≫ I.f = fA ≫ IA.f := by
    calc
      fK ≫ I.f = k ≫ K.f ≫ I.f := by simp [fK, Category.assoc]
      _ = a ≫ A.f := hka
      _ = fA ≫ IA.f := by
        have hA :
            a ≫ ((projectionDescentTotalCoverInner (J := J) hSheaf D A).f ≫
                (projectionDescentTotalCoverOuter (J := J) hSheaf D A).f) =
              a ≫ A.f :=
          congrArg (fun q => a ≫ q)
            (projectionDescentTotalCover_fac (J := J) hSheaf D A)
        simpa [fA, IA, projectionDescentTotalCoverOuterMap, Category.assoc] using hA.symm
  let hAB : fA ≫ IA.f = fB ≫ IB.f :=
    projectionDescentTotalCoverOuterMap_fac (J := J) hSheaf D A B a b hab
  let hKB : fK ≫ I.f = fB ≫ IB.f := hKA.trans hAB
  have hbase :
      D.hom (fA ≫ IA.f) fA fB rfl hAB.symm =
        D.hom (fK ≫ I.f) fA fB hKA.symm hKB.symm := by
    exact
      projectionDescentDatumHom_congr_base (J := J) hSheaf D hKA.symm
        fA fB rfl hAB.symm hKA.symm hKB.symm
  dsimp [projectionDescentOuterFiberHomFromDatumInnerToTotalCover,
    projectionDescentOuterFiberHomForTotalCover, projectionDescentOuterFiberHom]
  change D.hom (fK ≫ I.f) fK fA rfl hKA.symm ≫
      D.hom (fA ≫ IA.f) fA fB rfl hAB.symm =
    D.hom (fK ≫ I.f) fK fB rfl hKB.symm
  rw [hbase]
  exact D.hom_comp (fK ≫ I.f) fK fA fB rfl hKA.symm hKB.symm

/-- Source stage 3.13 inverse-realization cocycle after transporting the canonical outer
morphisms to the explicit pullback owners used in the descent-completion construction. -/
theorem projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_comp_forTotalCover
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : Y ⟶ K.Y)
    (A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : Y ⟶ A.Y) (b : Y ⟶ B.Y)
    (hka : k ≫ K.f ≫ I.f = a ≫ A.f)
    (hab : a ≫ A.f = b ≫ B.f) :
    letI := category (J := J) hSheaf
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
        (J := J) hSheaf D I K k A a hka ≫
      projectionDescentExplicitOuterFiberHomForTotalCover
        (J := J) hSheaf D A B a b hab =
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
      (J := J) hSheaf D I K k B b (hka.trans hab) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let eK :=
    projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D I (k ≫ K.f)
  let eA :=
    projectionDescentDatumPullbackIsoCanonicalOriginal
      (J := J) hSheaf D (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
  let eB :=
    projectionDescentDatumPullbackIsoCanonicalOriginal
      (J := J) hSheaf D (projectionDescentTotalCoverOuter (J := J) hSheaf D B)
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b)
  let outerKA := projectionDescentOuterFiberHomFromDatumInnerToTotalCover
    (J := J) hSheaf D I K k A a hka
  let outerAB := projectionDescentOuterFiberHomForTotalCover (J := J) hSheaf D A B a b hab
  let outerKB := projectionDescentOuterFiberHomFromDatumInnerToTotalCover
    (J := J) hSheaf D I K k B b (hka.trans hab)
  have houter : outerKA ≫ outerAB = outerKB := by
    simpa [outerKA, outerAB, outerKB] using
      projectionDescentOuterFiberHomFromDatumInnerToTotalCover_comp_forTotalCover
        (J := J) hSheaf D I K k A B a b hka hab
  have houterF :
      Functor.Fiber.fiberInclusion.map outerKA ≫
          Functor.Fiber.fiberInclusion.map outerAB =
        Functor.Fiber.fiberInclusion.map outerKB := by
    have h := congrArg (fun q => Functor.Fiber.fiberInclusion.map q) houter
    simpa only [Functor.map_comp] using h
  have hcancelF :
      Functor.Fiber.fiberInclusion.map eA.inv ≫
          Functor.Fiber.fiberInclusion.map eA.hom =
        𝟙 _ := by
    have h := congrArg (fun q => Functor.Fiber.fiberInclusion.map q) eA.inv_hom_id
    simpa only [Functor.map_comp, Functor.map_id] using h
  apply Functor.Fiber.hom_ext
  rw [Functor.map_comp]
  dsimp [projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover,
    projectionDescentExplicitOuterFiberHomForTotalCover]
  change (Functor.Fiber.fiberInclusion.map eK.hom ≫
      Functor.Fiber.fiberInclusion.map outerKA ≫
      Functor.Fiber.fiberInclusion.map eA.inv) ≫
      Functor.Fiber.fiberInclusion.map eA.hom ≫
      Functor.Fiber.fiberInclusion.map outerAB ≫
      Functor.Fiber.fiberInclusion.map eB.inv =
    Functor.Fiber.fiberInclusion.map eK.hom ≫
      Functor.Fiber.fiberInclusion.map outerKB ≫
      Functor.Fiber.fiberInclusion.map eB.inv
  let inc : P.Fiber Y ⥤ DescentCompletionObject (J := J) X :=
    Functor.Fiber.fiberInclusion
  calc
    (inc.map eK.hom ≫ inc.map outerKA ≫ inc.map eA.inv) ≫ inc.map eA.hom ≫
        inc.map outerAB ≫ inc.map eB.inv
        = inc.map eK.hom ≫ inc.map outerKA ≫
            (inc.map eA.inv ≫ inc.map eA.hom) ≫ inc.map outerAB ≫ inc.map eB.inv := by
          simp [inc, Category.assoc]
    _ = inc.map eK.hom ≫ inc.map outerKA ≫ 𝟙 _ ≫ inc.map outerAB ≫ inc.map eB.inv := by
          exact congrArg
            (fun q => inc.map eK.hom ≫ inc.map outerKA ≫ q ≫ inc.map outerAB ≫
              inc.map eB.inv)
            hcancelF
    _ = inc.map eK.hom ≫ (inc.map outerKA ≫ inc.map outerAB) ≫ inc.map eB.inv := by
          simp [Category.assoc]
    _ = inc.map eK.hom ≫ inc.map outerKB ≫ inc.map eB.inv := by
          exact congrArg (fun q => inc.map eK.hom ≫ q ≫ inc.map eB.inv) houterF

/-- Source stage 3.13 inverse-realization cocycle on explicit pullback-cover components.

This is the component-level equality for the target-overlap half of the inverse
`Lambda_a^{-1}` compatibility square, before the visible local-restriction owner isomorphisms are
cancelled. -/
theorem projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover_comp_forTotalCover
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : Y ⟶ K.Y)
    (A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : Y ⟶ A.Y) (b : Y ⟶ B.Y)
    (hka : k ≫ K.f ≫ I.f = a ≫ A.f)
    (hab : a ≫ A.f = b ≫ B.f) :
    projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover
        (J := J) hSheaf D I K k A a hka ≫
      projectionDescentTotalCoverExplicitTransitionComponent
        (J := J) hSheaf D A B a b hab =
    projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover
      (J := J) hSheaf D I K k B b (hka.trans hab) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let EK :=
    explicitPullbackFiberObject (J := J) hSheaf
      (projectionDescentDatumObject (J := J) hSheaf D I) (k ≫ K.f)
  let EA :=
    explicitPullbackFiberObject (J := J) hSheaf
      (projectionDescentDatumObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
  let EB :=
    explicitPullbackFiberObject (J := J) hSheaf
      (projectionDescentDatumObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D B))
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b)
  let IK := projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k
  let IA := projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a
  let IB := projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B b
  let α := projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
    (J := J) hSheaf D I K k A a hka
  let β := projectionDescentExplicitOuterFiberHomForTotalCover (J := J) hSheaf D A B a b hab
  let γ := projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
    (J := J) hSheaf D I K k B b (hka.trans hab)
  have hαbase : α.1.base = 𝟙 Y :=
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_base
      (J := J) hSheaf D I K k A a hka
  have hβbase : β.1.base = 𝟙 Y :=
    projectionDescentExplicitOuterFiberHomForTotalCover_base
      (J := J) hSheaf D A B a b hab
  have hγbase : γ.1.base = 𝟙 Y :=
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_base
      (J := J) hSheaf D I K k B b (hka.trans hab)
  let hKA : 𝟙 Y ≫ IK.f ≫ α.1.base = 𝟙 Y ≫ IA.f := by
    rw [hαbase]
    dsimp [IK, IA, projectionDescentDatumExplicitPullbackArrow,
      projectionDescentTotalCoverExplicitPullbackArrow]
    simp
  let hAB : 𝟙 Y ≫ IA.f ≫ β.1.base = 𝟙 Y ≫ IB.f := by
    rw [hβbase]
    dsimp [IA, IB, projectionDescentTotalCoverExplicitPullbackArrow]
    simp
  have hcompComponent :
      α.1.components.toHomOver.family IK IA (𝟙 Y) (𝟙 Y) hKA ≫
          β.1.components.toHomOver.family IA IB (𝟙 Y) (𝟙 Y) hAB =
        (Hom.compose (J := J) hSheaf α.1 β.1).components.toHomOver.family
          IK IB (𝟙 Y) (𝟙 Y)
          (by
            calc
              𝟙 Y ≫ IK.f ≫ (α.1.base ≫ β.1.base) =
                  𝟙 Y ≫ IA.f ≫ β.1.base := by
                    simpa [Category.assoc] using
                      congrArg (fun q => q ≫ β.1.base) hKA
              _ = 𝟙 Y ≫ IB.f := hAB) := by
    exact Hom.compose_component_eq_of_middle (J := J) hSheaf α.1 β.1
      IK IA IB (𝟙 Y) (𝟙 Y) (𝟙 Y) hKA hAB
  have hhom : α ≫ β = γ := by
    simpa [α, β, γ] using
      projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_comp_forTotalCover
        (J := J) hSheaf D I K k A B a b hka hab
  let componentOf (δ : EK ⟶ EB) :
      EK.1.object.restrictedLocalObject IK (𝟙 Y) ⟶
        EB.1.object.restrictedLocalObject IB (𝟙 Y) := by
    letI : P.IsHomLift (𝟙 Y) δ.1 := δ.2
    have hbase : δ.1.base = 𝟙 Y := by
      have hfac := IsHomLift.fac' P (𝟙 Y) δ.1
      simpa [P, projectionFunctor] using hfac
    exact δ.1.components.toHomOver.family IK IB (𝟙 Y) (𝟙 Y) (by
      rw [hbase]
      dsimp [IK, IB, projectionDescentDatumExplicitPullbackArrow,
        projectionDescentTotalCoverExplicitPullbackArrow]
      change 𝟙 Y ≫ 𝟙 Y ≫ 𝟙 Y = 𝟙 Y ≫ 𝟙 Y
      simp)
  have hcomponent := congrArg componentOf hhom
  dsimp [componentOf] at hcomponent
  dsimp [projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover,
    projectionDescentTotalCoverExplicitTransitionComponent]
  have hcomponent' :
      (Hom.compose (J := J) hSheaf α.1 β.1).components.toHomOver.family
          IK IB (𝟙 Y) (𝟙 Y)
          (by
            calc
              𝟙 Y ≫ IK.f ≫ (α.1.base ≫ β.1.base) =
                  𝟙 Y ≫ IA.f ≫ β.1.base := by
                    simpa [Category.assoc] using
                      congrArg (fun q => q ≫ β.1.base) hKA
              _ = 𝟙 Y ≫ IB.f := hAB) =
        γ.1.components.toHomOver.family IK IB (𝟙 Y) (𝟙 Y) (by
          rw [hγbase]
          dsimp [IK, IB, projectionDescentDatumExplicitPullbackArrow,
            projectionDescentTotalCoverExplicitPullbackArrow]
          change 𝟙 Y ≫ 𝟙 Y ≫ 𝟙 Y = 𝟙 Y ≫ 𝟙 Y
          simp) := by
    simpa [P, α, β, γ, EK, EB, IK, IB] using hcomponent
  exact (by
    simpa [α, β, γ, IK, IA, IB] using hcompComponent.trans hcomponent')

/-- Source stage 3.13 inverse-realization cocycle after cancelling the local-restriction owner
isomorphisms.

This is the full target-overlap equality
`rho_(a,i),(b,j) ≫ rho_(b,j),(c,k) = rho_(a,i),(c,k)` for one fixed source
inner owner `(a,i)`. -/
theorem projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover_comp_transition
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : Y ⟶ K.Y)
    (A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : Y ⟶ A.Y) (b : Y ⟶ B.Y)
    (hka : k ≫ K.f ≫ I.f = a ≫ A.f)
    (hab : a ≫ A.f = b ≫ B.f) :
    projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover
        (J := J) hSheaf D I K k A a hka ≫
      projectionDescentTotalCoverTransitionComponent
        (J := J) hSheaf D A B a b hab =
    projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover
      (J := J) hSheaf D I K k B b (hka.trans hab) := by
  dsimp [projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover,
    projectionDescentTotalCoverTransitionComponent]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc]
  rw [Iso.hom_inv_id_assoc]
  simpa [Category.assoc] using
    congrArg
      (fun q =>
        (projectionDescentDatumLocalRestrictionIso (J := J) hSheaf D I K k).hom ≫
          (projectionDescentDatumExplicitPullbackArrowRestrictionIso (J := J)
            hSheaf D I K k).inv ≫
          q ≫
          (projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso (J := J)
            hSheaf D B b).hom ≫
          (projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D B b).inv)
      (projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover_comp_forTotalCover
        (J := J) hSheaf D I K k A B a b hka hab)

/-- The actual inverse component on the pulled-back glued object is definitionally the
lower-level source-text component `rho_(a,i),(b,j)` after translating the pullback-cover owner
back to the total-cover owner. -/
theorem projectionDescentRealizationInverseComponent_eq_fromDatumInnerToTotalCover
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (A : (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f).cover.Arrow)
    {W : C} (k : W ⟶ K.Y) (a : W ⟶ A.Y)
    (h : k ≫ K.f ≫ 𝟙 I.Y = a ≫ A.f) :
    let G :=
      (projectionDescentTotalCoverGluedObjectOfTransitionLaws
        (J := J) hSheaf D hPull hComp).object
    let Atot := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) G I.f A
    let htotal : k ≫ K.f ≫ I.f = a ≫ Atot.f := by
      dsimp [Atot, G, DescentCompletionObjectOver.pullbackCoverBaseArrow]
      calc
        k ≫ K.f ≫ I.f = (k ≫ K.f ≫ 𝟙 I.Y) ≫ I.f := by
          simp [Category.assoc]
        _ = (a ≫ A.f) ≫ I.f := by rw [h]
        _ = a ≫ A.f ≫ I.f := by simp [Category.assoc]
    projectionDescentRealizationInverseComponent (J := J)
        hSheaf D hPull hComp I K A k a h =
      projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover
        (J := J) hSheaf D I K k Atot a htotal := by
  dsimp only
  rfl

/-- Target-overlap for the inverse realization component on the pulled-back glued object.

This is the target half of the compatibility square for `Lambda_a^{-1}`: changing the
total-cover member in `(glued X)|T_a` composes with the same `rho` cocycle. -/
theorem projectionDescentRealizationInverseComponent_targetOverlap_sameSource
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (I : S.Arrow)
    {W : C}
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (A₁ A₂ : (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f).cover.Arrow)
    (k : W ⟶ K.Y)
    (a₁ : W ⟶ A₁.Y) (a₂ : W ⟶ A₂.Y)
    (hA : a₁ ≫ A₁.f = a₂ ≫ A₂.f)
    (h₁ : k ≫ K.f ≫ 𝟙 I.Y = a₁ ≫ A₁.f)
    (h₂ : k ≫ K.f ≫ 𝟙 I.Y = a₂ ≫ A₂.f) :
    let Target :=
      DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f
    projectionDescentRealizationInverseComponent (J := J)
        hSheaf D hPull hComp I K A₁ (W := W) k a₁ h₁ ≫
        (Target.overlapIso a₁ a₂ hA).hom =
      projectionDescentRealizationInverseComponent (J := J)
        hSheaf D hPull hComp I K A₂ (W := W) k a₂ h₂ := by
  dsimp only
  let G :=
    (projectionDescentTotalCoverGluedObjectOfTransitionLaws
      (J := J) hSheaf D hPull hComp).object
  let Atot₁ := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) G I.f A₁
  let Atot₂ := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) G I.f A₂
  let htotalA : a₁ ≫ Atot₁.f = a₂ ≫ Atot₂.f := by
    dsimp [Atot₁, Atot₂, G, DescentCompletionObjectOver.pullbackCoverBaseArrow]
    simpa [Category.assoc] using congrArg (fun q => q ≫ I.f) hA
  let htotal₁ : k ≫ K.f ≫ I.f = a₁ ≫ Atot₁.f := by
    dsimp [Atot₁, G, DescentCompletionObjectOver.pullbackCoverBaseArrow]
    calc
      k ≫ K.f ≫ I.f = (k ≫ K.f ≫ 𝟙 I.Y) ≫ I.f := by
        simp [Category.assoc]
      _ = (a₁ ≫ A₁.f) ≫ I.f := by rw [h₁]
      _ = a₁ ≫ A₁.f ≫ I.f := by simp [Category.assoc]
  let htotal₂ : k ≫ K.f ≫ I.f = a₂ ≫ Atot₂.f := by
    dsimp [Atot₂, G, DescentCompletionObjectOver.pullbackCoverBaseArrow]
    calc
      k ≫ K.f ≫ I.f = (k ≫ K.f ≫ 𝟙 I.Y) ≫ I.f := by
        simp [Category.assoc]
      _ = (a₂ ≫ A₂.f) ≫ I.f := by rw [h₂]
      _ = a₂ ≫ A₂.f ≫ I.f := by simp [Category.assoc]
  have htarget :=
    projectionDescentRealizationSource_overlapIso_hom_eq_transition
      (J := J) hSheaf D hPull hComp I A₁ A₂ a₁ a₂ hA
  have hcomp₁ :=
    projectionDescentRealizationInverseComponent_eq_fromDatumInnerToTotalCover
      (J := J) hSheaf D hPull hComp I K A₁ k a₁ h₁
  have hcomp₂ :=
    projectionDescentRealizationInverseComponent_eq_fromDatumInnerToTotalCover
      (J := J) hSheaf D hPull hComp I K A₂ k a₂ h₂
  rw [hcomp₁, hcomp₂, htarget]
  simpa [G, Atot₁, Atot₂, htotalA, htotal₁, htotal₂] using
    projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover_comp_transition
      (J := J) hSheaf D I K k Atot₁ Atot₂ a₁ a₂ htotal₁ htotalA

/-- Source-base form of the canonical inverse transition used in `Lambda_a^{-1}`.

The source text only depends on the source map `q : W -> T_a`; the cover owner `(K, k)` is used
later to choose a component of the explicit pullback cover. -/
noncomputable def projectionDescentOuterFiberHomFromDatumBaseToTotalCover
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (q : W ⟶ I.Y)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y)
    (h : q ≫ I.f = a ≫ A.f) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    ((canonicalFiberPseudofunctor P).map q.op.toLoc).toFunctor.obj (D.obj I) ⟶
      ((canonicalFiberPseudofunctor P).map
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a).op.toLoc).toFunctor.obj
        (D.obj (projectionDescentTotalCoverOuter (J := J) hSheaf D A)) :=
  projectionDescentOuterFiberHom (J := J) hSheaf D
    I
    (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
    q
    (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
    (by
      calc
        q ≫ I.f = a ≫ A.f := h
        _ =
          projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a ≫
            (projectionDescentTotalCoverOuter (J := J) hSheaf D A).f := by
          have hA :
              a ≫ ((projectionDescentTotalCoverInner (J := J) hSheaf D A).f ≫
                  (projectionDescentTotalCoverOuter (J := J) hSheaf D A).f) =
                a ≫ A.f :=
            congrArg (fun t => a ≫ t)
              (projectionDescentTotalCover_fac (J := J) hSheaf D A)
          simpa [projectionDescentTotalCoverOuterMap, Category.assoc] using hA.symm)

/-- Source-base form of the explicit-owner inverse transition used in `Lambda_a^{-1}`. -/
noncomputable def projectionDescentExplicitOuterFiberHomFromDatumBaseToTotalCover
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (q : W ⟶ I.Y)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y)
    (h : q ≫ I.f = a ≫ A.f) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    explicitPullbackFiberObject (J := J) hSheaf
        (projectionDescentDatumObject (J := J) hSheaf D I) q ⟶
      explicitPullbackFiberObject (J := J) hSheaf
        (projectionDescentDatumObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let eSource := projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D I q
  let eTarget :=
    projectionDescentDatumPullbackIsoCanonicalOriginal
      (J := J) hSheaf D (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
  exact eSource.hom ≫
    projectionDescentOuterFiberHomFromDatumBaseToTotalCover (J := J)
      hSheaf D I q A a h ≫
      eTarget.inv

/-- The owner-indexed inverse explicit transition is the source-base transition specialized to
`q = k ≫ K.f`. -/
theorem projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_eq_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y)
    (h : k ≫ K.f ≫ I.f = a ≫ A.f) :
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
      (J := J) hSheaf D I K k A a h =
    projectionDescentExplicitOuterFiberHomFromDatumBaseToTotalCover
      (J := J) hSheaf D I (k ≫ K.f) A a (by simpa [Category.assoc] using h) := by
  dsimp [projectionDescentExplicitOuterFiberHomFromDatumBaseToTotalCover,
    projectionDescentOuterFiberHomFromDatumBaseToTotalCover,
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover,
    projectionDescentOuterFiberHomFromDatumInnerToTotalCover]

/-- The source-base inverse explicit transition respects equality transport of the source base
map. -/
theorem projectionDescentExplicitOuterFiberHomFromDatumBaseToTotalCover_congr_source
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (q₁ q₂ : W ⟶ I.Y)
    (hq : q₁ = q₂)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y)
    (h₁ : q₁ ≫ I.f = a ≫ A.f)
    (h₂ : q₂ ≫ I.f = a ≫ A.f) :
    let OB := projectionDescentDatumObject (J := J) hSheaf D I
    let eSource : explicitPullbackFiberObject (J := J) hSheaf OB q₁ ≅
        explicitPullbackFiberObject (J := J) hSheaf OB q₂ :=
      eqToIso (congrArg (fun q => explicitPullbackFiberObject (J := J) hSheaf OB q) hq)
    eSource.hom ≫
        projectionDescentExplicitOuterFiberHomFromDatumBaseToTotalCover
          (J := J) hSheaf D I q₂ A a h₂ =
      projectionDescentExplicitOuterFiberHomFromDatumBaseToTotalCover
        (J := J) hSheaf D I q₁ A a h₁ := by
  subst q₂
  have hp : h₁ = h₂ := Subsingleton.elim _ _
  subst hp
  simp

/-- The owner-indexed inverse explicit transition respects equality transport of the source base
map. -/
theorem projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_congr_source
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K₁ K₂ : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k₁ : W ⟶ K₁.Y) (k₂ : W ⟶ K₂.Y)
    (hK : k₁ ≫ K₁.f = k₂ ≫ K₂.f)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y)
    (h₁ : k₁ ≫ K₁.f ≫ I.f = a ≫ A.f)
    (h₂ : k₂ ≫ K₂.f ≫ I.f = a ≫ A.f) :
    let OB := projectionDescentDatumObject (J := J) hSheaf D I
    let eSource : explicitPullbackFiberObject (J := J) hSheaf OB (k₁ ≫ K₁.f) ≅
        explicitPullbackFiberObject (J := J) hSheaf OB (k₂ ≫ K₂.f) :=
      eqToIso (congrArg (fun q => explicitPullbackFiberObject (J := J) hSheaf OB q) hK)
    eSource.hom ≫
        projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
          (J := J) hSheaf D I K₂ k₂ A a h₂ =
      projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
        (J := J) hSheaf D I K₁ k₁ A a h₁ := by
  rw [projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_eq_base]
  rw [projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_eq_base]
  simpa [Category.assoc] using
    projectionDescentExplicitOuterFiberHomFromDatumBaseToTotalCover_congr_source
      (J := J) hSheaf D I (k₁ ≫ K₁.f) (k₂ ≫ K₂.f) hK A a
      (by simpa [Category.assoc] using h₁)
      (by simpa [Category.assoc] using h₂)

/-- Component-level source transport for the source-base inverse explicit outer morphism.

If the source base map is changed only by an equality `q = k ≫ K.f`, the directly rebuilt
component agrees with the component over the transported old pullback-cover arrow after the
visible source overlap in the datum object. -/
def projectionDescentExplicitOuterFiberHomFromDatumBaseToTotalCover_component_congr_source_explicit_law
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (q : W ⟶ I.Y)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y)
    (hq : q = k ≫ K.f)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y)
    (h₁ : q ≫ I.f = a ≫ A.f)
    (h₂ : k ≫ K.f ≫ I.f = a ≫ A.f) : Prop :=
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
    (DB.overlapIso (I₁ := KbaseOld) (I₂ := KbaseDirect)
        (𝟙 W) (𝟙 W) hbase).hom ≫
      (let α :=
        projectionDescentExplicitOuterFiberHomFromDatumBaseToTotalCover
          (J := J) hSheaf D I (k ≫ K.f) A a (by simpa [Category.assoc] using h₂)
      α.1.components.toHomOver.family Kdirect IA (𝟙 W) (𝟙 W)
        (by
          have hα : α.1.base = 𝟙 W := by
            letI := category (J := J) hSheaf
            let P := projectionFunctor (J := J) hSheaf
            haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
            letI : P.IsHomLift (𝟙 W) α.1 := α.2
            have hfac := IsHomLift.fac' P (𝟙 W) α.1
            simpa [P, projectionFunctor] using hfac
          rw [hα]
          dsimp [IA, Kdirect, projectionDescentTotalCoverExplicitPullbackArrow,
            projectionDescentDatumExplicitPullbackArrow]
          change 𝟙 W ≫ 𝟙 W ≫ 𝟙 W = 𝟙 W ≫ 𝟙 W
          simp)) =
      (let α :=
        projectionDescentExplicitOuterFiberHomFromDatumBaseToTotalCover
          (J := J) hSheaf D I q A a h₁
      α.1.components.toHomOver.family Kold IA (𝟙 W) (𝟙 W)
        (by
          have hα : α.1.base = 𝟙 W := by
            letI := category (J := J) hSheaf
            let P := projectionFunctor (J := J) hSheaf
            haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
            letI : P.IsHomLift (𝟙 W) α.1 := α.2
            have hfac := IsHomLift.fac' P (𝟙 W) α.1
            simpa [P, projectionFunctor] using hfac
          rw [hα]
          dsimp [IA, Kold, Kdirect, projectionDescentTotalCoverExplicitPullbackArrow,
            projectionDescentDatumExplicitPullbackArrow, pullbackCoverArrowOfEq]
          change 𝟙 W ≫ 𝟙 W ≫ 𝟙 W = 𝟙 W ≫ 𝟙 W
          simp))

/-- The explicit source-transport component law holds. -/
theorem projectionDescentExplicitOuterFiberHomFromDatumBaseToTotalCover_component_congr_source_explicit
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (q : W ⟶ I.Y)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : W ⟶ K.Y)
    (hq : q = k ≫ K.f)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y)
    (h₁ : q ≫ I.f = a ≫ A.f)
    (h₂ : k ≫ K.f ≫ I.f = a ≫ A.f) :
    projectionDescentExplicitOuterFiberHomFromDatumBaseToTotalCover_component_congr_source_explicit_law
      (J := J) hSheaf D I q K k hq A a h₁ h₂ := by
  subst q
  let h₂base : (k ≫ K.f) ≫ I.f = a ≫ A.f := by
    simpa [Category.assoc] using h₂
  have hp : h₁ = h₂base := Subsingleton.elim _ _
  cases hp
  unfold projectionDescentExplicitOuterFiberHomFromDatumBaseToTotalCover_component_congr_source_explicit_law
  dsimp [pullbackCoverArrowOfEq, projectionDescentDatumExplicitPullbackArrow,
    DescentCompletionObjectOver.pullbackCoverBaseArrow]
  have hp' : h₁ = (by simpa [Category.assoc] using h₂) := Subsingleton.elim _ _
  cases hp'
  rw [DescentCompletionObjectOver.overlapIso_self_hom]
  erw [Category.id_comp]

/-- Source-side component transport for the explicit inverse transition, with the final source
owner rebuilt directly over `k₂ ≫ K₂.f`.

This combines the old-owner compatibility square with the equality-transport comparison of the
explicit pullback source owner. -/
theorem projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover_comp_sourceOverlap
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K₁ K₂ : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k₁ : W ⟶ K₁.Y) (k₂ : W ⟶ K₂.Y)
    (hK : k₁ ≫ K₁.f = k₂ ≫ K₂.f)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y)
    (h₁ : k₁ ≫ K₁.f ≫ I.f = a ≫ A.f)
    (h₂ : k₂ ≫ K₂.f ≫ I.f = a ≫ A.f) :
    let DB := projectionDescentDatumLocalObject (J := J) hSheaf D I
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
    (DB.overlapIso (I₁ := Kbase₁) (I₂ := Kbase₂)
        (𝟙 W) (𝟙 W) hbase₁₂).hom ≫
      projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover
        (J := J) hSheaf D I K₂ k₂ A a h₂ =
    projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover
      (J := J) hSheaf D I K₁ k₁ A a h₁ := by
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
  let α₁ := projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
    (J := J) hSheaf D I K₁ k₁ A a h₁
  let α₂ := projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover
    (J := J) hSheaf D I K₂ k₂ A a h₂
  have hα₁ : α₁.1.base = 𝟙 W :=
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_base
      (J := J) hSheaf D I K₁ k₁ A a h₁
  have hα₂ : α₂.1.base = 𝟙 W :=
    projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_base
      (J := J) hSheaf D I K₂ k₂ A a h₂
  let mid₁ := α₁.1.components.toHomOver.family Karr₁ IA (𝟙 W) (𝟙 W)
    (by
      rw [hα₁]
      dsimp [IA, Karr₁, projectionDescentTotalCoverExplicitPullbackArrow,
        projectionDescentDatumExplicitPullbackArrow]
      change 𝟙 W ≫ 𝟙 W ≫ 𝟙 W = 𝟙 W ≫ 𝟙 W
      simp)
  let midOld := α₁.1.components.toHomOver.family Karr₂old IA (𝟙 W) (𝟙 W)
    (by
      rw [hα₁]
      dsimp [IA, Karr₂old, projectionDescentTotalCoverExplicitPullbackArrow]
      change 𝟙 W ≫ 𝟙 W ≫ 𝟙 W = 𝟙 W ≫ 𝟙 W
      simp)
  let mid₂ := α₂.1.components.toHomOver.family Karr₂ IA (𝟙 W) (𝟙 W)
    (by
      rw [hα₂]
      dsimp [IA, Karr₂, projectionDescentTotalCoverExplicitPullbackArrow,
        projectionDescentDatumExplicitPullbackArrow]
      change 𝟙 W ≫ 𝟙 W ≫ 𝟙 W = 𝟙 W ≫ 𝟙 W
      simp)
  let oldOverlap :=
    (DB.overlapIso (I₁ := Kbase₁) (I₂ := Kbase₂old)
      (𝟙 W) (𝟙 W) hbase₁₂old).hom
  let bridgeOverlap :=
    (DB.overlapIso (I₁ := Kbase₂old) (I₂ := Kbase₂)
      (𝟙 W) (𝟙 W) hbaseOld₂).hom
  let directOverlap :=
    (DB.overlapIso (I₁ := Kbase₁) (I₂ := Kbase₂)
      (𝟙 W) (𝟙 W) hbase₁₂).hom
  let hSrc : 𝟙 W ≫ Karr₁.f = 𝟙 W ≫ Karr₂old.f := by rfl
  let hTgt : 𝟙 W ≫ IA.f = 𝟙 W ≫ IA.f := rfl
  have hcompat :=
    α₁.1.components.toHomOver.compatible Karr₁ Karr₂old IA IA
      (𝟙 W) (𝟙 W) (𝟙 W) (𝟙 W)
      hSrc hTgt
      (by
        rw [hα₁]
        dsimp [IA, Karr₁, projectionDescentTotalCoverExplicitPullbackArrow,
          projectionDescentDatumExplicitPullbackArrow]
        change 𝟙 W ≫ 𝟙 W ≫ 𝟙 W = 𝟙 W ≫ 𝟙 W
        simp)
      (by
        rw [hα₁]
        dsimp [IA, Karr₂old, projectionDescentTotalCoverExplicitPullbackArrow]
        change 𝟙 W ≫ 𝟙 W ≫ 𝟙 W = 𝟙 W ≫ 𝟙 W
        simp)
  rw [DescentCompletionObjectOver.overlapIso_self_hom] at hcompat
  have hpullOverlap :
      ((DescentCompletionObjectOver.pullback (J := J) DB (k₁ ≫ K₁.f)).overlapIso
          (I₁ := Karr₁) (I₂ := Karr₂old) (𝟙 W) (𝟙 W) hSrc).hom =
        oldOverlap := by
    simpa [oldOverlap, Kbase₁, Kbase₂old, hbase₁₂old, Karr₁, Karr₂old] using
      DescentCompletionObjectOver.pullback_overlapIso_hom (J := J) DB (k₁ ≫ K₁.f)
        Karr₁ Karr₂old (𝟙 W) (𝟙 W) hSrc
  have hold : oldOverlap ≫ midOld = mid₁ := by
    rw [← hpullOverlap]
    simpa [mid₁, midOld, α₁, hα₁, IA, Karr₁, Karr₂old, hSrc, hTgt] using hcompat
  have htransport : bridgeOverlap ≫ mid₂ = midOld := by
    simpa [midOld, mid₂, bridgeOverlap, α₁, α₂, DB, IA, Karr₂old, Karr₂,
      Kbase₂old, Kbase₂, hbaseOld₂,
      projectionDescentExplicitOuterFiberHomFromDatumInnerToTotalCover_eq_base]
      using
        projectionDescentExplicitOuterFiberHomFromDatumBaseToTotalCover_component_congr_source_explicit
          (J := J) hSheaf D I (k₁ ≫ K₁.f) K₂ k₂ hK A a
          (by simpa [Category.assoc] using h₁) h₂
  have hover :=
    DescentCompletionObjectOver.overlapIso_hom_comp (J := J) DB
      (I₁ := Kbase₁) (I₂ := Kbase₂old) (I₃ := Kbase₂)
      (𝟙 W) (𝟙 W) (𝟙 W) hbase₁₂old hbaseOld₂
  have hover' : oldOverlap ≫ bridgeOverlap = directOverlap := by
    simpa [oldOverlap, bridgeOverlap, directOverlap, hbase₁₂] using hover
  change directOverlap ≫ mid₂ = mid₁
  rw [← hover']
  calc
    (oldOverlap ≫ bridgeOverlap) ≫ mid₂ =
        oldOverlap ≫ (bridgeOverlap ≫ mid₂) := by rw [Category.assoc]
    _ = oldOverlap ≫ midOld := congrArg (fun q => oldOverlap ≫ q) htransport
    _ = mid₁ := hold

/-- Source-overlap for the source-text inverse component, after cancelling the visible
local-restriction owner isomorphisms.

This is the source half of the compatibility square for `Lambda_a^{-1}`:
changing the source inner owner `(a,i)` does not change the component
`rho_(a,i),(b,j)` except by the source overlap map. -/
theorem projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover_sourceOverlap
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I : S.Arrow)
    (K₁ K₂ : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k₁ : W ⟶ K₁.Y) (k₂ : W ⟶ K₂.Y)
    (hK : k₁ ≫ K₁.f = k₂ ≫ K₂.f)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y)
    (h₁ : k₁ ≫ K₁.f ≫ I.f = a ≫ A.f)
    (h₂ : k₂ ≫ K₂.f ≫ I.f = a ≫ A.f) :
    let Source := projectionDescentDatumLocalObject (J := J) hSheaf D I
    (Source.overlapIso k₁ k₂ hK).hom ≫
        projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover
          (J := J) hSheaf D I K₂ k₂ A a h₂ =
      projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover
        (J := J) hSheaf D I K₁ k₁ A a h₁ := by
  dsimp only
  let Source := projectionDescentDatumLocalObject (J := J) hSheaf D I
  let Karr₁ := projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K₁ k₁
  let Karr₂ := projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K₂ k₂
  let Kbase₁ := DescentCompletionObjectOver.pullbackCoverBaseArrow
    (J := J) Source (k₁ ≫ K₁.f) Karr₁
  let Kbase₂ := DescentCompletionObjectOver.pullbackCoverBaseArrow
    (J := J) Source (k₂ ≫ K₂.f) Karr₂
  let Kref₁ := projectionDescentDatumRefinedInner (J := J) hSheaf D I K₁ k₁
  let Kref₂ := projectionDescentDatumRefinedInner (J := J) hSheaf D I K₂ k₂
  let hK₁ref : k₁ ≫ K₁.f = 𝟙 W ≫ Kref₁.f := by
    dsimp [Kref₁, projectionDescentDatumRefinedInner]
    simp
  let hK₂ref : k₂ ≫ K₂.f = 𝟙 W ≫ Kref₂.f := by
    dsimp [Kref₂, projectionDescentDatumRefinedInner]
    simp
  let href₁base : 𝟙 W ≫ Kref₁.f = 𝟙 W ≫ Kbase₁.f := by
    dsimp [Kref₁, Kbase₁, Karr₁, Source, projectionDescentDatumRefinedInner,
      projectionDescentDatumExplicitPullbackArrow,
      DescentCompletionObjectOver.pullbackCoverBaseArrow]
    simp
  let href₂base : 𝟙 W ≫ Kref₂.f = 𝟙 W ≫ Kbase₂.f := by
    dsimp [Kref₂, Kbase₂, Karr₂, Source, projectionDescentDatumRefinedInner,
      projectionDescentDatumExplicitPullbackArrow,
      DescentCompletionObjectOver.pullbackCoverBaseArrow]
    simp
  let hbase₁₂ : 𝟙 W ≫ Kbase₁.f = 𝟙 W ≫ Kbase₂.f :=
    href₁base.symm.trans (hK₁ref.symm.trans (hK.trans (hK₂ref.trans href₂base)))
  let sourceOverlap := (Source.overlapIso (I₁ := K₁) (I₂ := K₂) k₁ k₂ hK).hom
  let l₁ := (projectionDescentDatumLocalRestrictionIso (J := J) hSheaf D I K₁ k₁).hom
  let l₂ := (projectionDescentDatumLocalRestrictionIso (J := J) hSheaf D I K₂ k₂).hom
  let e₁ := (projectionDescentDatumExplicitPullbackArrowRestrictionIso
    (J := J) hSheaf D I K₁ k₁).inv
  let e₂ := (projectionDescentDatumExplicitPullbackArrowRestrictionIso
    (J := J) hSheaf D I K₂ k₂).inv
  let baseOverlap :=
    (Source.overlapIso (I₁ := Kbase₁) (I₂ := Kbase₂)
      (𝟙 W) (𝟙 W) hbase₁₂).hom
  have hsource_ref₂ :=
    DescentCompletionObjectOver.overlapIso_hom_comp (J := J) Source
      (I₁ := K₁) (I₂ := K₂) (I₃ := Kref₂)
      k₁ k₂ (𝟙 W) hK hK₂ref
  have hsource_ref₂' : sourceOverlap ≫ l₂ =
      (Source.overlapIso (I₁ := K₁) (I₂ := Kref₂)
        k₁ (𝟙 W) (hK.trans hK₂ref)).hom := by
    simpa [sourceOverlap, l₂, projectionDescentDatumLocalRestrictionIso, Kref₂] using
      hsource_ref₂
  have hsource_ref_base₂ :=
    DescentCompletionObjectOver.overlapIso_hom_comp (J := J) Source
      (I₁ := K₁) (I₂ := Kref₂) (I₃ := Kbase₂)
      k₁ (𝟙 W) (𝟙 W) (hK.trans hK₂ref) href₂base
  have hsource_base₂ : (sourceOverlap ≫ l₂) ≫ e₂ =
      (Source.overlapIso (I₁ := K₁) (I₂ := Kbase₂)
        k₁ (𝟙 W) ((hK.trans hK₂ref).trans href₂base)).hom := by
    rw [hsource_ref₂']
    dsimp [e₂, projectionDescentDatumExplicitPullbackArrowRestrictionIso, Kref₂, Kbase₂, Karr₂]
    rw [DescentCompletionObjectOver.overlapIso_inv]
    simpa [Category.assoc] using hsource_ref_base₂
  have hl₁_base₁ :=
    DescentCompletionObjectOver.overlapIso_hom_comp (J := J) Source
      (I₁ := K₁) (I₂ := Kref₁) (I₃ := Kbase₁)
      k₁ (𝟙 W) (𝟙 W) hK₁ref href₁base
  have hl₁e₁ : l₁ ≫ e₁ =
      (Source.overlapIso (I₁ := K₁) (I₂ := Kbase₁)
        k₁ (𝟙 W) (hK₁ref.trans href₁base)).hom := by
    dsimp [l₁, e₁, projectionDescentDatumLocalRestrictionIso,
      projectionDescentDatumExplicitPullbackArrowRestrictionIso, Kref₁, Kbase₁, Karr₁]
    rw [DescentCompletionObjectOver.overlapIso_inv]
    simpa [Category.assoc] using hl₁_base₁
  have hbase_comp :=
    DescentCompletionObjectOver.overlapIso_hom_comp (J := J) Source
      (I₁ := K₁) (I₂ := Kbase₁) (I₃ := Kbase₂)
      k₁ (𝟙 W) (𝟙 W) (hK₁ref.trans href₁base) hbase₁₂
  have hleft : sourceOverlap ≫ l₂ ≫ e₂ = l₁ ≫ e₁ ≫ baseOverlap := by
    calc
      sourceOverlap ≫ l₂ ≫ e₂ = (sourceOverlap ≫ l₂) ≫ e₂ := by simp [Category.assoc]
      _ = (Source.overlapIso (I₁ := K₁) (I₂ := Kbase₂)
            k₁ (𝟙 W) ((hK.trans hK₂ref).trans href₂base)).hom := hsource_base₂
      _ = (Source.overlapIso (I₁ := K₁) (I₂ := Kbase₁)
            k₁ (𝟙 W) (hK₁ref.trans href₁base)).hom ≫ baseOverlap := by
          simpa [baseOverlap, hbase₁₂] using hbase_comp.symm
      _ = l₁ ≫ e₁ ≫ baseOverlap := by
          simpa [Category.assoc] using congrArg (fun q => q ≫ baseOverlap) hl₁e₁.symm
  have hmid :=
    projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover_comp_sourceOverlap
      (J := J) hSheaf D I K₁ K₂ k₁ k₂ hK A a h₁ h₂
  dsimp [projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover]
  let mid₁ := projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover
    (J := J) hSheaf D I K₁ k₁ A a h₁
  let mid₂ := projectionDescentExplicitTransitionComponentFromDatumInnerToTotalCover
    (J := J) hSheaf D I K₂ k₂ A a h₂
  let t₁ := (projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso
    (J := J) hSheaf D A a).hom
  let t₂ := (projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D A a).inv
  change sourceOverlap ≫ l₂ ≫ e₂ ≫ mid₂ ≫ t₁ ≫ t₂ =
      l₁ ≫ e₁ ≫ mid₁ ≫ t₁ ≫ t₂
  calc
    sourceOverlap ≫ l₂ ≫ e₂ ≫ mid₂ ≫ t₁ ≫ t₂ =
        (l₁ ≫ e₁ ≫ baseOverlap) ≫ mid₂ ≫ t₁ ≫ t₂ := by
        simpa [Category.assoc] using
          congrArg (fun q => q ≫ mid₂ ≫ t₁ ≫ t₂) hleft
    _ = l₁ ≫ e₁ ≫ (baseOverlap ≫ mid₂) ≫ t₁ ≫ t₂ := by
        simp [Category.assoc]
    _ = l₁ ≫ e₁ ≫ mid₁ ≫ t₁ ≫ t₂ := by
        exact congrArg
          (fun q => l₁ ≫ e₁ ≫ q ≫ t₁ ≫ t₂)
          (by simpa [mid₁, mid₂, baseOverlap] using hmid)

/-- Source-overlap for the inverse realization component on the pulled-back glued object.

This is the source half of the compatibility square for `Lambda_a^{-1}`: changing the
source member of `X_a` composes with the same source descent transition. -/
theorem projectionDescentRealizationInverseComponent_sourceOverlap_sameTarget
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (I : S.Arrow)
    {W : C}
    (K₁ K₂ : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (A : (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentTotalCoverGluedObjectOfTransitionLaws
          (J := J) hSheaf D hPull hComp).object I.f).cover.Arrow)
    (k₁ : W ⟶ K₁.Y) (k₂ : W ⟶ K₂.Y)
    (a : W ⟶ A.Y)
    (hK : k₁ ≫ K₁.f = k₂ ≫ K₂.f)
    (h₁ : k₁ ≫ K₁.f ≫ 𝟙 I.Y = a ≫ A.f)
    (h₂ : k₂ ≫ K₂.f ≫ 𝟙 I.Y = a ≫ A.f) :
    let Source := projectionDescentDatumLocalObject (J := J) hSheaf D I
    (Source.overlapIso k₁ k₂ hK).hom ≫
        projectionDescentRealizationInverseComponent (J := J)
          hSheaf D hPull hComp I K₂ A (W := W) k₂ a h₂ =
      projectionDescentRealizationInverseComponent (J := J)
        hSheaf D hPull hComp I K₁ A (W := W) k₁ a h₁ := by
  dsimp only
  let G :=
    (projectionDescentTotalCoverGluedObjectOfTransitionLaws
      (J := J) hSheaf D hPull hComp).object
  let Atot := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) G I.f A
  let htotal₁ : k₁ ≫ K₁.f ≫ I.f = a ≫ Atot.f := by
    dsimp [Atot, G, DescentCompletionObjectOver.pullbackCoverBaseArrow]
    calc
      k₁ ≫ K₁.f ≫ I.f = (k₁ ≫ K₁.f ≫ 𝟙 I.Y) ≫ I.f := by
        simp [Category.assoc]
      _ = (a ≫ A.f) ≫ I.f := by rw [h₁]
      _ = a ≫ A.f ≫ I.f := by simp [Category.assoc]
  let htotal₂ : k₂ ≫ K₂.f ≫ I.f = a ≫ Atot.f := by
    dsimp [Atot, G, DescentCompletionObjectOver.pullbackCoverBaseArrow]
    calc
      k₂ ≫ K₂.f ≫ I.f = (k₂ ≫ K₂.f ≫ 𝟙 I.Y) ≫ I.f := by
        simp [Category.assoc]
      _ = (a ≫ A.f) ≫ I.f := by rw [h₂]
      _ = a ≫ A.f ≫ I.f := by simp [Category.assoc]
  have hcomp₁ :=
    projectionDescentRealizationInverseComponent_eq_fromDatumInnerToTotalCover
      (J := J) hSheaf D hPull hComp I K₁ A k₁ a h₁
  have hcomp₂ :=
    projectionDescentRealizationInverseComponent_eq_fromDatumInnerToTotalCover
      (J := J) hSheaf D hPull hComp I K₂ A k₂ a h₂
  rw [hcomp₁, hcomp₂]
  simpa [G, Atot, htotal₁, htotal₂] using
    projectionDescentRealizationInverseComponentFromDatumInnerToTotalCover_sourceOverlap
      (J := J) hSheaf D I K₁ K₂ k₁ k₂ hK Atot a htotal₁ htotal₂

/-- Source-text compatibility square for the inverse local realization component `Lambda_a^{-1}`.

This combines the source-overlap and target-overlap halves of the componentwise inverse
compatibility for the maps `rho_(a,i),(b,j)`. -/
theorem projectionDescentRealizationInverseComponent_compatible
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (hPull : projectionDescentTotalCoverTransitionComponentPullHomLaw (J := J) hSheaf D)
    (hComp : projectionDescentTotalCoverTransitionComponentHomCompLaw (J := J) hSheaf D)
    (I : S.Arrow) :
    projectionDescentRealizationInverseComponentCompatibleLaw
      (J := J) hSheaf D hPull hComp I := by
  dsimp [projectionDescentRealizationInverseComponentCompatibleLaw]
  intro W K₁ K₂ A₁ A₂ k₁ k₂ a₁ a₂ hK hA h₁ h₂
  let Source := projectionDescentDatumLocalObject (J := J) hSheaf D I
  let Target :=
    DescentCompletionObjectOver.pullback (J := J)
      (projectionDescentTotalCoverGluedObjectOfTransitionLaws
        (J := J) hSheaf D hPull hComp).object I.f
  let h₁A₂ : k₁ ≫ K₁.f ≫ 𝟙 I.Y = a₂ ≫ A₂.f := by
    calc
      k₁ ≫ K₁.f ≫ 𝟙 I.Y = k₂ ≫ K₂.f ≫ 𝟙 I.Y := by
        simpa [Category.assoc] using congrArg (fun q => q ≫ 𝟙 I.Y) hK
      _ = a₂ ≫ A₂.f := h₂
  have hsource :=
    projectionDescentRealizationInverseComponent_sourceOverlap_sameTarget
      (J := J) hSheaf D hPull hComp I K₁ K₂ A₂ k₁ k₂ a₂ hK h₁A₂ h₂
  have htarget :=
    projectionDescentRealizationInverseComponent_targetOverlap_sameSource
      (J := J) hSheaf D hPull hComp I K₁ A₁ A₂ k₁ a₁ a₂ hA h₁ h₁A₂
  dsimp [Source, Target] at hsource htarget
  calc
    (Source.overlapIso k₁ k₂ hK).hom ≫
        projectionDescentRealizationInverseComponent (J := J)
          hSheaf D hPull hComp I K₂ A₂ (W := W) k₂ a₂ h₂ =
      projectionDescentRealizationInverseComponent (J := J)
        hSheaf D hPull hComp I K₁ A₂ (W := W) k₁ a₂ h₁A₂ := hsource
    _ =
      projectionDescentRealizationInverseComponent (J := J)
          hSheaf D hPull hComp I K₁ A₁ (W := W) k₁ a₁ h₁ ≫
        (Target.overlapIso a₁ a₂ hA).hom := htarget.symm

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
