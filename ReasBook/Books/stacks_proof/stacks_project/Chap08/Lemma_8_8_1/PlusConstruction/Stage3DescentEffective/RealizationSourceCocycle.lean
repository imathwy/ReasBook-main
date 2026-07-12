import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.RealizationComponent
import StacksProject_2024.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.TransitionHomCompReduction

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

/-- Source stage 3.13 realization cocycle, canonical-owner form.

This is the source-side half of the compatibility of
`Lambda_a : X|T_a -> X_a`: composing a total-cover transition
`rho_(A,B)` with the realization component `rho_(B,(a,i))` is the realization component
`rho_(A,(a,i))`.  The proof is exactly the outer descent datum cocycle for `Theta`, with the
target kept as the explicit source-text owner `(a,i)` rather than rebuilt through `Cover.bind`. -/
theorem projectionDescentOuterFiberHomForTotalCover_comp_fromTotalCoverToDatumInner
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (a : Y ⟶ A.Y) (b : Y ⟶ B.Y)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : Y ⟶ K.Y)
    (hab : a ≫ A.f = b ≫ B.f) (hbk : b ≫ B.f = k ≫ K.f ≫ I.f) :
    letI := category (J := J) hSheaf
    projectionDescentOuterFiberHomForTotalCover (J := J) hSheaf D A B a b hab ≫
      projectionDescentOuterFiberHomFromTotalCoverToDatumInner (J := J)
        hSheaf D B I b K k hbk =
    projectionDescentOuterFiberHomFromTotalCoverToDatumInner (J := J)
      hSheaf D A I a K k (hab.trans hbk) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let IA := projectionDescentTotalCoverOuter (J := J) hSheaf D A
  let IB := projectionDescentTotalCoverOuter (J := J) hSheaf D B
  let fA := projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a
  let fB := projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b
  let fK := k ≫ K.f
  let hAB : fA ≫ IA.f = fB ≫ IB.f :=
    projectionDescentTotalCoverOuterMap_fac (J := J) hSheaf D A B a b hab
  let hBK : fB ≫ IB.f = fK ≫ I.f := by
    calc
      fB ≫ IB.f = b ≫ B.f := by
        have hB :
            b ≫ ((projectionDescentTotalCoverInner (J := J) hSheaf D B).f ≫
                (projectionDescentTotalCoverOuter (J := J) hSheaf D B).f) =
              b ≫ B.f :=
          congrArg (fun q => b ≫ q)
            (projectionDescentTotalCover_fac (J := J) hSheaf D B)
        simpa [fB, IB, projectionDescentTotalCoverOuterMap, Category.assoc] using hB
      _ = fK ≫ I.f := by simpa [fK, Category.assoc] using hbk
  let hAK : fA ≫ IA.f = fK ≫ I.f := hAB.trans hBK
  have hbase :
      D.hom (fB ≫ IB.f) fB fK rfl hBK.symm =
        D.hom (fA ≫ IA.f) fB fK hAB.symm hAK.symm := by
    exact
      projectionDescentDatumHom_congr_base (J := J) hSheaf D hAB.symm
        fB fK rfl hBK.symm hAB.symm hAK.symm
  dsimp [projectionDescentOuterFiberHomForTotalCover,
    projectionDescentOuterFiberHomFromTotalCoverToDatumInner, projectionDescentOuterFiberHom]
  change D.hom (fA ≫ IA.f) fA fB rfl hAB.symm ≫
      D.hom (fB ≫ IB.f) fB fK rfl hBK.symm =
    D.hom (fA ≫ IA.f) fA fK rfl hAK.symm
  rw [hbase]
  exact D.hom_comp (fA ≫ IA.f) fA fB fK rfl hAB.symm hAK.symm

/-- Source stage 3.13 realization cocycle after transporting the canonical outer morphisms to
the explicit pullback owners used by the descent-completion construction. -/
theorem projectionDescentExplicitOuterFiberHomForTotalCover_comp_fromTotalCoverToDatumInner
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (a : Y ⟶ A.Y) (b : Y ⟶ B.Y)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : Y ⟶ K.Y)
    (hab : a ≫ A.f = b ≫ B.f) (hbk : b ≫ B.f = k ≫ K.f ≫ I.f) :
    letI := category (J := J) hSheaf
    projectionDescentExplicitOuterFiberHomForTotalCover (J := J) hSheaf D A B a b hab ≫
      projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
        (J := J) hSheaf D B I b K k hbk =
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
      (J := J) hSheaf D A I a K k (hab.trans hbk) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let eA : explicitPullbackFiberObject (J := J) hSheaf
      (projectionDescentDatumObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a) ≅
    (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a) ^*[
        canonicalPullbackChoice P]
      D.obj (projectionDescentTotalCoverOuter (J := J) hSheaf D A) :=
    projectionDescentDatumPullbackIsoCanonicalOriginal
      (J := J) hSheaf D (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
  let eB : explicitPullbackFiberObject (J := J) hSheaf
      (projectionDescentDatumObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D B))
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b) ≅
    (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b) ^*[
        canonicalPullbackChoice P]
      D.obj (projectionDescentTotalCoverOuter (J := J) hSheaf D B) :=
    projectionDescentDatumPullbackIsoCanonicalOriginal
      (J := J) hSheaf D (projectionDescentTotalCoverOuter (J := J) hSheaf D B)
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b)
  let eK : explicitPullbackFiberObject (J := J) hSheaf
      (projectionDescentDatumObject (J := J) hSheaf D I) (k ≫ K.f) ≅
    (k ≫ K.f) ^*[canonicalPullbackChoice P] D.obj I :=
    projectionDescentDatumPullbackIsoCanonicalOriginal (J := J) hSheaf D I (k ≫ K.f)
  let outerAB := projectionDescentOuterFiberHomForTotalCover (J := J) hSheaf D A B a b hab
  let outerBK := projectionDescentOuterFiberHomFromTotalCoverToDatumInner
    (J := J) hSheaf D B I b K k hbk
  let outerAK := projectionDescentOuterFiberHomFromTotalCoverToDatumInner
    (J := J) hSheaf D A I a K k (hab.trans hbk)
  have houter : outerAB ≫ outerBK = outerAK := by
    simpa [outerAB, outerBK, outerAK] using
      projectionDescentOuterFiberHomForTotalCover_comp_fromTotalCoverToDatumInner
        (J := J) hSheaf D A B I a b K k hab hbk
  have houterF :
      Functor.Fiber.fiberInclusion.map outerAB ≫
          Functor.Fiber.fiberInclusion.map outerBK =
        Functor.Fiber.fiberInclusion.map outerAK := by
    have h := congrArg (fun q => Functor.Fiber.fiberInclusion.map q) houter
    simpa only [Functor.map_comp] using h
  have hcancelF :
      Functor.Fiber.fiberInclusion.map eB.inv ≫
          Functor.Fiber.fiberInclusion.map eB.hom =
        𝟙 _ := by
    have h := congrArg (fun q => Functor.Fiber.fiberInclusion.map q) eB.inv_hom_id
    simpa only [Functor.map_comp, Functor.map_id] using h
  apply Functor.Fiber.hom_ext
  rw [Functor.map_comp]
  dsimp [projectionDescentExplicitOuterFiberHomForTotalCover,
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner]
  change (Functor.Fiber.fiberInclusion.map eA.hom ≫
      Functor.Fiber.fiberInclusion.map outerAB ≫
      Functor.Fiber.fiberInclusion.map eB.inv) ≫
      Functor.Fiber.fiberInclusion.map eB.hom ≫
      Functor.Fiber.fiberInclusion.map outerBK ≫
      Functor.Fiber.fiberInclusion.map eK.inv =
    Functor.Fiber.fiberInclusion.map eA.hom ≫
      Functor.Fiber.fiberInclusion.map outerAK ≫
      Functor.Fiber.fiberInclusion.map eK.inv
  let inc : P.Fiber Y ⥤ DescentCompletionObject (J := J) X :=
    Functor.Fiber.fiberInclusion
  calc
    (inc.map eA.hom ≫ inc.map outerAB ≫ inc.map eB.inv) ≫ inc.map eB.hom ≫
        inc.map outerBK ≫ inc.map eK.inv
        = inc.map eA.hom ≫ inc.map outerAB ≫
            (inc.map eB.inv ≫ inc.map eB.hom) ≫ inc.map outerBK ≫ inc.map eK.inv := by
          simp [inc, Category.assoc]
    _ = inc.map eA.hom ≫ inc.map outerAB ≫ 𝟙 _ ≫ inc.map outerBK ≫ inc.map eK.inv := by
          exact congrArg
            (fun q => inc.map eA.hom ≫ inc.map outerAB ≫ q ≫ inc.map outerBK ≫
              inc.map eK.inv)
            hcancelF
    _ = inc.map eA.hom ≫ (inc.map outerAB ≫ inc.map outerBK) ≫ inc.map eK.inv := by
          simp [Category.assoc]
    _ = inc.map eA.hom ≫ inc.map outerAK ≫ inc.map eK.inv := by
          exact congrArg (fun q => inc.map eA.hom ≫ q ≫ inc.map eK.inv) houterF

/-- Source stage 3.13 realization cocycle on explicit pullback-cover components.

This is the component-level equality needed on the left side of the future
`Lambda_a` compatibility proof, before the outer source/target local-restriction isomorphisms are
cancelled. -/
theorem projectionDescentExplicitTransitionComponent_comp_fromTotalCoverToDatumInner
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (a : Y ⟶ A.Y) (b : Y ⟶ B.Y)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : Y ⟶ K.Y)
    (hab : a ≫ A.f = b ≫ B.f) (hbk : b ≫ B.f = k ≫ K.f ≫ I.f) :
    projectionDescentTotalCoverExplicitTransitionComponent
        (J := J) hSheaf D A B a b hab ≫
      projectionDescentExplicitTransitionComponentFromTotalCoverToDatumInner
        (J := J) hSheaf D B I b K k hbk =
    projectionDescentExplicitTransitionComponentFromTotalCoverToDatumInner
      (J := J) hSheaf D A I a K k (hab.trans hbk) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
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
  let EK :=
    explicitPullbackFiberObject (J := J) hSheaf
      (projectionDescentDatumObject (J := J) hSheaf D I) (k ≫ K.f)
  let IA := projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a
  let IB := projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B b
  let IK := projectionDescentDatumExplicitPullbackArrow (J := J) hSheaf D I K k
  let α := projectionDescentExplicitOuterFiberHomForTotalCover (J := J) hSheaf D A B a b hab
  let β := projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
    (J := J) hSheaf D B I b K k hbk
  let γ := projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner
    (J := J) hSheaf D A I a K k (hab.trans hbk)
  have hαbase : α.1.base = 𝟙 Y :=
    projectionDescentExplicitOuterFiberHomForTotalCover_base
      (J := J) hSheaf D A B a b hab
  have hβbase : β.1.base = 𝟙 Y :=
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
      (J := J) hSheaf D B I b K k hbk
  have hγbase : γ.1.base = 𝟙 Y :=
    projectionDescentExplicitOuterFiberHomFromTotalCoverToDatumInner_base
      (J := J) hSheaf D A I a K k (hab.trans hbk)
  let hAB : 𝟙 Y ≫ IA.f ≫ α.1.base = 𝟙 Y ≫ IB.f := by
    rw [hαbase]
    dsimp [IA, IB, projectionDescentTotalCoverExplicitPullbackArrow]
    simp
  let hBK : 𝟙 Y ≫ IB.f ≫ β.1.base = 𝟙 Y ≫ IK.f := by
    rw [hβbase]
    dsimp [IB, IK, projectionDescentTotalCoverExplicitPullbackArrow,
      projectionDescentDatumExplicitPullbackArrow]
    simp
  have hcompComponent :
      α.1.components.toHomOver.family IA IB (𝟙 Y) (𝟙 Y) hAB ≫
          β.1.components.toHomOver.family IB IK (𝟙 Y) (𝟙 Y) hBK =
        (Hom.compose (J := J) hSheaf α.1 β.1).components.toHomOver.family
          IA IK (𝟙 Y) (𝟙 Y)
          (by
            calc
              𝟙 Y ≫ IA.f ≫ (α.1.base ≫ β.1.base) =
                  𝟙 Y ≫ IB.f ≫ β.1.base := by
                    simpa [Category.assoc] using
                      congrArg (fun q => q ≫ β.1.base) hAB
              _ = 𝟙 Y ≫ IK.f := hBK) := by
    exact Hom.compose_component_eq_of_middle (J := J) hSheaf α.1 β.1
      IA IB IK (𝟙 Y) (𝟙 Y) (𝟙 Y) hAB hBK
  have hhom : α ≫ β = γ := by
    simpa [α, β, γ] using
      projectionDescentExplicitOuterFiberHomForTotalCover_comp_fromTotalCoverToDatumInner
        (J := J) hSheaf D A B I a b K k hab hbk
  let componentOf (δ : EA ⟶ EK) :
      EA.1.object.restrictedLocalObject IA (𝟙 Y) ⟶
        EK.1.object.restrictedLocalObject IK (𝟙 Y) := by
    letI : P.IsHomLift (𝟙 Y) δ.1 := δ.2
    have hbase : δ.1.base = 𝟙 Y := by
      have hfac := IsHomLift.fac' P (𝟙 Y) δ.1
      simpa [P, projectionFunctor] using hfac
    exact δ.1.components.toHomOver.family IA IK (𝟙 Y) (𝟙 Y) (by
      rw [hbase]
      dsimp [IA, IK, projectionDescentTotalCoverExplicitPullbackArrow,
        projectionDescentDatumExplicitPullbackArrow]
      change 𝟙 Y ≫ 𝟙 Y ≫ 𝟙 Y = 𝟙 Y ≫ 𝟙 Y
      simp)
  have hcomponent := congrArg componentOf hhom
  dsimp [componentOf] at hcomponent
  dsimp [projectionDescentTotalCoverExplicitTransitionComponent,
    projectionDescentExplicitTransitionComponentFromTotalCoverToDatumInner]
  have hcomponent' :
      (Hom.compose (J := J) hSheaf α.1 β.1).components.toHomOver.family
          IA IK (𝟙 Y) (𝟙 Y)
          (by
            calc
              𝟙 Y ≫ IA.f ≫ (α.1.base ≫ β.1.base) =
                  𝟙 Y ≫ IB.f ≫ β.1.base := by
                    simpa [Category.assoc] using
                      congrArg (fun q => q ≫ β.1.base) hAB
              _ = 𝟙 Y ≫ IK.f := hBK) =
        γ.1.components.toHomOver.family IA IK (𝟙 Y) (𝟙 Y) (by
          rw [hγbase]
          dsimp [IA, IK, projectionDescentTotalCoverExplicitPullbackArrow,
            projectionDescentDatumExplicitPullbackArrow]
          change 𝟙 Y ≫ 𝟙 Y ≫ 𝟙 Y = 𝟙 Y ≫ 𝟙 Y
          simp) := by
    simpa [P, α, β, γ, EA, EK, IA, IK] using hcomponent
  exact (by
    simpa [α, β, γ, IA, IB, IK] using hcompComponent.trans hcomponent')

/-- Source stage 3.13 realization cocycle after cancelling the local-restriction owner
isomorphisms.

This is the full source-side equality
`rho_(A,B) ≫ Lambda_B = Lambda_A` for one fixed target inner owner `(a,i)`.  It is the
left half of the final `Lambda_a` compatibility square; the remaining right half is the target
internal overlap of `X_a`. -/
theorem projectionDescentTotalCoverTransitionComponent_comp_realizationComponentFromTotalCoverToDatumInner
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U Y : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (I : S.Arrow)
    (a : Y ⟶ A.Y) (b : Y ⟶ B.Y)
    (K : (projectionDescentDatumLocalObject (J := J) hSheaf D I).cover.Arrow)
    (k : Y ⟶ K.Y)
    (hab : a ≫ A.f = b ≫ B.f) (hbk : b ≫ B.f = k ≫ K.f ≫ I.f) :
    projectionDescentTotalCoverTransitionComponent (J := J) hSheaf D A B a b hab ≫
      projectionDescentRealizationComponentFromTotalCoverToDatumInner
        (J := J) hSheaf D B I b K k hbk =
    projectionDescentRealizationComponentFromTotalCoverToDatumInner
      (J := J) hSheaf D A I a K k (hab.trans hbk) := by
  dsimp [projectionDescentTotalCoverTransitionComponent,
    projectionDescentRealizationComponentFromTotalCoverToDatumInner]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc]
  rw [Iso.hom_inv_id_assoc]
  simpa [Category.assoc] using
    congrArg
      (fun q =>
        (projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D A a).hom ≫
          (projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso (J := J)
            hSheaf D A a).inv ≫
          q ≫
          (projectionDescentDatumExplicitPullbackArrowRestrictionIso (J := J)
            hSheaf D I K k).hom ≫
          (projectionDescentDatumLocalRestrictionIso (J := J) hSheaf D I K k).inv)
      (projectionDescentExplicitTransitionComponent_comp_fromTotalCoverToDatumInner
        (J := J) hSheaf D A B I a b K k hab hbk)

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
