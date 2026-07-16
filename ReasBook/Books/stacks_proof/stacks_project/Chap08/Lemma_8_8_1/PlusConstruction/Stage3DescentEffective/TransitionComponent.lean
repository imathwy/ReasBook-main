import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective.OwnerBridge

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

/-- Source stage 3.13 owner bridge: specialize the outer transition `Theta_ab` to a total-cover
overlap and transport it from canonical pullback owners to the explicit pullback objects used by
the descent-completion construction. -/
noncomputable def projectionDescentExplicitOuterFiberHomForTotalCover
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y) (b : W ⟶ B.Y)
    (h : a ≫ A.f = b ≫ B.f) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    explicitPullbackFiberObject (J := J) hSheaf
        (projectionDescentDatumObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a) ⟶
      explicitPullbackFiberObject (J := J) hSheaf
        (projectionDescentDatumObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D B))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let eA :=
    projectionDescentDatumPullbackIsoCanonicalOriginal
      (J := J) hSheaf D (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
  let eB :=
    projectionDescentDatumPullbackIsoCanonicalOriginal
      (J := J) hSheaf D (projectionDescentTotalCoverOuter (J := J) hSheaf D B)
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b)
  exact eA.hom ≫
    projectionDescentOuterFiberHomForTotalCover (J := J) hSheaf D A B a b h ≫
      eB.inv

/-- Source stage 3.13 iso form of the transported outer transition `Theta_ab` on a total-cover
overlap.  This keeps the original isomorphism structure available for the later cocycle and
realization checks. -/
noncomputable def projectionDescentExplicitOuterFiberIsoForTotalCover
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y) (b : W ⟶ B.Y)
    (h : a ≫ A.f = b ≫ B.f) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    explicitPullbackFiberObject (J := J) hSheaf
        (projectionDescentDatumObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a) ≅
      explicitPullbackFiberObject (J := J) hSheaf
        (projectionDescentDatumObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D B))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b) := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let eA :=
    projectionDescentDatumPullbackIsoCanonicalOriginal
      (J := J) hSheaf D (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
  let eB :=
    projectionDescentDatumPullbackIsoCanonicalOriginal
      (J := J) hSheaf D (projectionDescentTotalCoverOuter (J := J) hSheaf D B)
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b)
  exact eA ≪≫
    D.iso
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a ≫
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A).f)
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b)
      rfl
      (projectionDescentTotalCoverOuterMap_fac (J := J) hSheaf D A B a b h).symm ≪≫
      eB.symm

@[simp]
theorem projectionDescentExplicitOuterFiberIsoForTotalCover_hom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y) (b : W ⟶ B.Y)
    (h : a ≫ A.f = b ≫ B.f) :
    (projectionDescentExplicitOuterFiberIsoForTotalCover (J := J)
        hSheaf D A B a b h).hom =
      projectionDescentExplicitOuterFiberHomForTotalCover (J := J)
        hSheaf D A B a b h := by
  rfl

/-- The explicit-owner outer transition is a vertical morphism over the overlap object `W`. -/
theorem projectionDescentExplicitOuterFiberHomForTotalCover_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y) (b : W ⟶ B.Y)
    (h : a ≫ A.f = b ≫ B.f) :
    letI := category (J := J) hSheaf
    (projectionDescentExplicitOuterFiberHomForTotalCover (J := J)
      hSheaf D A B a b h).1.base = 𝟙 W := by
  letI := category (J := J) hSheaf
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let α :=
    projectionDescentExplicitOuterFiberHomForTotalCover (J := J)
      hSheaf D A B a b h
  letI : P.IsHomLift (𝟙 W) α.1 := α.2
  have hfac := IsHomLift.fac' P (𝟙 W) α.1
  simpa [P, projectionFunctor, α] using hfac

/-- The transported outer transition restricts to the identity in the self-overlap case. -/
theorem projectionDescentExplicitOuterFiberHomForTotalCover_self
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y) :
    letI := category (J := J) hSheaf
    projectionDescentExplicitOuterFiberHomForTotalCover (J := J)
      hSheaf D A A a a rfl =
      𝟙 (explicitPullbackFiberObject (J := J) hSheaf
        (projectionDescentDatumObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)) := by
  letI := category (J := J) hSheaf
  haveI : (projectionFunctor (J := J) hSheaf).IsFibered :=
    projectionFunctor_isFibered (J := J) hSheaf
  let e :=
    projectionDescentDatumPullbackIsoCanonicalOriginal
      (J := J) hSheaf D (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
  have hDself :
      D.hom
          (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a ≫
            (projectionDescentTotalCoverOuter (J := J) hSheaf D A).f)
          (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
          (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
          rfl rfl =
        𝟙 (((canonicalFiberPseudofunctor (projectionFunctor (J := J) hSheaf)).map
            (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a).op.toLoc).toFunctor.obj
            (D.obj (projectionDescentTotalCoverOuter (J := J) hSheaf D A))) := by
    simpa using
      D.hom_self
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a ≫
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A).f)
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a) rfl
  dsimp [projectionDescentExplicitOuterFiberHomForTotalCover,
    projectionDescentOuterFiberHomForTotalCover, projectionDescentOuterFiberHom]
  change e.hom ≫
      D.hom
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a ≫
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A).f)
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
        rfl rfl ≫ e.inv =
    𝟙 (explicitPullbackFiberObject (J := J) hSheaf
        (projectionDescentDatumObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a))
  rw [hDself]
  change e.hom ≫
      𝟙 (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a
        ^*[canonicalPullbackChoice (projectionFunctor (J := J) hSheaf)]
          D.obj (projectionDescentTotalCoverOuter (J := J) hSheaf D A)) ≫
      e.inv =
    𝟙 (explicitPullbackFiberObject (J := J) hSheaf
        (projectionDescentDatumObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a))
  calc
    e.hom ≫
        𝟙 (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a
          ^*[canonicalPullbackChoice (projectionFunctor (J := J) hSheaf)]
            D.obj (projectionDescentTotalCoverOuter (J := J) hSheaf D A)) ≫
        e.inv = e.hom ≫ e.inv := by
          rw [Category.id_comp]
    _ = 𝟙 (explicitPullbackFiberObject (J := J) hSheaf
        (projectionDescentDatumObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)) :=
      e.hom_inv_id

/-- Source stage 3.13 component of `Theta_ab` on the explicit pullback covers of the two outer
objects, at the refined total-cover arrows over `W`. -/
noncomputable def projectionDescentTotalCoverExplicitTransitionComponent
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y) (b : W ⟶ B.Y)
    (h : a ≫ A.f = b ≫ B.f) :
    (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)).restrictedLocalObject
        (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a) (𝟙 W) ⟶
      (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D B))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b)).restrictedLocalObject
        (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B b) (𝟙 W) := by
  letI := category (J := J) hSheaf
  let α :=
    projectionDescentExplicitOuterFiberHomForTotalCover (J := J)
      hSheaf D A B a b h
  have hbase :
      α.1.base = 𝟙 W :=
    projectionDescentExplicitOuterFiberHomForTotalCover_base
      (J := J) hSheaf D A B a b h
  exact α.1.components.toHomOver.family
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a)
    (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D B b)
    (𝟙 W) (𝟙 W)
    (by
      rw [hbase]
      dsimp [projectionDescentTotalCoverExplicitPullbackArrow]
      change 𝟙 W ≫ 𝟙 W ≫ 𝟙 W = 𝟙 W ≫ 𝟙 W
      calc
        𝟙 W ≫ 𝟙 W ≫ 𝟙 W = 𝟙 W ≫ 𝟙 W := by rw [Category.id_comp]
        _ = 𝟙 W ≫ 𝟙 W := rfl)

/-- On a self-overlap, the explicit pullback-cover component of the transported outer transition
is the identity. -/
theorem projectionDescentTotalCoverExplicitTransitionComponent_self
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y) :
    projectionDescentTotalCoverExplicitTransitionComponent (J := J)
      hSheaf D A A a a rfl =
      𝟙 ((DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)).restrictedLocalObject
        (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a) (𝟙 W)) := by
  letI := category (J := J) hSheaf
  let α :=
    projectionDescentExplicitOuterFiberHomForTotalCover (J := J)
      hSheaf D A A a a rfl
  have hα :
      α =
        𝟙 (explicitPullbackFiberObject (J := J) hSheaf
          (projectionDescentDatumObject (J := J) hSheaf D
            (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
          (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)) :=
    projectionDescentExplicitOuterFiberHomForTotalCover_self (J := J) hSheaf D A a
  let P := projectionFunctor (J := J) hSheaf
  haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
  let E :=
    explicitPullbackFiberObject (J := J) hSheaf
      (projectionDescentDatumObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
      (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
  let I :=
    projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a
  let componentOf (β : E ⟶ E) :
      (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)).restrictedLocalObject
        I (𝟙 W) ⟶
      (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)).restrictedLocalObject
        I (𝟙 W) := by
    letI : P.IsHomLift (𝟙 W) β.1 := β.2
    have hbase : β.1.base = 𝟙 W := by
      have hfac := IsHomLift.fac' P (𝟙 W) β.1
      simpa [P, projectionFunctor] using hfac
    exact β.1.components.toHomOver.family I I (𝟙 W) (𝟙 W) (by
      rw [hbase]
      dsimp [I, projectionDescentTotalCoverExplicitPullbackArrow]
      change 𝟙 W ≫ 𝟙 W ≫ 𝟙 W = 𝟙 W ≫ 𝟙 W
      calc
        𝟙 W ≫ 𝟙 W ≫ 𝟙 W = 𝟙 W ≫ 𝟙 W := by rw [Category.id_comp]
        _ = 𝟙 W ≫ 𝟙 W := rfl)
  have hcomponent := congrArg componentOf hα
  dsimp [projectionDescentTotalCoverExplicitTransitionComponent]
  change componentOf α =
    𝟙 ((DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)).restrictedLocalObject
        I (𝟙 W))
  rw [hcomponent]
  dsimp [componentOf]
  change (DescentCompletionObject.identity (J := J) E.1).components.toHomOver.family
      I I (𝟙 W) (𝟙 W) _ =
    𝟙 ((DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)).restrictedLocalObject
        I (𝟙 W))
  dsimp [DescentCompletionObject.identity, DescentCompletionObjectOver.NaturalHomOver.id,
    DescentCompletionObjectOver.idHomOver]
  simpa [E, I, explicitPullbackFiberObject, projectionDescentDatumObject,
    DescentCompletionObjectOver.pullback, DescentCompletionObjectOver.restrictedLocalObject,
    projectionDescentTotalCoverExplicitPullbackArrow,
    DescentCompletionObjectOver.pullbackCoverBaseArrow] using
    (DescentCompletionObjectOver.overlapIso_self_hom (J := J)
      ((explicitPullbackFiberObject (J := J) hSheaf
        (projectionDescentDatumObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)).1.object)
      (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a) (𝟙 W))

/-- Source stage 3.13 transition component `rho_(ai)(bj)`: the outer descent transition
`Theta_ab`, evaluated on total-cover members and transported back to the original local objects
`x_ai` and `x_bj`. -/
noncomputable def projectionDescentTotalCoverTransitionComponent
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y) (b : W ⟶ B.Y)
    (h : a ≫ A.f = b ≫ B.f) :
    (projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A)).restrictedLocalObject
        (projectionDescentTotalCoverInner (J := J) hSheaf D A) a ⟶
      (projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D B)).restrictedLocalObject
        (projectionDescentTotalCoverInner (J := J) hSheaf D B) b :=
  (projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D A a).hom ≫
    (projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso (J := J)
      hSheaf D A a).inv ≫
    projectionDescentTotalCoverExplicitTransitionComponent (J := J)
      hSheaf D A B a b h ≫
    (projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso (J := J)
      hSheaf D B b).hom ≫
    (projectionDescentTotalCoverLocalRestrictionIso (J := J) hSheaf D B b).inv

/-- Source stage 3.13 self condition for `rho`: on a self-overlap of a total-cover member, the
transition component is the identity. -/
theorem projectionDescentTotalCoverTransitionComponent_self
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y) :
    projectionDescentTotalCoverTransitionComponent (J := J) hSheaf D A A a a rfl =
      𝟙 ((projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A)).restrictedLocalObject
        (projectionDescentTotalCoverInner (J := J) hSheaf D A) a) := by
  dsimp [projectionDescentTotalCoverTransitionComponent]
  rw [projectionDescentTotalCoverExplicitTransitionComponent_self]
  simp

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
