import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3DescentEffective

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

/-- Source stage 3.13 local-refinement helper: after restricting a total-cover member
`U_ai -> U` along a map `W -> U_ai`, regard the result as an arrow of the inner cover over
`T_a`.  This is the formal owner of the source refinement `W -> U_ai -> T_a`. -/
noncomputable abbrev projectionDescentTotalCoverRefinedInner
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y) :
    (projectionDescentDatumLocalObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D A)).cover.Arrow :=
  (projectionDescentTotalCoverInner (J := J) hSheaf D A).precomp a

@[simp]
theorem projectionDescentTotalCoverRefinedInner_f
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y) :
    (projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a).f =
      a ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D A).f :=
  rfl

/-- Source stage 3.13 local-refinement helper: the inner descent datum identifies the restriction
of the original local object `x_ai` to `W` with the local object attached to the refined inner
cover arrow `W -> U_ai -> T_a`. -/
noncomputable def projectionDescentTotalCoverLocalRestrictionIso
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y) :
    (projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A)).restrictedLocalObject
        (projectionDescentTotalCoverInner (J := J) hSheaf D A) a ≅
      (projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A)).restrictedLocalObject
        (projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a) (𝟙 W) :=
  (projectionDescentDatumLocalObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D A)).overlapIso
    (I₁ := projectionDescentTotalCoverInner (J := J) hSheaf D A)
    (I₂ := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a)
    a (𝟙 W) (by
      simp [projectionDescentTotalCoverRefinedInner])

/-- Source stage 3.13 local-refinement helper: the refined inner arrow is an arrow of the
explicit pullback cover of `X_a` along `W -> T_a`. -/
noncomputable def projectionDescentTotalCoverExplicitPullbackArrow
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y) :
    ((projectionDescentDatumLocalObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D A)).cover.pullback
        (a ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D A).f)).Arrow where
  Y := W
  f := 𝟙 W
  hf := by
    simpa [projectionDescentTotalCoverRefinedInner] using
      (projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a).hf

@[simp]
theorem projectionDescentTotalCoverExplicitPullbackArrow_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y) :
    DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
        (a ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D A).f)
        (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a) =
      projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a := by
  ext <;> simp [projectionDescentTotalCoverExplicitPullbackArrow,
    projectionDescentTotalCoverRefinedInner]
  rfl

noncomputable def projectionDescentTotalCoverExplicitPullbackArrowRestrictionIso
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y) :
    (DescentCompletionObjectOver.pullback (J := J)
        (projectionDescentDatumLocalObject (J := J) hSheaf D
          (projectionDescentTotalCoverOuter (J := J) hSheaf D A))
        (a ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D A).f)).restrictedLocalObject
        (projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a) (𝟙 W) ≅
      (projectionDescentDatumLocalObject (J := J) hSheaf D
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A)).restrictedLocalObject
        (projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a) (𝟙 W) := by
  let D₀ :=
    projectionDescentDatumLocalObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
  let h := a ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D A).f
  let I :=
    projectionDescentTotalCoverExplicitPullbackArrow (J := J) hSheaf D A a
  let Ib := DescentCompletionObjectOver.pullbackCoverBaseArrow (J := J) D₀ h I
  change D₀.restrictedLocalObject Ib (𝟙 W) ≅
    D₀.restrictedLocalObject
      (projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a) (𝟙 W)
  exact D₀.overlapIso (I₁ := Ib)
    (I₂ := projectionDescentTotalCoverRefinedInner (J := J) hSheaf D A a)
    (𝟙 W) (𝟙 W) (by
      dsimp [Ib, I, D₀, h, projectionDescentTotalCoverExplicitPullbackArrow,
        projectionDescentTotalCoverRefinedInner,
        DescentCompletionObjectOver.pullbackCoverBaseArrow]
      simp
      rfl)

/-- The map from a restricted total-cover member to its outer cover member.  This is the
source expression `W -> U_ai -> T_a`. -/
noncomputable abbrev projectionDescentTotalCoverOuterMap
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y) :
    W ⟶ (projectionDescentTotalCoverOuter (J := J) hSheaf D A).Y :=
  a ≫ (projectionDescentTotalCoverInner (J := J) hSheaf D A).f

/-- Compatibility of the two outer maps induced by an overlap of total-cover members. -/
theorem projectionDescentTotalCoverOuterMap_fac
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A B : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow)
    (a : W ⟶ A.Y) (b : W ⟶ B.Y)
    (h : a ≫ A.f = b ≫ B.f) :
    projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a ≫
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A).f =
      projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b ≫
        (projectionDescentTotalCoverOuter (J := J) hSheaf D B).f := by
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
    _ = b ≫ B.f := h
    _ =
      projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b ≫
        (projectionDescentTotalCoverOuter (J := J) hSheaf D B).f := by
        have hB :
            b ≫ ((projectionDescentTotalCoverInner (J := J) hSheaf D B).f ≫
                (projectionDescentTotalCoverOuter (J := J) hSheaf D B).f) =
              b ≫ B.f :=
          congrArg (fun q => b ≫ q)
            (projectionDescentTotalCover_fac (J := J) hSheaf D B)
        simpa [projectionDescentTotalCoverOuterMap, Category.assoc] using hB.symm

/-- Source stage 3.13 local-refinement helper: specialize the outer descent transition
`Theta_ab` to an overlap of two total-cover arrows. -/
noncomputable def projectionDescentOuterFiberHomForTotalCover
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
    ((canonicalFiberPseudofunctor P).map
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a).op.toLoc).toFunctor.obj
        (D.obj (projectionDescentTotalCoverOuter (J := J) hSheaf D A)) ⟶
      ((canonicalFiberPseudofunctor P).map
        (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b).op.toLoc).toFunctor.obj
        (D.obj (projectionDescentTotalCoverOuter (J := J) hSheaf D B)) :=
  projectionDescentOuterFiberHom (J := J) hSheaf D
    (projectionDescentTotalCoverOuter (J := J) hSheaf D A)
    (projectionDescentTotalCoverOuter (J := J) hSheaf D B)
    (projectionDescentTotalCoverOuterMap (J := J) hSheaf D A a)
    (projectionDescentTotalCoverOuterMap (J := J) hSheaf D B b)
    (projectionDescentTotalCoverOuterMap_fac (J := J) hSheaf D A B a b h)

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
