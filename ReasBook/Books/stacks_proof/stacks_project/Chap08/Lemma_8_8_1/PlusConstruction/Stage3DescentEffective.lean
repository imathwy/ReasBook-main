import stacks_proof.stacks_project.Chap08.Lemma_8_8_1.PlusConstruction.Stage3PullbackBridge

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

namespace DescentCompletionObjectOver

/-- Helper for Chap08 Lemma 8 8 1, source stage 3.13: the "total cover" obtained by
composing an outer cover `T_a -> U` with the descent-completion cover attached to each local
object over `T_a`.  This is the Lean owner for the source notation `{U_{ai} -> T_a -> U}`. -/
noncomputable def stage3TotalCover
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U : C}
    (S : J.Cover U)
    (D : ∀ I : S.Arrow, DescentCompletionObjectOver (J := J) X I.Y) :
    J.Cover U :=
  S.bind fun I => (D I).cover

/-- The outer cover arrow `T_a -> U` attached to an arrow of the total cover. -/
noncomputable abbrev stage3TotalCoverOuter
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U : C}
    {S : J.Cover U}
    {D : ∀ I : S.Arrow, DescentCompletionObjectOver (J := J) X I.Y}
    (A : (stage3TotalCover (J := J) S D).Arrow) :
    S.Arrow :=
  A.fromMiddle

/-- The inner cover arrow `U_{ai} -> T_a` attached to an arrow of the total cover. -/
noncomputable abbrev stage3TotalCoverInner
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U : C}
    {S : J.Cover U}
    {D : ∀ I : S.Arrow, DescentCompletionObjectOver (J := J) X I.Y}
    (A : (stage3TotalCover (J := J) S D).Arrow) :
    (D (stage3TotalCoverOuter (J := J) (D := D) A)).cover.Arrow :=
  A.toMiddle

/-- The displayed total-cover arrow is the composite of its inner and outer arrows. -/
@[simp]
theorem stage3TotalCover_fac
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U : C}
    {S : J.Cover U}
    {D : ∀ I : S.Arrow, DescentCompletionObjectOver (J := J) X I.Y}
    (A : (stage3TotalCover (J := J) S D).Arrow) :
    (stage3TotalCoverInner (J := J) (D := D) A).f ≫
        (stage3TotalCoverOuter (J := J) (D := D) A).f =
      A.f := by
  exact A.middle_spec

/-- The original local object carried by a total-cover arrow. -/
noncomputable abbrev stage3TotalCoverLocalObject
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U : C}
    {S : J.Cover U}
    {D : ∀ I : S.Arrow, DescentCompletionObjectOver (J := J) X I.Y}
    (A : (stage3TotalCover (J := J) S D).Arrow) :
    X.p.Fiber A.Y :=
  (D (stage3TotalCoverOuter (J := J) (D := D) A)).localObject
    (stage3TotalCoverInner (J := J) (D := D) A)

@[simp]
theorem stage3TotalCoverLocalObject_eq
    {X : FibredCategoryOver.{u, v, uX, vX} C} {U : C}
    {S : J.Cover U}
    {D : ∀ I : S.Arrow, DescentCompletionObjectOver (J := J) X I.Y}
    (A : (stage3TotalCover (J := J) S D).Arrow) :
    stage3TotalCoverLocalObject (J := J) (D := D) A =
      (D (stage3TotalCoverOuter (J := J) (D := D) A)).localObject
        (stage3TotalCoverInner (J := J) (D := D) A) :=
  rfl

end DescentCompletionObjectOver

namespace DescentCompletionObject

/-- Helper for Chap08 Lemma 8 8 1, source stage 3.13: a descent datum in the
descent-completion projection over a cover `S`.  This is the Lean owner for the source notation
`(X_a, Theta_ab)` where each `X_a` is already a completed descent object. -/
abbrev ProjectionDescentDatum
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} (S : J.Cover U) : Type _ :=
  letI := category (J := J) hSheaf
  haveI : (projectionFunctor (J := J) hSheaf).IsFibered :=
    projectionFunctor_isFibered (J := J) hSheaf
  (canonicalFiberPseudofunctor (projectionFunctor (J := J) hSheaf)).DescentData
    (X := fun I : S.Arrow => I.Y) (fun I => I.f)

/-- The inner completed object `X_a` attached to an outer cover member of a stage 3.13 descent
datum, transported out of the fiber subtype. -/
noncomputable def projectionDescentDatumLocalObject
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) (I : S.Arrow) :
    DescentCompletionObjectOver (J := J) X I.Y := by
  letI := category (J := J) hSheaf
  rcases D.obj I with ⟨⟨V, obj⟩, hV⟩
  dsimp [projectionFunctor] at hV
  subst hV
  exact obj

/-- The outer local object `X_a` of a stage 3.13 descent datum, repackaged as a completed
descent object with base definitionally equal to the corresponding cover member `T_a`. -/
noncomputable def projectionDescentDatumObject
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) (I : S.Arrow) :
    DescentCompletionObject (J := J) X where
  base := I.Y
  object := projectionDescentDatumLocalObject (J := J) hSheaf D I

@[simp]
theorem projectionDescentDatumObject_base
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) (I : S.Arrow) :
    (projectionDescentDatumObject (J := J) hSheaf D I).base = I.Y :=
  rfl

/-- The repackaged outer object is the original outer descent object in the projection fibre.
This bridge isolates the owner transport between the source notation `X_a` and the Lean object
with base definitionally equal to `T_a`. -/
theorem projectionDescentDatumObject_fiber_eq
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) (I : S.Arrow) :
    projectionFiberObject (J := J) hSheaf
        (projectionDescentDatumObject (J := J) hSheaf D I) =
      D.obj I := by
  letI := category (J := J) hSheaf
  cases hDI : D.obj I with
  | mk O hO =>
    cases O with
    | mk V obj =>
      simp only [projectionFiberObject, projectionDescentDatumObject,
        projectionDescentDatumLocalObject, hDI]
      dsimp [projectionFunctor] at hO ⊢
      cases hO
      apply Subtype.ext
      rfl

/-- The canonical/explicit pullback bridge specialized to an outer member `X_a` of a stage
3.13 descent datum. -/
theorem projectionDescentDatumPullbackIsoCanonical_nonempty
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S) (I : S.Arrow)
    (i : W ⟶ I.Y) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    Nonempty
      (explicitPullbackFiberObject (J := J) hSheaf
          (projectionDescentDatumObject (J := J) hSheaf D I) i ≅
        i ^*[canonicalPullbackChoice P]
          projectionFiberObject (J := J) hSheaf
            (projectionDescentDatumObject (J := J) hSheaf D I)) := by
  exact
    explicitPullbackFiberObject_iso_canonicalPullback_nonempty
      (J := J) hSheaf
      (projectionDescentDatumObject (J := J) hSheaf D I) i

/-- Source stage 3.13 total cover: compose the outer cover `T_a -> U` with the inner cover
carried by each completed object `X_a`.  This is the formal version of the source family
`{U_ai -> T_a -> U}`. -/
noncomputable def projectionDescentTotalCover
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} (S : J.Cover U)
    (D : ProjectionDescentDatum (J := J) hSheaf S) :
    J.Cover U :=
  DescentCompletionObjectOver.stage3TotalCover (J := J) S
    (fun I => projectionDescentDatumLocalObject (J := J) hSheaf D I)

/-- The outer index of a member of the stage 3.13 total cover. -/
noncomputable abbrev projectionDescentTotalCoverOuter
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow) :
    S.Arrow :=
  DescentCompletionObjectOver.stage3TotalCoverOuter (J := J)
    (D := fun I => projectionDescentDatumLocalObject (J := J) hSheaf D I) A

/-- The inner index of a member of the stage 3.13 total cover. -/
noncomputable abbrev projectionDescentTotalCoverInner
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow) :
    (projectionDescentDatumLocalObject (J := J) hSheaf D
      (projectionDescentTotalCoverOuter (J := J) hSheaf D A)).cover.Arrow :=
  DescentCompletionObjectOver.stage3TotalCoverInner (J := J)
    (D := fun I => projectionDescentDatumLocalObject (J := J) hSheaf D I) A

/-- The original local object `x_ai` carried by a member of the total cover. -/
noncomputable abbrev projectionDescentTotalCoverLocalObject
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow) :
    X.p.Fiber A.Y :=
  DescentCompletionObjectOver.stage3TotalCoverLocalObject (J := J)
    (D := fun I => projectionDescentDatumLocalObject (J := J) hSheaf D I) A

@[simp]
theorem projectionDescentTotalCover_fac
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (A : (projectionDescentTotalCover (J := J) hSheaf S D).Arrow) :
    (projectionDescentTotalCoverInner (J := J) hSheaf D A).f ≫
        (projectionDescentTotalCoverOuter (J := J) hSheaf D A).f =
      A.f := by
  exact
    DescentCompletionObjectOver.stage3TotalCover_fac (J := J)
      (D := fun I => projectionDescentDatumLocalObject (J := J) hSheaf D I) A

/-- The outer transition morphism supplied by a stage 3.13 descent datum, before extracting its
component family on the inner covers.  This is the typed owner of the source symbol
`Theta_ab`. -/
noncomputable def projectionDescentOuterFiberHom
    {X : FibredCategoryOver.{u, v, uX, vX} C}
    (hSheaf : DescentCompletionObjectOver.HomOver.homPresheavesAreSheaves (J := J) X)
    {U W : C} {S : J.Cover U}
    (D : ProjectionDescentDatum (J := J) hSheaf S)
    (I K : S.Arrow) (i : W ⟶ I.Y) (k : W ⟶ K.Y)
    (h : i ≫ I.f = k ≫ K.f) :
    letI := category (J := J) hSheaf
    let P := projectionFunctor (J := J) hSheaf
    haveI : P.IsFibered := projectionFunctor_isFibered (J := J) hSheaf
    ((canonicalFiberPseudofunctor P).map i.op.toLoc).toFunctor.obj (D.obj I) ⟶
      ((canonicalFiberPseudofunctor P).map k.op.toLoc).toFunctor.obj (D.obj K) := by
  letI := category (J := J) hSheaf
  haveI : (projectionFunctor (J := J) hSheaf).IsFibered :=
    projectionFunctor_isFibered (J := J) hSheaf
  exact D.hom (i ≫ I.f) i k rfl h.symm

end DescentCompletionObject
end FibredCategoryMor

end CategoryTheory
