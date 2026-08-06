import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.TopCat.Subspace

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

-- Semantic recall via `lean_leansearch`: no source-exact topological adjunction-space owner
-- surfaced in the current environment. This file provides the Chapter 10 owner needed across the
-- repository: the pushout `Y ∪_f X` together with the copy of `Y` inside it.

/-- The adjunction space `Y ∪_f X` obtained by gluing the subspace `A ⊆ X` to `Y` along
`f : A → Y`, represented as a pushout in `TopCat`. -/
abbrev cellularPushout
    {X : Type u} {Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (f : C(A, Y)) :
    TopCat :=
  pushout (TopCat.ofHom f) (TopCat.subtypeInclusion A)

/-- The copy of `Y` inside the adjunction space `cellularPushout A f`, represented by the range
of the left pushout leg. -/
abbrev cellularPushoutLeftRange
    {X : Type u} {Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (f : C(A, Y)) :
    Set (cellularPushout A f) :=
  Set.range (pushout.inl (TopCat.ofHom f) (TopCat.subtypeInclusion A)).hom

/-- The right pushout leg sends every point of `A` into the copy of `Y` inside `Y ∪_f X`. -/
theorem cellularPushout_inr_mem_leftRange_of_mem
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (f : C(A, Y)) {x : X} (hx : x ∈ A) :
    (pushout.inr (TopCat.ofHom f) (TopCat.subtypeInclusion A)).hom x ∈
      cellularPushoutLeftRange A f :=
  ⟨f ⟨x, hx⟩, by
    have hcond :
        TopCat.ofHom f ≫ pushout.inl (TopCat.ofHom f) (TopCat.subtypeInclusion A) =
          TopCat.subtypeInclusion A ≫ pushout.inr (TopCat.ofHom f) (TopCat.subtypeInclusion A) :=
      pushout.condition
    have hmaps := congrArg TopCat.Hom.hom hcond
    simpa using congrArg (fun g ↦ g ⟨x, hx⟩) hmaps⟩
