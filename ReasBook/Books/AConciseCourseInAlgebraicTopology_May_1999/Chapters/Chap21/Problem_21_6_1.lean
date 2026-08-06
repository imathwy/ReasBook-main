import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Proposition_21_4_3

-- Semantic recall via Chapter 21 precedent: `Proposition_21_4_2` already fixes the source-facing
-- owner `manifoldBoundary n M` for `∂M`, and `Proposition_21_4_3` fixes the inclusion
-- `manifoldBoundaryInclusion n M : TopCat.of (manifoldBoundary n M) ⟶ TopCat.of M`. This file
-- keeps the source-facing continuous-map retraction statement and reuses that categorical owner
-- through the canonical `TopCat` to `ContinuousMap` bridge.

open scoped Manifold

variable {n : ℕ} [NeZero n]
variable {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]

@[simp] theorem manifoldBoundaryInclusion_hom_apply (x : manifoldBoundary n M) :
    (manifoldBoundaryInclusion n M).hom x = x := rfl

/-- A continuous retraction of `M` onto `∂M` fixes each boundary point. -/
theorem manifoldBoundary_retraction_eq_self
    {r : C(M, manifoldBoundary n M)}
    (hret : r.comp (manifoldBoundaryInclusion n M).hom =
      ContinuousMap.id (manifoldBoundary n M))
    (x : manifoldBoundary n M) :
    r x = x := by
  have happly := congrArg (fun f : C(manifoldBoundary n M, manifoldBoundary n M) ↦ f x) hret
  simpa using happly

/-- A source-facing retraction of the canonical inclusion `∂M ↪ M` yields the corresponding
categorical retract in `TopCat`. -/
def manifoldBoundaryTopCatRetract (r : C(M, manifoldBoundary n M))
    (hret : r.comp (manifoldBoundaryInclusion n M).hom =
      ContinuousMap.id (manifoldBoundary n M)) :
    CategoryTheory.Retract (TopCat.of (manifoldBoundary n M)) (TopCat.of M) where
  i := manifoldBoundaryInclusion n M
  r := TopCat.ofHom r
  retract := by
    ext x
    simpa using congrArg Subtype.val (manifoldBoundary_retraction_eq_self hret x)

/-- Problem 21.6.1. If `M` is a compact connected positive-dimensional manifold with boundary,
in the source-facing sense recorded by `ChartedSpace (EuclideanHalfSpace n) M`, then `∂M` is not
a retract of `M`; equivalently, there is no continuous map `r : M → ∂M` whose composite with the
boundary inclusion `∂M ↪ M` is the identity on `∂M`. -/
theorem manifoldBoundary_not_retract [CompactSpace M] [ConnectedSpace M]
    : ¬ ∃ r : C(M, manifoldBoundary n M),
        r.comp (manifoldBoundaryInclusion n M).hom =
          ContinuousMap.id (manifoldBoundary n M) := sorry
