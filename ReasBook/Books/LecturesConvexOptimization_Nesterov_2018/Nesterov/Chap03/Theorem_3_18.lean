import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap03.Theorem_3_1_4_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 3.18 lives in the chapter's hyperplane-support domain.

Primary domain:
- affine hyperplanes and supporting hyperplanes for closed convex sets in finite-dimensional real
  inner-product spaces.

Relevant sampled declarations:
- `AffineHyperplane`
- `IsSupportingHyperplane`
- `Set.IsExposed`
- `exists_supporting_hyperplane_at_boundary_point_of_closed_convex`

Source-facing layer:
- existence of a supporting hyperplane through a boundary point of a closed convex set.

Core/canonical owner:
- `AffineHyperplane` from `Definition_3_1_4_1`, whose primitive data are the nonzero normal vector
  and offset.

Bridge/view:
- `hyperplane g γ` and `IsSupportingHyperplane Q g γ`, which spell the owner object in
  coordinate form.

The current file's former theorem was a third copy of the same source-facing result already
recorded upstream as
`exists_supporting_hyperplane_at_boundary_point_of_closed_convex`. The extra hypothesis
`Q.Nonempty` is redundant here, since `x₀ ∈ frontier Q` implies `x₀ ∈ closure Q`, while
`closure ∅ = ∅`. This file therefore reuses the earlier theorem directly instead of keeping a
parallel local shell with a strictly longer hypothesis list. -/
recall exists_supporting_hyperplane_at_boundary_point_of_closed_convex
    [FiniteDimensional ℝ E] (Q : Set E) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    {x₀ : E}
    (hx₀ : x₀ ∈ frontier Q) :
    ∃ g : E, ∃ γ : ℝ, x₀ ∈ hyperplane g γ ∧ IsSupportingHyperplane Q g γ

end
