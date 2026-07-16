import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap05.Corollary_5_24_2

noncomputable section

open scoped Pointwise Rockafellar Topology

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Function

variable {f : E → WithBotTop ℝ}

-- Proof sketch: transport the canonical dual-valued clause
-- `exists_pos_subdifferentialAt_subset_add_closedBall_of_mem_interior_dom` through
-- `InnerProductSpace.toDualMap ℝ E`.
/-- Corollary 5.24.2 (2), Euclidean bridge form: for a proper convex function, every interior point
`x ∈ interior (dom(f))`
and every `ε > 0` admit a radius `δ > 0` such that for every
`z ∈ Metric.closedBall x δ`, the Euclidean subdifferential satisfies
`∂ᵥf(z) ⊆ ∂ᵥf(x) + Metric.closedBall (0 : E) ε`. -/
theorem exists_pos_subdifferentialAt_subset_add_closedBall_of_mem_interior_dom_euclidean
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    {x : E} (hx : x ∈ interior (dom(f))) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ Metric.closedBall x δ,
      (∂ᵥf(z)) ⊆ (∂ᵥf(x)) + Metric.closedBall (0 : E) ε := sorry

end Function

end
