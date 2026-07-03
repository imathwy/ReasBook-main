import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Metric

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "P" => fun x ↦
  (metricProjection C hC_nonempty hC_closed.isComplete hC_convex x : E)

-- Proof sketch: apply the projection variational inequality to `v` with test point `P_C(w)` and to
-- `w` with test point `P_C(v)`, then add the resulting inequalities and rearrange the inner-product
-- terms to obtain the standard firm nonexpansiveness estimate.
/-- Theorem 5.4 (1): the metric projection onto a nonempty closed convex set in a complete real
inner product space is firmly nonexpansive. -/
theorem metricProjection_firmly_nonexpansive (v w : E) :
    inner ℝ (P v - P w) (v - w) ≥ ‖P v - P w‖ ^ 2 := sorry

-- Proof sketch: combine firm nonexpansiveness with Cauchy-Schwarz:
-- `‖P_C(v) - P_C(w)‖ ^ 2 ≤ ⟪P_C(v) - P_C(w), v - w⟫ ≤ ‖P_C(v) - P_C(w)‖ * ‖v - w‖`, then
-- divide by `‖P_C(v) - P_C(w)‖` in the nontrivial case, and package the conclusion in the
-- canonical `LipschitzWith 1` form.
/-- Theorem 5.4 (2): the metric projection onto a nonempty closed convex set in a complete real
inner product space is nonexpansive. -/
theorem metricProjection_nonexpansive :
    LipschitzWith 1 P := sorry

end
