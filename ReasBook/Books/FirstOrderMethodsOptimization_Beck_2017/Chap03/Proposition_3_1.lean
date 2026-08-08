import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Metric

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Proposition 3.1 is `source-facing` for the norm example in the chapter extendedRealSubdifferential theory.
Its owner stack already lives upstream: `is_subgradient_at` is the primitive predicate,
`extendedRealSubdifferential` is the source-facing owner set, and `strongDualSubdifferential` is the
continuous-dual `bridge/view`. The proposition should therefore stay as a direct identification of
that existing owner object, not introduce a parallel wrapper API. -/

-- Proof sketch: unfold `strongDualSubdifferential`, simplify `‖0‖ = 0`, and identify the
-- resulting inequality
-- `(‖y‖ : EReal) ≥ g y` for all `y` with the dual-unit-ball condition `‖g‖ ≤ 1`, equivalently
-- `g ∈ closedBall (0 : StrongDual ℝ E) 1`.
/-- Proposition 3.1: the extendedRealSubdifferential of the norm at the origin is the closed unit ball of the
dual norm on `E*`. -/
theorem subdifferentialAt_norm_zero_eq_dual_closed_unit_ball :
    strongDualSubdifferential (fun x : E ↦ (‖x‖ : EReal)) (0 : E) =
      closedBall (0 : StrongDual ℝ E) 1 := sorry

end
