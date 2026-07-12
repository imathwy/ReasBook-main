import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-
Lemma 12.0.1 is `bridge/view`. Domain sampling in mathlib's real-logarithm API gives:
- `Real.log_lt_sub_one_of_pos` as the owner inequality;
- `Real.strictMonoOn_log` as the ambient order-theoretic owner on `(0, ∞)`;
- `Real.strictConcaveOn_log_Ioi` as the ambient convex-analytic owner on `(0, ∞)`;
- `Real.lt_log_one_add_of_pos` as a nearby `log (1 + x)` comparison theorem.

The primitive data for the textbook statement are only `x : ℝ` and `hx : 0 < x`. The target
inequality is the source-facing specialization of `Real.log_lt_sub_one_of_pos` at `1 + x`, so the
public API should stay a thin theorem-level bridge rather than a parallel local owner. -/

/-- Lemma 12.0.1: for every real `x > 0`, one has `log (1 + x) < x`. -/
-- Proof sketch: apply `Real.log_lt_sub_one_of_pos` to `1 + x`; positivity follows from `x > 0`,
-- and the right-hand side simplifies to `(1 + x) - 1 = x`.
theorem log_one_add_lt_self {x : ℝ} (hx : 0 < x) : Real.log (1 + x) < x := by
  have hpos : 0 < 1 + x := by positivity
  have hne : 1 + x ≠ 1 := by linarith
  simpa using Real.log_lt_sub_one_of_pos hpos hne
