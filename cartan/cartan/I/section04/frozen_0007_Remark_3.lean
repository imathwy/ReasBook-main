import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- The square pullback of mathlib's owner `expNegInvGlue` matches the textbook flat function:
it is `0` at the origin and `exp (-1 / x^2)` away from `0`. -/
lemma expNegInvGlue_sq_apply (x : ℝ) :
    expNegInvGlue (x ^ 2) = if x = 0 then 0 else Real.exp (-1 / x ^ 2) := by
  by_cases hx : x = 0
  · simp [hx]
  · have hxsq : 0 < x ^ 2 := sq_pos_of_ne_zero hx
    simp [expNegInvGlue, hx, not_le_of_gt hxsq, div_eq_mul_inv]

/-- The textbook flat function `x ↦ expNegInvGlue (x ^ 2)` is infinitely differentiable on `ℝ`. -/
-- Proof sketch: compose mathlib's owner theorem `expNegInvGlue.contDiff` with the polynomial map
-- `x ↦ x ^ 2`.
lemma expNegInvGlue_sq_contDiff : ContDiff ℝ ⊤ (fun x : ℝ ↦ expNegInvGlue (x ^ 2)) := sorry

/-- Every iterated derivative of the textbook flat function vanishes at the origin. -/
-- Proof sketch: work from the owner-based identity `expNegInvGlue (x ^ 2)`,
-- show by induction that
-- each iterated derivative is a polynomial in `x⁻¹` times the same rapidly decaying exponential,
-- and then take the limit at `0`.
lemma expNegInvGlue_sq_iteratedDeriv_zero (n : ℕ) :
    iteratedDeriv n (fun x : ℝ ↦ expNegInvGlue (x ^ 2)) 0 = 0 := sorry

/-- There exists a real-valued function that is differentiable on `ℝ` but whose derivative is not
differentiable at some point. -/
-- Proof sketch: start from a continuous function that fails to be differentiable at some point and
-- integrate it on intervals `0..x`; the fundamental theorem of calculus gives a differentiable
-- primitive whose derivative recovers the original continuous counterexample.
theorem exists_differentiable_with_no_second_derivative :
    ∃ f : ℝ → ℝ, Differentiable ℝ f ∧ ∃ x : ℝ, ¬ DifferentiableAt ℝ (deriv f) x := sorry

/-- Remark 3: the function that is `0` at `0` and `exp (-1 / x^2)` for `x ≠ 0`, equivalently
`x ↦ expNegInvGlue (x ^ 2)`, is smooth on `ℝ` but is not analytic at the origin. -/
lemma expNegInvGlue_sq_not_analyticAt_zero :
    ¬ AnalyticAt ℝ (fun x : ℝ ↦ expNegInvGlue (x ^ 2)) 0 := by
  intro hanalytic
  have htop : analyticOrderAt (fun x : ℝ ↦ expNegInvGlue (x ^ 2)) 0 = ⊤ := by
    apply le_antisymm le_top
    refine ENat.forall_natCast_le_iff_le.mp fun n _ ↦ ?_
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hanalytic]
    intro i hi
    exact expNegInvGlue_sq_iteratedDeriv_zero i
  rcases Metric.eventually_nhds_iff.mp (analyticOrderAt_eq_top.mp htop) with ⟨r, hr, hzero⟩
  have hhalf : r / 2 < r := by linarith
  have habs_half : |r| / 2 < r := by
    simpa [abs_of_pos hr] using hhalf
  have hvalue : expNegInvGlue ((r / 2) ^ 2) = 0 := by
    apply hzero
    simpa [Real.dist_eq, sub_zero] using habs_half
  have hpos : 0 < expNegInvGlue ((r / 2) ^ 2) :=
    expNegInvGlue.pos_of_pos (sq_pos_of_pos (half_pos hr))
  exact hpos.ne' hvalue
