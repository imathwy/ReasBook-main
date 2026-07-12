import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition I.3-extra-2: the inverse of the real exponential on the positive real axis is the
canonical logarithm `Real.log`. -/
recall Real.log

/- `Real.strictMonoOn_log` records that the logarithm is strictly increasing on `(0, ∞)`. -/
#check Real.strictMonoOn_log

/- `Real.log_mul` is the multiplicative functional equation
`log (t * t') = log t + log t'` for nonzero real factors. -/
#check Real.log_mul

/- `Real.log_one` is the identity `log 1 = 0`. -/
#check Real.log_one

/- `Real.hasStrictDerivAt_log_of_pos` is the canonical derivative theorem for the real logarithm on
`(0, ∞)`, with derivative `t⁻¹ = 1 / t`. -/
#check Real.hasStrictDerivAt_log_of_pos

/-- The alternating power series for `log (1 + u)` converges on the open unit interval. -/
theorem real_log_one_add_hasSum {u : ℝ} (hu : |u| < 1) :
    HasSum (fun n : ℕ ↦ (-1 : ℝ) ^ n * u ^ (n + 1) / (n + 1)) (Real.log (1 + u)) := by
  set v : ℝ := -u
  have hv : |v| < 1 := by
    simpa [v, abs_neg] using hu
  have hpow := (Real.hasSum_pow_div_log_of_abs_lt_one hv).neg
  have hterm (n : ℕ) :
      (-1 : ℝ) ^ n * u ^ (n + 1) / (n + 1 : ℝ) = -(v ^ (n + 1) / (n + 1 : ℝ)) := by
    subst v
    rw [neg_pow, pow_succ']
    ring
  convert hpow using 1
  · ext n
    exact hterm n
  · simp [v]

/- `Complex.norm_exp_ofReal_mul_I` states that `|exp (iy)| = 1` for every real `y`. -/
#check Complex.norm_exp_ofReal_mul_I

/- `Circle.coe_exp` identifies the circle-valued exponential with the complex parametrization
`y ↦ exp (y * I)`, and `Circle.exp_add` is its canonical homomorphism law. -/
#check Circle.coe_exp
#check Circle.exp_add
