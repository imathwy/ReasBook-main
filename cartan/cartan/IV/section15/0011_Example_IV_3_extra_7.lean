import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Complex InnerProductSpace Set

-- Domain sampling note: the canonical owner layer here is `InnerProductSpace.HarmonicOnNhd`,
-- with the relevant bridge theorems `AnalyticAt.harmonicAt_re` and `Complex.differentiableAt_tan`.

/-- Example IV.3-extra-7 (1). On the pole-free set of `tan`, the textbook quotient formula agrees
with `z ↦ (tan z).re`. -/
theorem tan_re_eqOn_formula :
    EqOn (fun z : ℂ ↦ (tan z).re)
      (fun z : ℂ ↦
        Real.sin z.re * Real.cos z.re / (Real.cos z.re ^ 2 + Real.sinh z.im ^ 2))
      {z : ℂ | cos z ≠ 0} := by
  rw [Set.EqOn]
  intro z _hz
  -- The textbook identity is an algebraic real-part computation, so the pole-free hypothesis
  -- is only needed later for harmonicity, not for this pointwise formula.
  rw [Complex.tan_eq_sin_div_cos, Complex.div_re]
  -- Expand `sin z` and `cos z` in `x + iy` form and read off their real and imaginary parts.
  have hsin_re : (Complex.sin z).re = Real.sin z.re * Real.cosh z.im := by
    simpa [mul_assoc] using congrArg Complex.re (Complex.sin_eq z)
  have hsin_im : (Complex.sin z).im = Real.cos z.re * Real.sinh z.im := by
    simpa [mul_assoc] using congrArg Complex.im (Complex.sin_eq z)
  have hcos_re : (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
    simpa [mul_assoc] using congrArg Complex.re (Complex.cos_eq z)
  have hcos_im : (Complex.cos z).im = -(Real.sin z.re * Real.sinh z.im) := by
    simpa [mul_assoc] using congrArg Complex.im (Complex.cos_eq z)
  -- Collapse the denominator `‖cos z‖^2` to the textbook expression.
  have hdenom : Complex.normSq (Complex.cos z) = Real.cos z.re ^ 2 + Real.sinh z.im ^ 2 := by
    rw [Complex.cos_eq]
    calc
      Complex.normSq
          (Complex.cos z.re * Complex.cosh z.im
            - Complex.sin z.re * Complex.sinh z.im * Complex.I)
          = (Real.cos z.re * Real.cosh z.im) ^ 2 + (-(Real.sin z.re * Real.sinh z.im)) ^ 2 := by
              simpa [sub_eq_add_neg, mul_assoc] using
                (Complex.normSq_add_mul_I (Real.cos z.re * Real.cosh z.im)
                  (-(Real.sin z.re * Real.sinh z.im)))
      _ = Real.cos z.re ^ 2 * Real.cosh z.im ^ 2
            + Real.sin z.re ^ 2 * Real.sinh z.im ^ 2 := by
              ring
      _ = Real.cos z.re ^ 2 + Real.sinh z.im ^ 2 := by
        rw [Real.cosh_sq]
        calc
          Real.cos z.re ^ 2 * (Real.sinh z.im ^ 2 + 1)
              + Real.sin z.re ^ 2 * Real.sinh z.im ^ 2
              = Real.sinh z.im ^ 2 * (Real.cos z.re ^ 2 + Real.sin z.re ^ 2)
                  + Real.cos z.re ^ 2 := by
                    ring
          _ = Real.cos z.re ^ 2 + Real.sinh z.im ^ 2 := by
            rw [Real.cos_sq_add_sin_sq]
            ring
  -- After substituting the standard expansions, the numerator simplifies by
  -- `cosh^2 - sinh^2 = 1`.
  rw [hsin_re, hsin_im, hcos_re, hcos_im, hdenom]
  calc
    Real.sin z.re * Real.cosh z.im * (Real.cos z.re * Real.cosh z.im) /
          (Real.cos z.re ^ 2 + Real.sinh z.im ^ 2) +
        (Real.cos z.re * Real.sinh z.im) * (-(Real.sin z.re * Real.sinh z.im)) /
          (Real.cos z.re ^ 2 + Real.sinh z.im ^ 2)
        =
        (Real.sin z.re * Real.cos z.re * (Real.cosh z.im ^ 2 - Real.sinh z.im ^ 2)) /
          (Real.cos z.re ^ 2 + Real.sinh z.im ^ 2) := by
            ring
    _ = Real.sin z.re * Real.cos z.re / (Real.cos z.re ^ 2 + Real.sinh z.im ^ 2) := by
      rw [Real.cosh_sq_sub_sinh_sq]
      ring

/-- Example IV.3-extra-7 (2). The textbook function is harmonic on the pole-free set of `tan`. -/
theorem tan_re_harmonicOnNhd :
    HarmonicOnNhd (fun z : ℂ ↦ (tan z).re) {z : ℂ | cos z ≠ 0} := by
  let s : Set ℂ := {z : ℂ | cos z ≠ 0}
  have htan : DifferentiableOn ℂ tan s := fun z hz ↦
    (Complex.differentiableAt_tan.2 hz).differentiableWithinAt
  intro z hz
  have htan_analytic : AnalyticAt ℂ tan z :=
    htan.analyticAt ((isOpen_ne_fun continuous_cos continuous_const).mem_nhds hz)
  simpa using htan_analytic.harmonicAt_re
