import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Finset
open scoped BigOperators

/- The canonical owner for the finite geometric-series identity underlying this exercise is
`geom_sum_eq`; the trigonometric closed forms come from applying it to `Complex.exp (x * I)` and
then taking imaginary and real parts. -/
recall geom_sum_eq

/-- Helper for Exercise 9: the complex exponential sum along the arithmetic progression
`p ↦ p * x + y` is a geometric series with ratio `Complex.exp (x * Complex.I)`. -/
lemma sum_range_exp_arith_progression_eq_geom
    (x y : ℝ) (n : ℕ) (hq : Complex.exp (x * Complex.I) ≠ 1) :
    (∑ p ∈ range (n + 1), Complex.exp ((p * x + y) * Complex.I)) =
      Complex.exp (y * Complex.I) *
        (((Complex.exp (x * Complex.I)) ^ (n + 1) - 1) / (Complex.exp (x * Complex.I) - 1)) := by
  -- Rewrite each summand as a fixed factor times a power of the common ratio.
  have hterm :
      ∀ p : ℕ,
        Complex.exp ((p * x + y) * Complex.I) =
          Complex.exp (y * Complex.I) * (Complex.exp (x * Complex.I)) ^ p := by
    intro p
    have harg : ((p * x + y : ℝ) : ℂ) * Complex.I = y * Complex.I + (p : ℂ) * (x * Complex.I) := by
      norm_num
      ring
    calc
      Complex.exp ((p * x + y) * Complex.I)
          = Complex.exp (y * Complex.I + (p : ℂ) * (x * Complex.I)) := by
              simpa using congrArg Complex.exp harg
      _ = Complex.exp (y * Complex.I) * Complex.exp ((p : ℂ) * (x * Complex.I)) := by
            rw [Complex.exp_add]
      _ = Complex.exp (y * Complex.I) * (Complex.exp (x * Complex.I)) ^ p := by
            rw [Complex.exp_nat_mul]
  calc
    (∑ p ∈ range (n + 1), Complex.exp ((p * x + y) * Complex.I))
        = ∑ p ∈ range (n + 1), Complex.exp (y * Complex.I) * (Complex.exp (x * Complex.I)) ^ p := by
            simp_rw [hterm]
    _ = Complex.exp (y * Complex.I) *
          ∑ p ∈ range (n + 1), (Complex.exp (x * Complex.I)) ^ p := by
          rw [Finset.mul_sum]
    _ = Complex.exp (y * Complex.I) *
          (((Complex.exp (x * Complex.I)) ^ (n + 1) - 1) / (Complex.exp (x * Complex.I) - 1)) := by
          rw [geom_sum_eq hq]

/-- Helper for Exercise 9: the difference `exp (t * I) - 1` factors through the half-angle
expression involving `sin (t / 2)`. -/
lemma exp_mul_I_sub_one_eq_exp_half_mul_two_sin_half (t : ℝ) :
    Complex.exp (t * Complex.I) - 1 =
      Complex.exp (t / 2 * Complex.I) * ((((2 * Real.sin (t / 2)) : ℝ) : ℂ) * Complex.I) := by
  -- Rewrite the sine factor using `Complex.two_sin`, then factor `exp (t * I) - 1`.
  have hsin :
      ((((2 * Real.sin (t / 2)) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (t / 2 * Complex.I) - Complex.exp (-(t / 2) * Complex.I) := by
    calc
      ((((2 * Real.sin (t / 2)) : ℝ) : ℂ) * Complex.I)
          = ((2 : ℂ) * Complex.sin (t / 2)) * Complex.I := by
              norm_num
      _ = Complex.exp (t / 2 * Complex.I) - Complex.exp (-(t / 2) * Complex.I) := by
            rw [Complex.two_sin]
            ring_nf
            simp
  calc
    Complex.exp (t * Complex.I) - 1
        = Complex.exp (t / 2 * Complex.I) * Complex.exp (t / 2 * Complex.I) -
            Complex.exp (t / 2 * Complex.I) * Complex.exp (-(t / 2) * Complex.I) := by
              have hsplit : t * Complex.I = t / 2 * Complex.I + t / 2 * Complex.I := by
                ring
              rw [hsplit, Complex.exp_add]
              have hone :
                  Complex.exp (t / 2 * Complex.I) * Complex.exp (-(t / 2) * Complex.I) = 1 := by
                calc
                  Complex.exp (t / 2 * Complex.I) * Complex.exp (-(t / 2) * Complex.I)
                      = Complex.exp (t / 2 * Complex.I + -(t / 2) * Complex.I) := by
                          rw [← Complex.exp_add]
                  _ = Complex.exp 0 := by
                        congr 1
                        ring
                  _ = 1 := by
                        simp
              rw [hone]
    _ = Complex.exp (t / 2 * Complex.I) *
          (Complex.exp (t / 2 * Complex.I) - Complex.exp (-(t / 2) * Complex.I)) := by
            ring
    _ = Complex.exp (t / 2 * Complex.I) * ((((2 * Real.sin (t / 2)) : ℝ) : ℂ) * Complex.I) := by
          rw [hsin]

/-- Helper for Exercise 9: the denominator in the geometric-series formula is nonzero as soon as
`sin (x / 2)` is nonzero. -/
lemma exp_mul_I_ne_one_of_sin_half_ne_zero
    (x : ℝ) (hx : Real.sin (x / 2) ≠ 0) :
    Complex.exp (x * Complex.I) ≠ 1 := by
  -- The half-angle factorization forces `exp (x * I) - 1` to vanish only when `sin (x / 2)` does.
  intro h
  have hzero : Complex.exp (x * Complex.I) - 1 = 0 := sub_eq_zero.mpr h
  rw [exp_mul_I_sub_one_eq_exp_half_mul_two_sin_half] at hzero
  have hs :
      ((((2 * Real.sin (x / 2)) : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    refine mul_ne_zero ?_ Complex.I_ne_zero
    exact_mod_cast mul_ne_zero two_ne_zero hx
  have hexp : Complex.exp (x / 2 * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  exact hs ((mul_eq_zero.mp hzero).resolve_left hexp)

/-- Helper for Exercise 9: cancelling the common factor `2 * I` in the half-angle quotient leaves
the expected real sine ratio. -/
lemma sine_factor_div_eq_ratio
    (a b : ℝ) (hb : Real.sin b ≠ 0) :
    ((((2 * Real.sin a) : ℝ) : ℂ) * Complex.I) /
        ((((2 * Real.sin b) : ℝ) : ℂ) * Complex.I) =
      (((Real.sin a / Real.sin b : ℝ) : ℂ)) := by
  -- Cancel `I` first, then simplify the remaining real quotient.
  have h2 : (2 * Real.sin b : ℝ) ≠ 0 := mul_ne_zero two_ne_zero hb
  have hB : ((((2 * Real.sin b) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast h2
  calc
    ((((2 * Real.sin a) : ℝ) : ℂ) * Complex.I) /
        ((((2 * Real.sin b) : ℝ) : ℂ) * Complex.I)
        = ((((2 * Real.sin a) : ℝ) : ℂ)) / ((((2 * Real.sin b) : ℝ) : ℂ)) := by
            field_simp [hB, Complex.I_ne_zero]
    _ = (((2 * Real.sin a) / (2 * Real.sin b) : ℝ) : ℂ) := by
          norm_cast
    _ = (((Real.sin a / Real.sin b : ℝ) : ℂ)) := by
          congr 1
          field_simp [h2]

/-- Helper for Exercise 9: dividing the two half-angle exponentials produces the midpoint
exponential factor. -/
lemma exp_half_ratio_eq_midpoint (x : ℝ) (n : ℕ) :
    Complex.exp (((n + 1) * x) / 2 * Complex.I) / Complex.exp (x / 2 * Complex.I) =
      Complex.exp (n * x / 2 * Complex.I) := by
  -- Multiply back by the nonvanishing denominator and combine the exponents.
  apply (div_eq_iff (Complex.exp_ne_zero _)).2
  calc
    Complex.exp (((n + 1) * x) / 2 * Complex.I)
        = Complex.exp (n * x / 2 * Complex.I + x / 2 * Complex.I) := by
            congr 1
            ring
    _ = Complex.exp (n * x / 2 * Complex.I) * Complex.exp (x / 2 * Complex.I) := by
          rw [Complex.exp_add]

/-- Helper for Exercise 9: after simplifying the geometric-series quotient with the half-angle
factorization, the complex sum becomes a real scalar times the midpoint exponential. -/
lemma sum_range_exp_arith_progression_eq_sin_ratio_mul_exp_midpoint
    (x y : ℝ) (n : ℕ) (hx : Real.sin (x / 2) ≠ 0) :
    (∑ p ∈ range (n + 1), Complex.exp ((p * x + y) * Complex.I)) =
      (((Real.sin ((n + 1) * x / 2) / Real.sin (x / 2) : ℝ) : ℂ)) *
        Complex.exp ((n * x / 2 + y) * Complex.I) := by
  -- Route correction: keep the textbook complex-geometric route, then rewrite the quotient once
  -- into the midpoint form instead of duplicating the trigonometric algebra in the final theorems.
  have hq : Complex.exp (x * Complex.I) ≠ 1 :=
    exp_mul_I_ne_one_of_sin_half_ne_zero x hx
  have hpow :
      (Complex.exp (x * Complex.I)) ^ (n + 1) =
        Complex.exp (((n + 1) * x) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hnum :
      Complex.exp ((n + 1) * x * Complex.I) - 1 =
        Complex.exp (((n + 1) * x) / 2 * Complex.I) *
          ((((2 * Real.sin (((n + 1) * x) / 2)) : ℝ) : ℂ) * Complex.I) := by
    simpa [mul_assoc] using exp_mul_I_sub_one_eq_exp_half_mul_two_sin_half ((n + 1) * x)
  have hden :
      Complex.exp (x * Complex.I) - 1 =
        Complex.exp (x / 2 * Complex.I) * ((((2 * Real.sin (x / 2)) : ℝ) : ℂ) * Complex.I) := by
    simpa using exp_mul_I_sub_one_eq_exp_half_mul_two_sin_half x
  calc
    (∑ p ∈ range (n + 1), Complex.exp ((p * x + y) * Complex.I))
        = Complex.exp (y * Complex.I) *
            ((Complex.exp (((n + 1) * x) * Complex.I) - 1) /
              (Complex.exp (x * Complex.I) - 1)) := by
              rw [sum_range_exp_arith_progression_eq_geom x y n hq, hpow]
    _ = Complex.exp (y * Complex.I) *
          ((Complex.exp (((n + 1) * x) / 2 * Complex.I) /
              Complex.exp (x / 2 * Complex.I)) *
            (((((2 * Real.sin (((n + 1) * x) / 2)) : ℝ) : ℂ) * Complex.I) /
              ((((2 * Real.sin (x / 2)) : ℝ) : ℂ) * Complex.I))) := by
          rw [hnum, hden, mul_div_mul_comm]
    _ = Complex.exp (y * Complex.I) *
          (Complex.exp (n * x / 2 * Complex.I) *
            (((Real.sin ((n + 1) * x / 2) / Real.sin (x / 2) : ℝ) : ℂ))) := by
          rw [exp_half_ratio_eq_midpoint x n,
            sine_factor_div_eq_ratio (((n + 1) * x) / 2) (x / 2) hx]
    _ = (((Real.sin ((n + 1) * x / 2) / Real.sin (x / 2) : ℝ) : ℂ)) *
          (Complex.exp (y * Complex.I) * Complex.exp (n * x / 2 * Complex.I)) := by
          ring
    _ = (((Real.sin ((n + 1) * x / 2) / Real.sin (x / 2) : ℝ) : ℂ)) *
          Complex.exp ((n * x / 2 + y) * Complex.I) := by
          rw [← Complex.exp_add]
          congr 1
          ring

/-- Exercise 9 (1): if `sin (x / 2)` is nonzero, the finite arithmetic progression sum
`∑_{0 ≤ p ≤ n} sin (p x + y)` has the usual closed form obtained from the geometric series for
`exp (I * (p x + y))`. -/
-- Proof sketch: factor the complex exponential sum into `Complex.exp (y * Complex.I)` times a
-- geometric series with ratio `Complex.exp (x * Complex.I)`, apply `geom_sum_eq`, simplify with
-- the half-angle identity for `exp (t * Complex.I) - 1`, then take imaginary parts using
-- `Complex.exp_mul_I`.
theorem sum_range_sin_arith_progression
    (x y : ℝ) (n : ℕ) (hx : Real.sin (x / 2) ≠ 0) :
    (∑ p ∈ range (n + 1), Real.sin (p * x + y)) =
      Real.sin (n * x / 2 + y) * Real.sin ((n + 1) * x / 2) /
        Real.sin (x / 2) := by
  -- Take imaginary parts of the shared complex closed form.
  set r : ℝ := Real.sin ((n + 1) * x / 2) / Real.sin (x / 2)
  have hsum :
      (∑ p ∈ range (n + 1), Complex.exp ((p * x + y) * Complex.I)) =
        (r : ℂ) * Complex.exp ((n * x / 2 + y) * Complex.I) := by
    simpa [r] using sum_range_exp_arith_progression_eq_sin_ratio_mul_exp_midpoint x y n hx
  have him := congrArg Complex.im hsum
  have hsummand :
      ∀ p : ℕ, (Complex.exp ((p * x + y) * Complex.I)).im = Real.sin (p * x + y) := by
    intro p
    simpa using Complex.exp_ofReal_mul_I_im (p * x + y)
  have hmid :
      (Complex.exp ((n * x / 2 + y) * Complex.I)).im = Real.sin (n * x / 2 + y) := by
    simpa using Complex.exp_ofReal_mul_I_im (n * x / 2 + y)
  have him' :
      (∑ p ∈ range (n + 1), Real.sin (p * x + y)) = r * Real.sin (n * x / 2 + y) := by
    simpa [Complex.im_sum, Complex.im_ofReal_mul, hsummand, hmid] using him
  simpa [r, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using him'

/-- Exercise 9 (2): if `sin (x / 2)` is nonzero, the finite arithmetic progression sum
`∑_{0 ≤ p ≤ n} cos (p x + y)` has the usual closed form obtained from the geometric series for
`exp (I * (p x + y))`. -/
-- Proof sketch: use the same geometric-series reduction via `geom_sum_eq` as in the sine case and
-- then take real parts using `Complex.exp_mul_I`.
theorem sum_range_cos_arith_progression
    (x y : ℝ) (n : ℕ) (hx : Real.sin (x / 2) ≠ 0) :
    (∑ p ∈ range (n + 1), Real.cos (p * x + y)) =
      Real.cos (n * x / 2 + y) * Real.sin ((n + 1) * x / 2) /
        Real.sin (x / 2) := by
  -- Take real parts of the same complex closed form used for the sine sum.
  set r : ℝ := Real.sin ((n + 1) * x / 2) / Real.sin (x / 2)
  have hsum :
      (∑ p ∈ range (n + 1), Complex.exp ((p * x + y) * Complex.I)) =
        (r : ℂ) * Complex.exp ((n * x / 2 + y) * Complex.I) := by
    simpa [r] using sum_range_exp_arith_progression_eq_sin_ratio_mul_exp_midpoint x y n hx
  have hre := congrArg Complex.re hsum
  have hsummand :
      ∀ p : ℕ, (Complex.exp ((p * x + y) * Complex.I)).re = Real.cos (p * x + y) := by
    intro p
    simpa using Complex.exp_ofReal_mul_I_re (p * x + y)
  have hmid :
      (Complex.exp ((n * x / 2 + y) * Complex.I)).re = Real.cos (n * x / 2 + y) := by
    simpa using Complex.exp_ofReal_mul_I_re (n * x / 2 + y)
  have hre' :
      (∑ p ∈ range (n + 1), Real.cos (p * x + y)) = r * Real.cos (n * x / 2 + y) := by
    simpa [Complex.re_sum, Complex.re_ofReal_mul, hsummand, hmid] using hre
  simpa [r, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hre'
