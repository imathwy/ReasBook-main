import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Complex

/-- Exercise 14 (1): the squared modulus of `sin (x + iy)` is `sin^2 x + sinh^2 y`. -/
-- Proof sketch: expand `Complex.sin (x + y * Complex.I)` via `Complex.sin_add_mul_I`,
-- compute `Complex.normSq` from the real and imaginary parts, and simplify with
-- `Real.cosh_sq` and `Real.sin_sq_add_cos_sq`.
theorem normSq_sin_add_mul_I (x y : ℝ) :
    normSq (sin (x + y * I)) = Real.sin x ^ 2 + Real.sinh y ^ 2 := by
  rw [Complex.sin_add_mul_I, Complex.normSq_apply]
  simp [Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re,
    Complex.cosh_ofReal_re, sq]
  have hs := Real.sin_sq_add_cos_sq x
  have hc := Real.cosh_sq y
  nlinarith

/-- Exercise 14 (2): the squared modulus of `cos (x + iy)` is `cos^2 x + sinh^2 y`. -/
-- Proof sketch: rewrite `Complex.cos (x + y * Complex.I)` using `Complex.cos_add_mul_I`,
-- compute the norm square from the real and imaginary parts, and simplify with
-- `Real.cosh_sq` and `Real.sin_sq_add_cos_sq`.
theorem normSq_cos_add_mul_I (x y : ℝ) :
    normSq (cos (x + y * I)) = Real.cos x ^ 2 + Real.sinh y ^ 2 := by
  rw [Complex.cos_add_mul_I, Complex.normSq_apply]
  simp [Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re,
    Complex.cosh_ofReal_re, sq]
  have hs := Real.sin_sq_add_cos_sq x
  have hc := Real.cosh_sq y
  nlinarith

/-- Exercise 14 (3): the zeros of `z ↦ sin (a z)` for nonzero real `a` are the points
`kπ / a`. -/
-- Proof sketch: apply `Complex.sin_eq_zero_iff` to `(a : ℂ) * z` and divide by `a`,
-- using `ha` to justify the rearrangement.
theorem sin_real_mul_eq_zero_iff (a : ℝ) (ha : a ≠ 0) (z : ℂ) :
    sin ((a : ℂ) * z) = 0 ↔ ∃ k : ℤ, z = (k * Real.pi / a : ℂ) := by
  have haC : (a : ℂ) ≠ 0 := by
    exact_mod_cast ha
  constructor
  · intro hz
    rcases Complex.sin_eq_zero_iff.mp hz with ⟨k, hk⟩
    refine ⟨k, (eq_div_iff haC).2 ?_⟩
    simpa [mul_comm] using hk
  · rintro ⟨k, rfl⟩
    rw [Complex.sin_eq_zero_iff]
    refine ⟨k, ?_⟩
    field_simp [haC]

/-- Exercise 14 (4): the zeros of `z ↦ cos (a z)` for nonzero real `a` are the odd
half-integral multiples of `π / a`. -/
-- Proof sketch: use `Complex.cos_eq_zero_iff` on `((a : ℂ) * z)` and divide the resulting
-- identity by `(a : ℂ)`, using `ha` to justify the rearrangement.
theorem cos_real_mul_eq_zero_iff (a : ℝ) (ha : a ≠ 0) (z : ℂ) :
    cos ((a : ℂ) * z) = 0 ↔
      ∃ k : ℤ, z = (((2 * k + 1) * Real.pi / 2) / a : ℂ) := by
  have haC : (a : ℂ) ≠ 0 := by
    exact_mod_cast ha
  constructor
  · intro hz
    rcases Complex.cos_eq_zero_iff.mp hz with ⟨k, hk⟩
    refine ⟨k, (eq_div_iff haC).2 ?_⟩
    simpa [mul_comm] using hk
  · rintro ⟨k, rfl⟩
    rw [Complex.cos_eq_zero_iff]
    refine ⟨k, ?_⟩
    field_simp [haC]

/-- Helper for Exercise 14: the cosine of a half-integral multiple of `π` vanishes. -/
-- Proof sketch: rewrite `π (n + 1 / 2)` as `nπ + π / 2` and evaluate the addition formula.
lemma cos_pi_nat_add_half (n : ℕ) :
    Real.cos (Real.pi * ((n : ℝ) + 1 / 2)) = 0 := by
  -- Expand the angle at `n * π + π / 2`, where the cosine term is zero.
  rw [show Real.pi * ((n : ℝ) + 1 / 2) = (n : ℝ) * Real.pi + Real.pi / 2 by ring]
  rw [Real.cos_add]
  simp [Real.sin_nat_mul_pi, Real.cos_nat_mul_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- Helper for Exercise 14: the square of `sin (π (n + 1 / 2))` is `1`. -/
-- Proof sketch: combine `sin^2 + cos^2 = 1` with the vanishing half-integer cosine.
lemma sin_sq_pi_nat_add_half (n : ℕ) :
    Real.sin (Real.pi * ((n : ℝ) + 1 / 2)) ^ 2 = 1 := by
  -- Reduce the sine square to the Pythagorean identity at a half-integer multiple of `π`.
  have hcos : Real.cos (Real.pi * ((n : ℝ) + 1 / 2)) = 0 := cos_pi_nat_add_half n
  have hsc := Real.sin_sq_add_cos_sq (Real.pi * ((n : ℝ) + 1 / 2))
  nlinarith

/-- Helper for Exercise 14: the denominator on the vertical half-integer line has norm
`cosh (π y)`. -/
-- Proof sketch: compute the squared norm with `normSq_sin_add_mul_I`, use the half-integer
-- sine evaluation, and compare nonnegative squares.
lemma norm_sin_pi_vertical_half_integer (n : ℕ) (y : ℝ) :
    ‖Complex.sin (Real.pi * ((n : ℂ) + (1 / 2 : ℂ) + y * Complex.I))‖ =
      Real.cosh (Real.pi * y) := by
  -- Compare nonnegative quantities by identifying their squares.
  rw [← sq_eq_sq₀ (norm_nonneg _) (Real.cosh_pos _).le]
  have hsq :
      ‖Complex.sin (Real.pi * ((n : ℂ) + (1 / 2 : ℂ) + y * Complex.I))‖ ^ 2 =
        Real.sin (Real.pi * ((n : ℝ) + 1 / 2)) ^ 2 + Real.sinh (Real.pi * y) ^ 2 := by
    -- Normalize the complex argument to the form `x + t I`.
    simpa [Complex.sq_norm, mul_add, add_mul, mul_assoc, add_assoc, add_left_comm, add_comm] using
      (normSq_sin_add_mul_I (Real.pi * ((n : ℝ) + 1 / 2)) (Real.pi * y))
  have hsin : Real.sin (Real.pi * ((n : ℝ) + 1 / 2)) ^ 2 = 1 := sin_sq_pi_nat_add_half n
  have hcosh := Real.cosh_sq (Real.pi * y)
  -- The square identity becomes the defining relation `cosh^2 = 1 + sinh^2`.
  nlinarith

/-- Helper for Exercise 14: `‖sin (x + t i)‖` is bounded above by `cosh t`. -/
-- Proof sketch: square both sides and use `normSq_sin_add_mul_I` together with
-- `sin^2 x ≤ 1`.
lemma norm_sin_add_mul_I_le_cosh (x t : ℝ) :
    ‖Complex.sin (x + t * Complex.I)‖ ≤ Real.cosh t := by
  -- It is enough to compare squares because both sides are nonnegative.
  rw [← sq_le_sq₀ (norm_nonneg _) (Real.cosh_pos _).le]
  have hsq :
      ‖Complex.sin (x + t * Complex.I)‖ ^ 2 = Real.sin x ^ 2 + Real.sinh t ^ 2 := by
    simpa [Complex.sq_norm] using (normSq_sin_add_mul_I x t)
  have hcosh := Real.cosh_sq t
  have hsin := Real.sin_sq_le_one x
  -- The numerator square is at most `1 + sinh^2 t = cosh^2 t`.
  nlinarith

/-- Helper for Exercise 14: when `t ≥ 0`, the hyperbolic sine controls `‖sin (x + t i)‖`
from below. -/
-- Proof sketch: square both sides, discard the nonnegative `sin^2 x` term, and use the
-- nonnegativity of `sinh t`.
lemma sinh_le_norm_sin_add_mul_I (x t : ℝ) (ht : 0 ≤ t) :
    Real.sinh t ≤ ‖Complex.sin (x + t * Complex.I)‖ := by
  -- Compare nonnegative squares after isolating the explicit norm-square formula.
  rw [← sq_le_sq₀ (Real.sinh_nonneg_iff.mpr ht) (norm_nonneg _)]
  have hsq :
      ‖Complex.sin (x + t * Complex.I)‖ ^ 2 = Real.sin x ^ 2 + Real.sinh t ^ 2 := by
    simpa [Complex.sq_norm] using (normSq_sin_add_mul_I x t)
  have hsin_nonneg : 0 ≤ Real.sin x ^ 2 := sq_nonneg _
  -- The square of the norm dominates the square of `sinh t`.
  nlinarith

/-- Helper for Exercise 14: `sinh (π (n + 1 / 2))` is positive. -/
-- Proof sketch: the argument `π (n + 1 / 2)` is positive, so `Real.sinh_pos_iff` applies.
lemma sinh_pi_nat_add_half_pos (n : ℕ) :
    0 < Real.sinh (Real.pi * ((n : ℝ) + 1 / 2)) := by
  -- Positivity of the half-integer multiple of `π` transfers through `sinh`.
  rw [Real.sinh_pos_iff]
  positivity

/-- Exercise 14 (5): on the vertical half-integer line `z = n + 1 / 2 + iy`, the quotient
`sin (a z) / sin (π z)` is bounded by `cosh (a y) / cosh (π y)`. -/
-- Proof sketch: evaluate `Complex.sin` at `z = n + 1 / 2 + y * Complex.I` using the addition
-- formulas, simplify `sin (π z)` on a half-integer vertical line, and compare the resulting
-- norms with the hyperbolic expressions.
theorem norm_sin_real_mul_div_sin_pi_le_cosh_ratio_vertical_half_integer
    (a y : ℝ) (n : ℕ) :
    ‖sin ((a : ℂ) * ((n : ℂ) + (1 / 2 : ℂ) + y * I)) /
        sin (Real.pi * ((n : ℂ) + (1 / 2 : ℂ) + y * I))‖
      ≤ Real.cosh (a * y) / Real.cosh (Real.pi * y) := by
  -- Rewrite the quotient norm as a quotient of real norms.
  rw [norm_div, norm_sin_pi_vertical_half_integer]
  have hnum :
      ‖Complex.sin ((a : ℂ) * ((n : ℂ) + (1 / 2 : ℂ) + y * I))‖ ≤ Real.cosh (a * y) := by
    -- Normalize the numerator to the generic shape `x + t I`.
    simpa [mul_add, add_mul, mul_assoc, add_assoc, add_left_comm, add_comm] using
      (norm_sin_add_mul_I_le_cosh (a * ((n : ℝ) + 1 / 2)) (a * y))
  -- Divide the numerator bound by the positive denominator `cosh (π y)`.
  exact div_le_div_of_nonneg_right hnum (Real.cosh_pos _).le

/-- Exercise 14 (6): on the horizontal half-integer line `z = x + i (n + 1 / 2)`, the quotient
`sin (a z) / sin (π z)` is bounded by
`cosh (a (n + 1 / 2)) / sinh (π (n + 1 / 2))`. -/
-- Proof sketch: expand both numerator and denominator along the line
-- `z = x + ((n : ℂ) + 1 / 2) * Complex.I`, use the half-integer evaluations of the trigonometric
-- terms, and simplify the norm bound to the stated hyperbolic ratio.
theorem norm_sin_real_mul_div_sin_pi_le_cosh_ratio_horizontal_half_integer
    (a x : ℝ) (n : ℕ) :
    ‖sin ((a : ℂ) * (x + ((n : ℂ) + (1 / 2 : ℂ)) * I)) /
        sin (Real.pi * (x + ((n : ℂ) + (1 / 2 : ℂ)) * I))‖
      ≤ Real.cosh (a * ((n : ℝ) + 1 / 2)) / Real.sinh (Real.pi * ((n : ℝ) + 1 / 2)) := by
  -- Rewrite the quotient norm and estimate numerator and denominator separately.
  rw [norm_div]
  have hnum :
      ‖Complex.sin ((a : ℂ) * (x + ((n : ℂ) + (1 / 2 : ℂ)) * I))‖
        ≤ Real.cosh (a * ((n : ℝ) + 1 / 2)) := by
    -- Normalize the numerator to `x' + t I` and apply the generic upper bound.
    simpa [mul_add, add_mul, mul_assoc, add_assoc, add_left_comm, add_comm] using
      (norm_sin_add_mul_I_le_cosh (a * x) (a * ((n : ℝ) + 1 / 2)))
  have hden :
      Real.sinh (Real.pi * ((n : ℝ) + 1 / 2))
        ≤ ‖Complex.sin (Real.pi * (x + ((n : ℂ) + (1 / 2 : ℂ)) * I))‖ := by
    -- The denominator lies on a horizontal half-integer line with positive imaginary part.
    simpa [mul_add, add_mul, mul_assoc, add_assoc, add_left_comm, add_comm] using
      (sinh_le_norm_sin_add_mul_I (Real.pi * x) (Real.pi * ((n : ℝ) + 1 / 2))
        (by positivity))
  have hcosh_nonneg : 0 ≤ Real.cosh (a * ((n : ℝ) + 1 / 2)) := (Real.cosh_pos _).le
  have hsinh_pos : 0 < Real.sinh (Real.pi * ((n : ℝ) + 1 / 2)) := sinh_pi_nat_add_half_pos n
  have hinv :
      ‖Complex.sin (Real.pi * (x + ((n : ℂ) + (1 / 2 : ℂ)) * I))‖⁻¹
        ≤ (Real.sinh (Real.pi * ((n : ℝ) + 1 / 2)))⁻¹ := by
    -- Larger positive denominators give smaller reciprocals.
    simpa [one_div] using one_div_le_one_div_of_le hsinh_pos hden
  calc
    ‖Complex.sin ((a : ℂ) * (x + ((n : ℂ) + (1 / 2 : ℂ)) * I))‖ /
        ‖Complex.sin (Real.pi * (x + ((n : ℂ) + (1 / 2 : ℂ)) * I))‖
      ≤ Real.cosh (a * ((n : ℝ) + 1 / 2)) /
          ‖Complex.sin (Real.pi * (x + ((n : ℂ) + (1 / 2 : ℂ)) * I))‖ := by
        exact div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ Real.cosh (a * ((n : ℝ) + 1 / 2)) / Real.sinh (Real.pi * ((n : ℝ) + 1 / 2)) := by
      -- After inverting the denominator bound, multiply by the nonnegative numerator bound.
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv hcosh_nonneg
