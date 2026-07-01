import Mathlib
import cartan.II.section05.«0034_Example_II_1_extra_21»
import cartan.III.section11.«0003_Theorem_III_5_extra_2»

open Complex MeasureTheory
open scoped Real

noncomputable section

/-- Helper for Exercise 22: replacing `a` by `|a|` leaves the real integral unchanged because the
denominator depends on `a` only through the even function `cosh`. -/
lemma exercise22_integral_abs_parameter (a v : ℝ) :
    ∫ x in Set.Ioi (0 : ℝ), Real.cos (v * x) / (Real.cosh x + Real.cosh a) ∂volume =
      ∫ x in Set.Ioi (0 : ℝ), Real.cos (v * x) / (Real.cosh x + Real.cosh |a|) ∂volume := by
  -- Rewrite the integrand pointwise using the evenness of `cosh`.
  refine integral_congr_ae ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  rw [Real.cosh_abs]

/-- Helper for Exercise 22: the closed-form answer is unchanged when `a` is replaced by `|a|`,
because both `sin (v a)` and `sinh a` change sign together on the negative branch. -/
lemma exercise22_rhs_abs_parameter {a v : ℝ} (ha : a ≠ 0) :
    Real.pi * Real.sin (v * a) / (Real.sinh (Real.pi * v) * Real.sinh a) =
      Real.pi * Real.sin (v * |a|) / (Real.sinh (Real.pi * v) * Real.sinh |a|) := by
  by_cases hlt : a < 0
  · -- On the negative branch, `|a| = -a`, so the numerator and denominator pick up the same sign.
    rw [abs_of_neg hlt, mul_neg, Real.sin_neg, Real.sinh_neg]
    simp [div_eq_mul_inv, mul_assoc, mul_comm]
  · -- The remaining nonnegative branch is actually positive because `a = 0` is excluded.
    have hpos : 0 < a := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm ha)
    rw [abs_of_pos hpos]

/-- Helper for Exercise 22: replacing `v` by `|v|` leaves the real integral unchanged because
`cos` is even in its argument. -/
lemma exercise22_integral_abs_frequency (a v : ℝ) :
    ∫ x in Set.Ioi (0 : ℝ), Real.cos (v * x) / (Real.cosh x + Real.cosh a) ∂volume =
      ∫ x in Set.Ioi (0 : ℝ), Real.cos (|v| * x) / (Real.cosh x + Real.cosh a) ∂volume := by
  by_cases hlt : v < 0
  · -- On the negative branch, `|v| = -v`, and the cosine kernel is unchanged by sign reversal.
    rw [abs_of_neg hlt]
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    simp [neg_mul, Real.cos_neg]
  · -- The nonnegative branch is tautological because `|v| = v`.
    have hnonneg : 0 ≤ v := le_of_not_gt hlt
    rw [abs_of_nonneg hnonneg]

/-- Helper for Exercise 22: the closed-form expression is unchanged when `v` is replaced by `|v|`,
because both `sin (v a)` and `sinh (π v)` are odd in `v`. -/
lemma exercise22_rhs_abs_frequency {a v : ℝ} :
    Real.pi * Real.sin (v * a) / (Real.sinh (Real.pi * v) * Real.sinh a) =
      Real.pi * Real.sin (|v| * a) / (Real.sinh (Real.pi * |v|) * Real.sinh a) := by
  by_cases hlt : v < 0
  · -- On the negative branch, the numerator and the `sinh (π v)` factor pick up the same sign.
    rw [abs_of_neg hlt, neg_mul, Real.sin_neg]
    have hpi : Real.pi * (-v) = -(Real.pi * v) := by ring
    rw [hpi, Real.sinh_neg]
    simp [div_eq_mul_inv, mul_assoc, mul_comm]
  · -- The nonnegative branch is tautological because `|v| = v`.
    have hnonneg : 0 ≤ v := le_of_not_gt hlt
    rw [abs_of_nonneg hnonneg]

/-- Helper for Exercise 22: the source rectangle proof uses this meromorphic kernel. -/
abbrev exercise22Kernel (a v : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * ((v : ℂ) * z)) / (Complex.cosh z + Real.cosh a)

/-- Helper for Exercise 22: shifting the kernel by `2π i` multiplies it by `e^{-2π v}`. -/
lemma exercise22Kernel_add_two_pi_I (a v : ℝ) (z : ℂ) :
    exercise22Kernel a v (z + 2 * Real.pi * Complex.I) =
      Real.exp (-2 * Real.pi * v) * exercise22Kernel a v z := by
  -- Separate the exponential shift in the numerator from the `2π i`-periodicity of `cosh`.
  have hconst :
      Complex.I * ((v : ℂ) * (2 * Real.pi * Complex.I)) =
        ((-(2 * Real.pi * v) : ℝ) : ℂ) := by
    calc
      Complex.I * ((v : ℂ) * (2 * Real.pi * Complex.I)) =
          ((v : ℂ) * (2 * Real.pi)) * (Complex.I * Complex.I) := by
        ring
      _ = -((v : ℂ) * (2 * Real.pi)) := by simp [Complex.I_sq]
      _ = -(((2 * Real.pi * v : ℝ) : ℂ)) := by
        simpa [Complex.ofReal_mul, mul_assoc, mul_comm, mul_left_comm]
      _ = ((-(2 * Real.pi * v) : ℝ) : ℂ) := by
        simp
  have hexp :
      Complex.exp (Complex.I * ((v : ℂ) * (z + 2 * Real.pi * Complex.I))) =
        Real.exp (-2 * Real.pi * v) * Complex.exp (Complex.I * ((v : ℂ) * z)) := by
    calc
      Complex.exp (Complex.I * ((v : ℂ) * (z + 2 * Real.pi * Complex.I))) =
          Complex.exp
            (Complex.I * ((v : ℂ) * z) + Complex.I * ((v : ℂ) * (2 * Real.pi * Complex.I))) := by
        congr 1
        ring
      _ = Complex.exp (Complex.I * ((v : ℂ) * z)) *
            Complex.exp (Complex.I * ((v : ℂ) * (2 * Real.pi * Complex.I))) := by
        rw [Complex.exp_add]
      _ = Complex.exp (Complex.I * ((v : ℂ) * z)) * Real.exp (-2 * Real.pi * v) := by
        rw [hconst]
        simp
      _ = Real.exp (-2 * Real.pi * v) * Complex.exp (Complex.I * ((v : ℂ) * z)) := by
        ring
  -- After rewriting the numerator and denominator separately, only scalar reassociation remains.
  rw [exercise22Kernel, exercise22Kernel, hexp, Complex.cosh_periodic z]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Exercise 22: membership in a closed complex ball controls both coordinate
deviations by the radius. -/
lemma exercise22_coord_abs_sub_le_of_mem_closedBall {c z : ℂ} {ρ : ℝ}
    (hz : z ∈ Metric.closedBall c ρ) :
    |z.re - c.re| ≤ ρ ∧ |z.im - c.im| ≤ ρ := by
  -- Each coordinate difference is bounded by the ambient norm, hence by the closed-ball radius.
  have hdist : dist z c ≤ ρ := by
    simpa [Metric.mem_closedBall, dist_comm] using hz
  have hnorm : ‖z - c‖ ≤ ρ := by
    simpa [dist_eq_norm] using hdist
  constructor
  · exact le_trans (by simpa [sub_re] using (Complex.abs_re_le_norm (z - c))) hnorm
  · exact le_trans (by simpa [sub_im] using (Complex.abs_im_le_norm (z - c))) hnorm

/-- Helper for Exercise 22: `a + π i` is a zero of the denominator from the source strip. -/
lemma exercise22_denominator_zero_at_pos_pole (a : ℝ) :
    Complex.cosh ((a : ℂ) + Real.pi * Complex.I) + Real.cosh a = 0 := by
  -- Shift by `π i`, where `cosh` changes sign.
  have h :
      Complex.cosh ((a : ℂ) + Real.pi * Complex.I) = -((Real.cosh a : ℝ) : ℂ) := by
    simpa using (Complex.cosh_add_pi_mul_I (a : ℂ))
  exact eq_neg_iff_add_eq_zero.mp h

/-- Helper for Exercise 22: `-a + π i` is the second zero of the denominator in the source strip. -/
lemma exercise22_denominator_zero_at_neg_pole (a : ℝ) :
    Complex.cosh (-(a : ℂ) + Real.pi * Complex.I) + Real.cosh a = 0 := by
  -- The same `π i` shift works after using the evenness of `cosh`.
  have h :
      Complex.cosh (-(a : ℂ) + Real.pi * Complex.I) = -((Real.cosh a : ℝ) : ℂ) := by
    simpa using (Complex.cosh_add_pi_mul_I (-(a : ℂ)))
  exact eq_neg_iff_add_eq_zero.mp h

/-- Helper for Exercise 22: the derivative factor at `a + π i` is `-sinh a`. -/
lemma exercise22_sinh_at_pos_pole (a : ℝ) :
    Complex.sinh ((a : ℂ) + Real.pi * Complex.I) = -((Real.sinh a : ℝ) : ℂ) := by
  -- This is the `π i` antiperiodicity of `sinh`.
  simpa using (Complex.sinh_add_pi_mul_I (a : ℂ))

/-- Helper for Exercise 22: the derivative factor at `-a + π i` is `sinh a`. -/
lemma exercise22_sinh_at_neg_pole (a : ℝ) :
    Complex.sinh (-(a : ℂ) + Real.pi * Complex.I) = ((Real.sinh a : ℝ) : ℂ) := by
  -- Combining the `π i` shift with oddness of `sinh` removes the minus sign.
    simpa using (Complex.sinh_add_pi_mul_I (-(a : ℂ)))

/-- Helper for Exercise 22: the denominator factors through the positive pole as
`(z - z₊) * dslope cosh z₊ z`. -/
lemma exercise22_denominator_eq_sub_pos_pole_mul_dslope (a : ℝ) (z : ℂ) :
    Complex.cosh z + Real.cosh a =
      (z - ((a : ℂ) + Real.pi * Complex.I)) *
        dslope Complex.cosh ((a : ℂ) + Real.pi * Complex.I) z := by
  -- Replace `+ cosh a` by subtraction of the pole value, then use the divided-difference identity.
  have hpole :
      ((Real.cosh a : ℝ) : ℂ) = -Complex.cosh ((a : ℂ) + Real.pi * Complex.I) := by
    exact eq_neg_of_add_eq_zero_right (exercise22_denominator_zero_at_pos_pole a)
  calc
    Complex.cosh z + Real.cosh a =
        Complex.cosh z + (-Complex.cosh ((a : ℂ) + Real.pi * Complex.I)) := by
      rw [hpole]
    _ = Complex.cosh z - Complex.cosh ((a : ℂ) + Real.pi * Complex.I) := by
      ring
    _ =
        (z - ((a : ℂ) + Real.pi * Complex.I)) *
          dslope Complex.cosh ((a : ℂ) + Real.pi * Complex.I) z := by
      simpa using (sub_smul_dslope Complex.cosh ((a : ℂ) + Real.pi * Complex.I) z).symm

/-- Helper for Exercise 22: the denominator factors through the negative pole as
`(z - z₋) * dslope cosh z₋ z`. -/
lemma exercise22_denominator_eq_sub_neg_pole_mul_dslope (a : ℝ) (z : ℂ) :
    Complex.cosh z + Real.cosh a =
      (z - (-(a : ℂ) + Real.pi * Complex.I)) *
        dslope Complex.cosh (-(a : ℂ) + Real.pi * Complex.I) z := by
  -- The same divided-difference factorization works at the second strip pole.
  have hpole :
      ((Real.cosh a : ℝ) : ℂ) = -Complex.cosh (-(a : ℂ) + Real.pi * Complex.I) := by
    exact eq_neg_of_add_eq_zero_right (exercise22_denominator_zero_at_neg_pole a)
  calc
    Complex.cosh z + Real.cosh a =
        Complex.cosh z + (-Complex.cosh (-(a : ℂ) + Real.pi * Complex.I)) := by
      rw [hpole]
    _ = Complex.cosh z - Complex.cosh (-(a : ℂ) + Real.pi * Complex.I) := by
      ring
    _ =
        (z - (-(a : ℂ) + Real.pi * Complex.I)) *
          dslope Complex.cosh (-(a : ℂ) + Real.pi * Complex.I) z := by
      simpa using (sub_smul_dslope Complex.cosh (-(a : ℂ) + Real.pi * Complex.I) z).symm

/-- Helper for Exercise 22: the exponential numerator at `a + π i` splits into the decaying
vertical factor `e^{-π v}` times the horizontal oscillation `e^{i v a}`. -/
lemma exercise22_exp_at_pos_pole (a v : ℝ) :
    Complex.exp (Complex.I * ((v : ℂ) * ((a : ℂ) + Real.pi * Complex.I))) =
      Real.exp (-Real.pi * v) * Complex.exp (Complex.I * ((v : ℂ) * a)) := by
  -- Expand the translated pole into its real and imaginary pieces before separating exponentials.
  have hconst :
      Complex.I * ((v : ℂ) * (Real.pi * Complex.I)) = ((-(Real.pi * v) : ℝ) : ℂ) := by
    calc
      Complex.I * ((v : ℂ) * (Real.pi * Complex.I)) =
          ((v : ℂ) * Real.pi) * (Complex.I * Complex.I) := by
        ring
      _ = -((v : ℂ) * Real.pi) := by simp [Complex.I_sq]
      _ = -(((Real.pi * v : ℝ) : ℂ)) := by
        simp [Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc]
      _ = ((-(Real.pi * v) : ℝ) : ℂ) := by simp
  calc
    Complex.exp (Complex.I * ((v : ℂ) * ((a : ℂ) + Real.pi * Complex.I))) =
        Complex.exp
          (Complex.I * ((v : ℂ) * (a : ℂ)) + Complex.I * ((v : ℂ) * (Real.pi * Complex.I))) := by
      congr 1
      ring
    _ = Complex.exp (Complex.I * ((v : ℂ) * (a : ℂ))) *
          Complex.exp (Complex.I * ((v : ℂ) * (Real.pi * Complex.I))) := by
      rw [Complex.exp_add]
    _ = Complex.exp (Complex.I * ((v : ℂ) * (a : ℂ))) * Real.exp (-Real.pi * v) := by
      rw [hconst]
      simp
    _ = Real.exp (-Real.pi * v) * Complex.exp (Complex.I * ((v : ℂ) * a)) := by
      simp [mul_comm]

/-- Helper for Exercise 22: the exponential numerator at `-a + π i` splits into the same
decaying vertical factor `e^{-π v}` and the conjugate oscillation `e^{-i v a}`. -/
lemma exercise22_exp_at_neg_pole (a v : ℝ) :
    Complex.exp (Complex.I * ((v : ℂ) * (-(a : ℂ) + Real.pi * Complex.I))) =
      Real.exp (-Real.pi * v) * Complex.exp (-Complex.I * ((v : ℂ) * a)) := by
  -- The same vertical translation appears, while the real part contributes the opposite phase.
  have hconst :
      Complex.I * ((v : ℂ) * (Real.pi * Complex.I)) = ((-(Real.pi * v) : ℝ) : ℂ) := by
    calc
      Complex.I * ((v : ℂ) * (Real.pi * Complex.I)) =
          ((v : ℂ) * Real.pi) * (Complex.I * Complex.I) := by
        ring
      _ = -((v : ℂ) * Real.pi) := by simp [Complex.I_sq]
      _ = -(((Real.pi * v : ℝ) : ℂ)) := by
        simp [Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc]
      _ = ((-(Real.pi * v) : ℝ) : ℂ) := by simp
  calc
    Complex.exp (Complex.I * ((v : ℂ) * (-(a : ℂ) + Real.pi * Complex.I))) =
        Complex.exp
          (Complex.I * ((v : ℂ) * (-(a : ℂ))) +
            Complex.I * ((v : ℂ) * (Real.pi * Complex.I))) := by
      congr 1
      ring
    _ = Complex.exp (Complex.I * ((v : ℂ) * (-(a : ℂ)))) *
          Complex.exp (Complex.I * ((v : ℂ) * (Real.pi * Complex.I))) := by
      rw [Complex.exp_add]
    _ = Complex.exp (Complex.I * ((v : ℂ) * (-(a : ℂ)))) * Real.exp (-Real.pi * v) := by
      rw [hconst]
      simp
    _ = Real.exp (-Real.pi * v) * Complex.exp (Complex.I * ((v : ℂ) * (-(a : ℂ)))) := by
      ring
    _ = Real.exp (-Real.pi * v) * Complex.exp (-Complex.I * ((v : ℂ) * a)) := by
      congr 1
      ring

/-- Helper for Exercise 22: the positive pole contributes the explicit residue coefficient from the
source rectangle argument. -/
lemma exercise22_pos_pole_residue_value (a v : ℝ) :
    Complex.exp (Complex.I * ((v : ℂ) * ((a : ℂ) + Real.pi * Complex.I))) /
      Complex.sinh ((a : ℂ) + Real.pi * Complex.I) =
        -(Real.exp (-Real.pi * v) * Complex.exp (Complex.I * ((v : ℂ) * a)) / Real.sinh a) := by
  -- Evaluate the numerator and denominator separately and then normalize the remaining scalar sign.
  rw [exercise22_exp_at_pos_pole, exercise22_sinh_at_pos_pole]
  simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

/-- Helper for Exercise 22: the negative pole contributes the second explicit residue coefficient
from the source rectangle argument. -/
lemma exercise22_neg_pole_residue_value (a v : ℝ) :
    Complex.exp (Complex.I * ((v : ℂ) * (-(a : ℂ) + Real.pi * Complex.I))) /
      Complex.sinh (-(a : ℂ) + Real.pi * Complex.I) =
        Real.exp (-Real.pi * v) * Complex.exp (-Complex.I * ((v : ℂ) * a)) / Real.sinh a := by
  -- The negative pole has the same vertical decay but no extra sign in the `sinh` factor.
  simpa [exercise22_exp_at_neg_pole, exercise22_sinh_at_neg_pole]

/-- Helper for Exercise 22: the real part of `cosh z` is `cosh (Re z) cos (Im z)`. -/
lemma exercise22_cosh_re (z : ℂ) :
    (Complex.cosh z).re = Real.cosh z.re * Real.cos z.im := by
  -- Expand `z` into real and imaginary parts and read off the real coordinate of `cosh`.
  have hzdecomp : z = (z.re : ℂ) + Complex.I * (z.im : ℂ) := by
    simpa [mul_comm] using (Complex.re_add_im z).symm
  have hdecomp :
      Complex.cosh z =
        (Real.cosh z.re * Real.cos z.im : ℝ) +
          (Real.sinh z.re * Real.sin z.im : ℝ) * Complex.I := by
    rw [hzdecomp, Complex.cosh_add]
    have hcosh_imag : Complex.cosh (Complex.I * (z.im : ℂ)) = Real.cos z.im := by
      simpa [mul_comm] using (Complex.cosh_mul_I (z.im : ℂ))
    have hsinh_imag : Complex.sinh (Complex.I * (z.im : ℂ)) = Real.sin z.im * Complex.I := by
      simpa [mul_comm] using (Complex.sinh_mul_I (z.im : ℂ))
    rw [hcosh_imag, hsinh_imag]
    simp [mul_assoc, mul_comm, mul_left_comm]
  -- Taking real parts of the explicit decomposition gives the coordinate formula.
  simpa using congrArg Complex.re hdecomp

/-- Helper for Exercise 22: the imaginary part of `cosh z` is `sinh (Re z) sin (Im z)`. -/
lemma exercise22_cosh_im (z : ℂ) :
    (Complex.cosh z).im = Real.sinh z.re * Real.sin z.im := by
  -- Expand `z` into real and imaginary parts and read off the imaginary coordinate of `cosh`.
  have hzdecomp : z = (z.re : ℂ) + Complex.I * (z.im : ℂ) := by
    simpa [mul_comm] using (Complex.re_add_im z).symm
  have hdecomp :
      Complex.cosh z =
        (Real.cosh z.re * Real.cos z.im : ℝ) +
          (Real.sinh z.re * Real.sin z.im : ℝ) * Complex.I := by
    rw [hzdecomp, Complex.cosh_add]
    have hcosh_imag : Complex.cosh (Complex.I * (z.im : ℂ)) = Real.cos z.im := by
      simpa [mul_comm] using (Complex.cosh_mul_I (z.im : ℂ))
    have hsinh_imag : Complex.sinh (Complex.I * (z.im : ℂ)) = Real.sin z.im * Complex.I := by
      simpa [mul_comm] using (Complex.sinh_mul_I (z.im : ℂ))
    rw [hcosh_imag, hsinh_imag]
    simp [mul_assoc, mul_comm, mul_left_comm]
  -- Taking imaginary parts of the explicit decomposition gives the coordinate formula.
  simpa using congrArg Complex.im hdecomp

/-- Helper for Exercise 22: inside the strip `-(π/2) < Im z < 5π/2`, the denominator vanishes
exactly at the two poles from the source rectangle argument. -/
lemma exercise22_strip_poles {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : z ∈ {w : ℂ | -(Real.pi / 2) < w.im ∧ w.im < 5 * Real.pi / 2}) :
    (Complex.cosh z + Real.cosh a = 0 ↔
      z = (a : ℂ) + Real.pi * Complex.I ∨ z = -(a : ℂ) + Real.pi * Complex.I) := by
  constructor
  · intro hzero
    -- Compare real and imaginary parts of the denominator exactly as in the source strip argument.
    have hre : Real.cosh z.re * Real.cos z.im + Real.cosh a = 0 := by
      simpa [exercise22_cosh_re] using congrArg Complex.re hzero
    have him : Real.sinh z.re * Real.sin z.im = 0 := by
      simpa [exercise22_cosh_im] using congrArg Complex.im hzero
    have hcos_neg : Real.cos z.im < 0 := by
      have hcosh_nonneg : 0 ≤ Real.cosh z.re := (Real.cosh_pos _).le
      by_contra hnonneg
      have hcos_nonneg : 0 ≤ Real.cos z.im := le_of_not_gt hnonneg
      have hmul_nonneg : 0 ≤ Real.cosh z.re * Real.cos z.im :=
        mul_nonneg hcosh_nonneg hcos_nonneg
      have hneg : -Real.cosh a < 0 := by
        nlinarith [Real.cosh_pos a]
      have hmul_eq : Real.cosh z.re * Real.cos z.im = -Real.cosh a := by
        linarith
      linarith
    have hsin : Real.sin z.im = 0 := by
      rcases mul_eq_zero.mp him with hsinh | hsin
      · have hzre_zero : z.re = 0 := (Real.sinh_eq_zero).1 hsinh
        have hcos_eq : Real.cos z.im = -Real.cosh a := by
          rw [hzre_zero, Real.cosh_zero] at hre
          linarith
        have hcosh_gt : 1 < Real.cosh a := (Real.one_lt_cosh).2 ha.ne'
        have hcos_ge : -1 ≤ Real.cos z.im := Real.neg_one_le_cos _
        linarith
      · exact hsin
    have hcos_neg_one : Real.cos z.im = -1 := by
      rcases (Real.sin_eq_zero_iff_cos_eq).1 hsin with hcos_one | hcos_neg_one
      · linarith
      · exact hcos_neg_one
    rcases (Real.cos_eq_neg_one_iff).1 hcos_neg_one with ⟨k, hk⟩
    have hk_lower : (-1 : ℝ) < k := by
      nlinarith [hz.1, hk, Real.pi_pos]
    have hk_upper : (k : ℝ) < 1 := by
      nlinarith [hz.2, hk, Real.pi_pos]
    have hk_lower_int : -1 < k := by
      exact_mod_cast hk_lower
    have hk_upper_int : k < 1 := by
      exact_mod_cast hk_upper
    have hk_zero : k = 0 := by
      omega
    have hIm : z.im = Real.pi := by
      simpa [hk_zero] using hk.symm
    have hcosh_eq : Real.cosh z.re = Real.cosh a := by
      rw [hIm, Real.cos_pi] at hre
      linarith
    have habs_le : |z.re| ≤ |a| := by
      exact (Real.cosh_le_cosh).1 <| by simpa [hcosh_eq] using le_of_eq hcosh_eq
    have habs_ge : |a| ≤ |z.re| := by
      exact (Real.cosh_le_cosh).1 <| by simpa [hcosh_eq] using ge_of_eq hcosh_eq
    have habs : |z.re| = a := by
      have habs' : |z.re| = |a| := le_antisymm habs_le habs_ge
      simpa [abs_of_pos ha] using habs'
    have hRe : z.re = a ∨ z.re = -a := by
      by_cases hzre_nonneg : 0 ≤ z.re
      · left
        rw [abs_of_nonneg hzre_nonneg] at habs
        linarith
      · right
        have hzre_neg : z.re < 0 := lt_of_not_ge hzre_nonneg
        rw [abs_of_neg hzre_neg] at habs
        linarith
    rcases hRe with hRe | hRe
    · left
      apply Complex.ext <;> simp [hRe, hIm]
    · right
      apply Complex.ext <;> simp [hRe, hIm]
  · intro hzpole
    rcases hzpole with rfl | rfl
    · simpa using exercise22_denominator_zero_at_pos_pole a
    · simpa using exercise22_denominator_zero_at_neg_pole a

/-- Helper for Exercise 22: the textbook radius
`min(a / 2, min((R - a) / 2, π / 2))` keeps both pole discs inside the height-`2π` rectangle and
separates them from each other. -/
lemma exercise22_rectangle_pole_radius_geometry {a R : ℝ} (ha : 0 < a) (hRa : a < R) :
    let K : Set ℂ := Complex.Rectangle (-R) (R + 2 * Real.pi * Complex.I)
    let D : Set ℂ := {z : ℂ | -(Real.pi / 2) < z.im ∧ z.im < 5 * Real.pi / 2}
    let zPos : ℂ := (a : ℂ) + Real.pi * Complex.I
    let zNeg : ℂ := -(a : ℂ) + Real.pi * Complex.I
    let ρ : ℝ := min (a / 2) (min ((R - a) / 2) (Real.pi / 2))
    Metric.closedBall zPos ρ ⊆ interior K ∩ D ∧
      Metric.closedBall zNeg ρ ⊆ interior K ∩ D ∧
      zNeg ∉ Metric.closedBall zPos ρ ∧
      zPos ∉ Metric.closedBall zNeg ρ := by
  -- The source rectangle uses one common radius small enough for both horizontal and vertical
  -- clearance, so we record all four geometric consequences at once.
  dsimp
  set ρ : ℝ := min (a / 2) (min ((R - a) / 2) (Real.pi / 2))
  have hρ_le_a2 : ρ ≤ a / 2 := by
    have : min (a / 2) (min ((R - a) / 2) (Real.pi / 2)) ≤ a / 2 := min_le_left _ _
    simpa [ρ] using this
  have hρ_le_Ra2 : ρ ≤ (R - a) / 2 := by
    have :
        min (a / 2) (min ((R - a) / 2) (Real.pi / 2)) ≤ (R - a) / 2 := by
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    simpa [ρ] using this
  have hρ_le_pi2 : ρ ≤ Real.pi / 2 := by
    have :
        min (a / 2) (min ((R - a) / 2) (Real.pi / 2)) ≤ Real.pi / 2 := by
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    simpa [ρ] using this
  have hρ_nonneg : 0 ≤ ρ := by
    have : 0 ≤ min (a / 2) (min ((R - a) / 2) (Real.pi / 2)) := by
      positivity
    simpa [ρ] using this
  have hrect_re : (-R : ℝ) ≤ R := by
    linarith
  have hrect_im : (0 : ℝ) ≤ 2 * Real.pi := by
    positivity
  constructor
  · intro z hz
    rcases exercise22_coord_abs_sub_le_of_mem_closedBall
        (c := (a : ℂ) + Real.pi * Complex.I) hz with ⟨hre_abs, him_abs⟩
    have hre_bounds : -ρ ≤ z.re - a ∧ z.re - a ≤ ρ := abs_le.mp <| by
      simpa [sub_re] using hre_abs
    have him_bounds : -ρ ≤ z.im - Real.pi ∧ z.im - Real.pi ≤ ρ := abs_le.mp <| by
      simpa [sub_im] using him_abs
    have hzre_lower : -R < z.re := by
      nlinarith [hre_bounds.1, hρ_le_a2, ha]
    have hzre_upper : z.re < R := by
      nlinarith [hre_bounds.2, hρ_le_Ra2, hRa]
    have hzim_lower : 0 < z.im := by
      nlinarith [him_bounds.1, hρ_le_pi2, Real.pi_pos]
    have hzim_upper : z.im < 2 * Real.pi := by
      nlinarith [him_bounds.2, hρ_le_pi2, Real.pi_pos]
    have hmemK :
        z ∈ interior (Complex.Rectangle (-R) (R + 2 * Real.pi * Complex.I)) := by
      rw [Complex.Rectangle, Complex.interior_reProdIm, Complex.mem_reProdIm]
      exact by
        simpa [Set.uIcc, interior_Icc, hrect_re, hrect_im] using
          ⟨(show z.re ∈ Set.Ioo (-R) R from ⟨hzre_lower, hzre_upper⟩),
            (show z.im ∈ Set.Ioo (0 : ℝ) (2 * Real.pi) from ⟨hzim_lower, hzim_upper⟩)⟩
    have hmemD : z ∈ {w : ℂ | -(Real.pi / 2) < w.im ∧ w.im < 5 * Real.pi / 2} := by
      constructor <;> nlinarith [hzim_lower, hzim_upper, Real.pi_pos]
    exact ⟨hmemK, hmemD⟩
  constructor
  · intro z hz
    rcases exercise22_coord_abs_sub_le_of_mem_closedBall
        (c := -(a : ℂ) + Real.pi * Complex.I) hz with ⟨hre_abs, him_abs⟩
    have hre_bounds : -ρ ≤ z.re + a ∧ z.re + a ≤ ρ := abs_le.mp <| by
      simpa [sub_re] using hre_abs
    have him_bounds : -ρ ≤ z.im - Real.pi ∧ z.im - Real.pi ≤ ρ := abs_le.mp <| by
      simpa [sub_im] using him_abs
    have hzre_lower : -R < z.re := by
      nlinarith [hre_bounds.1, hρ_le_Ra2, hRa]
    have hzre_upper : z.re < R := by
      nlinarith [hre_bounds.2, hρ_le_a2, ha]
    have hzim_lower : 0 < z.im := by
      nlinarith [him_bounds.1, hρ_le_pi2, Real.pi_pos]
    have hzim_upper : z.im < 2 * Real.pi := by
      nlinarith [him_bounds.2, hρ_le_pi2, Real.pi_pos]
    have hmemK :
        z ∈ interior (Complex.Rectangle (-R) (R + 2 * Real.pi * Complex.I)) := by
      rw [Complex.Rectangle, Complex.interior_reProdIm, Complex.mem_reProdIm]
      exact by
        simpa [Set.uIcc, interior_Icc, hrect_re, hrect_im] using
          ⟨(show z.re ∈ Set.Ioo (-R) R from ⟨hzre_lower, hzre_upper⟩),
            (show z.im ∈ Set.Ioo (0 : ℝ) (2 * Real.pi) from ⟨hzim_lower, hzim_upper⟩)⟩
    have hmemD : z ∈ {w : ℂ | -(Real.pi / 2) < w.im ∧ w.im < 5 * Real.pi / 2} := by
      constructor <;> nlinarith [hzim_lower, hzim_upper, Real.pi_pos]
    exact ⟨hmemK, hmemD⟩
  constructor
  · intro hz
    have hdistRe :
        |(((-(a : ℂ) + Real.pi * Complex.I) - ((a : ℂ) + Real.pi * Complex.I)).re)| ≤
          dist (-(a : ℂ) + Real.pi * Complex.I) ((a : ℂ) + Real.pi * Complex.I) := by
      simpa [dist_eq_norm] using
        (Complex.abs_re_le_norm
          (((-(a : ℂ) + Real.pi * Complex.I) - ((a : ℂ) + Real.pi * Complex.I))))
    have hdist : 2 * a ≤ dist (-(a : ℂ) + Real.pi * Complex.I) ((a : ℂ) + Real.pi * Complex.I) := by
      have habs : |(((-(a : ℂ) + Real.pi * Complex.I) - ((a : ℂ) + Real.pi * Complex.I)).re)| =
          2 * a := by
        have hnonpos :
            (((-(a : ℂ) + Real.pi * Complex.I) - ((a : ℂ) + Real.pi * Complex.I)).re) ≤ 0 := by
          simp [sub_re]
          linarith
        rw [abs_of_nonpos hnonpos]
        simp [sub_re]
        ring
      rw [habs] at hdistRe
      exact hdistRe
    have hzdist :
        dist (-(a : ℂ) + Real.pi * Complex.I) ((a : ℂ) + Real.pi * Complex.I) ≤ ρ := by
      simpa [Metric.mem_closedBall, dist_comm, ρ] using hz
    nlinarith [hρ_le_a2, ha, hdist, hzdist]
  · intro hz
    have hdistRe :
        |((((a : ℂ) + Real.pi * Complex.I) - (-(a : ℂ) + Real.pi * Complex.I)).re)| ≤
          dist ((a : ℂ) + Real.pi * Complex.I) (-(a : ℂ) + Real.pi * Complex.I) := by
      simpa [dist_eq_norm] using
        (Complex.abs_re_le_norm
          ((((a : ℂ) + Real.pi * Complex.I) - (-(a : ℂ) + Real.pi * Complex.I))))
    have hdist : 2 * a ≤ dist ((a : ℂ) + Real.pi * Complex.I) (-(a : ℂ) + Real.pi * Complex.I) := by
      have habs : |((((a : ℂ) + Real.pi * Complex.I) - (-(a : ℂ) + Real.pi * Complex.I)).re)| =
          2 * a := by
        have hnonneg :
            0 ≤ (((((a : ℂ) + Real.pi * Complex.I) - (-(a : ℂ) + Real.pi * Complex.I)).re)) := by
          simp [sub_re]
          linarith
        rw [abs_of_nonneg hnonneg]
        simp [sub_re]
        ring
      rw [habs] at hdistRe
      exact hdistRe
    have hzdist :
        dist ((a : ℂ) + Real.pi * Complex.I) (-(a : ℂ) + Real.pi * Complex.I) ≤ ρ := by
      simpa [Metric.mem_closedBall, dist_comm, ρ] using hz
    nlinarith [hρ_le_a2, ha, hdist, hzdist]

/-- Helper for Exercise 22: away from the two strip poles, the kernel is holomorphic on the strip
used by the source rectangle argument. -/
lemma exercise22_kernel_differentiableOn_strip_punctured
    {a v : ℝ} (ha : 0 < a) :
    DifferentiableOn ℂ (exercise22Kernel a v)
      ({z : ℂ | -(Real.pi / 2) < z.im ∧ z.im < 5 * Real.pi / 2} \
        ({(a : ℂ) + Real.pi * Complex.I, -(a : ℂ) + Real.pi * Complex.I} : Set ℂ)) := by
  intro z hz
  rcases hz with ⟨hz_strip, hz_not_pole⟩
  -- The strip classification turns the puncture condition into denominator nonvanishing.
  have hdenom_ne : Complex.cosh z + Real.cosh a ≠ 0 := by
    intro hzero
    have hz_pole := (exercise22_strip_poles ha hz_strip).1 hzero
    have hz_mem :
        z ∈ ({(a : ℂ) + Real.pi * Complex.I, -(a : ℂ) + Real.pi * Complex.I} : Set ℂ) := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hz_pole
    exact hz_not_pole hz_mem
  -- Both numerator and denominator are entire, so the quotient is holomorphic off the poles.
  have hnum :
      DifferentiableAt ℂ (fun w : ℂ => Complex.exp (Complex.I * ((v : ℂ) * w))) z := by
    fun_prop
  have hden :
      DifferentiableAt ℂ (fun w : ℂ => Complex.cosh w + Real.cosh a) z := by
    fun_prop
  -- Unfold the kernel once so the quotient rule matches the goal definitionally.
  show
    DifferentiableWithinAt ℂ
      (fun w : ℂ => Complex.exp (Complex.I * ((v : ℂ) * w)) / (Complex.cosh w + Real.cosh a))
      ({z : ℂ | -(Real.pi / 2) < z.im ∧ z.im < 5 * Real.pi / 2} \
        ({(a : ℂ) + Real.pi * Complex.I, -(a : ℂ) + Real.pi * Complex.I} : Set ℂ))
      z
  exact (hnum.div hden hdenom_ne).differentiableWithinAt

/-- Helper for Exercise 22: on the source strip with only the negative pole removed, the divided
difference factor at the positive pole never vanishes. -/
lemma exercise22_dslope_pos_ne_zero_on_strip_minus_neg_pole
    {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz :
      z ∈ {w : ℂ | -(Real.pi / 2) < w.im ∧ w.im < 5 * Real.pi / 2} \
        ({-(a : ℂ) + Real.pi * Complex.I} : Set ℂ)) :
    dslope Complex.cosh ((a : ℂ) + Real.pi * Complex.I) z ≠ 0 := by
  rcases hz with ⟨hz_strip, hz_not_neg_mem⟩
  have hz_ne_neg : z ≠ -(a : ℂ) + Real.pi * Complex.I := by
    simpa [Set.mem_singleton_iff] using hz_not_neg_mem
  by_cases hz_pos : z = (a : ℂ) + Real.pi * Complex.I
  · subst hz_pos
    -- At the center, `dslope` is the derivative `sinh`, and the source assumption `a > 0`
    -- excludes its vanishing.
    have hsinh_ne_real : Real.sinh a ≠ 0 := Real.sinh_ne_zero.2 ha.ne'
    have hsinh_ne : (((Real.sinh a : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast hsinh_ne_real
    simpa [dslope_same, Complex.deriv_cosh, exercise22_sinh_at_pos_pole] using
      neg_ne_zero.mpr hsinh_ne
  · -- Off the center, vanishing of the cofactor would force the denominator to vanish at a strip
    -- point other than the two classified poles.
    intro hdslope
    have hdenom_zero : Complex.cosh z + Real.cosh a = 0 := by
      rw [exercise22_denominator_eq_sub_pos_pole_mul_dslope, hdslope]
      simp
    rcases (exercise22_strip_poles ha hz_strip).1 hdenom_zero with hz_eq_pos | hz_eq_neg
    · exact hz_pos hz_eq_pos
    · exact hz_ne_neg hz_eq_neg

/-- Helper for Exercise 22: on the source strip with only the positive pole removed, the divided
difference factor at the negative pole never vanishes. -/
lemma exercise22_dslope_neg_ne_zero_on_strip_minus_pos_pole
    {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz :
      z ∈ {w : ℂ | -(Real.pi / 2) < w.im ∧ w.im < 5 * Real.pi / 2} \
        ({(a : ℂ) + Real.pi * Complex.I} : Set ℂ)) :
    dslope Complex.cosh (-(a : ℂ) + Real.pi * Complex.I) z ≠ 0 := by
  rcases hz with ⟨hz_strip, hz_not_pos_mem⟩
  have hz_ne_pos : z ≠ (a : ℂ) + Real.pi * Complex.I := by
    simpa [Set.mem_singleton_iff] using hz_not_pos_mem
  by_cases hz_neg : z = -(a : ℂ) + Real.pi * Complex.I
  · subst hz_neg
    -- At the center, `dslope` is again the derivative `sinh`, now with the sign from the
    -- translated negative pole.
    have hsinh_ne_real : Real.sinh a ≠ 0 := Real.sinh_ne_zero.2 ha.ne'
    have hsinh_ne : (((Real.sinh a : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast hsinh_ne_real
    simpa [dslope_same, Complex.deriv_cosh, exercise22_sinh_at_neg_pole] using hsinh_ne
  · -- Off the center, the same denominator factorization reduces vanishing to the strip pole
    -- classification.
    intro hdslope
    have hdenom_zero : Complex.cosh z + Real.cosh a = 0 := by
      rw [exercise22_denominator_eq_sub_neg_pole_mul_dslope, hdslope]
      simp
    rcases (exercise22_strip_poles ha hz_strip).1 hdenom_zero with hz_eq_pos | hz_eq_neg
    · exact hz_ne_pos hz_eq_pos
    · exact hz_neg hz_eq_neg

/-- Helper for Exercise 22: after using the evenness in `v`, the remaining source-faithful contour
computation is exactly the textbook case `0 < a` and `0 < v`. -/
lemma exercise22_positive_parameters_formula_core
    {a v : ℝ} (ha : 0 < a) (hv : 0 < v) :
    ∫ x in Set.Ioi (0 : ℝ), Real.cos (v * x) / (Real.cosh x + Real.cosh a) ∂volume =
      Real.pi * Real.sin (v * a) / (Real.sinh (Real.pi * v) * Real.sinh a) := by
  -- Route correction: the nonzero-frequency theorem below is now reduced to `0 < v`, so the
  -- remaining contour work only has to treat the decaying-frequency rectangle regime.
  let F : ℂ → ℂ := exercise22Kernel a v
  let D : Set ℂ := {z : ℂ | -(Real.pi / 2) < z.im ∧ z.im < 5 * Real.pi / 2}
  let s : Set ℂ := ({(a : ℂ) + Real.pi * Complex.I, -(a : ℂ) + Real.pi * Complex.I} : Set ℂ)
  let Dpos : Set ℂ := D \ ({-(a : ℂ) + Real.pi * Complex.I} : Set ℂ)
  let Dneg : Set ℂ := D \ ({(a : ℂ) + Real.pi * Complex.I} : Set ℂ)
  have hshift : ∀ z : ℂ, F (z + 2 * Real.pi * Complex.I) = Real.exp (-2 * Real.pi * v) * F z :=
    exercise22Kernel_add_two_pi_I a v
  have hposPole : Complex.cosh ((a : ℂ) + Real.pi * Complex.I) + Real.cosh a = 0 :=
    exercise22_denominator_zero_at_pos_pole a
  have hnegPole : Complex.cosh (-(a : ℂ) + Real.pi * Complex.I) + Real.cosh a = 0 :=
    exercise22_denominator_zero_at_neg_pole a
  have hsinhPos : Complex.sinh ((a : ℂ) + Real.pi * Complex.I) = -((Real.sinh a : ℝ) : ℂ) :=
    exercise22_sinh_at_pos_pole a
  have hsinhNeg : Complex.sinh (-(a : ℂ) + Real.pi * Complex.I) = ((Real.sinh a : ℝ) : ℂ) :=
    exercise22_sinh_at_neg_pole a
  have hresPos :
      Complex.exp (Complex.I * ((v : ℂ) * ((a : ℂ) + Real.pi * Complex.I))) /
        Complex.sinh ((a : ℂ) + Real.pi * Complex.I) =
          -(Real.exp (-Real.pi * v) * Complex.exp (Complex.I * ((v : ℂ) * a)) / Real.sinh a) :=
    exercise22_pos_pole_residue_value a v
  have hresNeg :
      Complex.exp (Complex.I * ((v : ℂ) * (-(a : ℂ) + Real.pi * Complex.I))) /
        Complex.sinh (-(a : ℂ) + Real.pi * Complex.I) =
          Real.exp (-Real.pi * v) * Complex.exp (-Complex.I * ((v : ℂ) * a)) / Real.sinh a :=
    exercise22_neg_pole_residue_value a v
  have hstrip :
      ∀ z ∈ D, Complex.cosh z + Real.cosh a = 0 ↔
        z = (a : ℂ) + Real.pi * Complex.I ∨ z = -(a : ℂ) + Real.pi * Complex.I := by
    intro z hz
    exact exercise22_strip_poles ha hz
  have hhol : DifferentiableOn ℂ F (D \ s) := by
    simpa [F, D, s] using exercise22_kernel_differentiableOn_strip_punctured (a := a) (v := v) ha
  have hfactorPos :
      ∀ z : ℂ,
        Complex.cosh z + Real.cosh a =
          (z - ((a : ℂ) + Real.pi * Complex.I)) *
            dslope Complex.cosh ((a : ℂ) + Real.pi * Complex.I) z :=
    exercise22_denominator_eq_sub_pos_pole_mul_dslope a
  have hfactorNeg :
      ∀ z : ℂ,
        Complex.cosh z + Real.cosh a =
          (z - (-(a : ℂ) + Real.pi * Complex.I)) *
            dslope Complex.cosh (-(a : ℂ) + Real.pi * Complex.I) z :=
    exercise22_denominator_eq_sub_neg_pole_mul_dslope a
  have hdslopePos :
      ∀ z ∈ Dpos, dslope Complex.cosh ((a : ℂ) + Real.pi * Complex.I) z ≠ 0 := by
    intro z hz
    simpa [Dpos, D] using
      exercise22_dslope_pos_ne_zero_on_strip_minus_neg_pole (a := a) ha hz
  have hdslopeNeg :
      ∀ z ∈ Dneg, dslope Complex.cosh (-(a : ℂ) + Real.pi * Complex.I) z ≠ 0 := by
    intro z hz
    simpa [Dneg, D] using
      exercise22_dslope_neg_ne_zero_on_strip_minus_pos_pole (a := a) ha hz
  let _ := ha
  let _ := hv
  let _ := hshift
  let _ := hposPole
  let _ := hnegPole
  let _ := hsinhPos
  let _ := hsinhNeg
  let _ := hresPos
  let _ := hresNeg
  let _ := hstrip
  let _ := hhol
  let _ := hfactorPos
  let _ := hfactorNeg
  let _ := hdslopePos
  let _ := hdslopeNeg
  -- TODO: fix `R > a`, use `exercise22_rectangle_pole_radius_geometry` to choose a common radius
  -- around the two poles, build the positive/negative `LocalResidueCircle` data on `Dpos` and `Dneg`
  -- from `hfactorPos`, `hfactorNeg`, `hdslopePos`, and `hdslopeNeg`, then apply the
  -- height-`2π i` rectangle residue theorem and pass `R → ∞`.
  sorry

/-- Helper for Exercise 22: in the textbook `a > 0` regime, the contour integral over the
rectangle with vertices `±R` and `±R + 2π i` yields the stated formula after letting `R → ∞`. -/
lemma exercise22_positive_parameter_formula
    {a v : ℝ} (ha : 0 < a) (hv : v ≠ 0) :
    ∫ x in Set.Ioi (0 : ℝ), Real.cos (v * x) / (Real.cosh x + Real.cosh a) ∂volume =
      Real.pi * Real.sin (v * a) / (Real.sinh (Real.pi * v) * Real.sinh a) := by
  -- Reduce the remaining nonzero-frequency case to the positive-frequency core using evenness.
  rw [exercise22_integral_abs_frequency a v, exercise22_rhs_abs_frequency]
  exact exercise22_positive_parameters_formula_core ha (abs_pos.mpr hv)

/-- Exercise 22. If `a ≠ 0` and `v ≠ 0`, then
`∫ x : ℝ in Set.Ioi 0, cos (v x) / (cosh x + cosh a) dx = π sin (v a) / (sinh (π v) sinh a)`.

The nonzero-parameter hypothesis is the canonical one here: the displayed formula is even in `a`, so
the textbook assumption `a > 0` is stronger than needed, while `a = 0` makes the right-hand side
totalize to `0` in Lean. The nonzero-frequency hypothesis is also part of the stated formula: at
`v = 0`, the displayed right-hand side does not agree with the integral. -/
theorem integral_cos_div_cosh_add_cosh
    {a v : ℝ} (ha : a ≠ 0) (hv : v ≠ 0) :
    ∫ x in Set.Ioi (0 : ℝ), Real.cos (v * x) / (Real.cosh x + Real.cosh a) ∂volume =
      Real.pi * Real.sin (v * a) / (Real.sinh (Real.pi * v) * Real.sinh a) := by
  -- Reduce the general nonzero parameter case to the textbook positive-parameter statement.
  rw [exercise22_integral_abs_parameter a v, exercise22_rhs_abs_parameter ha]
  exact exercise22_positive_parameter_formula (abs_pos.mpr ha) hv
