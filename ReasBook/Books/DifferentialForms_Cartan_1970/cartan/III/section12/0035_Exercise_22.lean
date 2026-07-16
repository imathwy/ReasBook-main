import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0034_Example_II_1_extra_21»
import DifferentialForms_Cartan_1970.cartan.III.section11.frozen_0003_Theorem_III_5_extra_2

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

/-- Helper for Exercise 22: a holomorphic kernel of the form `g(z) / (z - a)` realizes the
residue `g(a)` on every small circle contained in both `interior K` and `D`. -/
lemma exercise22_localResidueCircle_div_sub_of_differentiableOn
    {K D : Set ℂ} {g : ℂ → ℂ} {z : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hK : Metric.closedBall z r ⊆ interior K)
    (hD : Metric.closedBall z r ⊆ D)
    (hg : DifferentiableOn ℂ g D) :
    LocalResidueCircle K D (fun w ↦ g w / (w - z)) z (g z) := by
  -- Use the chosen circle directly and evaluate the Cauchy kernel integral there.
  refine ⟨r, hr, hK, hD, ?_⟩
  have hg_ball : DifferentiableOn ℂ g (Metric.closedBall z r) := hg.mono hD
  have hz_ball : z ∈ Metric.ball z r := Metric.mem_ball_self hr
  simpa [div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    hg_ball.circleIntegral_sub_inv_smul hz_ball

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

/-- Helper for Exercise 22: the positive strip pole carries the explicit local residue circle
needed for the rectangle argument. -/
lemma exercise22_pos_pole_localResidueCircle
    {a v R : ℝ} (ha : 0 < a) (hRa : a < R) :
    let K : Set ℂ := Complex.Rectangle (-R) (R + 2 * Real.pi * Complex.I)
    let D : Set ℂ := {z : ℂ | -(Real.pi / 2) < z.im ∧ z.im < 5 * Real.pi / 2}
    let zPos : ℂ := (a : ℂ) + Real.pi * Complex.I
    LocalResidueCircle
      K
      D
      (exercise22Kernel a v)
      zPos
      (-(Real.exp (-Real.pi * v) * Complex.exp (Complex.I * ((v : ℂ) * a)) / Real.sinh a)) := by
  dsimp
  let K : Set ℂ := Complex.Rectangle (-R) (R + 2 * Real.pi * Complex.I)
  let D : Set ℂ := {z : ℂ | -(Real.pi / 2) < z.im ∧ z.im < 5 * Real.pi / 2}
  let zPos : ℂ := (a : ℂ) + Real.pi * Complex.I
  let zNeg : ℂ := -(a : ℂ) + Real.pi * Complex.I
  let Dpos : Set ℂ := D \ ({zNeg} : Set ℂ)
  let g : ℂ → ℂ := fun z ↦
    Complex.exp (Complex.I * ((v : ℂ) * z)) / dslope Complex.cosh zPos z
  let ρ : ℝ := min (a / 2) (min ((R - a) / 2) (Real.pi / 2))
  have hgeom := exercise22_rectangle_pole_radius_geometry (a := a) (R := R) ha hRa
  dsimp [K, D, zPos, zNeg, ρ] at hgeom
  rcases hgeom with ⟨hballPos, hballNeg, hzNeg_not_ball, hzPos_not_ball⟩
  have hballK :
      Metric.closedBall zPos ρ ⊆ interior K := by
    intro z hz
    exact (hballPos hz).1
  have hballD :
      Metric.closedBall zPos ρ ⊆ D := by
    intro z hz
    exact (hballPos hz).2
  have hballDpos :
      Metric.closedBall zPos ρ ⊆ Dpos := by
    intro z hz
    refine ⟨hballD hz, ?_⟩
    intro hzNeg
    rcases Set.mem_singleton_iff.mp hzNeg with rfl
    exact hzNeg_not_ball hz
  have hD_open : IsOpen D := by
    refine (isOpen_lt continuous_const Complex.continuous_im).inter ?_
    exact isOpen_lt Complex.continuous_im continuous_const
  have hzPos_ne_zNeg : zPos ≠ zNeg := by
    intro hEq
    have hre := congrArg Complex.re hEq
    simp [zPos, zNeg] at hre
    linarith
  have hzPos_mem_Dpos : zPos ∈ Dpos := by
    refine ⟨?_, ?_⟩
    · constructor
      · simp [zPos]
        nlinarith [Real.pi_pos]
      · simp [zPos]
        nlinarith [Real.pi_pos]
    · simpa [Set.mem_singleton_iff] using hzPos_ne_zNeg
  have hDpos_nhds : Dpos ∈ nhds zPos := by
    have hDpos_open : IsOpen Dpos := hD_open.sdiff isClosed_singleton
    exact hDpos_open.mem_nhds hzPos_mem_Dpos
  have hdslope_diff : DifferentiableOn ℂ (dslope Complex.cosh zPos) Dpos := by
    exact
      (Complex.differentiableOn_dslope (c := zPos) hDpos_nhds).2
        Complex.differentiable_cosh.differentiableOn
  have hg : DifferentiableOn ℂ g Dpos := by
    intro z hz
    have hnum :
        DifferentiableWithinAt ℂ (fun w : ℂ => Complex.exp (Complex.I * ((v : ℂ) * w))) Dpos z := by
      fun_prop
    have hden :
        DifferentiableWithinAt ℂ (fun w : ℂ => dslope Complex.cosh zPos w) Dpos z :=
      hdslope_diff z hz
    have hden_ne : dslope Complex.cosh zPos z ≠ 0 := by
      simpa [Dpos, D, zPos, zNeg] using
        exercise22_dslope_pos_ne_zero_on_strip_minus_neg_pole (a := a) ha hz
    exact hnum.div hden hden_ne
  have hlocal :
      LocalResidueCircle K Dpos (fun z ↦ g z / (z - zPos)) zPos (g zPos) :=
    exercise22_localResidueCircle_div_sub_of_differentiableOn
      (K := K) (D := Dpos) (g := g) (z := zPos) (r := ρ)
      (by positivity) hballK hballDpos hg
  have hg_center :
      g zPos =
        -(Real.exp (-Real.pi * v) * Complex.exp (Complex.I * ((v : ℂ) * a)) / Real.sinh a) := by
    dsimp [g, zPos]
    simpa [dslope_same, Complex.deriv_cosh] using exercise22_pos_pole_residue_value a v
  rcases hlocal with ⟨radius, hradius, hradiusK, hradiusDpos, hcircle⟩
  refine ⟨radius, hradius, hradiusK, ?_, ?_⟩
  · intro z hz
    exact (hradiusDpos hz).1
  · have hcongr :
        (∮ w in C(zPos, radius), exercise22Kernel a v w) =
          ∮ w in C(zPos, radius), g w / (w - zPos) := by
      refine circleIntegral.integral_congr hradius.le ?_
      intro w hw
      have hw_ball : w ∈ Metric.closedBall zPos radius := by
        simpa [Metric.mem_closedBall, Complex.dist_eq] using le_of_eq hw
      have hwDpos : w ∈ Dpos := hradiusDpos hw_ball
      have hw_ne_zPos : w ≠ zPos := by
        intro hEq
        have hdist : dist w zPos = radius := by
          simpa [Complex.dist_eq] using hw
        rw [hEq, dist_self] at hdist
        exact hradius.ne' hdist.symm
      have hdslope_ne : dslope Complex.cosh zPos w ≠ 0 := by
        simpa [Dpos, D, zPos, zNeg] using
          exercise22_dslope_pos_ne_zero_on_strip_minus_neg_pole (a := a) ha hwDpos
      calc
        exercise22Kernel a v w =
            Complex.exp (Complex.I * ((v : ℂ) * w)) /
              ((w - zPos) * dslope Complex.cosh zPos w) := by
          rw [exercise22Kernel, exercise22_denominator_eq_sub_pos_pole_mul_dslope]
        _ = (Complex.exp (Complex.I * ((v : ℂ) * w)) / dslope Complex.cosh zPos w) / (w - zPos) := by
          field_simp [hdslope_ne, sub_ne_zero.mpr hw_ne_zPos]
        _ = g w / (w - zPos) := by
          rfl
    -- Rewrite the source integrand on the residue circle into the standard Cauchy kernel model.
    calc
      (∮ w in C(zPos, radius), exercise22Kernel a v w) =
          ∮ w in C(zPos, radius), g w / (w - zPos) := hcongr
      _ = (2 * Real.pi * Complex.I : ℂ) * g zPos := hcircle
      _ =
          (2 * Real.pi * Complex.I : ℂ) *
            (-(Real.exp (-Real.pi * v) * Complex.exp (Complex.I * ((v : ℂ) * a)) /
              Real.sinh a)) := by
              rw [hg_center]

/-- Helper for Exercise 22: the negative strip pole carries the second explicit local residue
circle needed for the rectangle argument. -/
lemma exercise22_neg_pole_localResidueCircle
    {a v R : ℝ} (ha : 0 < a) (hRa : a < R) :
    let K : Set ℂ := Complex.Rectangle (-R) (R + 2 * Real.pi * Complex.I)
    let D : Set ℂ := {z : ℂ | -(Real.pi / 2) < z.im ∧ z.im < 5 * Real.pi / 2}
    let zNeg : ℂ := -(a : ℂ) + Real.pi * Complex.I
    LocalResidueCircle
      K
      D
      (exercise22Kernel a v)
      zNeg
      (Real.exp (-Real.pi * v) * Complex.exp (-Complex.I * ((v : ℂ) * a)) / Real.sinh a) := by
  dsimp
  let K : Set ℂ := Complex.Rectangle (-R) (R + 2 * Real.pi * Complex.I)
  let D : Set ℂ := {z : ℂ | -(Real.pi / 2) < z.im ∧ z.im < 5 * Real.pi / 2}
  let zPos : ℂ := (a : ℂ) + Real.pi * Complex.I
  let zNeg : ℂ := -(a : ℂ) + Real.pi * Complex.I
  let Dneg : Set ℂ := D \ ({zPos} : Set ℂ)
  let g : ℂ → ℂ := fun z ↦
    Complex.exp (Complex.I * ((v : ℂ) * z)) / dslope Complex.cosh zNeg z
  let ρ : ℝ := min (a / 2) (min ((R - a) / 2) (Real.pi / 2))
  have hgeom := exercise22_rectangle_pole_radius_geometry (a := a) (R := R) ha hRa
  dsimp [K, D, zPos, zNeg, ρ] at hgeom
  rcases hgeom with ⟨hballPos, hballNeg, hzNeg_not_ball, hzPos_not_ball⟩
  have hballK :
      Metric.closedBall zNeg ρ ⊆ interior K := by
    intro z hz
    exact (hballNeg hz).1
  have hballD :
      Metric.closedBall zNeg ρ ⊆ D := by
    intro z hz
    exact (hballNeg hz).2
  have hballDneg :
      Metric.closedBall zNeg ρ ⊆ Dneg := by
    intro z hz
    refine ⟨hballD hz, ?_⟩
    intro hzPos
    rcases Set.mem_singleton_iff.mp hzPos with rfl
    exact hzPos_not_ball hz
  have hD_open : IsOpen D := by
    refine (isOpen_lt continuous_const Complex.continuous_im).inter ?_
    exact isOpen_lt Complex.continuous_im continuous_const
  have hzNeg_ne_zPos : zNeg ≠ zPos := by
    intro hEq
    exact (show zPos ≠ zNeg from by
      intro hEq'
      have hre := congrArg Complex.re hEq'
      simp [zPos, zNeg] at hre
      linarith) hEq.symm
  have hzNeg_mem_Dneg : zNeg ∈ Dneg := by
    refine ⟨?_, ?_⟩
    · constructor
      · simp [zNeg]
        nlinarith [Real.pi_pos]
      · simp [zNeg]
        nlinarith [Real.pi_pos]
    · simpa [Set.mem_singleton_iff] using hzNeg_ne_zPos
  have hDneg_nhds : Dneg ∈ nhds zNeg := by
    have hDneg_open : IsOpen Dneg := hD_open.sdiff isClosed_singleton
    exact hDneg_open.mem_nhds hzNeg_mem_Dneg
  have hdslope_diff : DifferentiableOn ℂ (dslope Complex.cosh zNeg) Dneg := by
    exact
      (Complex.differentiableOn_dslope (c := zNeg) hDneg_nhds).2
        Complex.differentiable_cosh.differentiableOn
  have hg : DifferentiableOn ℂ g Dneg := by
    intro z hz
    have hnum :
        DifferentiableWithinAt ℂ (fun w : ℂ => Complex.exp (Complex.I * ((v : ℂ) * w))) Dneg z := by
      fun_prop
    have hden :
        DifferentiableWithinAt ℂ (fun w : ℂ => dslope Complex.cosh zNeg w) Dneg z :=
      hdslope_diff z hz
    have hden_ne : dslope Complex.cosh zNeg z ≠ 0 := by
      simpa [Dneg, D, zPos, zNeg] using
        exercise22_dslope_neg_ne_zero_on_strip_minus_pos_pole (a := a) ha hz
    exact hnum.div hden hden_ne
  have hlocal :
      LocalResidueCircle K Dneg (fun z ↦ g z / (z - zNeg)) zNeg (g zNeg) :=
    exercise22_localResidueCircle_div_sub_of_differentiableOn
      (K := K) (D := Dneg) (g := g) (z := zNeg) (r := ρ)
      (by positivity) hballK hballDneg hg
  have hg_center :
      g zNeg =
        Real.exp (-Real.pi * v) * Complex.exp (-Complex.I * ((v : ℂ) * a)) / Real.sinh a := by
    dsimp [g, zNeg]
    simpa [dslope_same, Complex.deriv_cosh] using exercise22_neg_pole_residue_value a v
  rcases hlocal with ⟨radius, hradius, hradiusK, hradiusDneg, hcircle⟩
  refine ⟨radius, hradius, hradiusK, ?_, ?_⟩
  · intro z hz
    exact (hradiusDneg hz).1
  · have hcongr :
        (∮ w in C(zNeg, radius), exercise22Kernel a v w) =
          ∮ w in C(zNeg, radius), g w / (w - zNeg) := by
      refine circleIntegral.integral_congr hradius.le ?_
      intro w hw
      have hw_ball : w ∈ Metric.closedBall zNeg radius := by
        simpa [Metric.mem_closedBall, Complex.dist_eq] using le_of_eq hw
      have hwDneg : w ∈ Dneg := hradiusDneg hw_ball
      have hw_ne_zNeg : w ≠ zNeg := by
        intro hEq
        have hdist : dist w zNeg = radius := by
          simpa [Complex.dist_eq] using hw
        rw [hEq, dist_self] at hdist
        exact hradius.ne' hdist.symm
      have hdslope_ne : dslope Complex.cosh zNeg w ≠ 0 := by
        simpa [Dneg, D, zPos, zNeg] using
          exercise22_dslope_neg_ne_zero_on_strip_minus_pos_pole (a := a) ha hwDneg
      calc
        exercise22Kernel a v w =
            Complex.exp (Complex.I * ((v : ℂ) * w)) /
              ((w - zNeg) * dslope Complex.cosh zNeg w) := by
          rw [exercise22Kernel, exercise22_denominator_eq_sub_neg_pole_mul_dslope]
        _ = (Complex.exp (Complex.I * ((v : ℂ) * w)) / dslope Complex.cosh zNeg w) / (w - zNeg) := by
          field_simp [hdslope_ne, sub_ne_zero.mpr hw_ne_zNeg]
        _ = g w / (w - zNeg) := by
          rfl
    -- Rewrite the source integrand on the residue circle into the standard Cauchy kernel model.
    calc
      (∮ w in C(zNeg, radius), exercise22Kernel a v w) =
          ∮ w in C(zNeg, radius), g w / (w - zNeg) := hcongr
      _ = (2 * Real.pi * Complex.I : ℂ) * g zNeg := hcircle
      _ =
          (2 * Real.pi * Complex.I : ℂ) *
            (Real.exp (-Real.pi * v) * Complex.exp (-Complex.I * ((v : ℂ) * a)) /
              Real.sinh a) := by
              rw [hg_center]

/-- Helper for Exercise 22: for every fixed rectangle with `a < R`, both strip poles come with
the explicit local residue circles required by the source rectangle proof. -/
lemma exercise22_localResidueCircle_pair
    {a v R : ℝ} (ha : 0 < a) (hRa : a < R) :
    let K : Set ℂ := Complex.Rectangle (-R) (R + 2 * Real.pi * Complex.I)
    let D : Set ℂ := {z : ℂ | -(Real.pi / 2) < z.im ∧ z.im < 5 * Real.pi / 2}
    let zPos : ℂ := (a : ℂ) + Real.pi * Complex.I
    let zNeg : ℂ := -(a : ℂ) + Real.pi * Complex.I
    LocalResidueCircle
      K
      D
      (exercise22Kernel a v)
      zPos
      (-(Real.exp (-Real.pi * v) * Complex.exp (Complex.I * ((v : ℂ) * a)) / Real.sinh a)) ∧
    LocalResidueCircle
      K
      D
      (exercise22Kernel a v)
      zNeg
      (Real.exp (-Real.pi * v) * Complex.exp (-Complex.I * ((v : ℂ) * a)) / Real.sinh a) := by
  -- Bundle the two one-pole residue-circle constructions so the fixed-rectangle step can consume
  -- them uniformly.
  constructor
  · simpa using exercise22_pos_pole_localResidueCircle (a := a) (v := v) (R := R) ha hRa
  · simpa using exercise22_neg_pole_localResidueCircle (a := a) (v := v) (R := R) ha hRa

/-- Helper for Cartan section12 0035_Exercise_22: the positive strip pole admits an isolated local
residue circle for the two-point pole finset. -/
lemma exercise22_pos_pole_isolatedLocalResidueCircle
    {a v R : ℝ} (ha : 0 < a) (hRa : a < R) :
    let K : Set ℂ := Complex.Rectangle (-R) (R + 2 * Real.pi * Complex.I)
    let D : Set ℂ := {z : ℂ | -(Real.pi / 2) < z.im ∧ z.im < 5 * Real.pi / 2}
    let zPos : ℂ := (a : ℂ) + Real.pi * Complex.I
    let zNeg : ℂ := -(a : ℂ) + Real.pi * Complex.I
    let s : Finset ℂ := {zPos, zNeg}
    IsolatedLocalResidueCircle
      K
      D
      s
      (exercise22Kernel a v)
      zPos
      (-(Real.exp (-Real.pi * v) * Complex.exp (Complex.I * ((v : ℂ) * a)) / Real.sinh a)) := by
  dsimp
  let K : Set ℂ := Complex.Rectangle (-R) (R + 2 * Real.pi * Complex.I)
  let D : Set ℂ := {z : ℂ | -(Real.pi / 2) < z.im ∧ z.im < 5 * Real.pi / 2}
  let zPos : ℂ := (a : ℂ) + Real.pi * Complex.I
  let zNeg : ℂ := -(a : ℂ) + Real.pi * Complex.I
  let s : Finset ℂ := {zPos, zNeg}
  let ρ : ℝ := min (a / 2) (min ((R - a) / 2) (Real.pi / 2))
  have hρ_pos : 0 < ρ := by
    positivity
  have hgeom := exercise22_rectangle_pole_radius_geometry (a := a) (R := R) ha hRa
  dsimp [K, D, zPos, zNeg, ρ] at hgeom
  rcases hgeom with ⟨hballPos, hballNeg, hzNeg_not_ball, hzPos_not_ball⟩
  have hzPos_ne_zNeg : zPos ≠ zNeg := by
    intro hEq
    have hre := congrArg Complex.re hEq
    simp [zPos, zNeg] at hre
    linarith
  let Dpos : Set ℂ := D \ ({zNeg} : Set ℂ)
  let g : ℂ → ℂ := fun z ↦
    Complex.exp (Complex.I * ((v : ℂ) * z)) / dslope Complex.cosh zPos z
  have hballK :
      Metric.closedBall zPos ρ ⊆ interior K := by
    intro z hz
    exact (hballPos hz).1
  have hballD :
      Metric.closedBall zPos ρ ⊆ D := by
    intro z hz
    exact (hballPos hz).2
  have hballDpos :
      Metric.closedBall zPos ρ ⊆ Dpos := by
    intro z hz
    refine ⟨hballD hz, ?_⟩
    intro hzNeg
    rcases Set.mem_singleton_iff.mp hzNeg with rfl
    exact hzNeg_not_ball hz
  have hD_open : IsOpen D := by
    refine (isOpen_lt continuous_const Complex.continuous_im).inter ?_
    exact isOpen_lt Complex.continuous_im continuous_const
  have hzPos_mem_Dpos : zPos ∈ Dpos := by
    refine ⟨?_, ?_⟩
    · constructor
      · simp [zPos]
        nlinarith [Real.pi_pos]
      · simp [zPos]
        nlinarith [Real.pi_pos]
    · simpa [Set.mem_singleton_iff] using hzPos_ne_zNeg
  have hDpos_nhds : Dpos ∈ nhds zPos := by
    have hDpos_open : IsOpen Dpos := hD_open.sdiff isClosed_singleton
    exact hDpos_open.mem_nhds hzPos_mem_Dpos
  have hdslope_diff : DifferentiableOn ℂ (dslope Complex.cosh zPos) Dpos := by
    exact
      (Complex.differentiableOn_dslope (c := zPos) hDpos_nhds).2
        Complex.differentiable_cosh.differentiableOn
  have hg : DifferentiableOn ℂ g Dpos := by
    intro z hz
    have hnum :
        DifferentiableWithinAt ℂ (fun w : ℂ => Complex.exp (Complex.I * ((v : ℂ) * w))) Dpos z := by
      fun_prop
    have hden :
        DifferentiableWithinAt ℂ (fun w : ℂ => dslope Complex.cosh zPos w) Dpos z :=
      hdslope_diff z hz
    have hden_ne : dslope Complex.cosh zPos z ≠ 0 := by
      simpa [Dpos, D, zPos, zNeg] using
        exercise22_dslope_pos_ne_zero_on_strip_minus_neg_pole (a := a) ha hz
    exact hnum.div hden hden_ne
  have hg_ball : DifferentiableOn ℂ g (Metric.closedBall zPos ρ) := hg.mono hballDpos
  have hzPos_ball : zPos ∈ Metric.ball zPos ρ := Metric.mem_ball_self hρ_pos
  have hcircle :
      (∮ w in C(zPos, ρ), g w / (w - zPos)) = (2 * Real.pi * Complex.I : ℂ) * g zPos := by
    simpa [div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      hg_ball.circleIntegral_sub_inv_smul hzPos_ball
  have hg_center :
      g zPos =
        -(Real.exp (-Real.pi * v) * Complex.exp (Complex.I * ((v : ℂ) * a)) / Real.sinh a) := by
    dsimp [g, zPos]
    simpa [dslope_same, Complex.deriv_cosh] using exercise22_pos_pole_residue_value a v
  have havoid :
      ∀ w ∈ s, w ≠ zPos → w ∉ Metric.closedBall zPos ρ := by
    intro w hw hwne hwBall
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hwne rfl
    · have hwEq : w = zNeg := by simpa using hw
      subst hwEq
      exact hzNeg_not_ball hwBall
  have hdiff :
      DifferentiableOn ℂ (exercise22Kernel a v) (Metric.ball zPos ρ \ ({zPos} : Set ℂ)) := by
    refine (exercise22_kernel_differentiableOn_strip_punctured (a := a) ha).mono ?_
    intro w hw
    have hwDpos : w ∈ Dpos := hballDpos (Metric.ball_subset_closedBall hw.1)
    refine ⟨hwDpos.1, ?_⟩
    intro hwPole
    rcases Set.mem_insert_iff.mp hwPole with hwPos | hwNeg
    · exact hw.2 (Set.mem_singleton_iff.mp hwPos)
    · exact hwDpos.2 (Set.mem_singleton_iff.mp hwNeg)
  refine ⟨ρ, hρ_pos, hballK, hballD, havoid, hdiff, ?_⟩
  have hcongr :
      (∮ w in C(zPos, ρ), exercise22Kernel a v w) =
        ∮ w in C(zPos, ρ), g w / (w - zPos) := by
    refine circleIntegral.integral_congr hρ_pos.le ?_
    intro w hw
    have hw_ball : w ∈ Metric.closedBall zPos ρ := by
      simpa [Metric.mem_closedBall, Complex.dist_eq] using le_of_eq hw
    have hwDpos : w ∈ Dpos := hballDpos hw_ball
    have hw_ne_zPos : w ≠ zPos := by
      intro hEq
      have hdist : dist w zPos = ρ := by
        simpa [Complex.dist_eq] using hw
      rw [hEq, dist_self] at hdist
      exact hρ_pos.ne' hdist.symm
    have hdslope_ne : dslope Complex.cosh zPos w ≠ 0 := by
      simpa [Dpos, D, zPos, zNeg] using
        exercise22_dslope_pos_ne_zero_on_strip_minus_neg_pole (a := a) ha hwDpos
    calc
      exercise22Kernel a v w =
          Complex.exp (Complex.I * ((v : ℂ) * w)) /
            ((w - zPos) * dslope Complex.cosh zPos w) := by
        rw [exercise22Kernel, exercise22_denominator_eq_sub_pos_pole_mul_dslope]
      _ = (Complex.exp (Complex.I * ((v : ℂ) * w)) / dslope Complex.cosh zPos w) / (w - zPos) := by
        field_simp [hdslope_ne, sub_ne_zero.mpr hw_ne_zPos]
      _ = g w / (w - zPos) := by
        rfl
  calc
    (∮ w in C(zPos, ρ), exercise22Kernel a v w) =
        ∮ w in C(zPos, ρ), g w / (w - zPos) := hcongr
    _ = (2 * Real.pi * Complex.I : ℂ) * g zPos := hcircle
    _ =
        (2 * Real.pi * Complex.I : ℂ) *
          (-(Real.exp (-Real.pi * v) * Complex.exp (Complex.I * ((v : ℂ) * a)) /
            Real.sinh a)) := by
          rw [hg_center]

/-- Helper for Cartan section12 0035_Exercise_22: the negative strip pole admits an isolated local
residue circle for the two-point pole finset. -/
lemma exercise22_neg_pole_isolatedLocalResidueCircle
    {a v R : ℝ} (ha : 0 < a) (hRa : a < R) :
    let K : Set ℂ := Complex.Rectangle (-R) (R + 2 * Real.pi * Complex.I)
    let D : Set ℂ := {z : ℂ | -(Real.pi / 2) < z.im ∧ z.im < 5 * Real.pi / 2}
    let zPos : ℂ := (a : ℂ) + Real.pi * Complex.I
    let zNeg : ℂ := -(a : ℂ) + Real.pi * Complex.I
    let s : Finset ℂ := {zPos, zNeg}
    IsolatedLocalResidueCircle
      K
      D
      s
      (exercise22Kernel a v)
      zNeg
      (Real.exp (-Real.pi * v) * Complex.exp (-Complex.I * ((v : ℂ) * a)) / Real.sinh a) := by
  dsimp
  let K : Set ℂ := Complex.Rectangle (-R) (R + 2 * Real.pi * Complex.I)
  let D : Set ℂ := {z : ℂ | -(Real.pi / 2) < z.im ∧ z.im < 5 * Real.pi / 2}
  let zPos : ℂ := (a : ℂ) + Real.pi * Complex.I
  let zNeg : ℂ := -(a : ℂ) + Real.pi * Complex.I
  let s : Finset ℂ := {zPos, zNeg}
  let ρ : ℝ := min (a / 2) (min ((R - a) / 2) (Real.pi / 2))
  have hρ_pos : 0 < ρ := by
    positivity
  have hgeom := exercise22_rectangle_pole_radius_geometry (a := a) (R := R) ha hRa
  dsimp [K, D, zPos, zNeg, ρ] at hgeom
  rcases hgeom with ⟨hballPos, hballNeg, hzNeg_not_ball, hzPos_not_ball⟩
  have hzNeg_ne_zPos : zNeg ≠ zPos := by
    intro hEq
    have hre := congrArg Complex.re hEq
    simp [zPos, zNeg] at hre
    linarith
  let Dneg : Set ℂ := D \ ({zPos} : Set ℂ)
  let g : ℂ → ℂ := fun z ↦
    Complex.exp (Complex.I * ((v : ℂ) * z)) / dslope Complex.cosh zNeg z
  have hballK :
      Metric.closedBall zNeg ρ ⊆ interior K := by
    intro z hz
    exact (hballNeg hz).1
  have hballD :
      Metric.closedBall zNeg ρ ⊆ D := by
    intro z hz
    exact (hballNeg hz).2
  have hballDneg :
      Metric.closedBall zNeg ρ ⊆ Dneg := by
    intro z hz
    refine ⟨hballD hz, ?_⟩
    intro hzPos
    rcases Set.mem_singleton_iff.mp hzPos with rfl
    exact hzPos_not_ball hz
  have hD_open : IsOpen D := by
    refine (isOpen_lt continuous_const Complex.continuous_im).inter ?_
    exact isOpen_lt Complex.continuous_im continuous_const
  have hzNeg_mem_Dneg : zNeg ∈ Dneg := by
    refine ⟨?_, ?_⟩
    · constructor
      · simp [zNeg]
        nlinarith [Real.pi_pos]
      · simp [zNeg]
        nlinarith [Real.pi_pos]
    · simpa [Set.mem_singleton_iff] using hzNeg_ne_zPos
  have hDneg_nhds : Dneg ∈ nhds zNeg := by
    have hDneg_open : IsOpen Dneg := hD_open.sdiff isClosed_singleton
    exact hDneg_open.mem_nhds hzNeg_mem_Dneg
  have hdslope_diff : DifferentiableOn ℂ (dslope Complex.cosh zNeg) Dneg := by
    exact
      (Complex.differentiableOn_dslope (c := zNeg) hDneg_nhds).2
        Complex.differentiable_cosh.differentiableOn
  have hg : DifferentiableOn ℂ g Dneg := by
    intro z hz
    have hnum :
        DifferentiableWithinAt ℂ (fun w : ℂ => Complex.exp (Complex.I * ((v : ℂ) * w))) Dneg z := by
      fun_prop
    have hden :
        DifferentiableWithinAt ℂ (fun w : ℂ => dslope Complex.cosh zNeg w) Dneg z :=
      hdslope_diff z hz
    have hden_ne : dslope Complex.cosh zNeg z ≠ 0 := by
      simpa [Dneg, D, zPos, zNeg] using
        exercise22_dslope_neg_ne_zero_on_strip_minus_pos_pole (a := a) ha hz
    exact hnum.div hden hden_ne
  have hg_ball : DifferentiableOn ℂ g (Metric.closedBall zNeg ρ) := hg.mono hballDneg
  have hzNeg_ball : zNeg ∈ Metric.ball zNeg ρ := Metric.mem_ball_self hρ_pos
  have hcircle :
      (∮ w in C(zNeg, ρ), g w / (w - zNeg)) = (2 * Real.pi * Complex.I : ℂ) * g zNeg := by
    simpa [div_eq_mul_inv, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      hg_ball.circleIntegral_sub_inv_smul hzNeg_ball
  have hg_center :
      g zNeg =
        Real.exp (-Real.pi * v) * Complex.exp (-Complex.I * ((v : ℂ) * a)) / Real.sinh a := by
    dsimp [g, zNeg]
    simpa [dslope_same, Complex.deriv_cosh] using exercise22_neg_pole_residue_value a v
  have havoid :
      ∀ w ∈ s, w ≠ zNeg → w ∉ Metric.closedBall zNeg ρ := by
    intro w hw hwne hwBall
    rcases Finset.mem_insert.mp hw with hw | hw
    · have hwEq : w = zPos := by simpa using hw
      subst hwEq
      exact hzPos_not_ball hwBall
    · have hwEq : w = zNeg := by simpa using hw
      exact hwne hwEq
  have hdiff :
      DifferentiableOn ℂ (exercise22Kernel a v) (Metric.ball zNeg ρ \ ({zNeg} : Set ℂ)) := by
    refine (exercise22_kernel_differentiableOn_strip_punctured (a := a) ha).mono ?_
    intro w hw
    have hwDneg : w ∈ Dneg := hballDneg (Metric.ball_subset_closedBall hw.1)
    refine ⟨hwDneg.1, ?_⟩
    intro hwPole
    rcases Set.mem_insert_iff.mp hwPole with hwPos | hwNeg
    · exact hwDneg.2 (Set.mem_singleton_iff.mp hwPos)
    · exact hw.2 (Set.mem_singleton_iff.mp hwNeg)
  refine ⟨ρ, hρ_pos, hballK, hballD, havoid, hdiff, ?_⟩
  have hcongr :
      (∮ w in C(zNeg, ρ), exercise22Kernel a v w) =
        ∮ w in C(zNeg, ρ), g w / (w - zNeg) := by
    refine circleIntegral.integral_congr hρ_pos.le ?_
    intro w hw
    have hw_ball : w ∈ Metric.closedBall zNeg ρ := by
      simpa [Metric.mem_closedBall, Complex.dist_eq] using le_of_eq hw
    have hwDneg : w ∈ Dneg := hballDneg hw_ball
    have hw_ne_zNeg : w ≠ zNeg := by
      intro hEq
      have hdist : dist w zNeg = ρ := by
        simpa [Complex.dist_eq] using hw
      rw [hEq, dist_self] at hdist
      exact hρ_pos.ne' hdist.symm
    have hdslope_ne : dslope Complex.cosh zNeg w ≠ 0 := by
      simpa [Dneg, D, zPos, zNeg] using
        exercise22_dslope_neg_ne_zero_on_strip_minus_pos_pole (a := a) ha hwDneg
    calc
      exercise22Kernel a v w =
          Complex.exp (Complex.I * ((v : ℂ) * w)) /
            ((w - zNeg) * dslope Complex.cosh zNeg w) := by
        rw [exercise22Kernel, exercise22_denominator_eq_sub_neg_pole_mul_dslope]
      _ = (Complex.exp (Complex.I * ((v : ℂ) * w)) / dslope Complex.cosh zNeg w) / (w - zNeg) := by
        field_simp [hdslope_ne, sub_ne_zero.mpr hw_ne_zNeg]
      _ = g w / (w - zNeg) := by
        rfl
  calc
    (∮ w in C(zNeg, ρ), exercise22Kernel a v w) =
        ∮ w in C(zNeg, ρ), g w / (w - zNeg) := hcongr
    _ = (2 * Real.pi * Complex.I : ℂ) * g zNeg := hcircle
    _ =
        (2 * Real.pi * Complex.I : ℂ) *
          (Real.exp (-Real.pi * v) * Complex.exp (-Complex.I * ((v : ℂ) * a)) /
            Real.sinh a) := by
          rw [hg_center]

/-- Helper for Cartan section12 0035_Exercise_22: for a fixed rectangle with `a < R`, the two
strip poles admit isolated local residue circles for the two-point pole finset. -/
lemma exercise22_isolatedLocalResidueCircle_pair
    {a v R : ℝ} (ha : 0 < a) (hRa : a < R) :
    let K : Set ℂ := Complex.Rectangle (-R) (R + 2 * Real.pi * Complex.I)
    let D : Set ℂ := {z : ℂ | -(Real.pi / 2) < z.im ∧ z.im < 5 * Real.pi / 2}
    let zPos : ℂ := (a : ℂ) + Real.pi * Complex.I
    let zNeg : ℂ := -(a : ℂ) + Real.pi * Complex.I
    let s : Finset ℂ := {zPos, zNeg}
    IsolatedLocalResidueCircle
      K
      D
      s
      (exercise22Kernel a v)
      zPos
      (-(Real.exp (-Real.pi * v) * Complex.exp (Complex.I * ((v : ℂ) * a)) / Real.sinh a)) ∧
    IsolatedLocalResidueCircle
      K
      D
      s
      (exercise22Kernel a v)
      zNeg
      (Real.exp (-Real.pi * v) * Complex.exp (-Complex.I * ((v : ℂ) * a)) / Real.sinh a) := by
  constructor
  · simpa using exercise22_pos_pole_isolatedLocalResidueCircle (a := a) (v := v) (R := R) ha hRa
  · simpa using exercise22_neg_pole_isolatedLocalResidueCircle (a := a) (v := v) (R := R) ha hRa

/-- Helper for Exercise 22: the top side of the height-`2π i` rectangle is the translated bottom
edge with reversed orientation, so its contour integral is `-e^{-2π v}` times the bottom one. -/
lemma exercise22_top_side_eq_neg_exp_mul_bottom {a v R : ℝ} :
    ∫ᶜ z in Path.segment (R + 2 * Real.pi * Complex.I) (-R + 2 * Real.pi * Complex.I),
      ((exercise22Kernel a v dz) z) =
      -(Real.exp (-2 * Real.pi * v)) *
        ∫ᶜ z in Path.segment (-R : ℂ) (R : ℂ), ((exercise22Kernel a v dz) z) := by
  let shift : ℂ := 2 * Real.pi * Complex.I
  have htranslate :
      ∫ᶜ z in Path.segment ((-R : ℂ) + shift) ((R : ℂ) + shift), ((exercise22Kernel a v dz) z) =
        Real.exp (-2 * Real.pi * v) *
          ∫ᶜ z in Path.segment (-R : ℂ) (R : ℂ), ((exercise22Kernel a v dz) z) := by
    -- Rewrite both segments as affine interval integrals and use the `2π i`-shift identity pointwise.
    rw [curveIntegral_segment, curveIntegral_segment]
    rw [← intervalIntegral.integral_const_mul]
    refine (intervalIntegral.integral_congr
      (a := (0 : ℝ)) (b := 1) (μ := MeasureTheory.volume)
      (f := fun t : ℝ ↦
        (((exercise22Kernel a v) dz)
          (AffineMap.lineMap ((-R : ℂ) + shift) ((R : ℂ) + shift) t))
          (((R : ℂ) + shift) - ((-R : ℂ) + shift)))
      (g := fun t : ℝ ↦
        Real.exp (-2 * Real.pi * v) *
          ((((exercise22Kernel a v) dz) (AffineMap.lineMap (-R : ℂ) (R : ℂ) t))
            ((R : ℂ) - (-R : ℂ))))
      ?_)
    intro t ht
    have hline :
        AffineMap.lineMap ((-R : ℂ) + shift) ((R : ℂ) + shift) t =
          AffineMap.lineMap (-R : ℂ) (R : ℂ) t + shift := by
      simp [AffineMap.lineMap_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hdir :
        (((R : ℂ) + shift) - ((-R : ℂ) + shift)) = ((R : ℂ) - (-R : ℂ)) := by
      ring
    -- Evaluate the scalar one-form on the translated segment and then apply the kernel shift law.
    calc
      (((exercise22Kernel a v) dz)
          (AffineMap.lineMap ((-R : ℂ) + shift) ((R : ℂ) + shift) t))
          (((R : ℂ) + shift) - ((-R : ℂ) + shift)) =
        exercise22Kernel a v (AffineMap.lineMap (-R : ℂ) (R : ℂ) t + shift) *
          (((R : ℂ) - (-R : ℂ))) := by
            rw [Complex.scalarOneForm_apply, hline, hdir, mul_comm]
      _ =
        (Real.exp (-2 * Real.pi * v) *
          exercise22Kernel a v (AffineMap.lineMap (-R : ℂ) (R : ℂ) t)) *
            (((R : ℂ) - (-R : ℂ))) := by
              rw [exercise22Kernel_add_two_pi_I]
      _ =
        Real.exp (-2 * Real.pi * v) *
          ((((exercise22Kernel a v) dz) (AffineMap.lineMap (-R : ℂ) (R : ℂ) t))
            (((R : ℂ) - (-R : ℂ)))) := by
              simp [Complex.scalarOneForm_apply, mul_assoc, mul_left_comm, mul_comm]
  have hsymm :
      ∫ᶜ z in Path.segment ((R : ℂ) + shift) ((-R : ℂ) + shift), ((exercise22Kernel a v dz) z) =
        -∫ᶜ z in Path.segment ((-R : ℂ) + shift) ((R : ℂ) + shift),
          ((exercise22Kernel a v dz) z) := by
    -- Reverse the translated bottom edge to match the top-edge orientation in the source rectangle.
    simpa [shift, Path.segment_symm] using
      (curveIntegral_symm ((exercise22Kernel a v) dz)
        (Path.segment ((-R : ℂ) + shift) ((R : ℂ) + shift)))
  calc
    ∫ᶜ z in Path.segment (R + 2 * Real.pi * Complex.I) (-R + 2 * Real.pi * Complex.I),
        ((exercise22Kernel a v dz) z) =
      -∫ᶜ z in Path.segment ((-R : ℂ) + shift) ((R : ℂ) + shift),
        ((exercise22Kernel a v dz) z) := by
          simpa [shift] using hsymm
    _ = -(Real.exp (-2 * Real.pi * v) *
          ∫ᶜ z in Path.segment (-R : ℂ) (R : ℂ), ((exercise22Kernel a v dz) z)) := by
            rw [htranslate]
    _ = -(Real.exp (-2 * Real.pi * v)) *
          ∫ᶜ z in Path.segment (-R : ℂ) (R : ℂ), ((exercise22Kernel a v dz) z) := by
            ring

/-- Helper for Exercise 22: on the real axis, pairing the kernel at `x` and `-x` cancels the
imaginary parts and leaves twice the cosine kernel from the source integral. -/
lemma exercise22Kernel_real_axis_pair (a v x : ℝ) :
    exercise22Kernel a v (-(x : ℂ)) + exercise22Kernel a v (x : ℂ) =
      (((2 * (Real.cos (v * x) / (Real.cosh x + Real.cosh a)) : ℝ) : ℂ)) := by
  have hden :
      Complex.cosh (-(x : ℂ)) + Real.cosh a = Complex.cosh (x : ℂ) + Real.cosh a := by
    -- The denominator is even on the real axis, so both summands already share one denominator.
    simp [Complex.cosh_neg]
  have hsumexp :
      Complex.exp (Complex.I * ((v : ℂ) * (-(x : ℂ)))) +
          Complex.exp (Complex.I * ((v : ℂ) * (x : ℂ))) =
        ((2 * Real.cos (v * x) : ℝ) : ℂ) := by
    -- Euler's formula turns the paired exponentials into the standard `2 cos` combination.
    calc
      Complex.exp (Complex.I * ((v : ℂ) * (-(x : ℂ)))) +
          Complex.exp (Complex.I * ((v : ℂ) * (x : ℂ))) =
            Complex.exp (-(((v * x : ℝ) : ℂ) * Complex.I)) +
              Complex.exp ((((v * x : ℝ) : ℂ) * Complex.I)) := by
          simp [Complex.ofReal_mul, mul_comm]
      _ = (2 : ℂ) * Complex.cos (((v * x : ℝ) : ℂ)) := by
          symm
          simpa [two_mul, add_comm] using (Complex.two_cos (((v * x : ℝ) : ℂ)))
      _ = ((2 * Real.cos (v * x) : ℝ) : ℂ) := by
          simp [Complex.ofReal_cos, two_mul]
  -- After combining the numerators, the remaining denominator is real and positive.
  calc
    exercise22Kernel a v (-(x : ℂ)) + exercise22Kernel a v (x : ℂ) =
        (Complex.exp (Complex.I * ((v : ℂ) * (-(x : ℂ)))) +
            Complex.exp (Complex.I * ((v : ℂ) * (x : ℂ)))) /
          (Complex.cosh (x : ℂ) + Real.cosh a) := by
          rw [exercise22Kernel, exercise22Kernel, hden]
          field_simp
    _ = (((2 * Real.cos (v * x) : ℝ) : ℂ)) /
          (Complex.cosh (x : ℂ) + Real.cosh a) := by
          rw [hsumexp]
    _ = (((2 * (Real.cos (v * x) / (Real.cosh x + Real.cosh a)) : ℝ) : ℂ)) := by
          rw [Complex.ofReal_cosh]
          norm_num [Complex.ofReal_mul, Complex.ofReal_div, div_eq_mul_inv, mul_assoc,
            mul_left_comm, mul_comm]

/-- Helper for Exercise 22: the bottom side of the rectangle is the complexification of
`2 * ∫_0^R cos (v x) / (cosh x + cosh a) dx`. -/
lemma exercise22_bottom_segment_eq_double_intervalIntegral
    {a v R : ℝ} :
    ∫ᶜ z in Path.segment (-R : ℂ) (R : ℂ), ((exercise22Kernel a v dz) z) =
      (((2 : ℝ) : ℂ) *
        ∫ x in (0 : ℝ)..R,
          ((Real.cos (v * x) / (Real.cosh x + Real.cosh a) : ℝ) : ℂ)) := by
  let f : ℝ → ℂ := fun x ↦ exercise22Kernel a v (x : ℂ)
  have hseg :
      ∫ᶜ z in Path.segment (-R : ℂ) (R : ℂ), ((exercise22Kernel a v dz) z) =
        ∫ x in (0 : ℝ)..1, ((2 * R : ℝ) : ℂ) * f (-R + (2 * R) * x) := by
    -- Rewrite the contour integral as the affine parameter integral along the horizontal segment.
    rw [curveIntegral_segment]
    refine intervalIntegral.integral_congr ?_
    intro x hx
    simp [f, exercise22Kernel, AffineMap.lineMap_apply, Complex.ofReal_mul, add_mul, mul_add,
      sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]
    ring
  have hchange :
      ∫ x in (0 : ℝ)..1, ((2 * R : ℝ) : ℂ) * f (-R + (2 * R) * x) =
        ∫ x in (-R : ℝ)..R, f x := by
    -- The affine reparameterization `x ↦ -R + 2 R x` turns `[0, 1]` into `[-R, R]`.
    have hupper : -R + 2 * R = R := by
      nlinarith
    calc
      ∫ x in (0 : ℝ)..1, ((2 * R : ℝ) : ℂ) * f (-R + (2 * R) * x) =
          ((2 * R : ℝ) : ℂ) * ∫ x in (0 : ℝ)..1, f (-R + (2 * R) * x) := by
            rw [intervalIntegral.integral_const_mul]
      _ = ((2 * R : ℝ) : ℂ) *
            ∫ x in (0 : ℝ)..1,
              (fun y : ℝ ↦ exercise22Kernel a v (y : ℂ)) (-R + (2 * R) * x) := by
            rfl
      _ = ∫ x in (-R : ℝ)..R, (fun y : ℝ ↦ exercise22Kernel a v (y : ℂ)) x := by
            simpa [smul_eq_mul, hupper] using
              (intervalIntegral.smul_integral_comp_add_mul
                (f := fun y : ℝ ↦ exercise22Kernel a v (y : ℂ))
                (a := (0 : ℝ)) (b := 1) (c := 2 * R) (d := -R))
      _ = ∫ x in (-R : ℝ)..R, f x := by
            rfl
  have hden_pos : ∀ x : ℝ, 0 < Real.cosh x + Real.cosh a := by
    intro x
    positivity
  have hf_cont : Continuous f := by
    -- On the real axis the denominator never vanishes, so the kernel is continuous there.
    refine Continuous.div ?_ ?_ ?_
    · fun_prop
    · fun_prop
    · intro x
      have hne : ((Real.cosh x + Real.cosh a : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (hden_pos x))
      simpa [f, exercise22Kernel, Complex.ofReal_cosh] using hne
  have hf_int_neg : IntervalIntegrable f volume (-R) 0 := hf_cont.intervalIntegrable _ _
  have hf_int_pos : IntervalIntegrable f volume 0 R := hf_cont.intervalIntegrable _ _
  have hfneg_cont : Continuous (fun x : ℝ ↦ f (-x)) := hf_cont.comp (by fun_prop)
  have hfneg_int : IntervalIntegrable (fun x : ℝ ↦ f (-x)) volume 0 R :=
    hfneg_cont.intervalIntegrable _ _
  have hsplit :
      ∫ x in (-R : ℝ)..R, f x = (∫ x in (-R : ℝ)..0, f x) + ∫ x in (0 : ℝ)..R, f x := by
    -- Split the symmetric interval at `0` before pairing the two halves.
    simpa using (intervalIntegral.integral_add_adjacent_intervals hf_int_neg hf_int_pos).symm
  have hneg_to_pos : ∫ x in (-R : ℝ)..0, f x = ∫ x in (0 : ℝ)..R, f (-x) := by
    -- The negative half is the positive half after the substitution `x ↦ -x`.
    simpa [f] using (intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := R)).symm
  -- Pair the symmetric real-axis values and then collapse them with the cosine identity above.
  calc
    ∫ᶜ z in Path.segment (-R : ℂ) (R : ℂ), ((exercise22Kernel a v dz) z) =
        ∫ x in (-R : ℝ)..R, f x := by
          rw [hseg, hchange]
    _ = (∫ x in (-R : ℝ)..0, f x) + ∫ x in (0 : ℝ)..R, f x := hsplit
    _ = (∫ x in (0 : ℝ)..R, f (-x)) + ∫ x in (0 : ℝ)..R, f x := by
          rw [hneg_to_pos]
    _ = ∫ x in (0 : ℝ)..R, (f (-x) + f x) := by
          simpa using (intervalIntegral.integral_add hfneg_int hf_int_pos).symm
    _ = ∫ x in (0 : ℝ)..R,
          (((2 * (Real.cos (v * x) / (Real.cosh x + Real.cosh a)) : ℝ) : ℂ)) := by
          refine intervalIntegral.integral_congr ?_
          intro x hx
          simpa [f] using exercise22Kernel_real_axis_pair a v x
    _ = ∫ x in (0 : ℝ)..R,
          (((2 : ℝ) : ℂ) *
            ((Real.cos (v * x) / (Real.cosh x + Real.cosh a) : ℝ) : ℂ)) := by
          refine intervalIntegral.integral_congr ?_
          intro x hx
          simp [Complex.ofReal_mul, div_eq_mul_inv, mul_assoc, mul_comm]
    _ = (((2 : ℝ) : ℂ) *
          ∫ x in (0 : ℝ)..R,
            ((Real.cos (v * x) / (Real.cosh x + Real.cosh a) : ℝ) : ℂ)) := by
          rw [intervalIntegral.integral_const_mul]

/-- Helper for Exercise 22: the oscillatory exponential on the contour has norm
`exp (-v * Im z)`, so only the imaginary part contributes to the ML estimate. -/
lemma exercise22_exp_phase_norm (v : ℝ) (z : ℂ) :
    ‖Complex.exp (Complex.I * ((v : ℂ) * z))‖ = Real.exp (-v * z.im) := by
  -- Expand the real part of `I * (v z)` in coordinates and apply `‖exp w‖ = exp (Re w)`.
  rcases z with ⟨x, y⟩
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Cartan section12 0035_Exercise_22: the rectangle boundary loop for the source
contour stays inside the pole-free strip because the two poles lie strictly in the rectangle
interior. -/
lemma exercise22_rectangle_boundary_subset_puncturedStrip
    {a R : ℝ} (ha : 0 < a) (hRa : a < R) :
    let D : Set ℂ := {z : ℂ | -(Real.pi / 2) < z.im ∧ z.im < 5 * Real.pi / 2}
    let s : Finset ℂ := {((a : ℂ) + Real.pi * Complex.I), (-(a : ℂ) + Real.pi * Complex.I)}
    Set.range (axisParallelRectangleBoundaryPath (-R : ℂ) (R + 2 * Real.pi * Complex.I)) ⊆
      D \ (↑s : Set ℂ) := by
  dsimp
  have hR_pos : 0 < R := lt_trans ha hRa
  have hRR : -R ≤ R := by linarith
  have h0pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  intro z hz
  rw [axisParallelRectangleBoundaryPath_range_eq_frontier (-R : ℂ) (R + 2 * Real.pi * Complex.I)] at hz
  have hclosed :
      IsClosed (Complex.Rectangle (-R : ℂ) (R + 2 * Real.pi * Complex.I)) := by
    simpa [Complex.Rectangle, Set.uIcc_of_le hRR, Set.uIcc_of_le h0pi] using
      isClosed_Icc.reProdIm isClosed_Icc
  have hzRect : z ∈ Complex.Rectangle (-R : ℂ) (R + 2 * Real.pi * Complex.I) := by
    simpa [hclosed.closure_eq] using frontier_subset_closure hz
  have hzRe : -R ≤ z.re ∧ z.re ≤ R := by
    simpa [Set.uIcc_of_le hRR] using
      (show z.re ∈ Set.uIcc (-R) R by
        simpa [Complex.Rectangle, Complex.mem_reProdIm] using hzRect.1)
  have hzIm : 0 ≤ z.im ∧ z.im ≤ 2 * Real.pi := by
    simpa [Set.uIcc_of_le h0pi] using
      (show z.im ∈ Set.uIcc 0 (2 * Real.pi) by
        simpa [Complex.Rectangle, Complex.mem_reProdIm] using hzRect.2)
  refine ⟨?_, ?_⟩
  · constructor
    · nlinarith [hzIm.1, Real.pi_pos]
    · nlinarith [hzIm.2, Real.pi_pos]
  · intro hzS
    have hzInterior :
        z ∈ interior (Complex.Rectangle (-R : ℂ) (R + 2 * Real.pi * Complex.I)) := by
      rcases Finset.mem_insert.mp hzS with hEq | hzS'
      · subst hEq
        rw [Complex.Rectangle, Complex.interior_reProdIm, Complex.mem_reProdIm]
        simpa [Set.uIcc_of_le hRR, Set.uIcc_of_le h0pi, interior_Icc] using
          ⟨(show a ∈ Set.Ioo (-R) R from by constructor <;> linarith),
            (show Real.pi ∈ Set.Ioo (0 : ℝ) (2 * Real.pi) from by constructor <;> nlinarith [Real.pi_pos])⟩
      · have hEq : z = -(a : ℂ) + Real.pi * Complex.I := by simpa using hzS'
        subst hEq
        rw [Complex.Rectangle, Complex.interior_reProdIm, Complex.mem_reProdIm]
        have hnegRe :
            (-(a : ℂ) + Real.pi * Complex.I).re ∈
              interior (Set.uIcc ((-R : ℂ)).re (R + 2 * Real.pi * Complex.I).re) := by
          simpa [Set.uIcc_of_le hRR, interior_Icc] using
            (show a < R ∧ -a < R from by constructor <;> linarith)
        have hpiIm :
            (-(a : ℂ) + Real.pi * Complex.I).im ∈
              interior (Set.uIcc ((-R : ℂ)).im (R + 2 * Real.pi * Complex.I).im) := by
          simpa [Set.uIcc_of_le h0pi, interior_Icc] using
            (show Real.pi ∈ Set.Ioo (0 : ℝ) (2 * Real.pi) from by
              constructor <;> nlinarith [Real.pi_pos])
        exact ⟨hnegRe, hpiIm⟩
    exact (Set.disjoint_left.mp disjoint_interior_frontier) hzInterior hz

/-- Helper for Cartan section12 0035_Exercise_22: each affine side of the source rectangle is one
of the four branches of the concatenated boundary loop. -/
lemma exercise22_rectangle_boundary_side_ranges_subset (R : ℝ) :
    let z₀ : ℂ := (-R : ℂ)
    let w : ℂ := R + 2 * Real.pi * Complex.I
    let zw : ℂ := Complex.mk w.re z₀.im
    let wz : ℂ := Complex.mk z₀.re w.im
    Set.range (Path.segment z₀ zw) ⊆ Set.range (axisParallelRectangleBoundaryPath z₀ w) ∧
      Set.range (Path.segment zw w) ⊆ Set.range (axisParallelRectangleBoundaryPath z₀ w) ∧
      Set.range (Path.segment w wz) ⊆ Set.range (axisParallelRectangleBoundaryPath z₀ w) ∧
      Set.range (Path.segment wz z₀) ⊆ Set.range (axisParallelRectangleBoundaryPath z₀ w) := by
  let z₀ : ℂ := (-R : ℂ)
  let w : ℂ := R + 2 * Real.pi * Complex.I
  let zw : ℂ := Complex.mk w.re z₀.im
  let wz : ℂ := Complex.mk z₀.re w.im
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    dsimp [z₀, w, zw, wz, axisParallelRectangleBoundaryPath]
    rw [Path.trans_range, Path.trans_range, Path.trans_range]
    exact Or.inl hz
  · intro z hz
    dsimp [z₀, w, zw, wz, axisParallelRectangleBoundaryPath]
    rw [Path.trans_range, Path.trans_range, Path.trans_range]
    exact Or.inr <| Or.inl hz
  · intro z hz
    dsimp [z₀, w, zw, wz, axisParallelRectangleBoundaryPath]
    rw [Path.trans_range, Path.trans_range, Path.trans_range]
    exact Or.inr <| Or.inr <| Or.inl hz
  · intro z hz
    dsimp [z₀, w, zw, wz, axisParallelRectangleBoundaryPath]
    rw [Path.trans_range, Path.trans_range, Path.trans_range]
    exact Or.inr <| Or.inr <| Or.inr hz

/-- Helper for Cartan section12 0035_Exercise_22: unpacking a loop through `toClosedPath.toPath`
only inserts the trivial endpoint cast. -/
lemma exercise22_loop_toClosedPath_toPath_eq_cast {x : ℂ} (γ : Path x x) :
    γ.toClosedPath.toPath = γ.cast γ.source γ.source := by
  cases γ
  rfl

/-- Helper for Cartan section12 0035_Exercise_22: passing a loop through `toClosedPath.toPath`
does not change its curve integral. -/
lemma exercise22_curveIntegral_loop_toClosedPath_toPath
    {x : ℂ} (ω : ℂ → ℂ →L[ℂ] ℂ) (γ : Path x x) :
    ∫ᶜ z in γ.toClosedPath.toPath, ω z = ∫ᶜ z in γ, ω z := by
  rw [exercise22_loop_toClosedPath_toPath_eq_cast, curveIntegral_def', curveIntegral_def']
  change
    ∫ t in (0 : ℝ)..1, curveIntegralFun (fun z ↦ ω z) (γ.cast γ.source γ.source) t =
      ∫ t in (0 : ℝ)..1, curveIntegralFun (fun z ↦ ω z) γ t
  simpa using
    congrArg
      (fun f : ℝ → ℂ ↦ ∫ t in (0 : ℝ)..1, f t)
      (curveIntegralFun_cast (fun z ↦ ω z) γ γ.source γ.source)

/-- Helper for Exercise 22: any affine segment that stays in the punctured strip carries a
curve-integrable copy of the kernel `exercise22Kernel`. -/
lemma exercise22_curveIntegrable_segment_of_subset
    {a v : ℝ} (ha : 0 < a) {p q : ℂ}
    (hsubset :
      segment ℝ p q ⊆
        {z : ℂ | -(Real.pi / 2) < z.im ∧ z.im < 5 * Real.pi / 2} \
          ({(a : ℂ) + Real.pi * Complex.I, -(a : ℂ) + Real.pi * Complex.I} : Set ℂ)) :
    CurveIntegrable ((exercise22Kernel a v) dz) (Path.segment p q) := by
  -- Rewrite the segment integral as an interval integral of a continuous pullback.
  rw [curveIntegrable_segment]
  have hcontKernel : ContinuousOn (exercise22Kernel a v) (segment ℝ p q) :=
    (exercise22_kernel_differentiableOn_strip_punctured (a := a) ha).continuousOn.mono hsubset
  have hcontPullback :
      ContinuousOn (fun t : ℝ ↦ exercise22Kernel a v (AffineMap.lineMap p q t)) (Set.Icc 0 1) := by
    refine hcontKernel.comp ?_ ?_
    · simpa [ContinuousAffineMap.coe_lineMap_eq] using
        (ContinuousAffineMap.continuous (ContinuousAffineMap.lineMap (R := ℝ) p q)).continuousOn
    · intro t ht
      simpa [segment_eq_uIcc] using lineMap_mem_segment ℝ p q ht
  have hcont :
      ContinuousOn
        (fun t : ℝ ↦ (q - p) * exercise22Kernel a v (AffineMap.lineMap p q t))
        (Set.Icc 0 1) := continuousOn_const.mul hcontPullback
  have hcont' :
      ContinuousOn
        (fun t : ℝ ↦ (q - p) * exercise22Kernel a v (AffineMap.lineMap p q t))
        (Set.uIcc 0 1) := by
    simpa [Set.uIcc_of_le zero_le_one] using hcont
  simpa [Complex.scalarOneForm_apply, mul_comm] using
    hcont'.intervalIntegrable (μ := MeasureTheory.volume)

/-- Helper for Exercise 22: the exact height-`2π i` rectangle boundary already carries the two
local residues needed by the source contour argument. -/
lemma exercise22_rectangle_boundary_residue_sum
    {a v R : ℝ} (ha : 0 < a) (hRa : a < R) :
    ∫ᶜ z in (axisParallelRectangleBoundaryPath (-R : ℂ) (R + 2 * Real.pi * Complex.I)).toClosedPath.toPath,
      ((exercise22Kernel a v dz) z) =
      (((4 * Real.pi * Real.exp (-Real.pi * v) * Real.sin (v * a) / Real.sinh a : ℝ)) : ℂ) := by
  let K : Set ℂ := Complex.Rectangle (-R : ℂ) (R + 2 * Real.pi * Complex.I)
  let D : Set ℂ := {z : ℂ | -(Real.pi / 2) < z.im ∧ z.im < 5 * Real.pi / 2}
  let zPos : ℂ := (a : ℂ) + Real.pi * Complex.I
  let zNeg : ℂ := -(a : ℂ) + Real.pi * Complex.I
  let posResidue : ℂ :=
    -(Real.exp (-Real.pi * v) * Complex.exp (Complex.I * ((v : ℂ) * a)) / Real.sinh a)
  let negResidue : ℂ :=
    Real.exp (-Real.pi * v) * Complex.exp (-Complex.I * ((v : ℂ) * a)) / Real.sinh a
  let s : Finset ℂ := {zPos, zNeg}
  let residue : ℂ → ℂ := fun z ↦ if z = zPos then posResidue else negResidue
  let Γ : Unit → ClosedPath ℂ := fun _ ↦
    (axisParallelRectangleBoundaryPath (-R : ℂ) (R + 2 * Real.pi * Complex.I)).toClosedPath
  have hR_pos : 0 < R := lt_trans ha hRa
  have hzPos_ne_zNeg : zPos ≠ zNeg := by
    intro hEq
    have hre := congrArg Complex.re hEq
    simp [zPos, zNeg] at hre
    linarith
  have hzNeg_ne_zPos : zNeg ≠ zPos := hzPos_ne_zNeg.symm
  have hΓ :
      IsOrientedBoundaryOf K Γ := by
    simpa [Γ, K] using
      axisParallelRectangleBoundary_isOrientedBoundaryOf
        (-R : ℂ) (R + 2 * Real.pi * Complex.I)
        (by simpa using (show -R < R by linarith))
        (by simpa using (show (0 : ℝ) < 2 * Real.pi by positivity))
  have hKD : K ⊆ D := by
    have hRR : -R ≤ R := by linarith
    have h0pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    intro z hz
    have hzRe : -R ≤ z.re ∧ z.re ≤ R := by
      simpa [Set.uIcc_of_le hRR] using
        (show z.re ∈ Set.uIcc (-R) R by
          simpa [K, Complex.Rectangle, Complex.mem_reProdIm] using hz.1)
    have hzIm : 0 ≤ z.im ∧ z.im ≤ 2 * Real.pi := by
      simpa [Set.uIcc_of_le h0pi] using
        (show z.im ∈ Set.uIcc 0 (2 * Real.pi) by
          simpa [K, Complex.Rectangle, Complex.mem_reProdIm] using hz.2)
    constructor
    · nlinarith [hzIm.1, Real.pi_pos]
    · nlinarith [hzIm.2, Real.pi_pos]
  have hboundary_subset :
      Set.range (axisParallelRectangleBoundaryPath (-R : ℂ) (R + 2 * Real.pi * Complex.I)) ⊆
        D \ (↑s : Set ℂ) :=
    exercise22_rectangle_boundary_subset_puncturedStrip (a := a) (R := R) ha hRa
  have hboundary_disjoint : ∀ i : Unit, Disjoint (Set.range (Γ i).toPath) (↑s : Set ℂ) := by
    intro i
    cases i
    refine Set.disjoint_left.2 ?_
    intro z hzΓ hzS
    exact (hboundary_subset (by simpa [Γ, Path.toClosedPath] using hzΓ)).2 hzS
  have hhol :
      DifferentiableOn ℂ (exercise22Kernel a v) (D \ (↑s : Set ℂ)) := by
    simpa [D, s, zPos, zNeg] using
      exercise22_kernel_differentiableOn_strip_punctured (a := a) ha
  have hres :
      ∀ z ∈ s, IsolatedLocalResidueCircle K D s (exercise22Kernel a v) z (residue z) := by
    have hisolated := exercise22_isolatedLocalResidueCircle_pair (a := a) (v := v) (R := R) ha hRa
    dsimp [K, D, zPos, zNeg, s] at hisolated
    rcases hisolated with ⟨hpos, hneg⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · simpa [residue, posResidue] using hpos
    · have hzEq : z = zNeg := by simpa using hz
      subst hzEq
      simpa [residue, hzNeg_ne_zPos, negResidue] using hneg
  have hboundary_sum :
      ∑ i, ∫ᶜ z in (Γ i).toPath, ((exercise22Kernel a v dz) z) =
        (2 * Real.pi * Complex.I : ℂ) * Finset.sum s residue := by
    exact
      orientedBoundary_sum_curveIntegral_eq_two_pi_I_mul_sum_residue
        (Γ := Γ) (K := K) (D := D)
        (f := exercise22Kernel a v) (s := s) (residue := residue)
        hΓ hKD (by
          refine (isOpen_lt continuous_const Complex.continuous_im).inter ?_
          exact isOpen_lt Complex.continuous_im continuous_const)
        hboundary_disjoint hhol hres
  have hresidue_sum :
      (2 * Real.pi * Complex.I : ℂ) * Finset.sum s residue =
        (((4 * Real.pi * Real.exp (-Real.pi * v) * Real.sin (v * a) / Real.sinh a : ℝ)) : ℂ) := by
    rw [Finset.sum_insert]
    · rw [Finset.sum_singleton]
      dsimp [residue, posResidue, negResidue]
      simp [hzPos_ne_zNeg, hzNeg_ne_zPos]
      have hposExp :
          Complex.exp (Complex.I * ((v : ℂ) * a)) =
            Real.cos (v * a) + Real.sin (v * a) * Complex.I := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using Complex.exp_mul_I (v * a)
      have hnegExp :
          Complex.exp (-(Complex.I * ((v : ℂ) * a))) =
            Real.cos (v * a) - Real.sin (v * a) * Complex.I := by
        simpa [neg_mul, mul_assoc, mul_comm, mul_left_comm, Real.cos_neg, Real.sin_neg,
          sub_eq_add_neg] using Complex.exp_mul_I (-(v * a))
      rw [hposExp, hnegExp]
      ring_nf
      simp [Complex.I_sq, mul_assoc, mul_comm, mul_left_comm]
    · simp [hzPos_ne_zNeg]
  calc
    ∫ᶜ z in (axisParallelRectangleBoundaryPath (-R : ℂ) (R + 2 * Real.pi * Complex.I)).toClosedPath.toPath,
        ((exercise22Kernel a v dz) z) =
      ∑ i, ∫ᶜ z in (Γ i).toPath, ((exercise22Kernel a v dz) z) := by
        simpa [Γ]
    _ = (2 * Real.pi * Complex.I : ℂ) * Finset.sum s residue := hboundary_sum
    _ = (((4 * Real.pi * Real.exp (-Real.pi * v) * Real.sin (v * a) / Real.sinh a : ℝ)) : ℂ) :=
      hresidue_sum

/-- Helper for Exercise 22: after rewriting the top edge by the `2π i` shift law, the fixed
rectangle contour identity keeps only the bottom integral and the vertical pair. -/
lemma exercise22_fixed_rectangle_identity
    {a v R : ℝ} (ha : 0 < a) (hRa : a < R) :
    let z₀ : ℂ := (-R : ℂ)
    let w : ℂ := R + 2 * Real.pi * Complex.I
    let zw : ℂ := Complex.mk w.re z₀.im
    let wz : ℂ := Complex.mk z₀.re w.im
    let bottom :=
      ∫ᶜ z in Path.segment z₀ zw, ((exercise22Kernel a v dz) z)
    let verticalPair :=
      ∫ᶜ z in Path.segment zw w, ((exercise22Kernel a v dz) z) +
        ∫ᶜ z in Path.segment wz z₀, ((exercise22Kernel a v dz) z)
    ((((1 - Real.exp (-2 * Real.pi * v)) : ℝ) : ℂ) * bottom) + verticalPair =
      (((4 * Real.pi * Real.exp (-Real.pi * v) * Real.sin (v * a) / Real.sinh a : ℝ)) : ℂ) := by
  dsimp
  let z₀ : ℂ := (-R : ℂ)
  let w : ℂ := R + 2 * Real.pi * Complex.I
  let zw : ℂ := Complex.mk w.re z₀.im
  let wz : ℂ := Complex.mk z₀.re w.im
  have hzw : zw = (R : ℂ) := by
    apply Complex.ext <;> simp [z₀, w, zw]
  have hwz : wz = (-R + 2 * Real.pi * Complex.I) := by
    apply Complex.ext <;> simp [z₀, w, wz]
  change
    ((((1 - Real.exp (-2 * Real.pi * v)) : ℝ) : ℂ) *
        ∫ᶜ z in Path.segment z₀ zw, ((exercise22Kernel a v dz) z)) +
        (∫ᶜ z in Path.segment zw w, ((exercise22Kernel a v dz) z) +
          ∫ᶜ z in Path.segment wz z₀, ((exercise22Kernel a v dz) z)) =
      (((4 * Real.pi * Real.exp (-Real.pi * v) * Real.sin (v * a) / Real.sinh a : ℝ)) : ℂ)
  let strip :
      Set ℂ := {z : ℂ | -(Real.pi / 2) < z.im ∧ z.im < 5 * Real.pi / 2}
  let poles : Set ℂ := {((a : ℂ) + Real.pi * Complex.I), (-(a : ℂ) + Real.pi * Complex.I)}
  have hboundary_subset :
      Set.range (axisParallelRectangleBoundaryPath z₀ w) ⊆ strip \ poles := by
    simpa [z₀, w, zw, wz, strip, poles] using
      exercise22_rectangle_boundary_subset_puncturedStrip (a := a) (R := R) ha hRa
  have hsides := exercise22_rectangle_boundary_side_ranges_subset R
  dsimp [z₀, w, zw, wz] at hsides
  have hbottom_subset : segment ℝ z₀ zw ⊆ strip \ poles := by
    intro z hz
    have hzrange : z ∈ Set.range (Path.segment z₀ zw) := by
      simpa [Path.range_segment] using hz
    exact hboundary_subset (hsides.1 hzrange)
  have hright_subset : segment ℝ zw w ⊆ strip \ poles := by
    intro z hz
    have hzrange : z ∈ Set.range (Path.segment zw w) := by
      simpa [Path.range_segment] using hz
    exact hboundary_subset (hsides.2.1 hzrange)
  have htop_subset : segment ℝ w wz ⊆ strip \ poles := by
    intro z hz
    have hzrange : z ∈ Set.range (Path.segment w wz) := by
      simpa [Path.range_segment] using hz
    exact hboundary_subset (hsides.2.2.1 hzrange)
  have hleft_subset : segment ℝ wz z₀ ⊆ strip \ poles := by
    intro z hz
    have hzrange : z ∈ Set.range (Path.segment wz z₀) := by
      simpa [Path.range_segment] using hz
    exact hboundary_subset (hsides.2.2.2 hzrange)
  have hbottom_int :
      CurveIntegrable ((exercise22Kernel a v) dz) (Path.segment z₀ zw) :=
    exercise22_curveIntegrable_segment_of_subset (a := a) (v := v) ha hbottom_subset
  have hright_int :
      CurveIntegrable ((exercise22Kernel a v) dz) (Path.segment zw w) :=
    exercise22_curveIntegrable_segment_of_subset (a := a) (v := v) ha hright_subset
  have htop_int :
      CurveIntegrable ((exercise22Kernel a v) dz) (Path.segment w wz) :=
    exercise22_curveIntegrable_segment_of_subset (a := a) (v := v) ha htop_subset
  have hleft_int :
      CurveIntegrable ((exercise22Kernel a v) dz) (Path.segment wz z₀) :=
    exercise22_curveIntegrable_segment_of_subset (a := a) (v := v) ha hleft_subset
  have hboundary_decomp :
      ∫ᶜ z in (axisParallelRectangleBoundaryPath z₀ w).toClosedPath.toPath,
          ((exercise22Kernel a v dz) z) =
        ∫ᶜ z in Path.segment z₀ zw, ((exercise22Kernel a v dz) z) +
          (∫ᶜ z in Path.segment zw w, ((exercise22Kernel a v dz) z) +
            (∫ᶜ z in Path.segment w wz, ((exercise22Kernel a v dz) z) +
              ∫ᶜ z in Path.segment wz z₀, ((exercise22Kernel a v dz) z))) := by
    calc
      ∫ᶜ z in (axisParallelRectangleBoundaryPath z₀ w).toClosedPath.toPath,
          ((exercise22Kernel a v dz) z) =
        ∫ᶜ z in axisParallelRectangleBoundaryPath z₀ w, ((exercise22Kernel a v dz) z) := by
            simpa using
              exercise22_curveIntegral_loop_toClosedPath_toPath
                ((exercise22Kernel a v) dz)
                (axisParallelRectangleBoundaryPath z₀ w)
      _ =
          ∫ᶜ z in Path.segment z₀ zw, ((exercise22Kernel a v dz) z) +
            ∫ᶜ z in (Path.segment zw w).trans ((Path.segment w wz).trans (Path.segment wz z₀)),
              ((exercise22Kernel a v dz) z) := by
            simpa [axisParallelRectangleBoundaryPath, z₀, w, zw, wz] using
              curveIntegral_trans hbottom_int (hright_int.trans (htop_int.trans hleft_int))
      _ =
          ∫ᶜ z in Path.segment z₀ zw, ((exercise22Kernel a v dz) z) +
            (∫ᶜ z in Path.segment zw w, ((exercise22Kernel a v dz) z) +
              ∫ᶜ z in (Path.segment w wz).trans (Path.segment wz z₀),
                ((exercise22Kernel a v dz) z)) := by
            rw [curveIntegral_trans hright_int (htop_int.trans hleft_int)]
      _ =
          ∫ᶜ z in Path.segment z₀ zw, ((exercise22Kernel a v dz) z) +
            (∫ᶜ z in Path.segment zw w, ((exercise22Kernel a v dz) z) +
              (∫ᶜ z in Path.segment w wz, ((exercise22Kernel a v dz) z) +
                ∫ᶜ z in Path.segment wz z₀, ((exercise22Kernel a v dz) z))) := by
            rw [curveIntegral_trans htop_int hleft_int]
  -- Rewrite the top edge using the `2π i` shift law and then compare with the residue identity.
  have htop :
      ∫ᶜ z in Path.segment w wz, ((exercise22Kernel a v dz) z) =
        -(Real.exp (-2 * Real.pi * v)) *
          ∫ᶜ z in Path.segment z₀ zw, ((exercise22Kernel a v dz) z) := by
    rw [hzw, hwz]
    exact exercise22_top_side_eq_neg_exp_mul_bottom (a := a) (v := v) (R := R)
  calc
    ((((1 - Real.exp (-2 * Real.pi * v)) : ℝ) : ℂ) *
        ∫ᶜ z in Path.segment z₀ zw, ((exercise22Kernel a v dz) z)) +
        (∫ᶜ z in Path.segment zw w, ((exercise22Kernel a v dz) z) +
          ∫ᶜ z in Path.segment wz z₀, ((exercise22Kernel a v dz) z)) =
      ∫ᶜ z in Path.segment z₀ zw, ((exercise22Kernel a v dz) z) +
        (∫ᶜ z in Path.segment zw w, ((exercise22Kernel a v dz) z) +
          (∫ᶜ z in Path.segment w wz, ((exercise22Kernel a v dz) z) +
            ∫ᶜ z in Path.segment wz z₀, ((exercise22Kernel a v dz) z))) := by
          rw [htop]
          have hmul :
              ((((1 - Real.exp (-2 * Real.pi * v)) : ℝ) : ℂ) *
                  ∫ᶜ z in Path.segment z₀ zw, ((exercise22Kernel a v dz) z)) =
                ∫ᶜ z in Path.segment z₀ zw, ((exercise22Kernel a v dz) z) -
                  (∫ᶜ z in Path.segment z₀ zw, ((exercise22Kernel a v dz) z)) *
                    (((Real.exp (-2 * Real.pi * v)) : ℝ) : ℂ) := by
            calc
              ((((1 - Real.exp (-2 * Real.pi * v)) : ℝ) : ℂ) *
                  ∫ᶜ z in Path.segment z₀ zw, ((exercise22Kernel a v dz) z)) =
                (((1 : ℂ) - (((Real.exp (-2 * Real.pi * v)) : ℝ) : ℂ)) *
                  ∫ᶜ z in Path.segment z₀ zw, ((exercise22Kernel a v dz) z)) := by
                    simp
              _ =
                  (1 : ℂ) * ∫ᶜ z in Path.segment z₀ zw, ((exercise22Kernel a v dz) z) -
                    (∫ᶜ z in Path.segment z₀ zw, ((exercise22Kernel a v dz) z)) *
                      (((Real.exp (-2 * Real.pi * v)) : ℝ) : ℂ) := by
                    ring
              _ =
                  ∫ᶜ z in Path.segment z₀ zw, ((exercise22Kernel a v dz) z) -
                    (∫ᶜ z in Path.segment z₀ zw, ((exercise22Kernel a v dz) z)) *
                      (((Real.exp (-2 * Real.pi * v)) : ℝ) : ℂ) := by
                    simp
          rw [hmul]
          ring_nf
    _ =
        ∫ᶜ z in (axisParallelRectangleBoundaryPath z₀ w).toClosedPath.toPath,
          ((exercise22Kernel a v dz) z) := by
          symm
          simpa [hzw, hwz] using hboundary_decomp
    _ =
        (((4 * Real.pi * Real.exp (-Real.pi * v) * Real.sin (v * a) / Real.sinh a : ℝ)) : ℂ) := by
          simpa [z₀, w] using
            exercise22_rectangle_boundary_residue_sum (a := a) (v := v) (R := R) ha hRa

/-- Helper for Cartan section12 0035_Exercise_22: on the right vertical line of the rectangle,
the denominator norm is bounded below by `cosh R - cosh a`. -/
lemma exercise22_right_vertical_denominator_lower_bound
    {a R y : ℝ} (ha : 0 < a) (hRa : a < R) :
    Real.cosh R - Real.cosh a ≤
      ‖Complex.cosh ((R : ℂ) + y * Complex.I) + Real.cosh a‖ := by
  have habs : |a| < |R| := by
    rw [abs_of_pos ha, abs_of_pos (lt_trans ha hRa)]
    exact hRa
  have hnonneg : 0 ≤ Real.cosh R - Real.cosh a := by
    exact sub_nonneg.mpr ((Real.cosh_le_cosh).2 habs.le)
  have hdecomp :
      Complex.cosh ((R : ℂ) + y * Complex.I) + Real.cosh a =
        (((Real.cosh R * Real.cos y + Real.cosh a : ℝ) : ℂ) +
          (Real.sinh R * Real.sin y : ℝ) * Complex.I) := by
    have hcoshI : Complex.cosh ((y : ℂ) * Complex.I) = Real.cos y := by
      simpa [mul_comm] using Complex.cosh_mul_I (y : ℂ)
    have hsinhI : Complex.sinh ((y : ℂ) * Complex.I) = Real.sin y * Complex.I := by
      simpa [mul_comm] using Complex.sinh_mul_I (y : ℂ)
    calc
      Complex.cosh ((R : ℂ) + y * Complex.I) + Real.cosh a =
          Complex.cosh (R : ℂ) * Complex.cosh ((y : ℂ) * Complex.I) +
            Complex.sinh (R : ℂ) * Complex.sinh ((y : ℂ) * Complex.I) + Real.cosh a := by
              rw [show y * Complex.I = (y : ℂ) * Complex.I by simp, Complex.cosh_add]
      _ =
          ((Real.cosh R : ℂ) * Real.cos y + (Real.sinh R : ℂ) * (Real.sin y * Complex.I) +
            Real.cosh a) := by
              simp [Complex.ofReal_cosh, Complex.ofReal_sinh, hcoshI, hsinhI]
      _ =
          (((Real.cosh R * Real.cos y + Real.cosh a : ℝ) : ℂ) +
            (Real.sinh R * Real.sin y : ℝ) * Complex.I) := by
              simp [Complex.ofReal_mul, Complex.ofReal_add, mul_assoc, mul_left_comm, mul_comm,
                add_assoc, add_left_comm, add_comm]
  have hmodel :
      Real.cosh R - Real.cosh a ≤
        ‖(((Real.cosh R * Real.cos y + Real.cosh a : ℝ) : ℂ) +
          (Real.sinh R * Real.sin y : ℝ) * Complex.I)‖ := by
    rw [← sq_le_sq₀ hnonneg (norm_nonneg _), Complex.sq_norm, Complex.normSq_add_mul_I]
    have htrig : Real.sin y ^ 2 + Real.cos y ^ 2 = 1 := by
      nlinarith [Real.sin_sq_add_cos_sq y]
    have hcos : -1 ≤ Real.cos y := Real.neg_one_le_cos y
    have hA : 1 ≤ Real.cosh R := Real.one_le_cosh R
    have hB : 1 ≤ Real.cosh a := Real.one_le_cosh a
    have hfactor :
        ((Real.cosh R * Real.cos y + Real.cosh a) ^ 2 + (Real.sinh R * Real.sin y) ^ 2) -
          (Real.cosh R - Real.cosh a) ^ 2 =
          (Real.cos y + 1) * (2 * Real.cosh R * Real.cosh a - (1 - Real.cos y)) := by
      nlinarith [Real.sinh_sq R, htrig]
    have hterm1 : 0 ≤ Real.cos y + 1 := by
      linarith
    have hterm2 : 0 ≤ 2 * Real.cosh R * Real.cosh a - (1 - Real.cos y) := by
      have h1c : 1 - Real.cos y ≤ 2 := by
        linarith
      nlinarith
    have hdiff :
        0 ≤
          ((Real.cosh R * Real.cos y + Real.cosh a) ^ 2 + (Real.sinh R * Real.sin y) ^ 2) -
            (Real.cosh R - Real.cosh a) ^ 2 := by
      rw [hfactor]
      exact mul_nonneg hterm1 hterm2
    nlinarith
  rw [hdecomp]
  exact hmodel

/-- Helper for Cartan section12 0035_Exercise_22: the right vertical side of the rectangle
has pointwise kernel norm bounded by `1 / (cosh R - cosh a)` along the standard parameterization. -/
lemma exercise22_right_vertical_kernel_norm_bound
    {a v R y : ℝ} (ha : 0 < a) (hv : 0 < v) (hRa : a < R)
    (hy : y ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    ‖exercise22Kernel a v ((R : ℂ) + y * Complex.I)‖ ≤
      1 / (Real.cosh R - Real.cosh a) := by
  have habs : |a| < |R| := by
    rw [abs_of_pos ha, abs_of_pos (lt_trans ha hRa)]
    exact hRa
  have hden_pos : 0 < Real.cosh R - Real.cosh a := by
    exact sub_pos.mpr ((Real.cosh_lt_cosh).2 habs)
  have hnum : ‖Complex.exp (Complex.I * ((v : ℂ) * ((R : ℂ) + y * Complex.I)))‖ ≤ 1 := by
    rw [exercise22_exp_phase_norm]
    have hle : -v * y ≤ 0 := by
      nlinarith [hv, hy.1]
    simpa using (Real.exp_le_one_iff.mpr hle)
  have hden_lower :
      Real.cosh R - Real.cosh a ≤
        ‖Complex.cosh ((R : ℂ) + y * Complex.I) + Real.cosh a‖ :=
    exercise22_right_vertical_denominator_lower_bound
      (a := a) (R := R) (y := y) ha hRa
  have hinv :
      ‖Complex.cosh ((R : ℂ) + y * Complex.I) + Real.cosh a‖⁻¹ ≤
        (Real.cosh R - Real.cosh a)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hden_pos hden_lower
  calc
    ‖exercise22Kernel a v ((R : ℂ) + y * Complex.I)‖ =
        ‖Complex.exp (Complex.I * ((v : ℂ) * ((R : ℂ) + y * Complex.I)))‖ *
          ‖Complex.cosh ((R : ℂ) + y * Complex.I) + Real.cosh a‖⁻¹ := by
      rw [exercise22Kernel, norm_div, div_eq_mul_inv]
    _ ≤ 1 * (Real.cosh R - Real.cosh a)⁻¹ := by
      gcongr
    _ = 1 / (Real.cosh R - Real.cosh a) := by
      rw [one_mul, one_div]

/-- Helper for Cartan section12 0035_Exercise_22: the right vertical side of the rectangle
contributes at most `2π / (cosh R - cosh a)` to the ML estimate. -/
lemma exercise22_right_vertical_segment_bound
    {a v R : ℝ} (ha : 0 < a) (hv : 0 < v) (hRa : a < R) :
    ‖∫ᶜ z in Path.segment (R : ℂ) (R + 2 * Real.pi * Complex.I), ((exercise22Kernel a v dz) z)‖ ≤
      2 * Real.pi / (Real.cosh R - Real.cosh a) := by
  have habs : |a| < |R| := by
    rw [abs_of_pos ha, abs_of_pos (lt_trans ha hRa)]
    exact hRa
  have hden_pos : 0 < Real.cosh R - Real.cosh a := by
    exact sub_pos.mpr ((Real.cosh_lt_cosh).2 habs)
  have hpi_nonneg : 0 ≤ Real.pi := by
    positivity
  have hbound :
      ∀ z ∈ segment ℝ (R : ℂ) (R + 2 * Real.pi * Complex.I),
        ‖((exercise22Kernel a v dz) z)‖ ≤ 1 / (Real.cosh R - Real.cosh a) := by
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨t, ht, rfl⟩
    have hy : 2 * Real.pi * t ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
      constructor <;> nlinarith [ht.1, ht.2, Real.pi_pos]
    have hline :
        AffineMap.lineMap (R : ℂ) (R + 2 * Real.pi * Complex.I) t =
          (R : ℂ) + (2 * Real.pi * t) * Complex.I := by
      simp [AffineMap.lineMap_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        mul_assoc, mul_left_comm, mul_comm]
    rw [hline]
    simpa [Complex.scalarOneForm] using
      exercise22_right_vertical_kernel_norm_bound
        (a := a) (v := v) (R := R) (y := 2 * Real.pi * t) ha hv hRa hy
  calc
    ‖∫ᶜ z in Path.segment (R : ℂ) (R + 2 * Real.pi * Complex.I), ((exercise22Kernel a v dz) z)‖ ≤
        (1 / (Real.cosh R - Real.cosh a)) * ‖(R + 2 * Real.pi * Complex.I) - (R : ℂ)‖ := by
          exact norm_curveIntegral_segment_le hbound
    _ = (1 / (Real.cosh R - Real.cosh a)) * (2 * Real.pi) := by
          simp [hpi_nonneg]
    _ = 2 * Real.pi / (Real.cosh R - Real.cosh a) := by
          field_simp [hden_pos.ne']

/-- Helper for Cartan section12 0035_Exercise_22: the left vertical side has the same pointwise
kernel norm bound after rewriting it against the right-side denominator estimate. -/
lemma exercise22_left_vertical_kernel_norm_bound
    {a v R y : ℝ} (ha : 0 < a) (hv : 0 < v) (hRa : a < R)
    (hy : y ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    ‖exercise22Kernel a v ((-R : ℂ) + y * Complex.I)‖ ≤
      1 / (Real.cosh R - Real.cosh a) := by
  have habs : |a| < |R| := by
    rw [abs_of_pos ha, abs_of_pos (lt_trans ha hRa)]
    exact hRa
  have hden_pos : 0 < Real.cosh R - Real.cosh a := by
    exact sub_pos.mpr ((Real.cosh_lt_cosh).2 habs)
  have hnum :
      ‖Complex.exp (Complex.I * ((v : ℂ) * ((-R : ℂ) + y * Complex.I)))‖ ≤ 1 := by
    rw [exercise22_exp_phase_norm]
    have hle : -v * y ≤ 0 := by
      nlinarith [hv, hy.1]
    simpa using (Real.exp_le_one_iff.mpr hle)
  have hcosh :
      Complex.cosh ((-R : ℂ) + y * Complex.I) =
        Complex.cosh ((R : ℂ) + (-y) * Complex.I) := by
    have harg :
        ((-R : ℂ) + y * Complex.I) = -((R : ℂ) + (-y) * Complex.I) := by
      apply Complex.ext <;> simp
    rw [harg, Complex.cosh_neg]
  have hden_lower :
      Real.cosh R - Real.cosh a ≤
        ‖Complex.cosh ((-R : ℂ) + y * Complex.I) + Real.cosh a‖ := by
    rw [hcosh]
    simpa [Real.cos_neg, Real.sin_neg] using
      exercise22_right_vertical_denominator_lower_bound
        (a := a) (R := R) (y := -y) ha hRa
  have hinv :
      ‖Complex.cosh ((-R : ℂ) + y * Complex.I) + Real.cosh a‖⁻¹ ≤
        (Real.cosh R - Real.cosh a)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hden_pos hden_lower
  calc
    ‖exercise22Kernel a v ((-R : ℂ) + y * Complex.I)‖ =
        ‖Complex.exp (Complex.I * ((v : ℂ) * ((-R : ℂ) + y * Complex.I)))‖ *
          ‖Complex.cosh ((-R : ℂ) + y * Complex.I) + Real.cosh a‖⁻¹ := by
      rw [exercise22Kernel, norm_div, div_eq_mul_inv]
    _ ≤ 1 * (Real.cosh R - Real.cosh a)⁻¹ := by
      gcongr
    _ = 1 / (Real.cosh R - Real.cosh a) := by
      rw [one_mul, one_div]

/-- Helper for Cartan section12 0035_Exercise_22: the left vertical side of the rectangle
obeys the same `2π / (cosh R - cosh a)` ML bound. -/
lemma exercise22_left_vertical_segment_bound
    {a v R : ℝ} (ha : 0 < a) (hv : 0 < v) (hRa : a < R) :
    ‖∫ᶜ z in Path.segment (-R + 2 * Real.pi * Complex.I) (-R), ((exercise22Kernel a v dz) z)‖ ≤
      2 * Real.pi / (Real.cosh R - Real.cosh a) := by
  have habs : |a| < |R| := by
    rw [abs_of_pos ha, abs_of_pos (lt_trans ha hRa)]
    exact hRa
  have hden_pos : 0 < Real.cosh R - Real.cosh a := by
    exact sub_pos.mpr ((Real.cosh_lt_cosh).2 habs)
  have hpi_nonneg : 0 ≤ Real.pi := by
    positivity
  have hbound :
      ∀ z ∈ segment ℝ (-R + 2 * Real.pi * Complex.I) (-R),
        ‖((exercise22Kernel a v dz) z)‖ ≤ 1 / (Real.cosh R - Real.cosh a) := by
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨t, ht, rfl⟩
    have hy : 2 * Real.pi * (1 - t) ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
      constructor <;> nlinarith [ht.1, ht.2, Real.pi_pos]
    have hline :
        AffineMap.lineMap (-R + 2 * Real.pi * Complex.I) (-R) t =
          (-R : ℂ) + (2 * Real.pi * (1 - t)) * Complex.I := by
      simp [AffineMap.lineMap_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        mul_assoc, mul_left_comm, mul_comm]
      ring
    rw [hline]
    simpa [Complex.scalarOneForm] using
      exercise22_left_vertical_kernel_norm_bound
        (a := a) (v := v) (R := R) (y := 2 * Real.pi * (1 - t)) ha hv hRa hy
  calc
    ‖∫ᶜ z in Path.segment (-R + 2 * Real.pi * Complex.I) (-R), ((exercise22Kernel a v dz) z)‖ ≤
        (1 / (Real.cosh R - Real.cosh a)) * ‖(-R : ℂ) - (-R + 2 * Real.pi * Complex.I)‖ := by
          exact norm_curveIntegral_segment_le hbound
    _ = (1 / (Real.cosh R - Real.cosh a)) * (2 * Real.pi) := by
          simp [hpi_nonneg]
    _ = 2 * Real.pi / (Real.cosh R - Real.cosh a) := by
          field_simp [hden_pos.ne']

/-- Helper for Exercise 22: on the exact right-plus-left normal form, the two vertical sides
satisfy the ML bound `4π / (cosh R - cosh a)`. -/
lemma exercise22_vertical_side_pair_bound
    {a v R : ℝ} (ha : 0 < a) (hv : 0 < v) (hRa : a < R) :
    ‖∫ᶜ z in Path.segment (R : ℂ) (R + 2 * Real.pi * Complex.I), ((exercise22Kernel a v dz) z) +
        ∫ᶜ z in Path.segment (-R + 2 * Real.pi * Complex.I) (-R), ((exercise22Kernel a v dz) z)‖ ≤
      4 * Real.pi / (Real.cosh R - Real.cosh a) := by
  calc
    ‖∫ᶜ z in Path.segment (R : ℂ) (R + 2 * Real.pi * Complex.I), ((exercise22Kernel a v dz) z) +
        ∫ᶜ z in Path.segment (-R + 2 * Real.pi * Complex.I) (-R), ((exercise22Kernel a v dz) z)‖ ≤
      ‖∫ᶜ z in Path.segment (R : ℂ) (R + 2 * Real.pi * Complex.I), ((exercise22Kernel a v dz) z)‖ +
        ‖∫ᶜ z in Path.segment (-R + 2 * Real.pi * Complex.I) (-R), ((exercise22Kernel a v dz) z)‖ := by
          exact norm_add_le _ _
    _ ≤ 2 * Real.pi / (Real.cosh R - Real.cosh a) +
        2 * Real.pi / (Real.cosh R - Real.cosh a) := by
          nlinarith [exercise22_right_vertical_segment_bound (a := a) (v := v) (R := R) ha hv hRa,
            exercise22_left_vertical_segment_bound (a := a) (v := v) (R := R) ha hv hRa]
    _ = 4 * Real.pi / (Real.cosh R - Real.cosh a) := by
          ring

/-- Helper for Exercise 22: the real kernel is dominated on `(0, ∞)` by `2 * exp (-x)`, which is
the comparison needed for improper-integral convergence. -/
lemma exercise22_realKernel_abs_le_two_exp_neg
    {a v x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    |Real.cos (v * x) / (Real.cosh x + Real.cosh a)| ≤ 2 * Real.exp (-x) := by
  -- Use `|cos| ≤ 1` and the lower bound `cosh x ≥ exp x / 2`.
  have hden_pos : 0 < Real.cosh x + Real.cosh a := by positivity
  have hcos : |Real.cos (v * x)| ≤ 1 := by exact Real.abs_cos_le_one (v * x)
  have hcosh_exp : Real.exp x / 2 ≤ Real.cosh x := by
    rw [Real.cosh_eq]
    nlinarith [Real.exp_pos (-x)]
  have hrecip :
      1 / (Real.cosh x + Real.cosh a) ≤ 2 * Real.exp (-x) := by
      have hden_ge : Real.exp x / 2 ≤ Real.cosh x + Real.cosh a := by
        nlinarith [hcosh_exp, Real.cosh_pos a]
      have hhalf_pos : 0 < Real.exp x / 2 := by positivity
      calc
        1 / (Real.cosh x + Real.cosh a) ≤ 1 / (Real.exp x / 2) := by
          exact one_div_le_one_div_of_le hhalf_pos hden_ge
        _ = 2 * Real.exp (-x) := by
          field_simp [Real.exp_ne_zero x]
          rw [← Real.exp_add]
          norm_num
  calc
    |Real.cos (v * x) / (Real.cosh x + Real.cosh a)| =
        |Real.cos (v * x)| / (Real.cosh x + Real.cosh a) := by
      rw [abs_div, abs_of_pos hden_pos]
    _ ≤ 1 / (Real.cosh x + Real.cosh a) := by
      gcongr
    _ ≤ 2 * Real.exp (-x) := hrecip

/-- Helper for Exercise 22: the truncated interval integrals converge to the `Set.Ioi` integral of
the real kernel because the exponential comparison gives absolute integrability. -/
lemma exercise22_intervalIntegral_tendsto_integral_Ioi
    {a v : ℝ} (ha : 0 < a) :
    Filter.Tendsto
      (fun R : ℝ ↦ ∫ x in (0 : ℝ)..R, Real.cos (v * x) / (Real.cosh x + Real.cosh a))
      Filter.atTop
      (nhds
        (∫ x in Set.Ioi (0 : ℝ), Real.cos (v * x) / (Real.cosh x + Real.cosh a) ∂volume)) := by
  let f : ℝ → ℝ := fun x ↦ Real.cos (v * x) / (Real.cosh x + Real.cosh a)
  have hdom : IntegrableOn (fun x : ℝ ↦ 2 * Real.exp (-x)) (Set.Ioi 0) := by
    simpa using (exp_neg_integrableOn_Ioi (0 : ℝ) (b := 1) zero_lt_one).const_mul (2 : ℝ)
  have hcont : Continuous f := by
    refine (Real.continuous_cos.comp (continuous_const.mul continuous_id)).div ?_ ?_
    · exact Real.continuous_cosh.add continuous_const
    · intro x
      positivity
  have hfint : IntegrableOn f (Set.Ioi 0) := by
    refine Integrable.mono' hdom hcont.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    have hden_pos : 0 < Real.cosh x + Real.cosh a := by positivity
    simpa [f, Real.norm_eq_abs, abs_div, abs_of_pos hden_pos] using
      exercise22_realKernel_abs_le_two_exp_neg (a := a) (v := v) (x := x) ha hx
  simpa [f] using
    (MeasureTheory.intervalIntegral_tendsto_integral_Ioi
      (μ := volume) (f := f) (a := (0 : ℝ)) (b := fun R : ℝ ↦ R) hfint Filter.tendsto_id)

/-- Cartan section12 0035_Exercise_22. After using the evenness in `v`, the remaining
source-faithful contour computation is exactly the textbook case `0 < a` and `0 < v`. -/
lemma exercise22_positive_parameters_formula_core
    {a v : ℝ} (ha : 0 < a) (hv : 0 < v) :
    ∫ x in Set.Ioi (0 : ℝ), Real.cos (v * x) / (Real.cosh x + Real.cosh a) ∂volume =
      Real.pi * Real.sin (v * a) / (Real.sinh (Real.pi * v) * Real.sinh a) := by
  let f : ℝ → ℝ := fun x ↦ Real.cos (v * x) / (Real.cosh x + Real.cosh a)
  let I : ℝ := ∫ x in Set.Ioi (0 : ℝ), f x ∂volume
  let bottomValue : ℝ → ℂ := fun R ↦
    (((2 : ℝ) : ℂ) * ∫ x in (0 : ℝ)..R, ((f x : ℝ) : ℂ))
  let verticalPair : ℝ → ℂ := fun R ↦
    ∫ᶜ z in Path.segment (R : ℂ) (R + 2 * Real.pi * Complex.I), ((exercise22Kernel a v dz) z) +
      ∫ᶜ z in Path.segment (-R + 2 * Real.pi * Complex.I) (-R), ((exercise22Kernel a v dz) z)
  let rhsC : ℂ :=
    (((4 * Real.pi * Real.exp (-Real.pi * v) * Real.sin (v * a) / Real.sinh a : ℝ)) : ℂ)
  have hEventuallyEq :
      ∀ᶠ R in Filter.atTop,
        ((((1 - Real.exp (-2 * Real.pi * v)) : ℝ) : ℂ) * bottomValue R) + verticalPair R = rhsC := by
    filter_upwards [Filter.eventually_gt_atTop a] with R hRa
    have hfixed := exercise22_fixed_rectangle_identity (a := a) (v := v) (R := R) ha hRa
    dsimp at hfixed
    have hzw : Complex.mk (R + (2 * Real.pi * Complex.I).re) (-0) = (R : ℂ) := by
      apply Complex.ext <;> simp
    have hwz : Complex.mk (-R) (0 + (2 * Real.pi * Complex.I).im) = -R + 2 * Real.pi * Complex.I := by
      apply Complex.ext <;> simp
    have hfixed' :
        ((((1 - Real.exp (-2 * Real.pi * v)) : ℝ) : ℂ) *
            ∫ᶜ z in Path.segment (-R : ℂ) (R : ℂ), ((exercise22Kernel a v dz) z)) +
            (∫ᶜ z in Path.segment (R : ℂ) (R + 2 * Real.pi * Complex.I), ((exercise22Kernel a v dz) z) +
              ∫ᶜ z in Path.segment (-R + 2 * Real.pi * Complex.I) (-R), ((exercise22Kernel a v dz) z)) =
          rhsC := by
      rw [hzw, hwz] at hfixed
      simpa [rhsC, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
        using hfixed
    dsimp [bottomValue, verticalPair, rhsC] at hfixed' ⊢
    rw [exercise22_bottom_segment_eq_double_intervalIntegral (a := a) (v := v) (R := R)] at hfixed'
    simpa [f] using hfixed'
  have hboundToZero :
      Filter.Tendsto
        (fun R : ℝ ↦ 4 * Real.pi / (Real.cosh R - Real.cosh a))
        Filter.atTop
        (nhds 0) := by
    have hden :
        Filter.Tendsto (fun R : ℝ ↦ Real.cosh R - Real.cosh a) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop.mpr ?_
      intro b
      have hExp :=
        Filter.tendsto_atTop.mp Real.tendsto_exp_atTop (2 * (b + Real.cosh a))
      filter_upwards [hExp] with R hR
      have hcosh_exp : Real.exp R / 2 ≤ Real.cosh R := by
        rw [Real.cosh_eq]
        nlinarith [Real.exp_pos (-R)]
      nlinarith
    simpa using Filter.Tendsto.div_atTop tendsto_const_nhds hden
  have hverticalZero : Filter.Tendsto verticalPair Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hboundToZero
    filter_upwards [Filter.eventually_gt_atTop a] with R hRa
    simpa [verticalPair] using
      exercise22_vertical_side_pair_bound (a := a) (v := v) (R := R) ha hv hRa
  have hintervalComplex :
      Filter.Tendsto
        (fun R : ℝ ↦ (((∫ x in (0 : ℝ)..R, f x : ℝ) : ℝ) : ℂ))
        Filter.atTop
        (nhds ((I : ℝ) : ℂ)) := by
    simpa [I, f] using
      (Complex.continuous_ofReal.continuousAt.tendsto.comp
        (exercise22_intervalIntegral_tendsto_integral_Ioi (a := a) (v := v) ha))
  have hbottomTendsto :
      Filter.Tendsto bottomValue Filter.atTop (nhds ((((2 : ℝ) : ℂ) * ((I : ℝ) : ℂ)))) := by
    simpa [bottomValue, intervalIntegral.integral_ofReal] using
      Filter.Tendsto.const_mul (((2 : ℝ) : ℂ)) hintervalComplex
  have hlhsTendsto :
      Filter.Tendsto
        (fun R : ℝ ↦ ((((1 - Real.exp (-2 * Real.pi * v)) : ℝ) : ℂ) * bottomValue R) + verticalPair R)
        Filter.atTop
        (nhds
          (((((1 - Real.exp (-2 * Real.pi * v)) : ℝ) : ℂ) * (((2 : ℝ) : ℂ) * ((I : ℝ) : ℂ))) + 0)) := by
    exact (Filter.Tendsto.const_mul (((1 - Real.exp (-2 * Real.pi * v)) : ℝ) : ℂ) hbottomTendsto).add
      hverticalZero
  have hlimit :
      (((((1 - Real.exp (-2 * Real.pi * v)) : ℝ) : ℂ) * (((2 : ℝ) : ℂ) * ((I : ℝ) : ℂ))) + 0) =
        rhsC := by
    exact
      tendsto_nhds_unique_of_eventuallyEq hlhsTendsto tendsto_const_nhds hEventuallyEq
  have hreal :
      (1 - Real.exp (-2 * Real.pi * v)) * (2 * I) =
        4 * Real.pi * Real.exp (-Real.pi * v) * Real.sin (v * a) / Real.sinh a := by
    apply Complex.ofReal_inj.mp
    simpa [I, rhsC, mul_assoc, mul_left_comm, mul_comm] using hlimit
  have hsinh_factor :
      2 * Real.exp (-Real.pi * v) * Real.sinh (Real.pi * v) =
        1 - Real.exp (-2 * Real.pi * v) := by
    have hneg : -Real.pi * v = -(Real.pi * v) := by
      ring
    have h1 : Real.exp (-(Real.pi * v)) * Real.exp (Real.pi * v) = 1 := by
      rw [← Real.exp_add]
      simp
    have h2 :
        Real.exp (-(Real.pi * v)) * Real.exp (-(Real.pi * v)) =
          Real.exp (-2 * Real.pi * v) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      2 * Real.exp (-Real.pi * v) * Real.sinh (Real.pi * v) =
          2 * Real.exp (-(Real.pi * v)) *
            ((Real.exp (Real.pi * v) - Real.exp (-(Real.pi * v))) / 2) := by
              rw [hneg, Real.sinh_eq]
      _ = Real.exp (-(Real.pi * v)) * Real.exp (Real.pi * v) -
            Real.exp (-(Real.pi * v)) * Real.exp (-(Real.pi * v)) := by
              ring
      _ = 1 - Real.exp (-2 * Real.pi * v) := by
            rw [h1, h2]
  have hsinh_a_ne : Real.sinh a ≠ 0 := Real.sinh_ne_zero.2 ha.ne'
  have hsinh_v_ne : Real.sinh (Real.pi * v) ≠ 0 := by
    exact Real.sinh_ne_zero.2 (by positivity)
  have hexp_ne : Real.exp (-Real.pi * v) ≠ 0 := Real.exp_ne_zero _
  have hsolve := hreal
  rw [← hsinh_factor] at hsolve
  field_simp [hsinh_a_ne, hsinh_v_ne, hexp_ne] at hsolve
  apply (eq_div_iff (mul_ne_zero hsinh_v_ne hsinh_a_ne)).2
  nlinarith

/-- Helper for Exercise 22: in the textbook `a > 0` regime, the contour integral over the
rectangle with vertices `±R` and `±R + 2π i` yields the stated formula after letting `R → ∞`. -/
lemma exercise22_positive_parameter_formula
    {a v : ℝ} (ha : 0 < a) (hv : v ≠ 0) :
    ∫ x in Set.Ioi (0 : ℝ), Real.cos (v * x) / (Real.cosh x + Real.cosh a) ∂volume =
      Real.pi * Real.sin (v * a) / (Real.sinh (Real.pi * v) * Real.sinh a) := by
  -- Reduce the remaining nonzero-frequency case to the positive-frequency core using evenness.
  rw [exercise22_integral_abs_frequency a v, exercise22_rhs_abs_frequency]
  exact exercise22_positive_parameters_formula_core ha (abs_pos.mpr hv)

/-- Corollary for Cartan section12 0035_Exercise_22: if `a ≠ 0` and `v ≠ 0`, then
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
