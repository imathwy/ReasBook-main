import Mathlib
import DifferentialForms_Cartan_1970.III.section11.«0003_Theorem_III_5_extra_2»

-- Declarations for this item will be appended below by the statement pipeline.

open Complex
open scoped Topology

/-
This example is organized around the core/canonical residue owner
`meromorphicTrailingCoeffAt`. Its contour companion is the chapter's established `bridge/view`
owner `LocalResidueCircle`, not a separate existential small-circle wrapper.
-/

/-- Helper for Example III.5-extra-5: the original integrand is the Cauchy first-derivative kernel
times the regular factor `z ↦ exp (I * z) / (z * (z + I)^2)`. -/
lemma exp_I_mul_div_z_mul_z_sq_add_one_sq_factor (z : ℂ) :
    exp (I * z) / (z * (z ^ 2 + 1) ^ 2) =
      (1 / (z - I) ^ 2) • (exp (I * z) / (z * (z + I) ^ 2)) := by
  by_cases hz0 : z = 0
  · -- At `z = 0`, both sides vanish because every denominator is interpreted via inversion.
    simp [hz0]
  · by_cases hzI : z = I
    · -- At the pole center `z = I`, both sides also reduce to zero in the field convention.
      simp [hzI]
    · by_cases hznegI : z = -I
      · -- At the other pole `z = -I`, the regular factor already vanishes after inversion.
        simp [hznegI]
      · -- Away from the three singular points, clear denominators after factoring `z^2 + 1`.
        have hz_sub_I : z - I ≠ 0 := sub_ne_zero.mpr hzI
        have hz_add_I : z + I ≠ 0 := by
          intro hzadd
          exact hznegI (eq_neg_of_add_eq_zero_left hzadd)
        have hfactor : z ^ 2 + 1 = (z - I) * (z + I) := by
          calc
            z ^ 2 + 1 = z ^ 2 - I ^ 2 := by simp [Complex.I_sq]
            _ = (z - I) * (z + I) := by ring
        rw [smul_eq_mul]
        field_simp [div_eq_mul_inv, hfactor, hz0, hz_sub_I, hz_add_I]
        rw [hfactor]
        ring

/-- Helper for Example III.5-extra-5: the denominator `z ↦ z * (z + I)^2` has derivative `-8` at
`z = I`. -/
lemma hasDerivAt_z_mul_z_add_I_sq_at_I :
    HasDerivAt (fun z : ℂ ↦ z * (z + I) ^ 2) (-8 : ℂ) I := by
  -- Differentiate the product `z · (z + I)^2` directly, then collapse the resulting constant.
  have h :
      HasDerivAt
        (fun z : ℂ ↦ z * (z + I) ^ 2)
        (1 * (I + I) ^ 2 + I * (2 * (I + I)))
        I := by
    simpa using (hasDerivAt_id I).mul (((hasDerivAt_id I).add_const I).pow 2)
  have hconst : (((I + I) ^ 2 + I * (2 * (I + I))) : ℂ) = -8 := by
    calc
      (((I + I) ^ 2 + I * (2 * (I + I))) : ℂ)
        = (2 * I) * (2 * I) + I * (4 * I) := by ring
      _ = -8 := by
        have hleft : (2 * I) * (2 * I) = (-4 : ℂ) := by
          calc
            (2 * I) * (2 * I) = (4 : ℂ) * (I * I) := by ring
            _ = (-4 : ℂ) := by simp
        have hright : I * (4 * I) = (-4 : ℂ) := by
          calc
            I * (4 * I) = (4 : ℂ) * (I * I) := by ring
            _ = (-4 : ℂ) := by simp
        rw [hleft, hright]
        norm_num
  simpa [hconst] using h

/-- Helper for Example III.5-extra-5: on the closed ball of radius `1/2` around `I`, the regular
factor denominator avoids the singular points `0` and `-I`. -/
lemma regular_factor_denominator_ne_zero_on_closedBall_I_half
    {z : ℂ} (hz : z ∈ Metric.closedBall I (1 / 2 : ℝ)) :
    z ≠ 0 ∧ z + I ≠ 0 := by
  rw [Metric.mem_closedBall, Complex.dist_eq] at hz
  constructor
  · -- The center `0` is distance `1` from `I`, so it cannot lie in this closed ball.
    intro hz0
    subst hz0
    norm_num at hz
  · -- Likewise `-I` is distance `2` from `I`, well outside the radius `1/2`.
    intro hzneg
    have hz_eq : z = -I := by simpa using eq_neg_of_add_eq_zero_left hzneg
    subst hz_eq
    have hnorm : ‖((-I : ℂ) - I)‖ = (2 : ℝ) := by
      calc
        ‖((-I : ℂ) - I)‖ = ‖((-2 : ℂ) * I)‖ := by
          congr 1
          ring
        _ = ‖(-2 : ℂ)‖ * ‖I‖ := norm_mul _ _
        _ = 2 := by norm_num
    linarith

/-- Helper for Example III.5-extra-5: the regular factor is holomorphic on the closed ball of
radius `1/2` around `I`. -/
lemma differentiableOn_exp_I_mul_div_z_mul_z_add_I_sq_closedBall_I_half :
    DifferentiableOn ℂ
      (fun z : ℂ ↦ exp (I * z) / (z * (z + I) ^ 2))
      (Metric.closedBall I (1 / 2 : ℝ)) := by
  intro z hz
  rcases regular_factor_denominator_ne_zero_on_closedBall_I_half hz with ⟨hz0, hzadd⟩
  have hden_ne : z * (z + I) ^ 2 ≠ 0 := mul_ne_zero hz0 (pow_ne_zero 2 hzadd)
  -- The only obstruction to holomorphy is denominator vanishing, which the previous lemma rules
  -- out on the chosen closed ball.
  exact
    ((Complex.differentiableAt_exp.comp z (hasDerivAt_const_mul I).differentiableAt).div
      (differentiableAt_id.mul ((differentiableAt_id.add_const I).pow 2))
      hden_ne).differentiableWithinAt

/-- Example III.5-extra-5: for
`f z = exp (I * z) / (z * (z ^ 2 + 1) ^ 2)`, the residue at the double pole `z = I`
is the derivative at `I` of the regular factor
`z ↦ exp (I * z) / (z * (z + I) ^ 2)`, namely `-(3 / (4 * exp 1))`. -/
theorem residue_exp_I_mul_div_z_mul_z_sq_add_one_sq_at_I :
    HasDerivAt
      (fun z : ℂ ↦ exp (I * z) / (z * (z + I) ^ 2))
      ((-(3 / (4 * Real.exp 1) : ℝ) : ℂ)) I := by
  have hnum :
      HasDerivAt (fun z : ℂ ↦ exp (I * z)) (I * exp (I * I)) I := by
    -- Differentiate the exponential numerator through the linear map `z ↦ I * z`.
    have hlin : HasDerivAt (fun z : ℂ ↦ I * z) I I := by
      simpa using (hasDerivAt_const_mul (x := I) I)
    have hcomp :
        HasDerivAt (fun z : ℂ ↦ exp (I * z)) (exp (I * I) * I) I := by
      simpa [Function.comp] using
        (Complex.hasDerivAt_exp (I * I)).comp I hlin
    simpa [mul_comm] using hcomp
  have hden_nonzero : (I : ℂ) * (I + I) ^ 2 ≠ 0 := by
    norm_num [pow_two, Complex.I_sq]
  have hquot :
      HasDerivAt
        (fun z : ℂ ↦ exp (I * z) / (z * (z + I) ^ 2))
        (((I * exp (I * I)) * (I * (I + I) ^ 2) - exp (I * I) * (-8 : ℂ)) /
          (I * (I + I) ^ 2) ^ 2)
        I := hnum.div hasDerivAt_z_mul_z_add_I_sq_at_I hden_nonzero
  -- Simplify the quotient-rule constant to the textbook value `-(3 / (4e))`.
  have hconst :
      (((I * exp (I * I)) * (I * (I + I) ^ 2) - exp (I * I) * (-8 : ℂ)) /
        (I * (I + I) ^ 2) ^ 2) =
        (-(3 / (4 * exp (1 : ℂ))) : ℂ) := by
    have hden : (I * (I + I) ^ 2 : ℂ) = (-4 : ℂ) * I := by
      have hI3 : (I : ℂ) ^ 3 = -I := by
        calc
          (I : ℂ) ^ 3 = I ^ 2 * I := by ring
          _ = -I := by simp [Complex.I_sq]
      calc
        (I * (I + I) ^ 2 : ℂ) = (4 : ℂ) * I ^ 3 := by ring
        _ = (4 : ℂ) * (-I) := by rw [hI3]
        _ = (-4 : ℂ) * I := by ring
    rw [show exp (I * I) = exp (-1 : ℂ) by simp, hden, Complex.exp_neg]
    simp [pow_two, div_eq_mul_inv]
    field_simp [Complex.exp_ne_zero (1 : ℂ)]
    norm_num [pow_two, Complex.I_sq]
  convert hquot using 1
  · simpa [Complex.ofReal_exp, show exp (I * I) = exp (-1 : ℂ) by simp] using
      hconst.symm

/-- Companion contour form of Example III.5-extra-5, stated with the chapter's canonical
small-circle bridge owner `LocalResidueCircle`. -/
theorem circleIntegral_exp_I_mul_div_z_mul_z_sq_add_one_sq_at_I :
    LocalResidueCircle
      Set.univ
      Set.univ
      (fun z : ℂ ↦ exp (I * z) / (z * (z ^ 2 + 1) ^ 2))
      I
      ((-(3 / (4 * Real.exp 1) : ℝ) : ℂ)) := by
  let g : ℂ → ℂ := fun z ↦ exp (I * z) / (z * (z + I) ^ 2)
  refine ⟨1 / 2, by norm_num, ?_, ?_, ?_⟩
  · -- Any closed ball is contained in `Set.univ`, hence in its interior.
    simp
  · -- The ambient domain is also `Set.univ`, so the containment is immediate.
    simp
  · have hderiv :
        deriv g I = ((-(3 / (4 * Real.exp 1) : ℝ) : ℂ)) := by
        simpa [g] using residue_exp_I_mul_div_z_mul_z_sq_add_one_sq_at_I.deriv
    have hcircle :
        ∮ w in C(I, 1 / 2),
          (1 / (w - I) ^ 2) • g w =
            (2 * Real.pi * Complex.I : ℂ) • deriv g I := by
      -- Apply the first-derivative Cauchy formula to the regular factor on the chosen ball.
      simpa [g] using
        (DifferentiableOn.deriv_eq_smul_circleIntegral
          (f := g) (c := I) (R := (1 / 2 : ℝ))
          (by norm_num : 0 < (1 / 2 : ℝ))
          differentiableOn_exp_I_mul_div_z_mul_z_add_I_sq_closedBall_I_half)
    calc
      ∮ w in C(I, 1 / 2), exp (I * w) / (w * (w ^ 2 + 1) ^ 2)
        = ∮ w in C(I, 1 / 2), (1 / (w - I) ^ 2) • g w := by
            -- Rewrite the contour integrand into the Cauchy derivative-kernel form.
            refine circleIntegral.integral_congr (show (0 : ℝ) ≤ 1 / 2 by norm_num) ?_
            intro w hw
            simpa [g] using exp_I_mul_div_z_mul_z_sq_add_one_sq_factor w
      _ = (2 * Real.pi * Complex.I : ℂ) • deriv g I := hcircle
      _ = (2 * Real.pi * Complex.I : ℂ) * ((-(3 / (4 * Real.exp 1) : ℝ) : ℂ)) := by
            simp [smul_eq_mul, hderiv]

/-- Auxiliary derivative computation for Example III.5-extra-5: if
`g z = exp (I * z) / (z * (z + I) ^ 2)`, then `g' (I) = -(3 / (4 * exp 1))`. -/
theorem hasDerivAt_exp_I_mul_div_z_mul_z_add_I_sq_at_I :
    HasDerivAt
      (fun z : ℂ ↦ exp (I * z) / (z * (z + I) ^ 2))
      ((-(3 / (4 * Real.exp 1) : ℝ) : ℂ)) I := by
  -- This auxiliary statement is exactly the derivative computation already proved above.
  simpa using residue_exp_I_mul_div_z_mul_z_sq_add_one_sq_at_I
