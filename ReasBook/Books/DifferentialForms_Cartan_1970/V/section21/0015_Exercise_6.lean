import Mathlib
import DifferentialForms_Cartan_1970.V.section20.«0007_Remark_V_3_extra_5»

open scoped BigOperators

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling: this file lies in the complex Gamma / digamma special-functions domain.
-- Sampled owner-layer declarations:
-- * `Complex.digamma`
-- * `Complex.digamma_apply_add_one`
-- * `Complex.Gamma_mul_Gamma_add_half`
-- * `DifferentialForms_Cartan_1970.V.section20.0007_Remark_V_3_extra_5.deriv_complex_digamma_eq_inverse_square_series`
-- Owner abstraction: the canonical owner for the logarithmic derivative `Γ' / Γ` is
-- `Complex.digamma`, while Legendre's duplication formula is owned by
-- `Complex.Gamma_mul_Gamma_add_half`.
-- Primitive data: `Complex.Gamma` and the derived owner `Complex.digamma`.
-- Derived API: the digamma functional equation, its derivative identities, and Gauss's
-- multiplication formula.
-- Layer triage: item (1) is a source-facing companion stated through the core owner
-- `Complex.digamma`; item (2) first recalls the core/canonical duplication theorem and then
-- states the source-facing Gauss multiplication formula.

/-- Helper for Exercise 6: if neither `z` nor `z + 1 / 2` is a Gamma pole, then `2z` is not a
Gamma pole either. -/
lemma two_mul_nonpole_of_shift_nonpoles {z : ℂ}
    (hz : ∀ m : ℕ, z ≠ -m)
    (hz_half : ∀ m : ℕ, z + (1 / 2 : ℂ) ≠ -m) :
    ∀ m : ℕ, (2 : ℂ) * z ≠ -m := by
  intro m hm
  rcases Nat.even_or_odd' m with ⟨k, hk | hk⟩
  · -- The even case reduces the pole of `2z` to a pole of `z`.
    subst m
    have htwo : (2 : ℂ) ≠ 0 := by norm_num
    have hzk : z = -(k : ℂ) := by
      apply (mul_right_injective₀ htwo)
      simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hm
    exact hz k hzk
  · -- The odd case reduces the pole of `2z` to a pole of `z + 1 / 2`.
    subst m
    have htwo : (2 : ℂ) ≠ 0 := by norm_num
    have hscaled : (2 : ℂ) * (z + (1 / 2 : ℂ)) = -(2 * k : ℂ) := by
      calc
        (2 : ℂ) * (z + (1 / 2 : ℂ)) = (2 : ℂ) * z + 1 := by ring
        _ = -(2 * k : ℂ) := by
              rw [hm]
              norm_num [Nat.cast_mul, Nat.cast_add]
    have hz_half_k : z + (1 / 2 : ℂ) = -(k : ℂ) := by
      apply (mul_right_injective₀ htwo)
      simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hscaled
    exact hz_half k hz_half_k

/-- Helper for Exercise 6: the inverse-square series on the nonnegative integers is summable. -/
lemma inverse_square_series_summable (z : ℂ) :
    Summable (fun n : ℕ ↦ 1 / ((z + n : ℂ) ^ (2 : ℕ))) := by
  -- Use the standard Eisenstein-series summability for the linear denominator `z + d`.
  simpa [one_div] using
    (summable_int_iff_summable_nat_and_neg.mp
      (EisensteinSeries.linear_right_summable z 1 (k := 2) (by norm_num))).1

/-- Helper for Exercise 6: the even fiber of the doubled inverse-square series is the original
inverse-square term at `z + n`. -/
lemma doubled_inverse_square_even {z : ℂ} {n : ℕ} (hz : z ≠ -(n : ℂ)) :
    4 * (1 / ((((2 : ℂ) * z) + (2 * n : ℂ)) ^ (2 : ℕ))) =
      1 / ((z + n : ℂ) ^ (2 : ℕ)) := by
  -- Rewrite the denominator as `2 * (z + n)` and cancel the resulting square factor.
  have hzn : (z + n : ℂ) ≠ 0 := by
    intro hzero
    apply hz
    simpa using eq_neg_of_add_eq_zero_left hzero
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  calc
    4 * (1 / ((((2 : ℂ) * z) + (2 * n : ℂ)) ^ (2 : ℕ)))
      = 4 * (1 / (((2 : ℂ) * (z + n : ℂ)) ^ (2 : ℕ))) := by
          congr 2
          ring
    _ = 4 * (1 / ((4 : ℂ) * ((z + n : ℂ) ^ (2 : ℕ)))) := by
          congr 2
          ring
    _ = 1 / ((z + n : ℂ) ^ (2 : ℕ)) := by
          field_simp [hzn, htwo]

/-- Helper for Exercise 6: the odd fiber of the doubled inverse-square series is the shifted
inverse-square term at `z + 1 / 2 + n`. -/
lemma doubled_inverse_square_odd {z : ℂ} {n : ℕ}
    (hz_half : z + (1 / 2 : ℂ) ≠ -(n : ℂ)) :
    4 * (1 / ((((2 : ℂ) * z) + (2 * n + 1 : ℂ)) ^ (2 : ℕ))) =
      1 / ((z + (1 / 2 : ℂ) + n : ℂ) ^ (2 : ℕ)) := by
  -- Rewrite the denominator as `2 * (z + 1 / 2 + n)` and cancel the square factor.
  have hzn : (z + (1 / 2 : ℂ) + n : ℂ) ≠ 0 := by
    intro hzero
    apply hz_half
    simpa [add_assoc] using eq_neg_of_add_eq_zero_left hzero
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  calc
    4 * (1 / ((((2 : ℂ) * z) + (2 * n + 1 : ℂ)) ^ (2 : ℕ)))
      = 4 * (1 / (((2 : ℂ) * (z + (1 / 2 : ℂ) + n : ℂ)) ^ (2 : ℕ))) := by
          congr 2
          ring
    _ = 4 * (1 / ((4 : ℂ) * ((z + (1 / 2 : ℂ) + n : ℂ) ^ (2 : ℕ)))) := by
          congr 2
          ring
    _ = 1 / ((z + (1 / 2 : ℂ) + n : ℂ) ^ (2 : ℕ)) := by
          field_simp [hzn, htwo]

/-- Exercise 6 (1): away from the poles of the relevant Gamma factors, the derivative identity for
the logarithmic derivative `Γ' / Γ` at `z`, `z + 1 / 2`, and `2z`. Written canonically using the
owner `Complex.digamma`. -/
theorem exercise_6_gamma_log_deriv_derivative_identity {z : ℂ}
    (hz : ∀ m : ℕ, z ≠ -m)
    (hz_half : ∀ m : ℕ, z + (1 / 2 : ℂ) ≠ -m) :
    deriv Complex.digamma z + deriv Complex.digamma (z + (1 / 2 : ℂ)) =
      4 * deriv Complex.digamma ((2 : ℂ) * z) := by
  -- Express all three derivatives through the inverse-square series from the previous section.
  have hz_two : ∀ m : ℕ, (2 : ℂ) * z ≠ -m :=
    two_mul_nonpole_of_shift_nonpoles hz hz_half
  have hseries_z :=
    deriv_complex_digamma_eq_inverse_square_series z hz
  have hseries_half :=
    deriv_complex_digamma_eq_inverse_square_series (z + (1 / 2 : ℂ)) hz_half
  have hseries_two :=
    deriv_complex_digamma_eq_inverse_square_series ((2 : ℂ) * z) hz_two
  let f : ℕ → ℂ := fun n ↦ 4 * (1 / ((((2 : ℂ) * z) + n : ℂ) ^ (2 : ℕ)))
  have hs_even : Summable (fun n : ℕ ↦ f (2 * n)) := by
    -- The even fiber is exactly the original inverse-square series at `z`.
    refine (inverse_square_series_summable z).congr ?_
    intro n
    simpa [f] using (doubled_inverse_square_even (z := z) (n := n) (hz := hz n)).symm
  have hs_odd : Summable (fun n : ℕ ↦ f (2 * n + 1)) := by
    -- The odd fiber is the shifted inverse-square series at `z + 1 / 2`.
    refine (inverse_square_series_summable (z + (1 / 2 : ℂ))).congr ?_
    intro n
    simpa [f] using (doubled_inverse_square_odd (z := z) (n := n) (hz_half := hz_half n)).symm
  calc
    deriv Complex.digamma z + deriv Complex.digamma (z + (1 / 2 : ℂ))
      = (∑' n : ℕ, 1 / ((z + n : ℂ) ^ (2 : ℕ))) +
          ∑' n : ℕ, 1 / ((z + (1 / 2 : ℂ) + n : ℂ) ^ (2 : ℕ)) := by
            rw [hseries_z, hseries_half]
    _ = (∑' n : ℕ, f (2 * n)) + ∑' n : ℕ, f (2 * n + 1) := by
          congr 1
          · apply tsum_congr
            intro n
            simpa [f] using
              (doubled_inverse_square_even (z := z) (n := n) (hz := hz n)).symm
          · apply tsum_congr
            intro n
            simpa [f] using
              (doubled_inverse_square_odd (z := z) (n := n) (hz_half := hz_half n)).symm
    _ = ∑' n : ℕ, f n := by
          simpa using tsum_even_add_odd hs_even hs_odd
    _ = 4 * ∑' n : ℕ, 1 / ((((2 : ℂ) * z) + n : ℂ) ^ (2 : ℕ)) := by
          simp [f, tsum_mul_left]
    _ = 4 * deriv Complex.digamma ((2 : ℂ) * z) := by
          rw [← hseries_two]

/- Exercise 6 (2): after integrating and determining the constants, the duplication formula is the
canonical mathlib theorem `Complex.Gamma_mul_Gamma_add_half`. -/
#check Complex.Gamma_mul_Gamma_add_half

/-- Helper for Exercise 6: the `p = 2` instance of Gauss's multiplication formula is exactly
Legendre's duplication formula after normalizing the scalar factor. -/
lemma gauss_multiplication_formula_two (z : ℂ) :
    Complex.Gamma ((2 : ℂ) * z) =
      ((2 * Real.pi : ℂ) ^ (-((2 - 1 : ℂ) / 2))) *
        (2 : ℂ) ^ ((2 : ℂ) * z - (1 / 2 : ℂ)) *
          (∏ j ∈ Finset.range 2, Complex.Gamma (z + (j : ℂ) / (2 : ℂ))) := by
  -- Start from the canonical duplication formula and divide by its nonzero scalar factor.
  have hsqrtpi : (↑(Real.sqrt Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr Real.pi_pos
  have hpow : (2 : ℂ) ^ (1 - (2 : ℂ) * z) ≠ 0 := by
    exact (Complex.cpow_ne_zero_iff).2 (Or.inl two_ne_zero)
  have hscalar :
      (2 : ℂ) ^ (1 - (2 : ℂ) * z) * ↑(Real.sqrt Real.pi) ≠ 0 :=
    mul_ne_zero hpow hsqrtpi
  have hdup := Complex.Gamma_mul_Gamma_add_half z
  have hdup_div :
      Complex.Gamma ((2 : ℂ) * z) =
        (Complex.Gamma z * Complex.Gamma (z + 1 / 2)) /
          ((2 : ℂ) ^ (1 - (2 : ℂ) * z) * ↑(Real.sqrt Real.pi)) := by
    -- This isolates the Gamma product with the inverse duplication scalar.
    apply (eq_div_iff hscalar).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hdup.symm
  have hpi_inv :
      ((Real.pi : ℂ) ^ (-(1 / 2 : ℂ))) = (↑(Real.sqrt Real.pi) : ℂ)⁻¹ := by
    -- Convert the positive real square root identity into the complex `cpow` normalization.
    rw [Complex.cpow_neg, Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_nonneg, Complex.ofReal_div,
      Complex.ofReal_one]
    norm_num
  have hcoeff :
      ((2 * Real.pi : ℂ) ^ (-((2 - 1 : ℂ) / 2))) * (2 : ℂ) ^ ((2 : ℂ) * z - (1 / 2 : ℂ)) =
        (((2 : ℂ) ^ (1 - (2 : ℂ) * z) * ↑(Real.sqrt Real.pi)) : ℂ)⁻¹ := by
    -- Normalize the scalar exactly to the inverse duplication coefficient.
    have hmul_pi :
        ((2 * Real.pi : ℂ) ^ (-(1 / 2 : ℂ))) =
          (2 : ℂ) ^ (-(1 / 2 : ℂ)) * (Real.pi : ℂ) ^ (-(1 / 2 : ℂ)) := by
      simpa using Complex.mul_cpow_ofReal_nonneg two_pos.le Real.pi_nonneg (-(1 / 2 : ℂ))
    calc
      ((2 * Real.pi : ℂ) ^ (-((2 - 1 : ℂ) / 2))) * (2 : ℂ) ^ ((2 : ℂ) * z - (1 / 2 : ℂ))
        = ((2 * Real.pi : ℂ) ^ (-(1 / 2 : ℂ))) * (2 : ℂ) ^ ((2 : ℂ) * z - (1 / 2 : ℂ)) := by
            norm_num
      _ = ((2 : ℂ) ^ (-(1 / 2 : ℂ)) * (Real.pi : ℂ) ^ (-(1 / 2 : ℂ))) *
            (2 : ℂ) ^ ((2 : ℂ) * z - (1 / 2 : ℂ)) := by
              rw [hmul_pi]
      _ = (Real.pi : ℂ) ^ (-(1 / 2 : ℂ)) *
            ((2 : ℂ) ^ (-(1 / 2 : ℂ)) * (2 : ℂ) ^ ((2 : ℂ) * z - (1 / 2 : ℂ))) := by
              ac_rfl
      _ = (Real.pi : ℂ) ^ (-(1 / 2 : ℂ)) * (2 : ℂ) ^ ((2 : ℂ) * z - (1 : ℂ)) := by
            rw [← Complex.cpow_add _ _ two_ne_zero]
            congr 1
            ring
      _ = (↑(Real.sqrt Real.pi) : ℂ)⁻¹ * (2 : ℂ) ^ ((2 : ℂ) * z - (1 : ℂ)) := by
            rw [hpi_inv]
      _ = (((2 : ℂ) ^ (1 - (2 : ℂ) * z) * ↑(Real.sqrt Real.pi)) : ℂ)⁻¹ := by
            rw [mul_inv_rev, ← Complex.cpow_neg]
            congr 1
            ring
  have hprod :
      ∏ j ∈ Finset.range 2, Complex.Gamma (z + (j : ℂ) / (2 : ℂ)) =
        Complex.Gamma z * Complex.Gamma (z + 1 / 2) := by
    -- The range-`2` product is exactly the two factors appearing in duplication.
    calc
      ∏ j ∈ Finset.range 2, Complex.Gamma (z + (j : ℂ) / (2 : ℂ))
        = Complex.Gamma (z + (0 : ℂ) / (2 : ℂ)) * Complex.Gamma (z + (1 : ℂ) / (2 : ℂ)) := by
            simp [Finset.prod_range_succ]
      _ = Complex.Gamma z * Complex.Gamma (z + 1 / 2) := by
            norm_num
  calc
    Complex.Gamma ((2 : ℂ) * z)
      = (Complex.Gamma z * Complex.Gamma (z + 1 / 2)) /
          ((2 : ℂ) ^ (1 - (2 : ℂ) * z) * ↑(Real.sqrt Real.pi)) := hdup_div
    _ = (Complex.Gamma z * Complex.Gamma (z + 1 / 2)) *
          (((2 : ℂ) ^ (1 - (2 : ℂ) * z) * ↑(Real.sqrt Real.pi)) : ℂ)⁻¹ := by
            rw [div_eq_mul_inv]
    _ = ((2 * Real.pi : ℂ) ^ (-((2 - 1 : ℂ) / 2))) *
          (2 : ℂ) ^ ((2 : ℂ) * z - (1 / 2 : ℂ)) *
            (∏ j ∈ Finset.range 2, Complex.Gamma (z + (j : ℂ) / (2 : ℂ))) := by
            rw [hcoeff, hprod]
            ac_rfl

/-- Helper for Exercise 6: the right half-plane is the source-faithful domain for integrating the
Gauss logarithmic-derivative identity. -/
abbrev gauss_right_half_plane : Set ℂ := {z : ℂ | 0 < z.re}

/-- Helper for Exercise 6: the right half-plane is open, so analytic identities there can be
integrated by `logDeriv_eqOn_iff`. -/
lemma isOpen_gauss_right_half_plane : IsOpen gauss_right_half_plane := by
  -- The defining inequality is the continuous real-part map against a constant.
  simpa [gauss_right_half_plane] using isOpen_lt continuous_const Complex.continuous_re

/-- Helper for Exercise 6: the right half-plane is preconnected, which is the geometric hypothesis
required by `logDeriv_eqOn_iff`. -/
lemma isPreconnected_gauss_right_half_plane : IsPreconnected gauss_right_half_plane := by
  -- This is the standard convex half-space in `ℂ`.
  simpa [gauss_right_half_plane] using (convex_halfSpace_re_gt 0).isPreconnected

/-- Helper for Exercise 6: shifting by the real quantity `j / p` keeps the right half-plane
invariant. -/
lemma gauss_shift_mem_right_half_plane {p j : ℕ} {z : ℂ}
    (hz : z ∈ gauss_right_half_plane) :
    z + (j : ℂ) / (p : ℂ) ∈ gauss_right_half_plane := by
  -- The shift adds a nonnegative real number, so the real part stays positive.
  dsimp [gauss_right_half_plane] at hz ⊢
  have hfrac_nonneg : 0 ≤ (((j : ℂ) / (p : ℂ)).re) := by
    -- The quotient is a nonnegative real number because both numerator and denominator are.
    rw [Complex.div_re]
    simp [Complex.normSq_natCast]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg j) (Nat.cast_nonneg p))
      (mul_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg p))
  simpa [Complex.add_re] using add_pos_of_pos_of_nonneg hz hfrac_nonneg

/-- Helper for Exercise 6: multiplying by `p` preserves the right half-plane when `p > 0`. -/
lemma gauss_scaled_mem_right_half_plane {p : ℕ} (hp : 0 < p) {z : ℂ}
    (hz : z ∈ gauss_right_half_plane) :
    (p : ℂ) * z ∈ gauss_right_half_plane := by
  -- A positive real scalar multiplies the real part by a positive factor.
  dsimp [gauss_right_half_plane] at hz ⊢
  have hp_real : (0 : ℝ) < p := by exact_mod_cast hp
  simpa [Complex.mul_re] using mul_pos hp_real hz

/-- Helper for Exercise 6: every point of the right half-plane avoids the nonpositive integers,
which are exactly the poles of `Γ` and `digamma`. -/
lemma gauss_nonpole_of_mem_right_half_plane {z : ℂ}
    (hz : z ∈ gauss_right_half_plane) :
    ∀ m : ℕ, z ≠ -(m : ℂ) := by
  intro m hm
  -- A nonpositive integer has nonpositive real part, contradicting `z.re > 0`.
  have hnonpos : (-(m : ℂ)).re ≤ 0 := by
    simp
  rw [← hm] at hnonpos
  exact (not_le_of_gt hz) hnonpos

/-- Helper for Exercise 6: every shifted point used in Gauss's formula stays away from the Gamma
poles on the right half-plane. -/
lemma gauss_shift_nonpole {p j : ℕ} {z : ℂ}
    (hz : z ∈ gauss_right_half_plane) :
    ∀ m : ℕ, z + (j : ℂ) / (p : ℂ) ≠ -(m : ℂ) := by
  -- The shift stays inside the right half-plane, so the pole-exclusion lemma applies there.
  exact gauss_nonpole_of_mem_right_half_plane (gauss_shift_mem_right_half_plane (p := p) (j := j) hz)

/-- Helper for Exercise 6: the scaled point used in Gauss's formula stays away from the Gamma poles
on the right half-plane. -/
lemma gauss_scaled_nonpole {p : ℕ} (hp : 0 < p) {z : ℂ}
    (hz : z ∈ gauss_right_half_plane) :
    ∀ m : ℕ, (p : ℂ) * z ≠ -(m : ℂ) := by
  -- Positive scaling also preserves the right half-plane, so the same pole exclusion applies.
  exact gauss_nonpole_of_mem_right_half_plane (gauss_scaled_mem_right_half_plane hp hz)

/-- Helper for Exercise 6: every shifted Gamma factor is nonzero on the right half-plane. -/
lemma gauss_gamma_shift_ne_zero {p j : ℕ} {z : ℂ}
    (hz : z ∈ gauss_right_half_plane) :
    Complex.Gamma (z + (j : ℂ) / (p : ℂ)) ≠ 0 := by
  -- The shift stays in the right half-plane, where Gamma has no zeros.
  exact Complex.Gamma_ne_zero_of_re_pos (gauss_shift_mem_right_half_plane hz)

/-- Helper for Exercise 6: the scaled Gamma factor is nonzero on the right half-plane. -/
lemma gauss_gamma_scaled_ne_zero {p : ℕ} (hp : 0 < p) {z : ℂ}
    (hz : z ∈ gauss_right_half_plane) :
    Complex.Gamma ((p : ℂ) * z) ≠ 0 := by
  -- The scaled argument remains in the same right-half-plane domain.
  exact Complex.Gamma_ne_zero_of_re_pos (gauss_scaled_mem_right_half_plane hp hz)

/-- Helper for Exercise 6: the finite product of shifted Gamma factors is nonzero on the right
half-plane. -/
lemma gauss_gamma_prod_ne_zero {p : ℕ} {z : ℂ}
    (hz : z ∈ gauss_right_half_plane) :
    ∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ)) ≠ 0 := by
  -- Each factor is nonzero on the right half-plane, so the finite product is too.
  refine Finset.prod_ne_zero_iff.2 ?_
  intro j hj
  exact gauss_gamma_shift_ne_zero hz

/-- Helper for Exercise 6: the complex-power prefactor in Gauss's formula never vanishes once the
integer base `p` is positive. -/
lemma gauss_cpow_factor_ne_zero {p : ℕ} (hp : 0 < p) {z : ℂ} :
    (p : ℂ) ^ ((p : ℂ) * z - (1 / 2 : ℂ)) ≠ 0 := by
  -- A nonzero complex base has nonvanishing `cpow` for every exponent.
  exact (Complex.cpow_ne_zero_iff).2 (Or.inl (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)))

/-- Helper for Exercise 6: the full Gauss right-hand side is nonzero on the right half-plane. -/
lemma gauss_rhs_ne_zero {p : ℕ} (hp : 0 < p) {z : ℂ}
    (hz : z ∈ gauss_right_half_plane) :
    (p : ℂ) ^ ((p : ℂ) * z - (1 / 2 : ℂ)) *
      ∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ)) ≠ 0 := by
  -- The `cpow` prefactor and every Gamma factor are nonzero on the chosen domain.
  exact mul_ne_zero (gauss_cpow_factor_ne_zero hp) (gauss_gamma_prod_ne_zero hz)

/-- Helper for Exercise 6: the Euler-Mascheroni series for `digamma` applies to every shifted Gauss
argument on the right half-plane. -/
lemma gauss_shift_digamma_series {p j : ℕ} {z : ℂ}
    (hz : z ∈ gauss_right_half_plane) :
    Complex.digamma (z + (j : ℂ) / (p : ℂ)) =
      -(1 / (z + (j : ℂ) / (p : ℂ))) - Real.eulerMascheroniConstant +
        ∑' n : ℕ, ((1 / (n + 1 : ℂ)) - 1 / (z + (j : ℂ) / (p : ℂ) + (n + 1 : ℂ))) := by
  -- The source-series formula is now available because the shifted point has no pole.
  simpa using
    complex_digamma_eq_euler_mascheroni_series (z + (j : ℂ) / (p : ℂ))
      (gauss_shift_nonpole (p := p) (j := j) hz)

/-- Helper for Exercise 6: the Euler-Mascheroni series for `digamma` also applies to the scaled
Gauss argument on the right half-plane. -/
lemma gauss_scaled_digamma_series {p : ℕ} (hp : 0 < p) {z : ℂ}
    (hz : z ∈ gauss_right_half_plane) :
    Complex.digamma ((p : ℂ) * z) =
      -(1 / ((p : ℂ) * z)) - Real.eulerMascheroniConstant +
        ∑' n : ℕ, ((1 / (n + 1 : ℂ)) - 1 / ((p : ℂ) * z + (n + 1 : ℂ))) := by
  -- Positive scaling keeps the argument away from the digamma poles.
  simpa using
    complex_digamma_eq_euler_mascheroni_series ((p : ℂ) * z) (gauss_scaled_nonpole hp hz)

/-- Helper for Exercise 6: the cast harmonic number is exactly the finite reciprocal sum used by
the Euler-Mascheroni digamma series. -/
lemma gauss_harmonic_cast_eq_sum (N : ℕ) :
    (((harmonic N : ℚ) : ℂ)) = ∑ n ∈ Finset.range N, (1 / (n + 1 : ℂ)) := by
  -- Expand `harmonic` and commute the rational cast through the finite sum termwise.
  simp [harmonic, div_eq_mul_inv]

/-- Helper for Exercise 6: the source finite-prefix normalization splits into the initial
reciprocal, the Euler-Mascheroni summand block, and the final harmonic tail. -/
lemma gauss_partial_sum_normal_form {x : ℂ} (N : ℕ) :
    ((((harmonic (N + 1) : ℚ) : ℂ)) - ∑ k ∈ Finset.range (N + 1), (x + k)⁻¹) =
      -(1 / x) +
        (∑ n ∈ Finset.range N, ((1 / (n + 1 : ℂ)) - 1 / (x + (n + 1 : ℂ)))) +
        1 / (N + 1 : ℂ) := by
  have hharm :
      (((harmonic (N + 1) : ℚ) : ℂ)) =
        (((harmonic N : ℚ) : ℂ)) + 1 / (N + 1 : ℂ) := by
    -- Split off the last harmonic term before matching the source truncation convention.
    calc
      (((harmonic (N + 1) : ℚ) : ℂ))
        = ∑ n ∈ Finset.range (N + 1), (1 / (n + 1 : ℂ)) := gauss_harmonic_cast_eq_sum (N + 1)
      _ = (∑ n ∈ Finset.range N, (1 / (n + 1 : ℂ))) + 1 / (N + 1 : ℂ) := by
            simpa [Nat.succ_eq_add_one, add_assoc, add_left_comm, add_comm] using
              (Finset.sum_range_succ (fun n : ℕ ↦ 1 / (n + 1 : ℂ)) N)
      _ = (((harmonic N : ℚ) : ℂ)) + 1 / (N + 1 : ℂ) := by
            rw [← gauss_harmonic_cast_eq_sum]
  have hsum :
      ∑ k ∈ Finset.range (N + 1), (x + k)⁻¹ =
        (1 / x) + ∑ k ∈ Finset.range N, 1 / (x + (k + 1 : ℂ)) := by
    -- Split the reciprocal block into its initial `k = 0` term and the shifted tail.
    simpa [Nat.succ_eq_add_one, add_assoc, add_left_comm, add_comm, one_div] using
      (Finset.sum_range_succ' (fun k : ℕ ↦ (x + k)⁻¹) N)
  -- Normalize both finite prefixes and regroup them into the source summand block.
  calc
    ((((harmonic (N + 1) : ℚ) : ℂ)) - ∑ k ∈ Finset.range (N + 1), (x + k)⁻¹)
      = ((((harmonic N : ℚ) : ℂ)) + 1 / (N + 1 : ℂ)) -
          ((1 / x) + ∑ k ∈ Finset.range N, 1 / (x + (k + 1 : ℂ))) := by
            rw [hharm, hsum]
    _ = -(1 / x) +
          ((((harmonic N : ℚ) : ℂ)) - ∑ k ∈ Finset.range N, 1 / (x + (k + 1 : ℂ))) +
          1 / (N + 1 : ℂ) := by
            ring
    _ = -(1 / x) +
          ((∑ n ∈ Finset.range N, (1 / (n + 1 : ℂ))) -
            ∑ k ∈ Finset.range N, 1 / (x + (k + 1 : ℂ))) +
          1 / (N + 1 : ℂ) := by
            rw [gauss_harmonic_cast_eq_sum]
    _ = -(1 / x) +
          (∑ n ∈ Finset.range N, ((1 / (n + 1 : ℂ)) - 1 / (x + (n + 1 : ℂ)))) +
          1 / (N + 1 : ℂ) := by
            rw [Finset.sum_sub_distrib]

/-- Helper for Exercise 6: on the right half-plane, the Euler-Mascheroni digamma series is
available as a genuine `HasSum`, not just as a `tsum` identity. -/
lemma gauss_digamma_series_hasSum_right_half_plane {x : ℂ} (hx : x ∈ gauss_right_half_plane) :
    HasSum
      (fun n : ℕ ↦ ((1 / (n + 1 : ℂ)) - 1 / (x + (n + 1 : ℂ))))
      (Complex.digamma x + Real.eulerMascheroniConstant + 1 / x) := by
  have hx_nonpole : ∀ m : ℕ, x ≠ -(m : ℂ) := gauss_nonpole_of_mem_right_half_plane hx
  have hsummable_core :
      Summable (fun n : ℕ ↦ (((-(n + 1 : ℂ)) * (x + (n + 1 : ℂ)))⁻¹)) := by
    -- Shift the standard Eisenstein-series summability to the source denominator
    -- `(-(n + 1)) * (x + (n + 1))`.
    apply ((summable_nat_add_iff 1).mpr
      (summable_int_iff_summable_nat_and_neg.mp
        (EisensteinSeries.summable_linear_sub_mul_linear_add x 0 1)).1).congr
    intro n
    simp [sub_eq_add_neg, add_left_comm, add_comm]
  have hsummable :
      Summable (fun n : ℕ ↦ ((1 / (n + 1 : ℂ)) - 1 / (x + (n + 1 : ℂ)))) := by
    -- Rewrite each summand as a fixed scalar times the summable reciprocal-product series.
    refine (hsummable_core.mul_left (-x)).congr ?_
    intro n
    have hnp1 : (n + 1 : ℂ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    have hxp1 : x + (n + 1 : ℂ) ≠ 0 := by
      intro hzero
      apply hx_nonpole (n + 1)
      simpa using eq_neg_of_add_eq_zero_left hzero
    have hfrac :
        (1 / (n + 1 : ℂ)) - 1 / (x + (n + 1 : ℂ)) =
          x / ((n + 1 : ℂ) * (x + (n + 1 : ℂ))) := by
      field_simp [hnp1, hxp1]
      ring
    have hterm :
        (-x) * (((-(n + 1 : ℂ)) * (x + (n + 1 : ℂ)))⁻¹) =
          (1 / (n + 1 : ℂ)) - 1 / (x + (n + 1 : ℂ)) := by
      calc
        (-x) * (((-(n + 1 : ℂ)) * (x + (n + 1 : ℂ)))⁻¹)
          = (-x) * (-(((n + 1 : ℂ) * (x + (n + 1 : ℂ)))⁻¹)) := by
              congr 1
              rw [show (-(n + 1 : ℂ)) * (x + (n + 1 : ℂ)) =
                  -((n + 1 : ℂ) * (x + (n + 1 : ℂ))) by ring]
              rw [inv_neg]
        _ = x * (((n + 1 : ℂ) * (x + (n + 1 : ℂ)))⁻¹) := by
              ring
        _ = x / ((n + 1 : ℂ) * (x + (n + 1 : ℂ))) := by
              rw [div_eq_mul_inv]
        _ = (1 / (n + 1 : ℂ)) - 1 / (x + (n + 1 : ℂ)) := hfrac.symm
    simpa using hterm
  have hseries :
      Complex.digamma x =
        -(1 / x) - Real.eulerMascheroniConstant +
          ∑' n : ℕ, ((1 / (n + 1 : ℂ)) - 1 / (x + (n + 1 : ℂ))) := by
    -- The textbook digamma series applies because points in the right half-plane avoid all poles.
    simpa using complex_digamma_eq_euler_mascheroni_series x hx_nonpole
  have htsum :
      ∑' n : ℕ, ((1 / (n + 1 : ℂ)) - 1 / (x + (n + 1 : ℂ))) =
        Complex.digamma x + Real.eulerMascheroniConstant + 1 / x := by
    -- Move the elementary pole term and Euler's constant to the other side.
    calc
      ∑' n : ℕ, ((1 / (n + 1 : ℂ)) - 1 / (x + (n + 1 : ℂ)))
        = (-(1 / x) - Real.eulerMascheroniConstant +
            ∑' n : ℕ, ((1 / (n + 1 : ℂ)) - 1 / (x + (n + 1 : ℂ)))) +
            Real.eulerMascheroniConstant + 1 / x := by
              ring
      _ = Complex.digamma x + Real.eulerMascheroniConstant + 1 / x := by
            rw [hseries]
  exact htsum ▸ hsummable.hasSum

/-- Helper for Exercise 6: on the right half-plane, the finite-prefix normalization in the
Euler-Mascheroni digamma series converges to `digamma x + γ`. -/
lemma gauss_digamma_partial_sum_tendsto {x : ℂ} (hx : x ∈ gauss_right_half_plane) :
    Filter.Tendsto
      (fun N : ℕ ↦
        ((((harmonic (N + 1) : ℚ) : ℂ)) -
          ∑ k ∈ Finset.range (N + 1), (x + k)⁻¹))
      Filter.atTop (nhds (Complex.digamma x + Real.eulerMascheroniConstant)) := by
  -- Route correction: the finite-prefix algebra has been separated into
  -- `gauss_partial_sum_normal_form`; the remaining work is only the analytic limit of that
  -- normalized series plus the tail `1 / (N + 1)`.
  let s : ℕ → ℂ := fun n ↦ ((1 / (n + 1 : ℂ)) - 1 / (x + (n + 1 : ℂ)))
  have hsum :
      HasSum s (Complex.digamma x + Real.eulerMascheroniConstant + 1 / x) :=
    gauss_digamma_series_hasSum_right_half_plane hx
  have hprefix :
      Filter.Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, s n) Filter.atTop
        (nhds (Complex.digamma x + Real.eulerMascheroniConstant + 1 / x)) :=
    hsum.tendsto_sum_nat
  have htail :
      Filter.Tendsto (fun N : ℕ ↦ 1 / (N + 1 : ℂ)) Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun N : ℕ ↦ 1 / ((N : ℂ) + 1)) Filter.atTop (nhds 0))
  have hnormalized' :
      Filter.Tendsto
        (fun N : ℕ ↦ -(1 / x) + ((∑ n ∈ Finset.range N, s n) + 1 / (N + 1 : ℂ)))
        Filter.atTop (nhds (Complex.digamma x + Real.eulerMascheroniConstant)) := by
    -- Combine the convergent partial sums with the vanishing tail term.
    have hsum_tail :
        Filter.Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.range N, s n) + 1 / (N + 1 : ℂ))
          Filter.atTop (nhds (Complex.digamma x + Real.eulerMascheroniConstant + 1 / x)) := by
      simpa using hprefix.add htail
    have hconst_add :
        Filter.Tendsto
          (fun N : ℕ ↦ -(1 / x) + ((∑ n ∈ Finset.range N, s n) + 1 / (N + 1 : ℂ)))
          Filter.atTop
          (nhds (-(1 / x) + (Complex.digamma x + Real.eulerMascheroniConstant + 1 / x))) :=
      by
        have hconst :
            Filter.Tendsto (fun _ : ℕ ↦ -(1 / x)) Filter.atTop (nhds (-(1 / x))) :=
          tendsto_const_nhds
        exact hconst.add hsum_tail
    have hlimit :
        -(1 / x) + (Complex.digamma x + Real.eulerMascheroniConstant + 1 / x) =
          Complex.digamma x + Real.eulerMascheroniConstant := by
      ring
    exact hlimit ▸ hconst_add
  have hnormalized :
      Filter.Tendsto
        (fun N : ℕ ↦ -(1 / x) + (∑ n ∈ Finset.range N, s n) + 1 / (N + 1 : ℂ))
        Filter.atTop (nhds (Complex.digamma x + Real.eulerMascheroniConstant)) := by
    simpa [add_assoc] using hnormalized'
  refine Filter.Tendsto.congr' ?_ hnormalized
  filter_upwards with N
  rw [gauss_partial_sum_normal_form (x := x) N]

/-- Helper for Exercise 6: scaling the shifted reciprocal isolates the exact denominator used by
the residue-class block decomposition. -/
lemma gauss_shifted_reciprocal_scale {p : ℕ} (hp : 0 < p) (w : ℂ) (j k : ℕ) :
    (w + (j : ℂ) / (p : ℂ) + k)⁻¹ =
      (p : ℂ) * (((p : ℂ) * w + (p * k + j : ℂ))⁻¹) := by
  -- Rewrite the shifted denominator as a single scaled denominator divided by `p`.
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
  have hrepr :
      w + (j : ℂ) / (p : ℂ) + k =
        ((p : ℂ) * w + (p * k + j : ℂ)) * (p : ℂ)⁻¹ := by
    field_simp [hpC]
    ring
  calc
    (w + (j : ℂ) / (p : ℂ) + k)⁻¹
      = ((((p : ℂ) * w + (p * k + j : ℂ)) * (p : ℂ)⁻¹))⁻¹ := by
          rw [hrepr]
    _ = ((p : ℂ)⁻¹)⁻¹ * (((p : ℂ) * w + (p * k + j : ℂ))⁻¹) := by
          rw [mul_inv_rev]
    _ = (p : ℂ) * (((p : ℂ) * w + (p * k + j : ℂ))⁻¹) := by
          simp

/-- Helper for Exercise 6: reindexing the `p` residue classes over one finite block produces the
single initial interval of length `p * (N + 1)`. -/
lemma gauss_residue_class_reindex {α : Type*} [AddCommMonoid α] {p N : ℕ} (hp : 0 < p)
    (f : ℕ → α) :
    ∑ jk ∈ (Finset.range p).product (Finset.range (N + 1)), f (p * jk.2 + jk.1) =
      ∑ n ∈ Finset.range (p * (N + 1)), f n := by
  classical
  -- Reindex the double block by the quotient-remainder bijection `n ↦ (n % p, n / p)`.
  refine Finset.sum_nbij' (fun jk ↦ p * jk.2 + jk.1) (fun n ↦ (n % p, n / p)) ?_ ?_ ?_ ?_
    (fun _ _ ↦ rfl)
  · intro jk hjk
    rcases Finset.mem_product.mp hjk with ⟨hj, hk⟩
    have hjlt : jk.1 < p := Finset.mem_range.mp hj
    have hklt : jk.2 < N + 1 := Finset.mem_range.mp hk
    apply Finset.mem_range.mpr
    -- The remainder part is bounded by `p`, so the block stays inside the first `p * (N + 1)`
    -- integers.
    calc
      p * jk.2 + jk.1 < p * jk.2 + p := Nat.add_lt_add_left hjlt _
      _ = p * (jk.2 + 1) := by ring
      _ ≤ p * (N + 1) := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hklt)
  · intro n hn
    refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hp), ?_⟩
    apply Finset.mem_range.mpr
    -- Dividing by `p` recovers the quotient index inside the original block.
    exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using Finset.mem_range.mp hn)
  · intro jk hjk
    rcases Finset.mem_product.mp hjk with ⟨hj, hk⟩
    have hjlt : jk.1 < p := Finset.mem_range.mp hj
    -- The quotient-remainder map returns the original pair because `jk.1` is already reduced
    -- modulo `p`.
    apply Prod.ext
    · dsimp
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hjlt]
    · dsimp
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hjlt, Nat.zero_add]
  · intro n hn
    -- Conversely, quotient and remainder reconstruct the original integer.
    simpa [Nat.add_comm] using (Nat.mod_add_div n p)

/-- Helper for Exercise 6: after scaling each shifted reciprocal term, the finite double block on
the left becomes the scaled initial block on the right. -/
lemma gauss_shifted_reciprocal_block_reindex {p N : ℕ} (hp : 0 < p) (w : ℂ) :
    ∑ jk ∈ (Finset.range p).product (Finset.range (N + 1)),
        (w + (jk.1 : ℂ) / (p : ℂ) + jk.2)⁻¹ =
      (p : ℂ) * ∑ n ∈ Finset.range (p * (N + 1)), (((p : ℂ) * w + n : ℂ)⁻¹) := by
  -- First rewrite each summand with the scaled denominator from Gauss's residue-class split.
  calc
    ∑ jk ∈ (Finset.range p).product (Finset.range (N + 1)),
        (w + (jk.1 : ℂ) / (p : ℂ) + jk.2)⁻¹
      = ∑ jk ∈ (Finset.range p).product (Finset.range (N + 1)),
          (p : ℂ) * (((p : ℂ) * w + (p * jk.2 + jk.1 : ℂ))⁻¹) := by
            refine Finset.sum_congr rfl ?_
            intro jk hjk
            simpa using gauss_shifted_reciprocal_scale hp w jk.1 jk.2
    _ = (p : ℂ) *
          ∑ jk ∈ (Finset.range p).product (Finset.range (N + 1)),
            (((p : ℂ) * w + (p * jk.2 + jk.1 : ℂ))⁻¹) := by
              rw [← Finset.mul_sum]
    _ = (p : ℂ) * ∑ n ∈ Finset.range (p * (N + 1)), (((p : ℂ) * w + n : ℂ)⁻¹) := by
          congr 1
          simpa [Nat.cast_mul, Nat.cast_add] using
            gauss_residue_class_reindex hp (fun n ↦ (((p : ℂ) * w + n : ℂ)⁻¹))

/-- Helper for Exercise 6: the same residue-class block normalization with the source-faithful
`Finset.range N` truncation convention. -/
lemma gauss_shifted_reciprocal_block_reindex_range {p N : ℕ} (hp : 0 < p) (w : ℂ) :
    ∑ jk ∈ (Finset.range p).product (Finset.range N),
        (w + (jk.1 : ℂ) / (p : ℂ) + jk.2)⁻¹ =
      (p : ℂ) * ∑ n ∈ Finset.range (p * N), (((p : ℂ) * w + n : ℂ)⁻¹) := by
  cases N with
  | zero =>
      -- The source truncation is empty at `N = 0`, so both finite blocks vanish.
      simp
  | succ N =>
      -- Reuse the existing `N + 1` normalization after identifying `Nat.succ N` with `N + 1`.
      simpa [Nat.succ_eq_add_one] using
        gauss_shifted_reciprocal_block_reindex (p := p) (N := N) hp w

/-- Helper for Exercise 6: adjoining the initial reciprocal terms to the shifted finite block
exactly recovers the first `p * (N + 1)` scaled reciprocals. -/
lemma gauss_shifted_reciprocal_initial_block_reindex {p N : ℕ} (hp : 0 < p) (w : ℂ) :
    (∑ j ∈ Finset.range p, (w + (j : ℂ) / (p : ℂ))⁻¹) +
      ∑ jk ∈ (Finset.range p).product (Finset.range N),
        (w + (jk.1 : ℂ) / (p : ℂ) + ((jk.2 + 1 : ℕ) : ℂ))⁻¹ =
      (p : ℂ) * ∑ n ∈ Finset.range (p * (N + 1)), (((p : ℂ) * w + n : ℂ)⁻¹) := by
  have hproduct :
      ∑ jk ∈ (Finset.range p).product (Finset.range (N + 1)),
        (w + (jk.1 : ℂ) / (p : ℂ) + jk.2)⁻¹ =
        ∑ k ∈ Finset.range (N + 1),
          ∑ j ∈ Finset.range p, (w + (j : ℂ) / (p : ℂ) + k)⁻¹ := by
    -- Rewrite the product-indexed sum as an outer sum over the truncation index `k`.
    simpa using
      (Finset.sum_product_right' (s := Finset.range p) (t := Finset.range (N + 1))
        (f := fun j k ↦ (w + (j : ℂ) / (p : ℂ) + k)⁻¹))
  have hsplit :
      ∑ jk ∈ (Finset.range p).product (Finset.range (N + 1)),
        (w + (jk.1 : ℂ) / (p : ℂ) + jk.2)⁻¹ =
        (∑ j ∈ Finset.range p, (w + (j : ℂ) / (p : ℂ))⁻¹) +
          ∑ jk ∈ (Finset.range p).product (Finset.range N),
            (w + (jk.1 : ℂ) / (p : ℂ) + ((jk.2 + 1 : ℕ) : ℂ))⁻¹ := by
    -- Separate the `k = 0` slice from the remaining `k + 1` block before reindexing.
    calc
      ∑ jk ∈ (Finset.range p).product (Finset.range (N + 1)),
          (w + (jk.1 : ℂ) / (p : ℂ) + jk.2)⁻¹
        = ∑ k ∈ Finset.range (N + 1),
            ∑ j ∈ Finset.range p, (w + (j : ℂ) / (p : ℂ) + k)⁻¹ := hproduct
      _ = (∑ j ∈ Finset.range p, (w + (j : ℂ) / (p : ℂ) + (0 : ℕ))⁻¹) +
            ∑ k ∈ Finset.range N,
              ∑ j ∈ Finset.range p, (w + (j : ℂ) / (p : ℂ) + ((k + 1 : ℕ) : ℂ))⁻¹ := by
                simpa [add_comm, add_left_comm, add_assoc] using
                  (Finset.sum_range_succ'
                    (fun k : ℕ ↦ ∑ j ∈ Finset.range p, (w + (j : ℂ) / (p : ℂ) + k)⁻¹) N)
      _ = (∑ j ∈ Finset.range p, (w + (j : ℂ) / (p : ℂ))⁻¹) +
            ∑ k ∈ Finset.range N,
              ∑ j ∈ Finset.range p, (w + (j : ℂ) / (p : ℂ) + ((k + 1 : ℕ) : ℂ))⁻¹ := by
                simp
      _ = (∑ j ∈ Finset.range p, (w + (j : ℂ) / (p : ℂ))⁻¹) +
            ∑ jk ∈ (Finset.range p).product (Finset.range N),
              (w + (jk.1 : ℂ) / (p : ℂ) + ((jk.2 + 1 : ℕ) : ℂ))⁻¹ := by
                congr 1
                symm
                simpa using
                  (Finset.sum_product_right' (s := Finset.range p) (t := Finset.range N)
                    (f := fun j k ↦
                      (w + (j : ℂ) / (p : ℂ) + ((k + 1 : ℕ) : ℂ))⁻¹))
  -- The remaining statement is exactly the previously normalized `N + 1` residue-class block.
  calc
    (∑ j ∈ Finset.range p, (w + (j : ℂ) / (p : ℂ))⁻¹) +
        ∑ jk ∈ (Finset.range p).product (Finset.range N),
          (w + (jk.1 : ℂ) / (p : ℂ) + ((jk.2 + 1 : ℕ) : ℂ))⁻¹
      =
        ∑ jk ∈ (Finset.range p).product (Finset.range (N + 1)),
          (w + (jk.1 : ℂ) / (p : ℂ) + jk.2)⁻¹ := by
            exact hsplit.symm
    _ = (p : ℂ) * ∑ n ∈ Finset.range (p * (N + 1)), (((p : ℂ) * w + n : ℂ)⁻¹) := by
          simpa using gauss_shifted_reciprocal_block_reindex_range (p := p) (N := N + 1) hp w

/-- Helper for Exercise 6: the source-faithful normalized truncations differ only by the harmonic
block correction once the reciprocal blocks are reindexed. -/
lemma gauss_digamma_truncation_difference {p N : ℕ} (hp : 0 < p) (w : ℂ) :
    (∑ j ∈ Finset.range p,
        ((((harmonic (N + 1) : ℚ) : ℂ)) -
          ∑ k ∈ Finset.range (N + 1), (w + (j : ℂ) / (p : ℂ) + k)⁻¹)) -
      ((p : ℂ) * ((((harmonic (p * (N + 1)) : ℚ) : ℂ)) -
        ∑ n ∈ Finset.range (p * (N + 1)), (((p : ℂ) * w + n : ℂ)⁻¹))) =
      (p : ℂ) * ((((harmonic (N + 1) : ℚ) : ℂ)) -
        (((harmonic (p * (N + 1)) : ℚ) : ℂ))) := by
  let hN : ℂ := (((harmonic (N + 1) : ℚ) : ℂ))
  let hPN : ℂ := (((harmonic (p * (N + 1)) : ℚ) : ℂ))
  have hblock :
      ∑ j ∈ Finset.range p, ∑ k ∈ Finset.range (N + 1), (w + (j : ℂ) / (p : ℂ) + k)⁻¹ =
        (p : ℂ) * ∑ n ∈ Finset.range (p * (N + 1)), (((p : ℂ) * w + n : ℂ)⁻¹) := by
    have hsplit :
        ∑ j ∈ Finset.range p, ∑ k ∈ Finset.range (N + 1), (w + (j : ℂ) / (p : ℂ) + k)⁻¹ =
          (∑ j ∈ Finset.range p, (w + (j : ℂ) / (p : ℂ))⁻¹) +
            ∑ jk ∈ (Finset.range p).product (Finset.range N),
              (w + (jk.1 : ℂ) / (p : ℂ) + ((jk.2 + 1 : ℕ) : ℂ))⁻¹ := by
      -- Split the `k = 0` slice from the remaining `k + 1` block to match the source
      -- normalization of the reciprocal sums.
      calc
        ∑ j ∈ Finset.range p, ∑ k ∈ Finset.range (N + 1), (w + (j : ℂ) / (p : ℂ) + k)⁻¹
          = ∑ k ∈ Finset.range (N + 1),
              ∑ j ∈ Finset.range p, (w + (j : ℂ) / (p : ℂ) + k)⁻¹ := by
                rw [Finset.sum_comm]
        _ = (∑ j ∈ Finset.range p, (w + (j : ℂ) / (p : ℂ) + (0 : ℕ))⁻¹) +
              ∑ k ∈ Finset.range N,
                ∑ j ∈ Finset.range p, (w + (j : ℂ) / (p : ℂ) + ((k + 1 : ℕ) : ℂ))⁻¹ := by
                  simpa [add_comm, add_left_comm, add_assoc] using
                    (Finset.sum_range_succ'
                      (fun k : ℕ ↦ ∑ j ∈ Finset.range p, (w + (j : ℂ) / (p : ℂ) + k)⁻¹) N)
        _ = (∑ j ∈ Finset.range p, (w + (j : ℂ) / (p : ℂ))⁻¹) +
              ∑ k ∈ Finset.range N,
                ∑ j ∈ Finset.range p, (w + (j : ℂ) / (p : ℂ) + ((k + 1 : ℕ) : ℂ))⁻¹ := by
                  simp
        _ = (∑ j ∈ Finset.range p, (w + (j : ℂ) / (p : ℂ))⁻¹) +
              ∑ jk ∈ (Finset.range p).product (Finset.range N),
                (w + (jk.1 : ℂ) / (p : ℂ) + ((jk.2 + 1 : ℕ) : ℂ))⁻¹ := by
                  congr 1
                  symm
                  simpa using
                    (Finset.sum_product_right' (s := Finset.range p) (t := Finset.range N)
                      (f := fun j k ↦
                        (w + (j : ℂ) / (p : ℂ) + ((k + 1 : ℕ) : ℂ))⁻¹))
    -- This is the exact reciprocal-block cancellation provided by the residue-class reindexing.
    calc
      ∑ j ∈ Finset.range p, ∑ k ∈ Finset.range (N + 1), (w + (j : ℂ) / (p : ℂ) + k)⁻¹
        = (∑ j ∈ Finset.range p, (w + (j : ℂ) / (p : ℂ))⁻¹) +
            ∑ jk ∈ (Finset.range p).product (Finset.range N),
              (w + (jk.1 : ℂ) / (p : ℂ) + ((jk.2 + 1 : ℕ) : ℂ))⁻¹ := hsplit
      _ = (p : ℂ) * ∑ n ∈ Finset.range (p * (N + 1)), (((p : ℂ) * w + n : ℂ)⁻¹) := by
            exact gauss_shifted_reciprocal_initial_block_reindex hp w
  have hconst :
      ∑ _j ∈ Finset.range p, hN = (p : ℂ) * hN := by
    -- Summing the constant harmonic truncation over `p` residue classes multiplies it by `p`.
    simpa [nsmul_eq_mul, Finset.card_range] using
      (Finset.sum_const hN : ∑ _j ∈ Finset.range p, hN = _)
  have hnormalized :
      ∑ j ∈ Finset.range p,
          (hN - ∑ k ∈ Finset.range (N + 1), (w + (j : ℂ) / (p : ℂ) + k)⁻¹) =
        (p : ℂ) * hN -
          ∑ j ∈ Finset.range p, ∑ k ∈ Finset.range (N + 1), (w + (j : ℂ) / (p : ℂ) + k)⁻¹ := by
    -- Normalize the left truncation into its harmonic part minus the reciprocal block.
    rw [Finset.sum_sub_distrib, hconst]
  -- After both normalizations, the reciprocal blocks cancel and only the harmonic correction
  -- remains.
  calc
    (∑ j ∈ Finset.range p,
        ((((harmonic (N + 1) : ℚ) : ℂ)) -
          ∑ k ∈ Finset.range (N + 1), (w + (j : ℂ) / (p : ℂ) + k)⁻¹)) -
        ((p : ℂ) * ((((harmonic (p * (N + 1)) : ℚ) : ℂ)) -
          ∑ n ∈ Finset.range (p * (N + 1)), (((p : ℂ) * w + n : ℂ)⁻¹)))
      = (∑ j ∈ Finset.range p,
          (hN - ∑ k ∈ Finset.range (N + 1), (w + (j : ℂ) / (p : ℂ) + k)⁻¹)) -
          ((p : ℂ) * (hPN -
            ∑ n ∈ Finset.range (p * (N + 1)), (((p : ℂ) * w + n : ℂ)⁻¹))) := by
              simp [hN, hPN]
    _ = ((p : ℂ) * hN -
          ∑ j ∈ Finset.range p, ∑ k ∈ Finset.range (N + 1), (w + (j : ℂ) / (p : ℂ) + k)⁻¹) -
          ((p : ℂ) * hPN -
            (p : ℂ) * ∑ n ∈ Finset.range (p * (N + 1)), (((p : ℂ) * w + n : ℂ)⁻¹)) := by
              rw [hnormalized, mul_sub]
    _ = (p : ℂ) * (hN - hPN) := by
          rw [hblock]
          ring
    _ = (p : ℂ) * ((((harmonic (N + 1) : ℚ) : ℂ)) -
          (((harmonic (p * (N + 1)) : ℚ) : ℂ))) := by
            simp [hN, hPN]

/-- Helper for Exercise 6: the harmonic correction for one residue-class block converges to the
logarithmic constant required by the Gauss source proof. -/
lemma gauss_harmonic_block_tendsto_log_real {p : ℕ} (hp : 0 < p) :
    Filter.Tendsto
      (fun N : ℕ ↦
        (p : ℝ) * ((((harmonic (N + 1) : ℚ) : ℝ)) - (((harmonic (p * (N + 1)) : ℚ) : ℝ))))
      Filter.atTop (nhds (-(p : ℝ) * Real.log p)) := by
  -- Compare both harmonic numbers to their canonical `harmonic - log` asymptotics.
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast hp
  have hblock : Filter.Tendsto (fun N : ℕ ↦ p * (N + 1)) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono ?_ Filter.tendsto_id
    intro N
    calc
      N ≤ N + 1 := Nat.le_succ N
      _ = 1 * (N + 1) := by simp
      _ ≤ p * (N + 1) := Nat.mul_le_mul_right (N + 1) (Nat.succ_le_of_lt hp)
  have hinv :
      Filter.Tendsto (fun N : ℕ ↦ 1 / ((N + 1 : ℕ) : ℝ)) Filter.atTop (nhds 0) := by
    simpa [Nat.cast_add] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun N : ℕ ↦ 1 / (N + 1 : ℝ)) Filter.atTop (nhds 0))
  have hleft :
      Filter.Tendsto
        (fun N : ℕ ↦ (((harmonic (N + 1) : ℚ) : ℝ) - Real.log (N + 1)))
        Filter.atTop (nhds Real.eulerMascheroniConstant) := by
    have hbase :
        Filter.Tendsto
          (fun N : ℕ ↦ (((harmonic N : ℚ) : ℝ) - Real.log (N + 1)))
          Filter.atTop (nhds Real.eulerMascheroniConstant) :=
      Real.tendsto_harmonic_sub_log_add_one
    -- Expand `harmonic (N + 1)` once so the extra reciprocal term tends to `0`.
    simpa [harmonic_succ, Rat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hbase.add hinv
  have hright :
      Filter.Tendsto
        (fun N : ℕ ↦ (((harmonic (p * (N + 1)) : ℚ) : ℝ) - Real.log (p * (N + 1))))
        Filter.atTop (nhds Real.eulerMascheroniConstant) := by
    have hright_base :
        Filter.Tendsto
          (((fun n : ℕ ↦ (((harmonic n : ℚ) : ℝ) - Real.log (n : ℝ))) : ℕ → ℝ) ∘
            fun N : ℕ ↦ p * (N + 1))
          Filter.atTop (nhds Real.eulerMascheroniConstant) :=
      Real.tendsto_harmonic_sub_log.comp hblock
    -- Now unfold the composition and normalize the cast of `p * (N + 1)`.
    convert hright_base using 1
    funext N
    simp [Function.comp, Nat.cast_mul, Nat.cast_add]
  have hdiff :
      Filter.Tendsto
        (fun N : ℕ ↦
          ((((harmonic (N + 1) : ℚ) : ℝ) - Real.log (N + 1)) -
            ((((harmonic (p * (N + 1)) : ℚ) : ℝ) - Real.log (p * (N + 1))) + Real.log p))
          )
        Filter.atTop (nhds (-Real.log p)) := by
    -- The two Euler-Mascheroni limits cancel, leaving only the constant `-log p`.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (hleft.sub (hright.const_add (Real.log p)))
  have hrewrite :
      (fun N : ℕ ↦
        (p : ℝ) * ((((harmonic (N + 1) : ℚ) : ℝ)) - (((harmonic (p * (N + 1)) : ℚ) : ℝ)))) =
        fun N : ℕ ↦
          (p : ℝ) *
            ((((harmonic (N + 1) : ℚ) : ℝ) - Real.log (N + 1)) -
              ((((harmonic (p * (N + 1)) : ℚ) : ℝ) - Real.log (p * (N + 1))) + Real.log p)) := by
    -- Expand the logarithm of `p * (N + 1)` and regroup the constant correction.
    funext N
    have hpR_ne : (p : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp
    have hNp_ne : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hlog_mul :
        Real.log (p * (N + 1) : ℝ) = Real.log p + Real.log (N + 1) := by
      simpa [Nat.cast_mul, Nat.cast_add] using Real.log_mul hpR_ne hNp_ne
    rw [hlog_mul]
    ring
  -- Multiply the limiting correction by the fixed scalar `p`.
  rw [hrewrite]
  simpa [neg_mul] using tendsto_const_nhds.mul hdiff

/-- Helper for Exercise 6: the complex-valued truncation difference converges to the logarithmic
constant in the source-faithful Gauss digamma argument. -/
lemma gauss_digamma_truncation_difference_tendsto {p : ℕ} (hp : 0 < p) (w : ℂ) :
    Filter.Tendsto
      (fun N : ℕ ↦
        (∑ j ∈ Finset.range p,
            ((((harmonic (N + 1) : ℚ) : ℂ)) -
              ∑ k ∈ Finset.range (N + 1), (w + (j : ℂ) / (p : ℂ) + k)⁻¹)) -
          ((p : ℂ) * ((((harmonic (p * (N + 1)) : ℚ) : ℂ)) -
            ∑ n ∈ Finset.range (p * (N + 1)), (((p : ℂ) * w + n : ℂ)⁻¹))))
      Filter.atTop (nhds (-(p : ℂ) * Real.log p)) := by
  have hreal := gauss_harmonic_block_tendsto_log_real hp
  have hcomplex :
      Filter.Tendsto
        (fun N : ℕ ↦
          (((p : ℝ) * ((((harmonic (N + 1) : ℚ) : ℝ)) -
            (((harmonic (p * (N + 1)) : ℚ) : ℝ)))) : ℂ))
        Filter.atTop (nhds ((-(p : ℝ) * Real.log p : ℝ) : ℂ)) := by
    -- Complexify the real harmonic-block limit through the continuous embedding `ℝ → ℂ`.
    have hcomplex0 :
        Filter.Tendsto
          (Complex.ofReal ∘
            fun N : ℕ ↦
              (p : ℝ) * ((((harmonic (N + 1) : ℚ) : ℝ)) -
                (((harmonic (p * (N + 1)) : ℚ) : ℝ))))
          Filter.atTop (nhds (Complex.ofReal (-(p : ℝ) * Real.log p))) := by
      exact (Complex.continuous_ofReal.tendsto _).comp hreal
    convert hcomplex0 using 1
    · ext N
      simp [Function.comp]
  -- The truncation-difference identity proved above reduces the whole sequence to the harmonic
  -- block correction, so the complexified real limit applies verbatim.
  convert hcomplex using 1
  · ext N
    rw [gauss_digamma_truncation_difference (p := p) (N := N) hp w]
    norm_num
  · norm_num

/-- Helper for Exercise 6: the scaled block-length truncation index still tends to infinity. -/
lemma gauss_block_length_index_tendsto {p : ℕ} (hp : 2 ≤ p) :
    Filter.Tendsto (fun N : ℕ ↦ p * (N + 1) - 1) Filter.atTop Filter.atTop := by
  -- For `p ≥ 2`, each scaled block endpoint dominates the identity sequence.
  refine Filter.tendsto_atTop_mono ?_ Filter.tendsto_id
  intro N
  have hp1 : 1 ≤ p := le_trans (by decide : 1 ≤ 2) hp
  have hmul : N + 1 ≤ p * (N + 1) := by
    calc
      N + 1 = 1 * (N + 1) := by simp
      _ ≤ p * (N + 1) := Nat.mul_le_mul_right (N + 1) hp1
  have hlt : N < p * (N + 1) := lt_of_lt_of_le (Nat.lt_succ_self N) hmul
  exact Nat.le_pred_of_lt hlt

/-- Helper for Exercise 6: summing the right-half-plane partial-sum limits over the `p` shifts
packages the shifted side of Gauss's truncation comparison. -/
lemma gauss_shifted_partial_sum_tendsto_finset_sum {p : ℕ} {w : ℂ}
    (hw : w ∈ gauss_right_half_plane) :
    Filter.Tendsto
      (fun N : ℕ ↦
        ∑ j ∈ Finset.range p,
          ((((harmonic (N + 1) : ℚ) : ℂ)) -
            ∑ k ∈ Finset.range (N + 1), (w + (j : ℂ) / (p : ℂ) + k)⁻¹))
      Filter.atTop
      (nhds
        (∑ j ∈ Finset.range p,
          (Complex.digamma (w + (j : ℂ) / (p : ℂ)) + Real.eulerMascheroniConstant))) := by
  -- Package the source truncation limit termwise, then sum the finitely many shifted limits.
  refine tendsto_finsetSum _ ?_
  intro j hj
  simpa using
    gauss_digamma_partial_sum_tendsto
      (gauss_shift_mem_right_half_plane (p := p) (j := j) hw)

/-- Helper for Exercise 6: composing the right-half-plane partial-sum limit with the scaled
block endpoints packages the scaled side of Gauss's truncation comparison. -/
lemma gauss_scaled_partial_sum_tendsto_composed {p : ℕ} (hp : 2 ≤ p) {w : ℂ}
    (hw : w ∈ gauss_right_half_plane) :
    Filter.Tendsto
      (fun N : ℕ ↦
        (p : ℂ) * ((((harmonic (p * (N + 1)) : ℚ) : ℂ)) -
          ∑ n ∈ Finset.range (p * (N + 1)), (((p : ℂ) * w + n : ℂ)⁻¹)))
      Filter.atTop
      (nhds ((p : ℂ) * (Complex.digamma ((p : ℂ) * w) + Real.eulerMascheroniConstant))) := by
  have hp0 : 0 < p := by omega
  have hindex :
      Filter.Tendsto (fun N : ℕ ↦ p * (N + 1) - 1) Filter.atTop Filter.atTop :=
    gauss_block_length_index_tendsto hp
  have hbase :
      Filter.Tendsto
        (fun M : ℕ ↦
          ((((harmonic (M + 1) : ℚ) : ℂ)) -
            ∑ n ∈ Finset.range (M + 1), (((p : ℂ) * w + n : ℂ)⁻¹)))
        Filter.atTop
        (nhds (Complex.digamma ((p : ℂ) * w) + Real.eulerMascheroniConstant)) :=
    gauss_digamma_partial_sum_tendsto (gauss_scaled_mem_right_half_plane hp0 hw)
  have hcomposed :
      Filter.Tendsto
        (fun N : ℕ ↦
          ((((harmonic ((p * (N + 1) - 1) + 1) : ℚ) : ℂ)) -
            ∑ n ∈ Finset.range ((p * (N + 1) - 1) + 1), (((p : ℂ) * w + n : ℂ)⁻¹)))
        Filter.atTop
        (nhds (Complex.digamma ((p : ℂ) * w) + Real.eulerMascheroniConstant)) :=
    hbase.comp hindex
  have hscaled_raw :
      Filter.Tendsto
        (fun N : ℕ ↦
          (p : ℂ) *
            ((((harmonic ((p * (N + 1) - 1) + 1) : ℚ) : ℂ)) -
              ∑ n ∈ Finset.range ((p * (N + 1) - 1) + 1), (((p : ℂ) * w + n : ℂ)⁻¹)))
        Filter.atTop
        (nhds ((p : ℂ) * (Complex.digamma ((p : ℂ) * w) + Real.eulerMascheroniConstant))) := by
    simpa using hcomposed.const_mul (p : ℂ)
  -- Normalize the endpoint arithmetic so the truncation really is `p * (N + 1)`.
  refine Filter.Tendsto.congr' ?_ hscaled_raw
  filter_upwards with N
  have hlen : (p * (N + 1) - 1) + 1 = p * (N + 1) := by
    have hpos : 0 < p * (N + 1) := Nat.mul_pos hp0 (Nat.succ_pos _)
    exact Nat.succ_pred_eq_of_pos hpos
  simp [hlen]

/-- Helper for Exercise 6: comparing the shifted and scaled partial-sum limits on the right
half-plane yields the Gauss digamma identity used in the integration step. -/
lemma gauss_digamma_sum_eq_scaled_digamma_sub_log {p : ℕ} (hp : 2 ≤ p) {w : ℂ}
    (hw : w ∈ gauss_right_half_plane) :
    ∑ j ∈ Finset.range p, Complex.digamma (w + (j : ℂ) / (p : ℂ)) =
      (p : ℂ) * Complex.digamma ((p : ℂ) * w) - (p : ℂ) * Real.log p := by
  have hp0 : 0 < p := by omega
  have hshift :
      Filter.Tendsto
        (fun N : ℕ ↦
          ∑ j ∈ Finset.range p,
            ((((harmonic (N + 1) : ℚ) : ℂ)) -
              ∑ k ∈ Finset.range (N + 1), (w + (j : ℂ) / (p : ℂ) + k)⁻¹))
        Filter.atTop
        (nhds
          (∑ j ∈ Finset.range p,
            (Complex.digamma (w + (j : ℂ) / (p : ℂ)) + Real.eulerMascheroniConstant))) :=
    gauss_shifted_partial_sum_tendsto_finset_sum hw
  have hscaled :
      Filter.Tendsto
        (fun N : ℕ ↦
          (p : ℂ) * ((((harmonic (p * (N + 1)) : ℚ) : ℂ)) -
            ∑ n ∈ Finset.range (p * (N + 1)), (((p : ℂ) * w + n : ℂ)⁻¹)))
        Filter.atTop
        (nhds ((p : ℂ) * (Complex.digamma ((p : ℂ) * w) + Real.eulerMascheroniConstant))) :=
    gauss_scaled_partial_sum_tendsto_composed hp hw
  have hdifference_left :
      Filter.Tendsto
        (fun N : ℕ ↦
          (∑ j ∈ Finset.range p,
              ((((harmonic (N + 1) : ℚ) : ℂ)) -
                ∑ k ∈ Finset.range (N + 1), (w + (j : ℂ) / (p : ℂ) + k)⁻¹)) -
            ((p : ℂ) * ((((harmonic (p * (N + 1)) : ℚ) : ℂ)) -
              ∑ n ∈ Finset.range (p * (N + 1)), (((p : ℂ) * w + n : ℂ)⁻¹))))
        Filter.atTop
        (nhds
          ((∑ j ∈ Finset.range p,
              (Complex.digamma (w + (j : ℂ) / (p : ℂ)) + Real.eulerMascheroniConstant)) -
            (p : ℂ) * (Complex.digamma ((p : ℂ) * w) + Real.eulerMascheroniConstant))) := by
    exact hshift.sub hscaled
  have hdifference :
      Filter.Tendsto
        (fun N : ℕ ↦
          (∑ j ∈ Finset.range p,
              ((((harmonic (N + 1) : ℚ) : ℂ)) -
                ∑ k ∈ Finset.range (N + 1), (w + (j : ℂ) / (p : ℂ) + k)⁻¹)) -
            ((p : ℂ) * ((((harmonic (p * (N + 1)) : ℚ) : ℂ)) -
              ∑ n ∈ Finset.range (p * (N + 1)), (((p : ℂ) * w + n : ℂ)⁻¹))))
        Filter.atTop
        (nhds
          ((∑ j ∈ Finset.range p, Complex.digamma (w + (j : ℂ) / (p : ℂ))) -
            (p : ℂ) * Complex.digamma ((p : ℂ) * w))) := by
    -- The Euler-Mascheroni contributions cancel because there are exactly `p` shifted terms.
    have hlimit :
        ((∑ j ∈ Finset.range p,
            (Complex.digamma (w + (j : ℂ) / (p : ℂ)) + Real.eulerMascheroniConstant)) -
          (p : ℂ) * (Complex.digamma ((p : ℂ) * w) + Real.eulerMascheroniConstant)) =
          ((∑ j ∈ Finset.range p, Complex.digamma (w + (j : ℂ) / (p : ℂ))) -
            (p : ℂ) * Complex.digamma ((p : ℂ) * w)) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
      ring
    exact hlimit ▸ hdifference_left
  have htrunc :
      Filter.Tendsto
        (fun N : ℕ ↦
          (∑ j ∈ Finset.range p,
              ((((harmonic (N + 1) : ℚ) : ℂ)) -
                ∑ k ∈ Finset.range (N + 1), (w + (j : ℂ) / (p : ℂ) + k)⁻¹)) -
            ((p : ℂ) * ((((harmonic (p * (N + 1)) : ℚ) : ℂ)) -
              ∑ n ∈ Finset.range (p * (N + 1)), (((p : ℂ) * w + n : ℂ)⁻¹))))
        Filter.atTop (nhds (-(p : ℂ) * Real.log p)) := by
    -- This is exactly the source truncation-difference limit already proved above.
    simpa using gauss_digamma_truncation_difference_tendsto hp0 w
  have hsum_eq :
      (∑ j ∈ Finset.range p, Complex.digamma (w + (j : ℂ) / (p : ℂ))) -
        (p : ℂ) * Complex.digamma ((p : ℂ) * w) =
          -(p : ℂ) * Real.log p :=
    tendsto_nhds_unique hdifference htrunc
  -- Rearranging the common-limit identity yields the desired Gauss digamma formula.
  calc
    ∑ j ∈ Finset.range p, Complex.digamma (w + (j : ℂ) / (p : ℂ))
      = ((∑ j ∈ Finset.range p, Complex.digamma (w + (j : ℂ) / (p : ℂ))) -
          (p : ℂ) * Complex.digamma ((p : ℂ) * w)) +
          (p : ℂ) * Complex.digamma ((p : ℂ) * w) := by
            ring
    _ = -(p : ℂ) * Real.log p + (p : ℂ) * Complex.digamma ((p : ℂ) * w) := by
          rw [hsum_eq]
    _ = (p : ℂ) * Complex.digamma ((p : ℂ) * w) - (p : ℂ) * Real.log p := by
          ring

/-- Helper for Exercise 6: on the right half-plane, the logarithmic derivative of the scaled Gamma
term is the scaled digamma function. -/
lemma gauss_logDeriv_scaled_gamma {p : ℕ} (hp : 0 < p) :
    Set.EqOn
      (logDeriv (fun w ↦ Complex.Gamma ((p : ℂ) * w)))
      (fun w ↦ (p : ℂ) * Complex.digamma ((p : ℂ) * w))
      gauss_right_half_plane := by
  intro w hw
  -- The scaled argument stays away from the Gamma poles, so the chain rule applies directly.
  have hGamma_diff : DifferentiableAt ℂ Complex.Gamma ((p : ℂ) * w) :=
    Complex.differentiableAt_Gamma _ (gauss_scaled_nonpole hp hw)
  calc
    logDeriv (fun z ↦ Complex.Gamma ((p : ℂ) * z)) w
      = logDeriv Complex.Gamma ((p : ℂ) * w) * deriv (fun z ↦ (p : ℂ) * z) w := by
          simpa [Function.comp] using
            logDeriv_comp (x := w) hGamma_diff (by fun_prop : DifferentiableAt ℂ (fun z ↦ (p : ℂ) * z) w)
    _ = Complex.digamma ((p : ℂ) * w) * deriv (fun z ↦ (p : ℂ) * z) w := by
          rw [Complex.digamma_def]
    _ = (p : ℂ) * Complex.digamma ((p : ℂ) * w) := by
          rw [deriv_const_mul_id]
          ring

/-- Helper for Exercise 6: on the right half-plane, shifting a Gamma factor by `j / p` turns its
logarithmic derivative into the corresponding shifted digamma term. -/
lemma gauss_logDeriv_shifted_gamma {p j : ℕ} :
    Set.EqOn
      (logDeriv (fun w ↦ Complex.Gamma (w + (j : ℂ) / (p : ℂ))))
      (fun w ↦ Complex.digamma (w + (j : ℂ) / (p : ℂ)))
      gauss_right_half_plane := by
  intro w hw
  -- The right-half-plane hypothesis keeps the shifted argument pole-free, so only the affine
  -- chain-rule factor remains, and that derivative is `1`.
  have hGamma_diff : DifferentiableAt ℂ Complex.Gamma (w + (j : ℂ) / (p : ℂ)) :=
    Complex.differentiableAt_Gamma _ (gauss_shift_nonpole (p := p) (j := j) hw)
  calc
    logDeriv (fun z ↦ Complex.Gamma (z + (j : ℂ) / (p : ℂ))) w
      = logDeriv Complex.Gamma (w + (j : ℂ) / (p : ℂ)) *
          deriv (fun z ↦ z + (j : ℂ) / (p : ℂ)) w := by
            simpa [Function.comp] using
              logDeriv_comp (x := w) hGamma_diff
                (by fun_prop : DifferentiableAt ℂ (fun z ↦ z + (j : ℂ) / (p : ℂ)) w)
    _ = Complex.digamma (w + (j : ℂ) / (p : ℂ)) *
          deriv (fun z ↦ z + (j : ℂ) / (p : ℂ)) w := by
            rw [Complex.digamma_def]
    _ = Complex.digamma (w + (j : ℂ) / (p : ℂ)) := by
          simp

/-- Helper for Exercise 6: on the right half-plane, the logarithmic derivative of the finite
shifted Gamma product is the finite sum of the shifted digamma terms. -/
lemma gauss_logDeriv_shifted_gamma_product {p : ℕ} :
    Set.EqOn
      (logDeriv (fun w ↦ ∏ j ∈ Finset.range p, Complex.Gamma (w + (j : ℂ) / (p : ℂ))))
      (fun w ↦ ∑ j ∈ Finset.range p, Complex.digamma (w + (j : ℂ) / (p : ℂ)))
      gauss_right_half_plane := by
  intro w hw
  -- `logDeriv_prod` reduces the finite product to the sum of the factor logarithmic derivatives.
  rw [logDeriv_prod]
  · -- Each factor has already been normalized to the corresponding shifted digamma term.
    refine Finset.sum_congr rfl ?_
    intro j hj
    simpa using gauss_logDeriv_shifted_gamma (p := p) (j := j) hw
  · intro j hj
    exact gauss_gamma_shift_ne_zero (p := p) (j := j) hw
  · intro j hj
    -- Each shifted Gamma factor is differentiable because the right half-plane avoids the poles.
    exact
      (Complex.differentiableAt_Gamma (w + (j : ℂ) / (p : ℂ))
        (gauss_shift_nonpole (p := p) (j := j) hw)).comp w
        (by fun_prop : DifferentiableAt ℂ (fun z ↦ z + (j : ℂ) / (p : ℂ)) w)

/-- Helper for Exercise 6: the exponential prefactor used in the integrated Gauss formula has
constant logarithmic derivative. -/
lemma gauss_logDeriv_exp_prefactor {p : ℕ} :
    Set.EqOn
      (logDeriv (fun w ↦ Complex.exp (((p : ℂ) * Real.log p) * w)))
      (fun _ ↦ (p : ℂ) * Real.log p)
      gauss_right_half_plane := by
  intro w hw
  let c : ℂ := (p : ℂ) * Real.log p
  -- The exponential factor is entire, so its logarithmic derivative is just the derivative of the
  -- linear exponent.
  calc
    logDeriv (fun z ↦ Complex.exp (c * z)) w
      = logDeriv Complex.exp (c * w) * deriv (fun z ↦ c * z) w := by
          simpa [c, Function.comp] using
            logDeriv_comp (x := w) ((Complex.hasDerivAt_exp (c * w)).differentiableAt)
              (by fun_prop : DifferentiableAt ℂ (fun z ↦ c * z) w)
    _ = (deriv Complex.exp (c * w) / Complex.exp (c * w)) * deriv (fun z ↦ c * z) w := by
          rw [logDeriv_apply]
    _ = deriv (fun z ↦ c * z) w := by
          rw [Complex.deriv_exp]
          field_simp [Complex.exp_ne_zero (c * w)]
    _ = (p : ℂ) * Real.log p := by
          simp [c, deriv_const_mul_id]

/-- Helper for Exercise 6: once the right-half-plane digamma sum is known, the integrated Gauss
right-hand side has the same logarithmic derivative as the scaled Gamma term. -/
lemma gauss_logDeriv_eqOn_exp_rhs_of_digamma_sum {p : ℕ} (hp : 0 < p)
    (h_digamma :
      ∀ ⦃w : ℂ⦄, w ∈ gauss_right_half_plane →
        ∑ j ∈ Finset.range p, Complex.digamma (w + (j : ℂ) / (p : ℂ)) =
          (p : ℂ) * Complex.digamma ((p : ℂ) * w) - (p : ℂ) * Real.log p) :
    Set.EqOn
      (logDeriv (fun w ↦ Complex.Gamma ((p : ℂ) * w)))
      (logDeriv
        (fun w ↦
          Complex.exp (((p : ℂ) * Real.log p) * w) *
            ∏ j ∈ Finset.range p, Complex.Gamma (w + (j : ℂ) / (p : ℂ))))
      gauss_right_half_plane := by
  intro w hw
  have h_exp_diff :
      DifferentiableAt ℂ (fun z ↦ Complex.exp (((p : ℂ) * Real.log p) * z)) w := by
    -- The exponential prefactor is entire.
    fun_prop
  have h_prod_diff :
      DifferentiableAt ℂ
        (fun z ↦ ∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ))) w := by
    -- The finite Gamma product is differentiable because each shifted factor is.
    refine DifferentiableAt.fun_finsetProd ?_
    intro j hj
    exact
      (Complex.differentiableAt_Gamma (w + (j : ℂ) / (p : ℂ))
        (gauss_shift_nonpole (p := p) (j := j) hw)).comp w
        (by fun_prop : DifferentiableAt ℂ (fun z ↦ z + (j : ℂ) / (p : ℂ)) w)
  -- Route correction: the integration bookkeeping is now isolated from the still-missing
  -- digamma summation identity.
  calc
    logDeriv (fun z ↦ Complex.Gamma ((p : ℂ) * z)) w
      = (p : ℂ) * Complex.digamma ((p : ℂ) * w) := by
          exact gauss_logDeriv_scaled_gamma hp hw
    _ = (p : ℂ) * Real.log p +
          ∑ j ∈ Finset.range p, Complex.digamma (w + (j : ℂ) / (p : ℂ)) := by
            rw [h_digamma hw]
            ring
    _ = logDeriv
          (fun z ↦
            Complex.exp (((p : ℂ) * Real.log p) * z) *
              ∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ))) w := by
            symm
            calc
              logDeriv
                  (fun z ↦
                    Complex.exp (((p : ℂ) * Real.log p) * z) *
                      ∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ))) w
                = logDeriv (fun z ↦ Complex.exp (((p : ℂ) * Real.log p) * z)) w +
                    logDeriv
                      (fun z ↦ ∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ))) w := by
                        simpa using
                          (logDeriv_mul
                            (x := w)
                            (f := fun z ↦ Complex.exp (((p : ℂ) * Real.log p) * z))
                            (g := fun z ↦
                              ∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ)))
                            (Complex.exp_ne_zero _)
                            (gauss_gamma_prod_ne_zero (p := p) hw) h_exp_diff h_prod_diff)
              _ = (p : ℂ) * Real.log p +
                    logDeriv
                      (fun z ↦ ∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ))) w := by
                        rw [gauss_logDeriv_exp_prefactor (p := p) hw]
              _ = (p : ℂ) * Real.log p +
                    ∑ j ∈ Finset.range p, Complex.digamma (w + (j : ℂ) / (p : ℂ)) := by
                        rw [gauss_logDeriv_shifted_gamma_product (p := p) hw]

/-- Helper for Exercise 6: after replacing the target `cpow` by the source-faithful exponential
prefactor, the right-hand side stays nonzero on the right half-plane. -/
lemma gauss_exp_rhs_ne_zero {p : ℕ} {w : ℂ}
    (hw : w ∈ gauss_right_half_plane) :
    Complex.exp (((p : ℂ) * Real.log p) * w) *
      ∏ j ∈ Finset.range p, Complex.Gamma (w + (j : ℂ) / (p : ℂ)) ≠ 0 := by
  -- The exponential never vanishes, and the finite Gamma product is already nonzero on this
  -- domain.
  exact mul_ne_zero (Complex.exp_ne_zero _) (gauss_gamma_prod_ne_zero hw)

/-- Helper for Exercise 6: at the normalization point `w = 1 / p`, the Gauss product reindexes to
the consecutive rational Gamma factors `Γ(q / p)` for `1 ≤ q ≤ p`. -/
lemma gauss_gamma_product_one_div_p_reindex {p : ℕ} :
    ∏ j ∈ Finset.range p, Complex.Gamma ((1 : ℂ) / (p : ℂ) + (j : ℂ) / (p : ℂ)) =
      ∏ q ∈ Finset.Icc 1 p, Complex.Gamma ((q : ℂ) / (p : ℂ)) := by
  -- Rewrite each factor as `Γ((j + 1) / p)` and convert the shifted range into the interval
  -- `Icc 1 p`.
  calc
    ∏ j ∈ Finset.range p, Complex.Gamma ((1 : ℂ) / (p : ℂ) + (j : ℂ) / (p : ℂ))
      = ∏ j ∈ Finset.range p, Complex.Gamma (((j + 1 : ℕ) : ℂ) / (p : ℂ)) := by
          refine Finset.prod_congr rfl ?_
          intro j hj
          have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le j) (Finset.mem_range.mp hj)
          have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
          congr 1
          field_simp [hpC]
          simp [Nat.cast_add, add_comm]
    _ = ∏ q ∈ Finset.Icc 1 p, Complex.Gamma ((q : ℂ) / (p : ℂ)) := by
          symm
          rw [← Finset.Ico_add_one_right_eq_Icc]
          simpa [add_comm] using
            (Finset.prod_Ico_eq_prod_range
              (fun q ↦ Complex.Gamma ((q : ℂ) / (p : ℂ))) 1 (p + 1))

/-- Helper for Exercise 6: the product at `w = 1 / p` splits into the rational factors with
`1 ≤ q ≤ p - 1` and the terminal factor `Γ 1`. -/
lemma gauss_gamma_product_one_div_p_split_range {p : ℕ} (hp : 0 < p) :
    ∏ j ∈ Finset.range p, Complex.Gamma ((1 : ℂ) / (p : ℂ) + (j : ℂ) / (p : ℂ)) =
      (∏ j ∈ Finset.range (p - 1), Complex.Gamma ((((j + 1 : ℕ) : ℂ) / (p : ℂ)))) *
        Complex.Gamma 1 := by
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
  -- Rewrite the sampled factors as the consecutive rational values `Γ((j + 1) / p)`.
  calc
    ∏ j ∈ Finset.range p, Complex.Gamma ((1 : ℂ) / (p : ℂ) + (j : ℂ) / (p : ℂ))
      = ∏ j ∈ Finset.range p, Complex.Gamma ((((j + 1 : ℕ) : ℂ) / (p : ℂ))) := by
          refine Finset.prod_congr rfl ?_
          intro j hj
          congr 1
          field_simp [hpC]
          simp [Nat.cast_add, add_comm]
    _ = (∏ j ∈ Finset.range (p - 1), Complex.Gamma ((((j + 1 : ℕ) : ℂ) / (p : ℂ)))) *
          Complex.Gamma ((((p - 1) + 1 : ℕ) : ℂ) / (p : ℂ)) := by
            -- Split off the terminal factor `j = p - 1` while staying on `Finset.range`.
            simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hp)] using
              (Finset.prod_range_succ
                (fun j ↦ Complex.Gamma ((((j + 1 : ℕ) : ℂ) / (p : ℂ)))) (p - 1))
    _ = (∏ j ∈ Finset.range (p - 1), Complex.Gamma ((((j + 1 : ℕ) : ℂ) / (p : ℂ)))) *
          Complex.Gamma ((p : ℂ) / (p : ℂ)) := by
            congr 2
            simp [Nat.sub_add_cancel (Nat.succ_le_of_lt hp)]
    _ = (∏ j ∈ Finset.range (p - 1), Complex.Gamma ((((j + 1 : ℕ) : ℂ) / (p : ℂ)))) *
          Complex.Gamma 1 := by
            rw [div_self hpC]

/-- Helper for Exercise 6: the product at `w = 1 / p` splits into the rational factors with
`1 ≤ q ≤ p - 1` and the terminal factor `Γ 1`. -/
lemma gauss_gamma_product_one_div_p_split {p : ℕ} (hp : 0 < p) :
    ∏ j ∈ Finset.range p, Complex.Gamma ((1 : ℂ) / (p : ℂ) + (j : ℂ) / (p : ℂ)) =
      (∏ q ∈ Finset.Icc 1 (p - 1), Complex.Gamma ((q : ℂ) / (p : ℂ))) * Complex.Gamma 1 := by
  have hrange_to_Icc :
      ∏ j ∈ Finset.range (p - 1), Complex.Gamma ((((j + 1 : ℕ) : ℂ) / (p : ℂ))) =
        ∏ q ∈ Finset.Icc 1 (p - 1), Complex.Gamma ((q : ℂ) / (p : ℂ)) := by
    have hIco :
        ∏ q ∈ Finset.Ico 1 p, Complex.Gamma ((q : ℂ) / (p : ℂ)) =
          ∏ j ∈ Finset.range (p - 1), Complex.Gamma ((((j + 1 : ℕ) : ℂ) / (p : ℂ))) := by
      simpa [add_comm] using
        (Finset.prod_Ico_eq_prod_range
          (fun q ↦ Complex.Gamma ((q : ℂ) / (p : ℂ))) 1 p)
    -- Replace the consecutive range `0, ..., p - 2` by the source interval `1, ..., p - 1`.
    rw [← Finset.Ico_add_one_right_eq_Icc]
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hp)] using hIco.symm
  -- Route correction: the constant evaluation should consume the range-native split first, then
  -- recover the textbook `Icc` notation only as a thin wrapper.
  calc
    ∏ j ∈ Finset.range p, Complex.Gamma ((1 : ℂ) / (p : ℂ) + (j : ℂ) / (p : ℂ))
      = (∏ j ∈ Finset.range (p - 1), Complex.Gamma ((((j + 1 : ℕ) : ℂ) / (p : ℂ)))) *
          Complex.Gamma 1 := by
            exact gauss_gamma_product_one_div_p_split_range hp
    _ = (∏ q ∈ Finset.Icc 1 (p - 1), Complex.Gamma ((q : ℂ) / (p : ℂ))) * Complex.Gamma 1 := by
          rw [hrange_to_Icc]

/-- Helper for Exercise 6: the normalization point `w = 1 / p` lies in the right half-plane. -/
lemma one_div_nat_mem_gauss_right_half_plane {p : ℕ} (hp : 0 < p) :
    (1 : ℂ) / (p : ℂ) ∈ gauss_right_half_plane := by
  -- Rewrite `1 / p` as a positive real number viewed inside `ℂ`.
  have hreal : (1 : ℂ) / (p : ℂ) = (((1 : ℝ) / (p : ℝ)) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_natCast, ← Complex.ofReal_div]
  have hpos : 0 < (1 : ℝ) / (p : ℝ) := by
    positivity
  simpa [gauss_right_half_plane, hreal] using hpos

/-- Helper for Exercise 6: the source exponential prefactor evaluates to `p` at `w = 1 / p`. -/
lemma gauss_exp_one_div_p {p : ℕ} (hp : 0 < p) :
    Complex.exp (((p : ℂ) * Real.log p) * ((1 : ℂ) / (p : ℂ))) = (p : ℂ) := by
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
  -- Cancel the factor `p` in the exponent before applying `exp_log`.
  calc
    Complex.exp (((p : ℂ) * Real.log p) * ((1 : ℂ) / (p : ℂ)))
      = Complex.exp (Real.log p) := by
          congr 1
          field_simp [hpC]
    _ = (p : ℂ) := by
          rw [Complex.natCast_log, Complex.exp_log hpC]

/-- Helper for Exercise 6: once the constant is known, the source-faithful exponential prefactor
rewrites to the target `cpow` scalar in one step. -/
lemma gauss_prefactor_normal_form {p : ℕ} (hp : 0 < p) (w : ℂ) :
    (((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) * (p : ℂ) ^ (-(1 / 2 : ℂ))) *
        Complex.exp (((p : ℂ) * Real.log p) * w) =
      ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
        (p : ℂ) ^ ((p : ℂ) * w - (1 / 2 : ℂ)) := by
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
  have hexp : Complex.exp (((p : ℂ) * Real.log p) * w) = (p : ℂ) ^ ((p : ℂ) * w) := by
    -- Rewrite the exponential as the defining exponential for the complex power `p ^ (p w)`.
    rw [Complex.cpow_def_of_ne_zero hpC]
    congr 1
    rw [Complex.natCast_log]
    ring
  -- Combine the two powers of `p` into the target exponent.
  calc
    (((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) * (p : ℂ) ^ (-(1 / 2 : ℂ))) *
        Complex.exp (((p : ℂ) * Real.log p) * w)
      = (((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) * (p : ℂ) ^ (-(1 / 2 : ℂ))) *
          (p : ℂ) ^ ((p : ℂ) * w) := by
            rw [hexp]
    _ = ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
          ((p : ℂ) ^ (-(1 / 2 : ℂ)) * (p : ℂ) ^ ((p : ℂ) * w)) := by
            ac_rfl
    _ = ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
          (p : ℂ) ^ (-(1 / 2 : ℂ) + (p : ℂ) * w) := by
            rw [← Complex.cpow_add _ _ hpC]
    _ = ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
          (p : ℂ) ^ ((p : ℂ) * w - (1 / 2 : ℂ)) := by
            congr 2
            ring

/-- Helper for Exercise 6: the norm of `1 - exp(2πiq / p)` is the absolute value of the
corresponding doubled sine factor. -/
lemma gauss_norm_one_sub_primitive_root_pow {p q : ℕ} (hp : 0 < p) :
    ‖1 - Complex.exp (2 * Real.pi * Complex.I / (p : ℂ)) ^ q‖ =
      ‖2 * Real.sin (Real.pi * (q : ℝ) / (p : ℝ))‖ := by
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp
  have hpow :
      Complex.exp (2 * Real.pi * Complex.I / (p : ℂ)) ^ q =
        Complex.exp (Complex.I * (2 * Real.pi * (q : ℝ) / (p : ℝ))) := by
    -- Rewrite the `q`th power as a single exponential on the unit circle.
    calc
      Complex.exp (2 * Real.pi * Complex.I / (p : ℂ)) ^ q
        = Complex.exp (((q : ℕ) : ℂ) * (2 * Real.pi * Complex.I / (p : ℂ))) := by
            symm
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              (Complex.exp_nat_mul (2 * Real.pi * Complex.I / (p : ℂ)) q)
      _ = Complex.exp (Complex.I * (2 * Real.pi * (q : ℝ) / (p : ℝ))) := by
            congr 1
            field_simp [hpC]
            norm_cast
            ring
  calc
    ‖1 - Complex.exp (2 * Real.pi * Complex.I / (p : ℂ)) ^ q‖
      = ‖Complex.exp (Complex.I * (2 * Real.pi * (q : ℝ) / (p : ℝ))) - 1‖ := by
          rw [hpow, norm_sub_rev]
    _ = ‖2 * Real.sin ((2 * Real.pi * (q : ℝ) / (p : ℝ)) / 2)‖ := by
          simpa using
            Complex.norm_exp_I_mul_ofReal_sub_one (2 * Real.pi * (q : ℝ) / (p : ℝ))
    _ = ‖2 * Real.sin (Real.pi * (q : ℝ) / (p : ℝ))‖ := by
          congr 2
          field_simp [hpR]

/-- Helper for Exercise 6: the finite sine factors occurring in Gauss's formula are positive on
`1 ≤ q ≤ p - 1`. -/
lemma gauss_sine_factor_pos {p q : ℕ} (hp : 2 ≤ p) (hq : q ∈ Finset.Icc 1 (p - 1)) :
    0 < Real.sin (Real.pi * (q : ℝ) / (p : ℝ)) := by
  rcases Finset.mem_Icc.mp hq with ⟨hq1, hq2⟩
  have hpR : (0 : ℝ) < p := by positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq1
  have hq_lt_p : q < p := by omega
  have hfrac : (q : ℝ) / (p : ℝ) < 1 := by
    exact (div_lt_one hpR).2 (by exact_mod_cast hq_lt_p)
  have harg_pos : 0 < Real.pi * (q : ℝ) / (p : ℝ) := by positivity
  have harg_lt : Real.pi * (q : ℝ) / (p : ℝ) < Real.pi := by
    have hmul : Real.pi * ((q : ℝ) / (p : ℝ)) < Real.pi * 1 := by
      exact mul_lt_mul_of_pos_left hfrac Real.pi_pos
    simpa [div_eq_mul_inv, mul_assoc] using hmul
  -- The argument lies strictly between `0` and `π`, so the sine is positive.
  exact Real.sin_pos_of_pos_of_lt_pi harg_pos harg_lt

/-- Helper for Exercise 6: reindexing `Icc 1 (p - 1)` by `q = j + 1` produces the native
`Finset.range (p - 1)` surface used in the constant evaluation. -/
lemma gauss_prod_Icc_eq_prod_range_succ {α : Type*} [CommMonoid α] {p : ℕ} (hp : 1 ≤ p)
    (f : ℕ → α) :
    ∏ q ∈ Finset.Icc 1 (p - 1), f q = ∏ j ∈ Finset.range (p - 1), f (j + 1) := by
  -- Replace the textbook interval `1 ≤ q ≤ p - 1` by `Ico 1 p`, then apply the standard
  -- interval-to-range reindexing.
  calc
    ∏ q ∈ Finset.Icc 1 (p - 1), f q
      = ∏ q ∈ Finset.Ico 1 p, f q := by
          rw [← Finset.Ico_add_one_right_eq_Icc]
          simp [Nat.sub_add_cancel hp]
    _ = ∏ j ∈ Finset.range (p - 1), f (j + 1) := by
          simpa [add_comm] using (Finset.prod_Ico_eq_prod_range f 1 p)

/-- Helper for Exercise 6: the sine factors are still positive after moving to the native
`Finset.range (p - 1)` indexing surface. -/
lemma gauss_sine_factor_pos_range {p j : ℕ} (hp : 2 ≤ p) (hj : j ∈ Finset.range (p - 1)) :
    0 < Real.sin (Real.pi * (((j + 1 : ℕ) : ℝ) / (p : ℝ))) := by
  have hjIcc : j + 1 ∈ Finset.Icc 1 (p - 1) := by
    refine Finset.mem_Icc.mpr ?_
    constructor
    · exact Nat.succ_le_succ (Nat.zero_le _)
    · have hj_lt : j < p - 1 := Finset.mem_range.mp hj
      omega
  -- Transfer the positivity statement from the textbook interval to the range-native index.
  simpa [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_assoc] using
    gauss_sine_factor_pos (p := p) (q := j + 1) hp hjIcc

/-- Helper for Exercise 6: on the native `Finset.range (p - 1)` indexing surface, Euler
reflection sends `((j + 1) / p)` to `((p - 1 - j) / p)`. -/
lemma gauss_one_sub_succ_div_eq_reflect {p j : ℕ} (hp : 2 ≤ p)
    (hj : j ∈ Finset.range (p - 1)) :
    1 - ((((j + 1 : ℕ) : ℝ) / (p : ℝ))) = (((p - 1 - j : ℕ) : ℝ) / (p : ℝ)) := by
  have hpR : (p : ℝ) ≠ 0 := by positivity
  have hj_le : j + 1 ≤ p := by
    have hj_lt : j < p - 1 := Finset.mem_range.mp hj
    omega
  -- Route correction: the earlier reflected-index formula with an extra `+ 1` is false.
  -- The source reflection step really lands on `(p - 1 - j) / p`.
  calc
    1 - ((((j + 1 : ℕ) : ℝ) / (p : ℝ)))
      = ((p : ℝ) - ((j + 1 : ℕ) : ℝ)) / (p : ℝ) := by
          field_simp [hpR]
    _ = (((p - (j + 1) : ℕ) : ℝ) / (p : ℝ)) := by
          rw [Nat.cast_sub hj_le]
    _ = (((p - 1 - j : ℕ) : ℝ) / (p : ℝ)) := by
          congr 1
          have hj_lt : j < p - 1 := Finset.mem_range.mp hj
          exact_mod_cast (show p - (j + 1) = p - 1 - j by omega)

/-- Helper for Exercise 6: the primitive-root product
`∏_{j=0}^{p-2} (1 - exp(2π i / p)^(j+1)) = p` yields the corresponding norm identity on the native
`Finset.range (p - 1)` surface. -/
lemma gauss_primitive_root_norm_product_range {p : ℕ} (hp : 2 ≤ p) :
    ∏ j ∈ Finset.range (p - 1),
      ‖1 - Complex.exp (2 * Real.pi * Complex.I / (p : ℂ)) ^ (j + 1)‖ = (p : ℝ) := by
  have hp_pos : 0 < p := by omega
  have hprim :
      IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (p : ℂ))) ((p - 1) + 1) := by
    -- Normalize the order parameter so the primitive-root product theorem applies on `range (p - 1)`.
    simpa [Nat.sub_add_cancel (show 1 ≤ p by omega)] using
      (Complex.isPrimitiveRoot_exp p (Nat.ne_of_gt hp_pos))
  have hprod :
      ∏ j ∈ Finset.range (p - 1),
          (1 - Complex.exp (2 * Real.pi * Complex.I / (p : ℂ)) ^ (j + 1)) = (p : ℂ) := by
    -- This is the source finite-product identity before taking norms.
    calc
      ∏ j ∈ Finset.range (p - 1),
          (1 - Complex.exp (2 * Real.pi * Complex.I / (p : ℂ)) ^ (j + 1))
        = (((p - 1) + 1 : ℕ) : ℂ) := by
            simpa using
              (IsPrimitiveRoot.prod_one_sub_pow_eq_order
                (n := p - 1) (μ := Complex.exp (2 * Real.pi * Complex.I / (p : ℂ))) hprim)
      _ = (p : ℂ) := by
            norm_num [Nat.sub_add_cancel (show 1 ≤ p by omega)]
  have hnorm := congrArg (fun z : ℂ ↦ ‖z‖) hprod
  -- Taking norms converts the primitive-root product into the real product needed for Gauss.
  simpa [norm_prod] using hnorm

/-- Helper for Exercise 6: Gauss's finite sine product on the `range` surface
`∏_{j=0}^{p-2} sin(π (j + 1) / p) = p / 2^(p-1)`. -/
lemma gauss_sine_product_range {p : ℕ} (hp : 2 ≤ p) :
    ∏ j ∈ Finset.range (p - 1), Real.sin (Real.pi * ((j + 1 : ℕ) : ℝ) / (p : ℝ)) =
      (p : ℝ) / 2 ^ (p - 1) := by
  let s : ℕ → ℝ := fun j ↦ Real.sin (Real.pi * ((j + 1 : ℕ) : ℝ) / (p : ℝ))
  have hnorm := gauss_primitive_root_norm_product_range hp
  have hnorm_to_sine :
      ∏ j ∈ Finset.range (p - 1),
          ‖1 - Complex.exp (2 * Real.pi * Complex.I / (p : ℂ)) ^ (j + 1)‖ =
        ∏ j ∈ Finset.range (p - 1),
          (2 * s j) := by
    -- Rewrite each primitive-root norm as the positive doubled sine factor from the source proof.
    refine Finset.prod_congr rfl ?_
    intro j hj
    rw [gauss_norm_one_sub_primitive_root_pow (p := p) (q := j + 1) (hp := by omega)]
    have hsin_pos' :
        0 < Real.sin (Real.pi * (((j + 1 : ℕ) : ℝ) / (p : ℝ))) :=
      gauss_sine_factor_pos_range hp hj
    have hsin_pos : 0 < s j := by
      dsimp [s]
      convert hsin_pos' using 1 <;> ring_nf
    have htwo_mul_pos : 0 < 2 * s j := by
      exact mul_pos (by norm_num) hsin_pos
    rw [Real.norm_eq_abs]
    exact abs_of_nonneg (le_of_lt htwo_mul_pos)
  have hsplit :
      ∏ j ∈ Finset.range (p - 1),
          (2 * s j) =
        (2 : ℝ) ^ (p - 1) *
          ∏ j ∈ Finset.range (p - 1),
            s j := by
    -- Factor the constant `2` out of the finite product.
    rw [Finset.prod_mul_distrib]
    simp
  have hmain :
      (2 : ℝ) ^ (p - 1) *
          ∏ j ∈ Finset.range (p - 1),
            s j =
        (p : ℝ) := by
    calc
      (2 : ℝ) ^ (p - 1) *
          ∏ j ∈ Finset.range (p - 1),
            s j
        = ∏ j ∈ Finset.range (p - 1),
            (2 * s j) := by
              simpa using hsplit.symm
      _ = ∏ j ∈ Finset.range (p - 1),
            ‖1 - Complex.exp (2 * Real.pi * Complex.I / (p : ℂ)) ^ (j + 1)‖ := by
              rw [hnorm_to_sine]
      _ = (p : ℝ) := hnorm
  have htwo_ne : (2 : ℝ) ^ (p - 1) ≠ 0 := by positivity
  -- Divide by the extracted constant factor to obtain Gauss's sine product.
  exact (eq_div_iff htwo_ne).2 (by simpa [s, mul_comm] using hmain)

/-- Helper for Exercise 6: Gauss's finite sine product
`∏_{q=1}^{p-1} sin(π q / p) = p / 2^(p-1)`. -/
lemma gauss_sine_product {p : ℕ} (hp : 2 ≤ p) :
    ∏ q ∈ Finset.Icc 1 (p - 1), Real.sin (Real.pi * (q : ℝ) / (p : ℝ)) =
      (p : ℝ) / 2 ^ (p - 1) := by
  -- Reindex the textbook interval to the range-native surface before invoking the main sine
  -- product identity.
  rw [gauss_prod_Icc_eq_prod_range_succ (p := p) (hp := by omega)
    (f := fun q : ℕ ↦ Real.sin (Real.pi * (q : ℝ) / (p : ℝ)))]
  exact gauss_sine_product_range hp

/-- Helper for Exercise 6: on `Finset.range (p - 1)`, the rational Gamma values satisfy Gauss's
square identity. -/
lemma gauss_rational_gamma_product_sq_range {p : ℕ} (hp : 2 ≤ p) :
    (∏ j ∈ Finset.range (p - 1), Real.Gamma ((((j + 1 : ℕ) : ℝ) / (p : ℝ)))) ^ 2 =
      ((2 * Real.pi) ^ (p - 1)) / (p : ℝ) := by
  let A : ℝ :=
    ∏ j ∈ Finset.range (p - 1), Real.Gamma ((((j + 1 : ℕ) : ℝ) / (p : ℝ)))
  have hp_pos : 0 < p := by omega
  have hpR_ne : (p : ℝ) ≠ 0 := by positivity
  have hreflect :
      ∏ j ∈ Finset.range (p - 1),
          Real.Gamma (1 - ((((j + 1 : ℕ) : ℝ) / (p : ℝ)))) = A := by
    -- Rewrite the reflected arguments through the native reflected index and then reflect the
    -- entire finite product back to the original ordering.
    calc
      ∏ j ∈ Finset.range (p - 1),
          Real.Gamma (1 - ((((j + 1 : ℕ) : ℝ) / (p : ℝ))))
        = ∏ j ∈ Finset.range (p - 1),
            Real.Gamma ((((p - 1 - j : ℕ) : ℝ) / (p : ℝ))) := by
              refine Finset.prod_congr rfl ?_
              intro j hj
              rw [gauss_one_sub_succ_div_eq_reflect hp hj]
      _ = ∏ j ∈ Finset.range (p - 1),
            Real.Gamma (((((p - 1) - 1 - j) + 1 : ℕ) : ℝ) / (p : ℝ)) := by
              refine Finset.prod_congr rfl ?_
              intro j hj
              have hj_lt : j < p - 1 := Finset.mem_range.mp hj
              have hnat : p - 1 - j = ((p - 1) - 1 - j) + 1 := by omega
              simp [hnat]
      _ = ∏ j ∈ Finset.range (p - 1),
            Real.Gamma ((((j + 1 : ℕ) : ℝ) / (p : ℝ))) := by
              simpa [A] using
                (Finset.prod_range_reflect
                  (fun k : ℕ ↦ Real.Gamma ((((k + 1 : ℕ) : ℝ) / (p : ℝ)))) (p - 1))
      _ = A := by rfl
  -- Multiply Euler reflection across the whole native range.
  calc
    A ^ 2 = A * A := by rw [sq]
    _ = (∏ j ∈ Finset.range (p - 1), Real.Gamma ((((j + 1 : ℕ) : ℝ) / (p : ℝ)))) *
          (∏ j ∈ Finset.range (p - 1),
            Real.Gamma (1 - ((((j + 1 : ℕ) : ℝ) / (p : ℝ))))) := by
            rw [show A = ∏ j ∈ Finset.range (p - 1),
                Real.Gamma ((((j + 1 : ℕ) : ℝ) / (p : ℝ))) by rfl, hreflect]
    _ = ∏ j ∈ Finset.range (p - 1),
          (Real.Gamma ((((j + 1 : ℕ) : ℝ) / (p : ℝ))) *
            Real.Gamma (1 - ((((j + 1 : ℕ) : ℝ) / (p : ℝ))))) := by
            rw [← Finset.prod_mul_distrib]
    _ = ∏ j ∈ Finset.range (p - 1),
          (Real.pi /
            Real.sin (Real.pi * ((((j + 1 : ℕ) : ℝ) / (p : ℝ))))) := by
            refine Finset.prod_congr rfl ?_
            intro j hj
            rw [Real.Gamma_mul_Gamma_one_sub]
    _ = ∏ j ∈ Finset.range (p - 1),
          (Real.pi /
            Real.sin (Real.pi * ((j + 1 : ℕ) : ℝ) / (p : ℝ))) := by
            refine Finset.prod_congr rfl ?_
            intro j hj
            congr 2
            field_simp [hpR_ne]
    _ = ∏ j ∈ Finset.range (p - 1),
          (Real.pi * (Real.sin (Real.pi * ((j + 1 : ℕ) : ℝ) / (p : ℝ)))⁻¹) := by
            refine Finset.prod_congr rfl ?_
            intro j hj
            simp [div_eq_mul_inv]
    _ = (∏ j ∈ Finset.range (p - 1), Real.pi) *
          ∏ j ∈ Finset.range (p - 1),
            (Real.sin (Real.pi * ((j + 1 : ℕ) : ℝ) / (p : ℝ)))⁻¹ := by
            rw [Finset.prod_mul_distrib]
    _ = (Real.pi ^ (p - 1)) *
          (∏ j ∈ Finset.range (p - 1),
            Real.sin (Real.pi * ((j + 1 : ℕ) : ℝ) / (p : ℝ)))⁻¹ := by
          simp
    _ = (Real.pi ^ (p - 1)) /
          (∏ j ∈ Finset.range (p - 1),
            Real.sin (Real.pi * ((j + 1 : ℕ) : ℝ) / (p : ℝ))) := by
          rw [div_eq_mul_inv]
    _ = (Real.pi ^ (p - 1)) / ((p : ℝ) / 2 ^ (p - 1)) := by
          rw [gauss_sine_product_range hp]
    _ = ((2 * Real.pi) ^ (p - 1)) / (p : ℝ) := by
          field_simp [hpR_ne]
          rw [mul_comm, ← mul_pow]

/-- Helper for Exercise 6: every factor in the rational Gamma product over `Finset.range (p - 1)`
is positive. -/
lemma gauss_rational_gamma_product_pos_range {p : ℕ} (hp : 2 ≤ p) :
    0 < ∏ j ∈ Finset.range (p - 1), Real.Gamma ((((j + 1 : ℕ) : ℝ) / (p : ℝ))) := by
  have hp_pos : 0 < p := by omega
  have hpR_pos : 0 < (p : ℝ) := by exact_mod_cast hp_pos
  -- Each Gamma factor is evaluated at a positive real, so the finite product stays positive.
  refine Finset.prod_pos ?_
  intro j hj
  have hj_arg_pos : 0 < (((j + 1 : ℕ) : ℝ) / (p : ℝ)) := by
    refine div_pos ?_ hpR_pos
    positivity
  exact Real.Gamma_pos_of_pos hj_arg_pos

/-- Helper for Exercise 6: the closed form appearing in the rational Gamma product formula is
strictly positive. -/
lemma gauss_closed_form_pos {p : ℕ} (hp : 2 ≤ p) :
    0 < (2 * Real.pi) ^ (((p - 1 : ℕ) : ℝ) / 2) * (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hp_pos : 0 < p := by omega
  have hpR_pos : 0 < (p : ℝ) := by exact_mod_cast hp_pos
  have htwo_pi_pos : 0 < 2 * Real.pi := by positivity
  -- Both `rpow` factors have positive bases, so the product is positive.
  exact mul_pos
    (Real.rpow_pos_of_pos htwo_pi_pos _)
    (Real.rpow_pos_of_pos hpR_pos _)

/-- Helper for Exercise 6: the proposed positive root has square equal to the already established
Gauss square constant. -/
lemma gauss_closed_form_square {p : ℕ} (hp : 2 ≤ p) :
    ((2 * Real.pi) ^ (((p - 1 : ℕ) : ℝ) / 2) * (p : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 =
      ((2 * Real.pi) ^ (p - 1)) / (p : ℝ) := by
  have hp_pos : 0 < p := by omega
  have hpR_pos : 0 < (p : ℝ) := by exact_mod_cast hp_pos
  have htwo_pi_pos : 0 < 2 * Real.pi := by positivity
  have hleft :
      (((2 * Real.pi) ^ (((p - 1 : ℕ) : ℝ) / 2)) ^ 2) =
        (2 * Real.pi) ^ (p - 1) := by
    -- Normalize the half-exponent square back to the natural-number power.
    have hp1 : 1 ≤ p := by omega
    rw [← Real.rpow_natCast (2 * Real.pi) (p - 1)]
    rw [← Real.rpow_natCast ((2 * Real.pi) ^ (((p - 1 : ℕ) : ℝ) / 2)) 2]
    rw [← Real.rpow_mul (le_of_lt htwo_pi_pos)]
    rw [Nat.cast_sub hp1]
    congr 1
    ring
  have hright :
      (((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2) = (p : ℝ)⁻¹ := by
    -- The negative half-power contributes exactly the reciprocal square root factor.
    rw [← Real.rpow_natCast ((p : ℝ) ^ (-(1 / 2 : ℝ))) 2]
    rw [← Real.rpow_mul (le_of_lt hpR_pos)]
    have hexp : (-(1 / 2 : ℝ)) * (((2 : ℕ) : ℝ)) = (-1 : ℝ) := by ring
    rw [hexp, Real.rpow_neg_one]
  -- Multiply the two normalized square factors and rewrite the reciprocal as division.
  calc
    (((2 * Real.pi) ^ (((p - 1 : ℕ) : ℝ) / 2)) * (p : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2
      = (((2 * Real.pi) ^ (((p - 1 : ℕ) : ℝ) / 2)) ^ 2) *
          (((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2) := by
            rw [mul_pow]
    _ = ((2 * Real.pi) ^ (p - 1)) * (p : ℝ)⁻¹ := by rw [hleft, hright]
    _ = ((2 * Real.pi) ^ (p - 1)) / (p : ℝ) := by rw [div_eq_mul_inv]

/-- Helper for Exercise 6: on `Finset.range (p - 1)`, the rational Gamma values have the expected
positive real product. -/
lemma gauss_rational_gamma_product_real_range {p : ℕ} (hp : 2 ≤ p) :
    ∏ j ∈ Finset.range (p - 1), Real.Gamma ((((j + 1 : ℕ) : ℝ) / (p : ℝ))) =
      (2 * Real.pi) ^ (((p - 1 : ℕ) : ℝ) / 2) * (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
  let A : ℝ :=
    ∏ j ∈ Finset.range (p - 1), Real.Gamma ((((j + 1 : ℕ) : ℝ) / (p : ℝ)))
  let B : ℝ :=
    (2 * Real.pi) ^ (((p - 1 : ℕ) : ℝ) / 2) * (p : ℝ) ^ (-(1 / 2 : ℝ))
  have hA_pos : 0 < A := by
    -- The Gamma-side product is positive because every factor lies on the positive real axis.
    dsimp [A]
    exact gauss_rational_gamma_product_pos_range hp
  have hB_pos : 0 < B := by
    -- The proposed closed form is also positive, so it is the positive square root.
    dsimp [B]
    exact gauss_closed_form_pos hp
  have hA_sq : A ^ 2 = ((2 * Real.pi) ^ (p - 1)) / (p : ℝ) := by
    -- Reuse the already-established square identity for the rational Gamma product.
    dsimp [A]
    exact gauss_rational_gamma_product_sq_range hp
  have hB_sq : B ^ 2 = ((2 * Real.pi) ^ (p - 1)) / (p : ℝ) := by
    -- Normalize the closed form once so the main proof only compares squares.
    dsimp [B]
    exact gauss_closed_form_square hp
  have hsq : A ^ 2 = B ^ 2 := by rw [hA_sq, hB_sq]
  -- Route correction: extract the positive root via `sq_eq_sq_iff_eq_or_eq_neg` and discard the
  -- negative branch using positivity on both sides.
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hAB | hAB
  · simpa [A, B] using hAB
  · exfalso
    rw [hAB] at hA_pos
    linarith

/-- Helper for Exercise 6: evaluating the integration constant at `w = 1 / p` determines the
unique scalar appearing in Gauss's right-half-plane identity. -/
lemma gauss_constant_from_one_div_p {p : ℕ} (hp : 2 ≤ p) {c : ℂ}
    (hc :
      Complex.Gamma 1 =
        c *
          (Complex.exp (((p : ℂ) * Real.log p) * ((1 : ℂ) / (p : ℂ))) *
            ∏ j ∈ Finset.range p, Complex.Gamma ((1 : ℂ) / (p : ℂ) + (j : ℂ) / (p : ℂ)))) :
    c = ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) * (p : ℂ) ^ (-(1 / 2 : ℂ)) := by
  let K : ℂ := ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) * (p : ℂ) ^ (-(1 / 2 : ℂ))
  let X : ℂ :=
    Complex.exp (((p : ℂ) * Real.log p) * ((1 : ℂ) / (p : ℂ))) *
      ∏ j ∈ Finset.range p, Complex.Gamma ((1 : ℂ) / (p : ℂ) + (j : ℂ) / (p : ℂ))
  have hp_pos : 0 < p := by omega
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp_pos)
  have htwo_pi_ne : (2 * Real.pi : ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have hrat :
      ∏ q ∈ Finset.Icc 1 (p - 1), Complex.Gamma ((q : ℂ) / (p : ℂ)) =
        ((2 * Real.pi : ℂ) ^ (((p - 1 : ℂ) / 2))) * (p : ℂ) ^ (-(1 / 2 : ℂ)) := by
    have hcast :
        (∏ q ∈ Finset.Icc 1 (p - 1), Complex.Gamma ((q : ℂ) / (p : ℂ))) =
          Complex.ofReal (∏ q ∈ Finset.Icc 1 (p - 1), Real.Gamma ((q : ℝ) / (p : ℝ))) := by
      -- Cast the positive real Gamma values into the complex product factor by factor.
      calc
        ∏ q ∈ Finset.Icc 1 (p - 1), Complex.Gamma ((q : ℂ) / (p : ℂ))
          = ∏ q ∈ Finset.Icc 1 (p - 1), Complex.ofReal (Real.Gamma ((q : ℝ) / (p : ℝ))) := by
              refine Finset.prod_congr rfl ?_
              intro q hq
              rw [← Complex.Gamma_ofReal]
              congr 1
              rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_div]
        _ = Complex.ofReal (∏ q ∈ Finset.Icc 1 (p - 1), Real.Gamma ((q : ℝ) / (p : ℝ))) := by
              symm
              exact map_prod Complex.ofRealHom
                (fun q : ℕ ↦ Real.Gamma ((q : ℝ) / (p : ℝ))) (Finset.Icc 1 (p - 1))
    have hreal :
        ∏ q ∈ Finset.Icc 1 (p - 1), Real.Gamma ((q : ℝ) / (p : ℝ)) =
          (2 * Real.pi) ^ ((p - 1 : ℝ) / 2) * (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
      have hp1 : 1 ≤ p := by omega
      rw [gauss_prod_Icc_eq_prod_range_succ (p := p) (hp := hp1)
        (f := fun q : ℕ ↦ Real.Gamma ((q : ℝ) / (p : ℝ)))]
      calc
        ∏ x ∈ Finset.range (p - 1), Real.Gamma ((((x + 1 : ℕ) : ℝ) / (p : ℝ)))
          = (2 * Real.pi) ^ (((p - 1 : ℕ) : ℝ) / 2) * (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
              simpa using gauss_rational_gamma_product_real_range hp
        _ = (2 * Real.pi) ^ ((p - 1 : ℝ) / 2) * (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
              rw [Nat.cast_sub hp1]
              norm_num
    rw [hcast, hreal, Complex.ofReal_mul,
      Complex.ofReal_cpow (by positivity), Complex.ofReal_cpow (by positivity)]
    congr 1 <;> norm_num
  have hX :
      X = ((2 * Real.pi : ℂ) ^ (((p - 1 : ℂ) / 2))) * (p : ℂ) ^ (1 / 2 : ℂ) := by
    -- Evaluate the right-half-plane factorization at `w = 1 / p` and split off the terminal `Γ 1`.
    calc
      X = (p : ℂ) *
            ((∏ q ∈ Finset.Icc 1 (p - 1), Complex.Gamma ((q : ℂ) / (p : ℂ))) * Complex.Gamma 1) := by
            dsimp [X]
            rw [gauss_exp_one_div_p hp_pos, gauss_gamma_product_one_div_p_split hp_pos]
      _ = (p : ℂ) *
            (((2 * Real.pi : ℂ) ^ (((p - 1 : ℂ) / 2))) * (p : ℂ) ^ (-(1 / 2 : ℂ))) := by
            rw [hrat, Complex.Gamma_one, mul_one]
      _ = ((2 * Real.pi : ℂ) ^ (((p - 1 : ℂ) / 2))) * ((p : ℂ) * (p : ℂ) ^ (-(1 / 2 : ℂ))) := by
            ac_rfl
      _ = ((2 * Real.pi : ℂ) ^ (((p - 1 : ℂ) / 2))) * (p : ℂ) ^ (1 / 2 : ℂ) := by
            have hp_half :
                (p : ℂ) * (p : ℂ) ^ (-(1 / 2 : ℂ)) = (p : ℂ) ^ (1 / 2 : ℂ) := by
              calc
                (p : ℂ) * (p : ℂ) ^ (-(1 / 2 : ℂ))
                  = (p : ℂ) ^ (1 : ℂ) * (p : ℂ) ^ (-(1 / 2 : ℂ)) := by
                      rw [Complex.cpow_one]
                _ = (p : ℂ) ^ ((1 : ℂ) + (-(1 / 2 : ℂ))) := by
                      rw [Complex.cpow_add _ _ hpC]
                _ = (p : ℂ) ^ (1 / 2 : ℂ) := by
                      congr 2
                      ring
            rw [hp_half]
  have hX_ne : X ≠ 0 := by
    rw [hX]
    exact mul_ne_zero
      ((Complex.cpow_ne_zero_iff).2 (Or.inl htwo_pi_ne))
      ((Complex.cpow_ne_zero_iff).2 (Or.inl hpC))
  have hc_mul : c * X = 1 := by
    -- After evaluating at `w = 1 / p`, the left-hand side becomes `Γ 1 = 1`.
    simpa [X, Complex.Gamma_one] using hc.symm
  have hK_mul : K * X = 1 := by
    -- The proposed constant is exactly the inverse of the evaluated right-hand factor.
    rw [hX]
    dsimp [K]
    have hpi :
        ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
            ((2 * Real.pi : ℂ) ^ (((p - 1 : ℂ) / 2))) = 1 := by
      calc
        ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
            ((2 * Real.pi : ℂ) ^ (((p - 1 : ℂ) / 2)))
          = (2 * Real.pi : ℂ) ^ ((-((p - 1 : ℂ) / 2)) + (((p - 1 : ℂ) / 2))) := by
              rw [← Complex.cpow_add _ _ htwo_pi_ne]
        _ = 1 := by
              congr 2
              ring
              simp
    have hpow :
        (p : ℂ) ^ (-(1 / 2 : ℂ)) * (p : ℂ) ^ (1 / 2 : ℂ) = 1 := by
      calc
        (p : ℂ) ^ (-(1 / 2 : ℂ)) * (p : ℂ) ^ (1 / 2 : ℂ)
          = (p : ℂ) ^ ((-(1 / 2 : ℂ)) + (1 / 2 : ℂ)) := by
              rw [← Complex.cpow_add _ _ hpC]
        _ = 1 := by
              congr 2
              ring
              simp
    calc
      (((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) * (p : ℂ) ^ (-(1 / 2 : ℂ))) *
          (((2 * Real.pi : ℂ) ^ (((p - 1 : ℂ) / 2))) * (p : ℂ) ^ (1 / 2 : ℂ))
        = (((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) * ((2 * Real.pi : ℂ) ^ (((p - 1 : ℂ) / 2)))) *
            ((p : ℂ) ^ (-(1 / 2 : ℂ)) * (p : ℂ) ^ (1 / 2 : ℂ)) := by
              ac_rfl
      _ = 1 := by
            rw [hpi]
            simpa using hpow
  have hsame : c * X = K * X := by rw [hc_mul, hK_mul]
  have hck : c = K := mul_right_cancel₀ hX_ne hsame
  simpa [K] using hck

lemma gauss_rational_gamma_product_sq {p : ℕ} (hp : 2 ≤ p) :
    (∏ q ∈ Finset.Icc 1 (p - 1), Real.Gamma ((q : ℝ) / (p : ℝ))) ^ 2 =
      ((2 * Real.pi) ^ (p - 1)) / (p : ℝ) := by
  -- Reindex the textbook interval before applying the range-native square identity.
  rw [gauss_prod_Icc_eq_prod_range_succ (p := p) (hp := by omega)
    (f := fun q : ℕ ↦ Real.Gamma ((q : ℝ) / (p : ℝ)))]
  exact gauss_rational_gamma_product_sq_range hp

/-- Helper for Exercise 6: the rational real Gamma product has the expected positive square root. -/
lemma gauss_rational_gamma_product_real {p : ℕ} (hp : 2 ≤ p) :
    ∏ q ∈ Finset.Icc 1 (p - 1), Real.Gamma ((q : ℝ) / (p : ℝ)) =
      (2 * Real.pi) ^ ((p - 1 : ℝ) / 2) * (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
  -- Reindex the textbook interval before applying the range-native positive-root identity.
  have hp1 : 1 ≤ p := by omega
  rw [gauss_prod_Icc_eq_prod_range_succ (p := p) (hp := by omega)
    (f := fun q : ℕ ↦ Real.Gamma ((q : ℝ) / (p : ℝ)))]
  calc
    ∏ x ∈ Finset.range (p - 1), Real.Gamma ((((x + 1 : ℕ) : ℝ) / (p : ℝ)))
      = (2 * Real.pi) ^ (((p - 1 : ℕ) : ℝ) / 2) * (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
          simpa using gauss_rational_gamma_product_real_range hp
    _ = (2 * Real.pi) ^ ((p - 1 : ℝ) / 2) * (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
          rw [Nat.cast_sub hp1]
          norm_num

/-- Helper for Exercise 6: the rational complex Gamma product is the complexification of the
positive real Gauss product. -/
lemma gauss_rational_gamma_product {p : ℕ} (hp : 2 ≤ p) :
    ∏ q ∈ Finset.Icc 1 (p - 1), Complex.Gamma ((q : ℂ) / (p : ℂ)) =
      ((2 * Real.pi : ℂ) ^ (((p - 1 : ℂ) / 2))) * (p : ℂ) ^ (-(1 / 2 : ℂ)) := by
  have hcast :
      (∏ q ∈ Finset.Icc 1 (p - 1), Complex.Gamma ((q : ℂ) / (p : ℂ))) =
        Complex.ofReal (∏ q ∈ Finset.Icc 1 (p - 1), Real.Gamma ((q : ℝ) / (p : ℝ))) := by
    -- Rewrite each complex Gamma factor as the complexification of the corresponding real one,
    -- then move `ofReal` across the finite product.
    calc
      ∏ q ∈ Finset.Icc 1 (p - 1), Complex.Gamma ((q : ℂ) / (p : ℂ))
        = ∏ q ∈ Finset.Icc 1 (p - 1), Complex.ofReal (Real.Gamma ((q : ℝ) / (p : ℝ))) := by
            refine Finset.prod_congr rfl ?_
            intro q hq
            rw [← Complex.Gamma_ofReal]
            congr 1
            rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_div]
      _ = Complex.ofReal (∏ q ∈ Finset.Icc 1 (p - 1), Real.Gamma ((q : ℝ) / (p : ℝ))) := by
            symm
            exact map_prod Complex.ofRealHom
              (fun q : ℕ ↦ Real.Gamma ((q : ℝ) / (p : ℝ))) (Finset.Icc 1 (p - 1))
  -- Cast the positive real Gauss product into `ℂ` and normalize the two `cpow` factors.
  rw [hcast, gauss_rational_gamma_product_real hp, Complex.ofReal_mul,
    Complex.ofReal_cpow (by positivity), Complex.ofReal_cpow (by positivity)]
  congr 1 <;> norm_num

/-- Helper for Exercise 6: shifting the Gamma argument by a natural number multiplies by the
expected finite affine product. -/
lemma gamma_add_nat_eq_prod {z : ℂ} (n : ℕ) (hz : ∀ m : ℕ, z ≠ -(m : ℂ)) :
    Complex.Gamma (z + n) = (∏ j ∈ Finset.range n, (z + j : ℂ)) * Complex.Gamma z := by
  induction n with
  | zero =>
      -- The empty product gives the trivial shift by `0`.
      simp
  | succ n ih =>
      -- Apply `Gamma_add_one` at the shifted point `z + n`, then use the induction hypothesis.
      have hzn : z + n ≠ 0 := by
        intro hzero
        apply hz n
        simpa using eq_neg_of_add_eq_zero_left hzero
      calc
        Complex.Gamma (z + n.succ)
          = Complex.Gamma ((z + n) + 1) := by simp [Nat.succ_eq_add_one, add_assoc]
        _ = (z + n) * Complex.Gamma (z + n) := by
              rw [Complex.Gamma_add_one (z + n) hzn]
        _ = (z + n) * ((∏ j ∈ Finset.range n, (z + j : ℂ)) * Complex.Gamma z) := by
              rw [ih]
        _ = (∏ j ∈ Finset.range n.succ, (z + j : ℂ)) * Complex.Gamma z := by
              rw [Finset.prod_range_succ]
              ring

/-- Helper for Exercise 6: a pole of `Γ((p : ℂ) * z)` is equivalent to a pole among the shifted
Gauss factors `Γ(z + j / p)`. -/
lemma gauss_scaled_nonpole_iff_shift_nonpoles {p : ℕ} (hp : 0 < p) (z : ℂ) :
    (∀ m : ℕ, (p : ℂ) * z ≠ -(m : ℂ)) ↔
      ∀ j ∈ Finset.range p, ∀ m : ℕ, z + (j : ℂ) / (p : ℂ) ≠ -(m : ℂ) := by
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
  constructor
  · intro hscaled j hj m hm
    have hmul : (p : ℂ) * (z + (j : ℂ) / (p : ℂ)) = -((p * m : ℕ) : ℂ) := by
      calc
        (p : ℂ) * (z + (j : ℂ) / (p : ℂ))
          = (p : ℂ) * (-(m : ℂ)) := by rw [hm]
        _ = -((p * m : ℕ) : ℂ) := by simp [Nat.cast_mul]
    have hscaled_eq : (p : ℂ) * z = -((p * m + j : ℕ) : ℂ) := by
      calc
        (p : ℂ) * z = (p : ℂ) * (z + (j : ℂ) / (p : ℂ)) - j := by
          field_simp [hpC]
          ring
        _ = -((p * m : ℕ) : ℂ) - j := by
          rw [hmul]
        _ = -((p * m + j : ℕ) : ℂ) := by
          rw [Nat.cast_add, Nat.cast_mul]
          ring
    exact hscaled (p * m + j) hscaled_eq
  · intro hshift m hscaled
    have hmcast : (((m % p + p * (m / p) : ℕ) : ℂ)) = (m : ℂ) := by
      exact_mod_cast (Nat.mod_add_div m p)
    have hmshift : z + ((m % p : ℕ) : ℂ) / (p : ℂ) = -((m / p : ℕ) : ℂ) := by
      apply (mul_right_injective₀ hpC)
      calc
        (p : ℂ) * (z + ((m % p : ℕ) : ℂ) / (p : ℂ))
          = (p : ℂ) * z + (((m % p : ℕ) : ℂ)) := by
              field_simp [hpC]
        _ = -(m : ℂ) + (((m % p : ℕ) : ℂ)) := by rw [hscaled]
        _ = -(((m % p + p * (m / p) : ℕ) : ℂ)) + (((m % p : ℕ) : ℂ)) := by
              simpa [hmcast]
        _ = -((p * (m / p) : ℕ) : ℂ) := by
              rw [Nat.cast_add, Nat.cast_mul]
              ring
        _ = (p : ℂ) * (-((m / p : ℕ) : ℂ)) := by
              simp [Nat.cast_mul]
    exact hshift (m % p) (Finset.mem_range.mpr (Nat.mod_lt _ hp)) (m / p) hmshift

/-- Helper for Exercise 6: shifting every factor in the Gauss product by `1` produces the
expected affine multiplier. -/
lemma gauss_shifted_gamma_product_add_one {p : ℕ} {z : ℂ}
    (hz : ∀ j ∈ Finset.range p, z + (j : ℂ) / (p : ℂ) ≠ 0) :
    ∏ j ∈ Finset.range p, Complex.Gamma (z + 1 + (j : ℂ) / (p : ℂ)) =
      (∏ j ∈ Finset.range p, (z + (j : ℂ) / (p : ℂ))) *
        ∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ)) := by
  -- Rewrite each factor with `Gamma_add_one`, then split the product of products.
  calc
    ∏ j ∈ Finset.range p, Complex.Gamma (z + 1 + (j : ℂ) / (p : ℂ))
      = ∏ j ∈ Finset.range p, ((z + (j : ℂ) / (p : ℂ)) * Complex.Gamma (z + (j : ℂ) / (p : ℂ))) := by
          refine Finset.prod_congr rfl ?_
          intro j hj
          rw [show z + 1 + (j : ℂ) / (p : ℂ) = (z + (j : ℂ) / (p : ℂ)) + 1 by ring]
          rw [Complex.Gamma_add_one (z + (j : ℂ) / (p : ℂ)) (hz j hj)]
    _ = (∏ j ∈ Finset.range p, (z + (j : ℂ) / (p : ℂ))) *
          ∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ)) := by
            rw [Finset.prod_mul_distrib]

/-- Helper for Exercise 6: the affine Gauss factors factor off the common power of `p`. -/
lemma gauss_affine_factor_product {p : ℕ} (hp : 0 < p) (z : ℂ) :
    ∏ j ∈ Finset.range p, ((p : ℂ) * z + j) =
      (p : ℂ) ^ p * ∏ j ∈ Finset.range p, (z + (j : ℂ) / (p : ℂ)) := by
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
  calc
    ∏ j ∈ Finset.range p, ((p : ℂ) * z + j)
      = ∏ j ∈ Finset.range p, ((p : ℂ) * (z + (j : ℂ) / (p : ℂ))) := by
          refine Finset.prod_congr rfl ?_
          intro j hj
          calc
            (p : ℂ) * z + j = (p : ℂ) * z + (p : ℂ) * ((j : ℂ) / (p : ℂ)) := by
              field_simp [hpC]
            _ = (p : ℂ) * (z + (j : ℂ) / (p : ℂ)) := by ring
    _ = (∏ _j ∈ Finset.range p, (p : ℂ)) * ∏ j ∈ Finset.range p, (z + (j : ℂ) / (p : ℂ)) := by
          rw [Finset.prod_mul_distrib]
    _ = (p : ℂ) ^ p * ∏ j ∈ Finset.range p, (z + (j : ℂ) / (p : ℂ)) := by
          simp

/-- Helper for Exercise 6: once Gauss's formula is known at `z + 1`, the shared Gamma recurrence
transfers it down to `z` provided the scaled argument avoids the poles. -/
lemma gauss_multiplication_formula_step_down {p : ℕ} (hp : 0 < p) {z : ℂ}
    (hscaled : ∀ m : ℕ, (p : ℂ) * z ≠ -(m : ℂ))
    (hstep :
      Complex.Gamma ((p : ℂ) * (z + 1)) =
        ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
          (p : ℂ) ^ ((p : ℂ) * (z + 1) - (1 / 2 : ℂ)) *
            (∏ j ∈ Finset.range p, Complex.Gamma (z + 1 + (j : ℂ) / (p : ℂ)))) :
    Complex.Gamma ((p : ℂ) * z) =
      ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
        (p : ℂ) ^ ((p : ℂ) * z - (1 / 2 : ℂ)) *
          (∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ))) := by
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
  have hshift_nonpoles :
      ∀ j ∈ Finset.range p, ∀ m : ℕ, z + (j : ℂ) / (p : ℂ) ≠ -(m : ℂ) :=
    (gauss_scaled_nonpole_iff_shift_nonpoles hp z).1 hscaled
  have hleft :
      Complex.Gamma ((p : ℂ) * (z + 1)) =
        (∏ j ∈ Finset.range p, ((p : ℂ) * z + j)) * Complex.Gamma ((p : ℂ) * z) := by
    -- Apply the Gamma recurrence to the scaled argument with exactly `p` successive shifts.
    calc
      Complex.Gamma ((p : ℂ) * (z + 1))
        = Complex.Gamma ((p : ℂ) * z + p) := by ring
      _ = (∏ j ∈ Finset.range p, (((p : ℂ) * z) + j : ℂ)) * Complex.Gamma ((p : ℂ) * z) := by
            simpa [add_assoc, add_comm, add_left_comm] using
              (gamma_add_nat_eq_prod (z := (p : ℂ) * z) p hscaled)
  have hshifted_gamma :
      ∏ j ∈ Finset.range p, Complex.Gamma (z + 1 + (j : ℂ) / (p : ℂ)) =
        (∏ j ∈ Finset.range p, (z + (j : ℂ) / (p : ℂ))) *
          ∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ)) := by
    -- Each shifted Gamma factor contributes its affine multiplier via `Gamma_add_one`.
    refine gauss_shifted_gamma_product_add_one (p := p) (z := z) ?_
    intro j hj
    simpa using hshift_nonpoles j hj 0
  have hpow :
      (p : ℂ) ^ ((p : ℂ) * (z + 1) - (1 / 2 : ℂ)) =
        (p : ℂ) ^ p * (p : ℂ) ^ ((p : ℂ) * z - (1 / 2 : ℂ)) := by
    -- The power factor splits off the expected common `p ^ p`.
    calc
      (p : ℂ) ^ ((p : ℂ) * (z + 1) - (1 / 2 : ℂ))
        = (p : ℂ) ^ (((p : ℂ) * z - (1 / 2 : ℂ)) + p) := by
            congr 2
            ring
      _ = (p : ℂ) ^ ((p : ℂ) * z - (1 / 2 : ℂ)) * (p : ℂ) ^ p := by
            rw [Complex.cpow_add _ _ hpC, Complex.cpow_natCast]
      _ = (p : ℂ) ^ p * (p : ℂ) ^ ((p : ℂ) * z - (1 / 2 : ℂ)) := by
            ac_rfl
  have hright :
      ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
          (p : ℂ) ^ ((p : ℂ) * (z + 1) - (1 / 2 : ℂ)) *
          (∏ j ∈ Finset.range p, Complex.Gamma (z + 1 + (j : ℂ) / (p : ℂ))) =
        (∏ j ∈ Finset.range p, ((p : ℂ) * z + j)) *
          (((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
            (p : ℂ) ^ ((p : ℂ) * z - (1 / 2 : ℂ)) *
            (∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ)))) := by
    -- Normalize the shift on the right-hand side into the same affine product as on the left.
    calc
      ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
          (p : ℂ) ^ ((p : ℂ) * (z + 1) - (1 / 2 : ℂ)) *
          (∏ j ∈ Finset.range p, Complex.Gamma (z + 1 + (j : ℂ) / (p : ℂ)))
        = ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
            ((p : ℂ) ^ p * (p : ℂ) ^ ((p : ℂ) * z - (1 / 2 : ℂ))) *
            ((∏ j ∈ Finset.range p, (z + (j : ℂ) / (p : ℂ))) *
              ∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ))) := by
              rw [hpow, hshifted_gamma]
      _ = ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
            (((p : ℂ) ^ p * ∏ j ∈ Finset.range p, (z + (j : ℂ) / (p : ℂ))) *
              ((p : ℂ) ^ ((p : ℂ) * z - (1 / 2 : ℂ)) *
                ∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ)))) := by
              ac_rfl
      _ = ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
            ((∏ j ∈ Finset.range p, ((p : ℂ) * z + j)) *
              ((p : ℂ) ^ ((p : ℂ) * z - (1 / 2 : ℂ)) *
                ∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ)))) := by
              rw [gauss_affine_factor_product hp z]
      _ = (∏ j ∈ Finset.range p, ((p : ℂ) * z + j)) *
            (((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
              (p : ℂ) ^ ((p : ℂ) * z - (1 / 2 : ℂ)) *
              (∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ)))) := by
              ac_rfl
  have haff_nonzero :
      ∏ j ∈ Finset.range p, ((p : ℂ) * z + j) ≠ 0 := by
    -- No affine factor vanishes because a zero would force a forbidden pole of `Γ ((p : ℂ) * z)`.
    refine Finset.prod_ne_zero_iff.2 ?_
    intro j hj
    intro hzj
    apply hscaled j
    exact (eq_neg_iff_add_eq_zero).2 hzj
  have hmain :
      (∏ j ∈ Finset.range p, ((p : ℂ) * z + j)) * Complex.Gamma ((p : ℂ) * z) =
        (∏ j ∈ Finset.range p, ((p : ℂ) * z + j)) *
          (((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
            (p : ℂ) ^ ((p : ℂ) * z - (1 / 2 : ℂ)) *
            (∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ)))) := by
    -- After rewriting both sides through the shared affine factor, the step hypothesis matches.
    calc
      (∏ j ∈ Finset.range p, ((p : ℂ) * z + j)) * Complex.Gamma ((p : ℂ) * z)
        = Complex.Gamma ((p : ℂ) * (z + 1)) := by
            symm
            exact hleft
      _ = ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
            (p : ℂ) ^ ((p : ℂ) * (z + 1) - (1 / 2 : ℂ)) *
            (∏ j ∈ Finset.range p, Complex.Gamma (z + 1 + (j : ℂ) / (p : ℂ))) := hstep
      _ = (∏ j ∈ Finset.range p, ((p : ℂ) * z + j)) *
            (((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
              (p : ℂ) ^ ((p : ℂ) * z - (1 / 2 : ℂ)) *
              (∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ)))) := hright
  exact mul_left_cancel₀ haff_nonzero hmain

/-- Helper for Exercise 6: once Gauss's formula is known on the right half-plane, repeated use of
the Gamma recurrence extends it to every nonpole argument. -/
lemma gauss_multiplication_formula_of_nonpole {p : ℕ} (hp : 0 < p)
    (h_right :
      Set.EqOn
        (fun w ↦ Complex.Gamma ((p : ℂ) * w))
        (fun w ↦
          ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
            (p : ℂ) ^ ((p : ℂ) * w - (1 / 2 : ℂ)) *
              ∏ j ∈ Finset.range p, Complex.Gamma (w + (j : ℂ) / (p : ℂ)))
        gauss_right_half_plane)
    {z : ℂ} (hscaled : ∀ m : ℕ, (p : ℂ) * z ≠ -(m : ℂ)) :
    Complex.Gamma ((p : ℂ) * z) =
      ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
        (p : ℂ) ^ ((p : ℂ) * z - (1 / 2 : ℂ)) *
          (∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ))) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, -z.re < n := exists_nat_gt (-z.re)
  have hz_right : z + n ∈ gauss_right_half_plane := by
    -- Choosing a large enough natural shift moves the real part into the right half-plane.
    dsimp [gauss_right_half_plane]
    have hz_re : 0 < z.re + n := by
      linarith
    simpa [Complex.add_re] using hz_re
  have hscaled_shift :
      ∀ k : ℕ, ∀ m : ℕ, (p : ℂ) * (z + k) ≠ -(m : ℂ) := by
    intro k m hm
    -- The same nonpole condition propagates under natural-number shifts.
    apply hscaled (m + p * k)
    calc
      (p : ℂ) * z = (p : ℂ) * (z + k) - (p : ℂ) * k := by ring
      _ = -(m : ℂ) - (p : ℂ) * k := by rw [hm]
      _ = -((m + p * k : ℕ) : ℂ) := by
            rw [Nat.cast_add, Nat.cast_mul]
            ring
  have hdesc :
      ∀ k : ℕ,
        Complex.Gamma ((p : ℂ) * (z + k)) =
            ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
              (p : ℂ) ^ ((p : ℂ) * (z + k) - (1 / 2 : ℂ)) *
                (∏ j ∈ Finset.range p, Complex.Gamma (z + k + (j : ℂ) / (p : ℂ))) →
          Complex.Gamma ((p : ℂ) * z) =
            ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
              (p : ℂ) ^ ((p : ℂ) * z - (1 / 2 : ℂ)) *
                (∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ))) := by
    intro k
    induction k with
    | zero =>
        intro hk
        simpa using hk
    | succ k ih =>
        intro hk
        -- Descend one step from `z + k + 1` to `z + k`, then iterate the induction hypothesis.
        apply ih
        have hk' :
            Complex.Gamma ((p : ℂ) * ((z + k) + 1)) =
              ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
                (p : ℂ) ^ ((p : ℂ) * ((z + k) + 1) - (1 / 2 : ℂ)) *
                  (∏ j ∈ Finset.range p, Complex.Gamma ((z + k) + 1 + (j : ℂ) / (p : ℂ))) := by
          simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using hk
        exact gauss_multiplication_formula_step_down (z := z + k) hp (hscaled_shift k) hk'
  exact hdesc n (h_right hz_right)

/-- Helper for Exercise 6: when the scaled Gamma factor hits a pole, one shifted factor on the
right also hits a pole, so both sides of Gauss's formula vanish. -/
lemma gauss_multiplication_formula_of_pole {p : ℕ} (hp : 0 < p) {z : ℂ}
    (hscaled : ∃ m : ℕ, (p : ℂ) * z = -(m : ℂ)) :
    Complex.Gamma ((p : ℂ) * z) =
      ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
        (p : ℂ) ^ ((p : ℂ) * z - (1 / 2 : ℂ)) *
          (∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ))) := by
  rcases hscaled with ⟨m, hm⟩
  have hleft : Complex.Gamma ((p : ℂ) * z) = 0 := by
    -- The left-hand side is exactly Gamma at a nonpositive integer.
    simpa [hm] using Complex.Gamma_neg_nat_eq_zero m
  have hnot_nonpole : ¬ ∀ n : ℕ, (p : ℂ) * z ≠ -(n : ℂ) := by
    intro h
    exact h m hm
  have hnot_shift :
      ¬ ∀ j ∈ Finset.range p, ∀ n : ℕ, z + (j : ℂ) / (p : ℂ) ≠ -(n : ℂ) := by
    -- Contrapositively, a pole on the left forces a pole among the shifted factors.
    intro hshift
    exact hnot_nonpole ((gauss_scaled_nonpole_iff_shift_nonpoles hp z).2 hshift)
  push_neg at hnot_shift
  rcases hnot_shift with ⟨j, hj, n, hjn⟩
  have hprod_zero :
      ∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ)) = 0 := by
    -- The single vanishing Gamma factor kills the whole finite product.
    refine Finset.prod_eq_zero_iff.2 ?_
    exact ⟨j, hj, by simpa [hjn] using Complex.Gamma_neg_nat_eq_zero n⟩
  calc
    Complex.Gamma ((p : ℂ) * z) = 0 := hleft
    _ = ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
          (p : ℂ) ^ ((p : ℂ) * z - (1 / 2 : ℂ)) *
          (∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ))) := by
            simp [hprod_zero]

/-- Helper for Exercise 6: the remaining nontrivial branch of Gauss's multiplication formula starts
at `p = 2`. -/
lemma gauss_multiplication_formula_of_two_le {p : ℕ} (hp : 2 ≤ p) (z : ℂ) :
    Complex.Gamma ((p : ℂ) * z) =
      ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
        (p : ℂ) ^ ((p : ℂ) * z - (1 / 2 : ℂ)) *
          (∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ))) := by
  by_cases hp_eq : p = 2
  · -- The boundary case `p = 2` is exactly duplication.
    subst hp_eq
    simpa using gauss_multiplication_formula_two z
  have hp_three : 3 ≤ p := by omega
  -- Route correction: the old `GammaSeq` branch drifted away from the source proof.
  -- The verified frontier now uses the right half-plane, where the shifted and scaled Gamma
  -- factors are nonvanishing and `logDeriv_eqOn_iff` is applicable.
  have h_open : IsOpen gauss_right_half_plane := isOpen_gauss_right_half_plane
  have h_preconnected : IsPreconnected gauss_right_half_plane := isPreconnected_gauss_right_half_plane
  have h_shift_nonzero :
      ∀ {w : ℂ}, w ∈ gauss_right_half_plane →
        ∏ j ∈ Finset.range p, Complex.Gamma (w + (j : ℂ) / (p : ℂ)) ≠ 0 := by
    intro w hw
    exact gauss_gamma_prod_ne_zero hw
  have h_scaled_nonzero :
      ∀ {w : ℂ}, w ∈ gauss_right_half_plane → Complex.Gamma ((p : ℂ) * w) ≠ 0 := by
    intro w hw
    exact gauss_gamma_scaled_ne_zero (show 0 < p by omega) hw
  have h_rhs_nonzero :
      ∀ {w : ℂ}, w ∈ gauss_right_half_plane →
        (p : ℂ) ^ ((p : ℂ) * w - (1 / 2 : ℂ)) *
          ∏ j ∈ Finset.range p, Complex.Gamma (w + (j : ℂ) / (p : ℂ)) ≠ 0 := by
    intro w hw
    -- This is the nonvanishing input needed for the eventual `logDeriv_eqOn_iff` step.
    exact gauss_rhs_ne_zero (show 0 < p by omega) hw
  have h_digamma :
      ∀ ⦃w : ℂ⦄, w ∈ gauss_right_half_plane →
        ∑ j ∈ Finset.range p, Complex.digamma (w + (j : ℂ) / (p : ℂ)) =
          (p : ℂ) * Complex.digamma ((p : ℂ) * w) - (p : ℂ) * Real.log p := by
    intro w hw
    exact gauss_digamma_sum_eq_scaled_digamma_sub_log hp hw
  have h_logDeriv :
      Set.EqOn
        (logDeriv (fun w ↦ Complex.Gamma ((p : ℂ) * w)))
        (logDeriv
          (fun w ↦
            Complex.exp (((p : ℂ) * Real.log p) * w) *
              ∏ j ∈ Finset.range p, Complex.Gamma (w + (j : ℂ) / (p : ℂ))))
        gauss_right_half_plane := by
    -- The right-half-plane digamma identity now supplies the exact logarithmic-derivative match.
    exact gauss_logDeriv_eqOn_exp_rhs_of_digamma_sum (show 0 < p by omega) h_digamma
  have h_scaled_diffOn :
      DifferentiableOn ℂ (fun w ↦ Complex.Gamma ((p : ℂ) * w)) gauss_right_half_plane := by
    intro w hw
    -- The scaled Gamma term is holomorphic on the right half-plane because no pole is reached.
    have hcomp :
        DifferentiableAt ℂ (Complex.Gamma ∘ fun z ↦ (p : ℂ) * z) w :=
      DifferentiableAt.comp (x := w) (g := Complex.Gamma) (f := fun z ↦ (p : ℂ) * z)
        (Complex.differentiableAt_Gamma _ (gauss_scaled_nonpole (show 0 < p by omega) hw))
        (by fun_prop : DifferentiableAt ℂ (fun z ↦ (p : ℂ) * z) w)
    simpa [Function.comp] using hcomp.differentiableWithinAt
  have h_exp_rhs_diffOn :
      DifferentiableOn ℂ
        (fun w ↦
          Complex.exp (((p : ℂ) * Real.log p) * w) *
            ∏ j ∈ Finset.range p, Complex.Gamma (w + (j : ℂ) / (p : ℂ)))
        gauss_right_half_plane := by
    intro w hw
    -- The source right-hand side is a product of an entire exponential factor and shifted Gamma
    -- factors that stay pole-free on the chosen domain.
    have h_exp_at :
        DifferentiableAt ℂ (fun z ↦ Complex.exp (((p : ℂ) * Real.log p) * z)) w := by
      fun_prop
    have h_prod_at :
        DifferentiableAt ℂ
          (fun z ↦ ∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ))) w := by
      refine DifferentiableAt.fun_finsetProd ?_
      intro j hj
      have hcomp :
          DifferentiableAt ℂ
            (Complex.Gamma ∘ fun z ↦ z + (j : ℂ) / (p : ℂ)) w :=
        DifferentiableAt.comp (x := w) (g := Complex.Gamma)
          (f := fun z ↦ z + (j : ℂ) / (p : ℂ))
          (Complex.differentiableAt_Gamma (w + (j : ℂ) / (p : ℂ))
            (gauss_shift_nonpole (p := p) (j := j) hw))
          (by fun_prop : DifferentiableAt ℂ (fun z ↦ z + (j : ℂ) / (p : ℂ)) w)
      simpa [Function.comp] using hcomp
    exact (h_exp_at.mul h_prod_at).differentiableWithinAt
  obtain ⟨c, hc, h_eqOn_exp_rhs⟩ :=
    (logDeriv_eqOn_iff h_scaled_diffOn h_exp_rhs_diffOn h_open h_preconnected
      (fun w hw ↦ gauss_exp_rhs_ne_zero hw) (fun w hw ↦ h_scaled_nonzero (w := w) hw)).mp h_logDeriv
  have hp_pos : 0 < p := by omega
  have h_right :
      Set.EqOn
        (fun w ↦ Complex.Gamma ((p : ℂ) * w))
        (fun w ↦
          ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
            (p : ℂ) ^ ((p : ℂ) * w - (1 / 2 : ℂ)) *
              ∏ j ∈ Finset.range p, Complex.Gamma (w + (j : ℂ) / (p : ℂ)))
        gauss_right_half_plane := by
    have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp_pos)
    have hw : ((1 : ℂ) / (p : ℂ)) ∈ gauss_right_half_plane :=
      one_div_nat_mem_gauss_right_half_plane hp_pos
    have hc_eval :
        Complex.Gamma 1 =
          c *
            (Complex.exp (((p : ℂ) * Real.log p) * ((1 : ℂ) / (p : ℂ))) *
              ∏ j ∈ Finset.range p, Complex.Gamma ((1 : ℂ) / (p : ℂ) + (j : ℂ) / (p : ℂ))) := by
      -- Evaluating the integrated identity at `w = 1 / p` turns the left-hand side into `Γ 1`.
      have hpoint := h_eqOn_exp_rhs hw
      have hmul : (p : ℂ) * ((1 : ℂ) / (p : ℂ)) = 1 := by
        field_simp [hpC]
      calc
        Complex.Gamma 1 = Complex.Gamma ((p : ℂ) * ((1 : ℂ) / (p : ℂ))) := by rw [hmul]
        _ = c *
              (Complex.exp (((p : ℂ) * Real.log p) * ((1 : ℂ) / (p : ℂ))) *
                ∏ j ∈ Finset.range p, Complex.Gamma ((1 : ℂ) / (p : ℂ) + (j : ℂ) / (p : ℂ))) := by
                simpa [smul_eq_mul] using hpoint
    have hc_const :
        c = ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) * (p : ℂ) ^ (-(1 / 2 : ℂ)) :=
      gauss_constant_from_one_div_p hp hc_eval
    intro w hw'
    -- Substitute the determined constant and normalize the exponential prefactor to the target
    -- `cpow` form.
    calc
      Complex.Gamma ((p : ℂ) * w)
        = c *
            (Complex.exp (((p : ℂ) * Real.log p) * w) *
              ∏ j ∈ Finset.range p, Complex.Gamma (w + (j : ℂ) / (p : ℂ))) := by
              simpa [smul_eq_mul] using h_eqOn_exp_rhs hw'
      _ = (((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) * (p : ℂ) ^ (-(1 / 2 : ℂ))) *
            (Complex.exp (((p : ℂ) * Real.log p) * w) *
              ∏ j ∈ Finset.range p, Complex.Gamma (w + (j : ℂ) / (p : ℂ))) := by
              rw [hc_const]
      _ = ((((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) * (p : ℂ) ^ (-(1 / 2 : ℂ))) *
            Complex.exp (((p : ℂ) * Real.log p) * w)) *
            ∏ j ∈ Finset.range p, Complex.Gamma (w + (j : ℂ) / (p : ℂ)) := by
              ac_rfl
      _ = (((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
            (p : ℂ) ^ ((p : ℂ) * w - (1 / 2 : ℂ))) *
            ∏ j ∈ Finset.range p, Complex.Gamma (w + (j : ℂ) / (p : ℂ)) := by
              rw [gauss_prefactor_normal_form hp_pos w]
      _ = ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
            (p : ℂ) ^ ((p : ℂ) * w - (1 / 2 : ℂ)) *
            ∏ j ∈ Finset.range p, Complex.Gamma (w + (j : ℂ) / (p : ℂ)) := by
              ac_rfl
  by_cases hscaled : ∀ m : ℕ, (p : ℂ) * z ≠ -(m : ℂ)
  · -- Once the right-half-plane formula is available, repeated recurrence handles every nonpole.
    exact gauss_multiplication_formula_of_nonpole hp_pos h_right hscaled
  · -- If the scaled point is a pole, a shifted factor on the right is also a pole.
    push_neg at hscaled
    exact gauss_multiplication_formula_of_pole hp_pos hscaled

/-- Exercise 6 (2): Gauss's multiplication formula for the complex Gamma function for every
positive integer `p`. -/
-- TODO: the remaining proof needs the full source-faithful integration step on the right
-- half-plane together with the constant-evaluation API for the rational Gamma product.
theorem exercise_6_gauss_multiplication_formula {p : ℕ} (hp : 0 < p) (z : ℂ) :
    Complex.Gamma ((p : ℂ) * z) =
      ((2 * Real.pi : ℂ) ^ (-((p - 1 : ℂ) / 2))) *
        (p : ℂ) ^ ((p : ℂ) * z - (1 / 2 : ℂ)) *
          (∏ j ∈ Finset.range p, Complex.Gamma (z + (j : ℂ) / (p : ℂ))) := by
  by_cases hp1 : p = 1
  · -- The `p = 1` case is tautological after simplifying the finite product and powers.
    subst hp1
    simp
  have hp2 : 2 ≤ p := by omega
  -- Route correction: after splitting off the tautological `p = 1` case, the entire remaining
  -- problem is the general `p ≥ 2` logarithmic-derivative argument from the plan.
  exact gauss_multiplication_formula_of_two_le hp2 z
