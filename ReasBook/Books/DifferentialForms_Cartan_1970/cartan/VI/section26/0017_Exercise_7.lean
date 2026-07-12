import Mathlib
import DifferentialForms_Cartan_1970.II.section06.«0015_Remark_II_2_extra_6»
import DifferentialForms_Cartan_1970.III.section12.«0022_Exercise_10»
import DifferentialForms_Cartan_1970.VI.section22.«0006_Definition_VI_1_extra_4»
import DifferentialForms_Cartan_1970.VI.section26.«0017_Exercise_7».Index

-- Declarations for this item will be appended below by the statement pipeline.

open Metric Set ComplexOrder
open scoped ComplexConjugate

noncomputable section

/-- Helper for Exercise 7: the global forward branch factors the square-root ambiguity into the
linear factor `z`, so the remaining square root is taken on a nonvanishing even factor. -/
def cassiniGlobalForward (a r : ℝ) : ℂ → ℂ :=
  fun z ↦ z * Complex.sqrt
    ((((r : ℂ) ^ 2) /
      (((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ))))

/-- Helper for Exercise 7: the global inverse branch uses the same odd factorization on the unit
disc side. -/
def cassiniGlobalInverse (a r : ℝ) : ℂ → ℂ :=
  fun w ↦ w * Complex.sqrt
    ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) /
      (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)))

/-- Helper for Exercise 7: the global forward branch squares to the source Möbius term. -/
lemma cassiniGlobalForward_sq {a r : ℝ} (z : ℂ) :
    cassiniGlobalForward a r z ^ 2 = cassiniOvalMobius a r (z ^ 2) := by
  -- Expanding the odd factorization leaves exactly the source Möbius quotient.
  unfold cassiniGlobalForward cassiniOvalMobius
  calc
    (z * Complex.sqrt
        (((r : ℂ) ^ 2) / (((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ)))) ^ 2 =
        z ^ 2 *
          (Complex.sqrt
            (((r : ℂ) ^ 2) / (((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ)))) ^ 2 := by
      ring
    _ = z ^ 2 *
          ((((r : ℂ) ^ 2) / (((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ)))) := by
      rw [sq_sqrt_complex]
    _ = (((r : ℂ) ^ 2) * z ^ 2) /
          (((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ)) := by
      rw [div_eq_mul_inv]
      ring

/-- Helper for Exercise 7: the global inverse branch squares to the solved quadratic inverse
expression. -/
lemma cassiniGlobalInverse_sq {a r : ℝ} (w : ℂ) :
    cassiniGlobalInverse a r w ^ 2 =
      ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) /
        (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)) := by
  -- The inverse factorization is the same algebra with the solved square variable.
  unfold cassiniGlobalInverse
  calc
    (w * Complex.sqrt
        ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) /
          (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)))) ^ 2 =
        w ^ 2 *
          (Complex.sqrt
            ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) /
              (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)))) ^ 2 := by
      ring
    _ = w ^ 2 *
          ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) /
            (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2))) := by
      rw [sq_sqrt_complex]
    _ = ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) /
          (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)) := by
      rw [div_eq_mul_inv]
      ring

/-- Helper for Exercise 7: the reciprocal of a slit-plane point remains on the slit plane. -/
lemma inv_mem_slitPlane_of_mem_slitPlane {Z : ℂ} (hZ : Z ∈ Complex.slitPlane) :
    Z⁻¹ ∈ Complex.slitPlane := by
  -- Inversion rescales the real and imaginary parts by the positive real factor `‖Z‖⁻²`.
  have hZ_ne : Z ≠ 0 := Complex.slitPlane_ne_zero hZ
  have hnorm_sq_pos : 0 < ‖Z‖ ^ 2 := by
    exact sq_pos_of_pos (norm_pos_iff.mpr hZ_ne)
  rw [Complex.mem_slitPlane_iff] at hZ ⊢
  rcases hZ with hZre | hZim
  · left
    have hre : (Z⁻¹).re = Z.re / ‖Z‖ ^ 2 := by
      simp [Complex.inv_re, Complex.normSq_eq_norm_sq]
    rw [hre]
    positivity
  · right
    have him : (Z⁻¹).im = -Z.im / ‖Z‖ ^ 2 := by
      simp [Complex.inv_im, Complex.normSq_eq_norm_sq]
    rw [him]
    exact div_ne_zero (neg_ne_zero.mpr hZim) (pow_ne_zero 2 (norm_ne_zero_iff.mpr hZ_ne))

/-- Helper for Exercise 7: inversion preserves strict positivity of the real part. -/
lemma inv_re_pos_of_re_pos {Z : ℂ} (hZre : 0 < Z.re) :
    0 < (Z⁻¹).re := by
  -- The real part of `Z⁻¹` is `Re Z / ‖Z‖²`.
  have hZ_ne : Z ≠ 0 := by
    intro hZ0
    have hnot : ¬ 0 < Z.re := by
      simp [hZ0]
    exact hnot hZre
  have hnorm_sq_pos : 0 < ‖Z‖ ^ 2 := by
    exact sq_pos_of_pos (norm_pos_iff.mpr hZ_ne)
  have hre : (Z⁻¹).re = Z.re / ‖Z‖ ^ 2 := by
    simp [Complex.inv_re, Complex.normSq_eq_norm_sq]
  rw [hre]
  positivity

/-- Helper for Exercise 7: on the principal slit plane, the principal square root commutes with
inversion. -/
lemma sqrt_inv_of_mem_slitPlane {Z : ℂ} (hZ : Z ∈ Complex.slitPlane) :
    Complex.sqrt Z⁻¹ = (Complex.sqrt Z)⁻¹ := by
  -- Both candidates square to `Z⁻¹`, and both have positive real part, so the principal branch
  -- selects the same root.
  have hZinv : Z⁻¹ ∈ Complex.slitPlane := inv_mem_slitPlane_of_mem_slitPlane hZ
  have hsqrt_re : 0 < (Complex.sqrt (Z⁻¹)).re := sqrt_re_pos_of_mem_slitPlane hZinv
  have hsqrt_inv_re : 0 < ((Complex.sqrt Z)⁻¹).re := by
    exact inv_re_pos_of_re_pos (sqrt_re_pos_of_mem_slitPlane hZ)
  have hsqrt_ne : Complex.sqrt Z ≠ 0 := by
    intro hsqrt_zero
    have hsq : Complex.sqrt Z ^ 2 = Z :=
      sq_sqrt_of_mem_slitPlane_or_zero (Or.inr hZ)
    rw [hsqrt_zero] at hsq
    exact Complex.slitPlane_ne_zero hZ (by simpa using hsq.symm)
  have hsq :
      (Complex.sqrt (Z⁻¹)) ^ 2 = ((Complex.sqrt Z)⁻¹) ^ 2 := by
    calc
      (Complex.sqrt (Z⁻¹)) ^ 2 = Z⁻¹ := by
        exact sq_sqrt_of_mem_slitPlane_or_zero (Or.inr hZinv)
      _ = ((Complex.sqrt Z) ^ 2)⁻¹ := by
        rw [sq_sqrt_of_mem_slitPlane_or_zero (Or.inr hZ)]
      _ = ((Complex.sqrt Z)⁻¹) ^ 2 := by
        rw [inv_pow]
  exact eq_of_sq_eq_sq_of_re_pos hsqrt_re hsqrt_inv_re hsq

/-- Helper for Exercise 7: the forward denominator has strictly positive real part on the full
Cassini interior. -/
lemma cassiniGlobalForwardDenominator_re_pos
    {a r : ℝ} (ha : 0 < a) (har : a < r) {z : ℂ}
    (hz : z ∈ cassiniOvalInterior a r) :
    0 < ((((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ)).re) := by
  let η : ℂ := ((z ^ 2 - (a : ℂ) ^ 2) / ((r : ℂ) ^ 2))
  have hr_pos : 0 < r := lt_trans ha har
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hη_ball : η ∈ ball (0 : ℂ) 1 := by
    -- The normalized square coordinate of a Cassini-interior point lies in the unit disc.
    simpa [η] using normalized_square_mem_unit_ball_of_mem_cassiniOvalInterior hz
  have hη_norm : ‖η‖ < 1 := mem_ball_zero_iff.mp hη_ball
  have hη_re_le : |η.re| ≤ ‖η‖ := Complex.abs_re_le_norm η
  have hη_re_gt : -1 < η.re := by
    -- Unit-disc control forces `Re η` to stay strictly above `-1`.
    have hη_re_abs_lt : |η.re| < 1 := lt_of_le_of_lt hη_re_le hη_norm
    exact (abs_lt.mp hη_re_abs_lt).1
  have hz_sq :
      z ^ 2 = (a : ℂ) ^ 2 + ((r : ℂ) ^ 2) * η := by
    -- Solve the normalization identity for `z^2`.
    dsimp [η]
    have hR : ((r : ℂ) ^ 2) ≠ 0 := by
      exact pow_ne_zero 2 (by exact_mod_cast hr_ne)
    field_simp [hR]
    ring
  have hden_re :
      ((((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ)).re) =
        a ^ 2 * r ^ 2 * η.re + r ^ 4 := by
    -- After substitution, the denominator is `r^2 (r^2 + a^2 η)`.
    rw [hz_sq]
    calc
      ((((a : ℂ) ^ 2) * ((a : ℂ) ^ 2 + ((r : ℂ) ^ 2) * η) +
          ((r ^ 4 - a ^ 4 : ℝ) : ℂ)).re) =
          a ^ 4 + a ^ 2 * r ^ 2 * η.re + (((r ^ 4 - a ^ 4 : ℝ) : ℂ)).re := by
        simp [Complex.mul_re, Complex.mul_im, pow_two, mul_add, mul_comm, mul_left_comm,
          mul_assoc]
        ring
      _ = a ^ 4 + a ^ 2 * r ^ 2 * η.re + (r ^ 4 - a ^ 4) := by
        have hcast : ((((r ^ 4 - a ^ 4 : ℝ) : ℂ)).re) = r ^ 4 - a ^ 4 := by
          rfl
        rw [hcast]
      _ = a ^ 2 * r ^ 2 * η.re + r ^ 4 := by ring
  have hden_pos : 0 < a ^ 2 * r ^ 2 * η.re + r ^ 4 := by
    -- Since `η.re > -1`, this is bounded below by `r^2 (r^2 - a^2) > 0`.
    have hgap2_pos : 0 < r ^ 2 - a ^ 2 := by
      nlinarith
    have hbase_pos : 0 < r ^ 2 * (r ^ 2 - a ^ 2) := by
      positivity
    have hscale_pos : 0 < a ^ 2 * r ^ 2 := by
      positivity
    have hη_scaled : -(a ^ 2 * r ^ 2) < a ^ 2 * r ^ 2 * η.re := by
      have hmul := mul_lt_mul_of_pos_left hη_re_gt hscale_pos
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    have hlower : r ^ 2 * (r ^ 2 - a ^ 2) < a ^ 2 * r ^ 2 * η.re + r ^ 4 := by
      nlinarith
    linarith
  nlinarith [hden_re, hden_pos]

/-- Helper for Exercise 7: the even forward scaling factor stays on the principal slit plane on
the full Cassini interior. -/
lemma cassiniGlobalForwardFactor_mem_slitPlane
    {a r : ℝ} (ha : 0 < a) (har : a < r) {z : ℂ}
    (hz : z ∈ cassiniOvalInterior a r) :
    ((((r : ℂ) ^ 2) /
      (((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ))) : ℂ) ∈ Complex.slitPlane := by
  -- A denominator with positive real part lies in the slit plane, and inversion plus positive
  -- real scaling preserve that branch-cut complement.
  have hden_re_pos :
      0 < ((((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ)).re) :=
    cassiniGlobalForwardDenominator_re_pos (a := a) (r := r) ha har hz
  have hden_slit :
      (((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ)) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl hden_re_pos
  have hden_inv_slit :
      ((((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ))⁻¹ : ℂ) ∈ Complex.slitPlane :=
    inv_mem_slitPlane_of_mem_slitPlane hden_slit
  have hr_sq_pos : 0 < r ^ 2 := by
    have hr_pos : 0 < r := lt_trans ha har
    positivity
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    mul_ofReal_mem_slitPlane_of_pos (x := r ^ 2) hr_sq_pos hden_inv_slit

/-- Helper for Exercise 7: the inverse denominator has strictly positive real part on the full
unit disc. -/
lemma cassiniGlobalInverseDenominator_re_pos
    {a r : ℝ} (ha : 0 < a) (har : a < r) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) 1) :
    0 < ((((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2).re) := by
  have hw_sq_ball : w ^ 2 ∈ ball (0 : ℂ) 1 := square_mem_ball_of_mem_ball hw
  have hw_sq_norm : ‖w ^ 2‖ < 1 := mem_ball_zero_iff.mp hw_sq_ball
  have hw_sq_re_le : |(w ^ 2).re| ≤ ‖w ^ 2‖ := Complex.abs_re_le_norm (w ^ 2)
  have hw_sq_re_lt : (w ^ 2).re < 1 := by
    -- The real part of `w^2` is still bounded above by `1`.
    have hw_sq_re_abs_lt : |(w ^ 2).re| < 1 := lt_of_le_of_lt hw_sq_re_le hw_sq_norm
    exact (abs_lt.mp hw_sq_re_abs_lt).2
  have hden_re :
      ((((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2).re) = r ^ 2 - a ^ 2 * (w ^ 2).re := by
    -- Only `Re (w^2)` contributes because the coefficient `a^2` is real.
    simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
    ring_nf
  rw [hden_re]
  -- The unit-disc bound yields the uniform lower bound `r^2 - a^2 > 0`.
  nlinarith

/-- Helper for Exercise 7: the even inverse scaling factor stays on the principal slit plane on
the full unit disc. -/
lemma cassiniGlobalInverseFactor_mem_slitPlane
    {a r : ℝ} (ha : 0 < a) (har : a < r) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) 1) :
    ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) /
      (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)) : ℂ) ∈ Complex.slitPlane := by
  -- The inverse denominator enjoys the same positive-real-part control as the forward one.
  have hden_re_pos :
      0 < ((((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2).re) :=
    cassiniGlobalInverseDenominator_re_pos (a := a) (r := r) ha har hw
  have hden_slit :
      (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl hden_re_pos
  have hden_inv_slit :
      ((((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)⁻¹ : ℂ) ∈ Complex.slitPlane :=
    inv_mem_slitPlane_of_mem_slitPlane hden_slit
  have hscale_pos : 0 < r ^ 4 - a ^ 4 := by
    have hgap2_pos : 0 < r ^ 2 - a ^ 2 := by
      nlinarith
    have hsum_pos : 0 < r ^ 2 + a ^ 2 := by
      positivity
    nlinarith
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    mul_ofReal_mem_slitPlane_of_pos (x := r ^ 4 - a ^ 4) hscale_pos hden_inv_slit

/-- Helper for Exercise 7: the global forward branch is holomorphic on the full Cassini interior. -/
lemma cassiniGlobalForward_analyticOnNhd
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    AnalyticOnNhd ℂ (cassiniGlobalForward a r) (cassiniOvalInterior a r) := by
  have hfactor_diff :
      DifferentiableOn ℂ
        (fun z : ℂ ↦
          (((r : ℂ) ^ 2) /
            (((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ))))
        (cassiniOvalInterior a r) := by
    intro z hz
    -- The only analytic issue is the denominator, which never vanishes on the Cassini interior.
    have hden_re_pos :
        0 < ((((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ)).re) :=
      cassiniGlobalForwardDenominator_re_pos (a := a) (r := r) ha har hz
    have hden_ne :
        (((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ)) ≠ 0 := by
      intro hden
      have hzero :
          ((((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ)).re) = 0 := by
        rw [hden]
        simp
      linarith
    fun_prop
  have hfactor_analytic :
      AnalyticOnNhd ℂ
        (fun z : ℂ ↦
          (((r : ℂ) ^ 2) /
            (((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ))))
        (cassiniOvalInterior a r) :=
    (Complex.analyticOnNhd_iff_differentiableOn (isOpen_cassiniOvalInterior a r)).2 hfactor_diff
  have hfactor_maps :
      Set.MapsTo
        (fun z : ℂ ↦
          (((r : ℂ) ^ 2) /
            (((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ))))
        (cassiniOvalInterior a r) Complex.slitPlane := by
    intro z hz
    exact cassiniGlobalForwardFactor_mem_slitPlane (a := a) (r := r) ha har hz
  have hsqrt_analytic :
      AnalyticOnNhd ℂ
        (fun z ↦
          Complex.sqrt
            ((((r : ℂ) ^ 2) /
              (((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ)))))
        (cassiniOvalInterior a r) :=
    analyticOnNhd_sqrt_of_mapsTo_slitPlane hfactor_analytic hfactor_maps
  -- The global branch is the identity map multiplied by that analytic principal square root.
  change AnalyticOnNhd ℂ
      (fun z ↦
        z *
          Complex.sqrt
            ((((r : ℂ) ^ 2) /
              (((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ)))))
      (cassiniOvalInterior a r)
  simpa using analyticOnNhd_id.mul hsqrt_analytic

/-- Helper for Exercise 7: the global inverse branch is holomorphic on the full unit disc. -/
lemma cassiniGlobalInverse_analyticOnNhd
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    AnalyticOnNhd ℂ (cassiniGlobalInverse a r) (ball (0 : ℂ) 1) := by
  have hfactor_diff :
      DifferentiableOn ℂ
        (fun w : ℂ ↦
          ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) /
            (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2))))
        (ball (0 : ℂ) 1) := by
    intro w hw
    -- The inverse denominator is also nonvanishing on the disc.
    have hden_re_pos :
        0 < ((((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2).re) :=
      cassiniGlobalInverseDenominator_re_pos (a := a) (r := r) ha har hw
    have hden_ne :
        (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2) ≠ 0 := by
      intro hden
      have hzero :
          ((((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2).re) = 0 := by
        rw [hden]
        simp
      linarith
    fun_prop
  have hfactor_analytic :
      AnalyticOnNhd ℂ
        (fun w : ℂ ↦
          ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) /
            (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2))))
        (ball (0 : ℂ) 1) :=
    (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2 hfactor_diff
  have hfactor_maps :
      Set.MapsTo
        (fun w : ℂ ↦
          ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) /
            (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2))))
        (ball (0 : ℂ) 1) Complex.slitPlane := by
    intro w hw
    exact cassiniGlobalInverseFactor_mem_slitPlane (a := a) (r := r) ha har hw
  have hsqrt_analytic :
      AnalyticOnNhd ℂ
        (fun w ↦
          Complex.sqrt
            ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) /
              (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2))))
        (ball (0 : ℂ) 1) :=
    analyticOnNhd_sqrt_of_mapsTo_slitPlane hfactor_analytic hfactor_maps
  -- The inverse branch is the same odd-times-even pattern on the disc side.
  change AnalyticOnNhd ℂ
      (fun w ↦
        w *
          Complex.sqrt
            ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) /
              (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2))))
      (ball (0 : ℂ) 1)
  simpa using analyticOnNhd_id.mul hsqrt_analytic

/-- Helper for Exercise 7: composing the inverse even factor with the forward branch turns it into
the reciprocal of the forward even factor. -/
lemma cassiniGlobalInverseFactor_comp_forward
    {a r : ℝ} (ha : 0 < a) (har : a < r) {z : ℂ}
    (hz : z ∈ cassiniOvalInterior a r) :
    ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) /
      (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * (cassiniGlobalForward a r z) ^ 2)) : ℂ) =
      ((((r : ℂ) ^ 2) /
        (((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ))) : ℂ)⁻¹ := by
  have hr_pos : 0 < r := lt_trans ha har
  have hr_sq_ne : ((r : ℂ) ^ 2) ≠ 0 := by
    exact pow_ne_zero 2 (by exact_mod_cast ne_of_gt hr_pos)
  have hgap4_pos : 0 < r ^ 4 - a ^ 4 := by
    have hgap2_pos : 0 < r ^ 2 - a ^ 2 := by
      nlinarith
    have hsum_pos : 0 < r ^ 2 + a ^ 2 := by
      positivity
    nlinarith
  have hgap4_ne : (((r ^ 4 - a ^ 4 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt hgap4_pos
  have hden_re_pos :
      0 < ((((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ)).re) :=
    cassiniGlobalForwardDenominator_re_pos (a := a) (r := r) ha har hz
  have hden_ne :
      (((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ)) ≠ 0 := by
    intro hden
    have hzero :
        ((((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ)).re) = 0 := by
      rw [hden]
      simp
    linarith
  -- Substitute the square identity for the forward branch and clear the nonvanishing factors.
  rw [cassiniGlobalForward_sq]
  unfold cassiniOvalMobius
  field_simp [hr_sq_ne, hgap4_ne, hden_ne]
  ring_nf
  simpa using mul_inv_cancel₀ hgap4_ne

/-- Helper for Exercise 7: composing the forward even factor with the inverse branch turns it into
the reciprocal of the inverse even factor. -/
lemma cassiniGlobalForwardFactor_comp_inverse
    {a r : ℝ} (ha : 0 < a) (har : a < r) {w : ℂ}
    (hw : w ∈ ball (0 : ℂ) 1) :
    ((((r : ℂ) ^ 2) /
      (((a : ℂ) ^ 2) * (cassiniGlobalInverse a r w) ^ 2 +
        ((r ^ 4 - a ^ 4 : ℝ) : ℂ))) : ℂ) =
      ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) /
        (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)) : ℂ)⁻¹ := by
  have hr_pos : 0 < r := lt_trans ha har
  have hr_sq_ne : ((r : ℂ) ^ 2) ≠ 0 := by
    exact pow_ne_zero 2 (by exact_mod_cast ne_of_gt hr_pos)
  have hgap4_pos : 0 < r ^ 4 - a ^ 4 := by
    have hgap2_pos : 0 < r ^ 2 - a ^ 2 := by
      nlinarith
    have hsum_pos : 0 < r ^ 2 + a ^ 2 := by
      positivity
    nlinarith
  have hgap4_ne : (((r ^ 4 - a ^ 4 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt hgap4_pos
  have hden_re_pos :
      0 < ((((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2).re) :=
    cassiniGlobalInverseDenominator_re_pos (a := a) (r := r) ha har hw
  have hden_ne :
      (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2) ≠ 0 := by
    intro hden
    have hzero :
        ((((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2).re) = 0 := by
      rw [hden]
      simp
    linarith
  -- The inverse square formula yields the same reciprocal identity after one algebraic cleanup.
  rw [cassiniGlobalInverse_sq]
  field_simp [hr_sq_ne, hgap4_ne, hden_ne]
  ring

/-- Cartan section26 0017_Exercise_7: the whole Cassini oval is sent biholomorphically to the unit
disc by the odd square-root factorization of the right-half branch and its inverse, with the real
and imaginary symmetry axes preserved. -/
theorem cassini_rotated_reflection_package
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    ∃ F G : ℂ → ℂ,
      AnalyticOnNhd ℂ F (cassiniOvalInterior a r) ∧
        Set.MapsTo F (cassiniOvalInterior a r) (ball (0 : ℂ) 1) ∧
        AnalyticOnNhd ℂ G (ball (0 : ℂ) 1) ∧
        Set.MapsTo G (ball (0 : ℂ) 1) (cassiniOvalInterior a r) ∧
        Set.EqOn (G ∘ F) id (cassiniOvalInterior a r) ∧
        Set.EqOn (F ∘ G) id (ball (0 : ℂ) 1) ∧
        Set.MapsTo F (cassiniOvalInteriorRealSlice a r) openUnitDiscRealSlice ∧
        Set.MapsTo F (cassiniOvalImaginaryAxisSegment a r) unitDiscImaginaryAxisSegment := by
  -- Route correction: the old reflection body depended on false closed-slice continuity inputs,
  -- so the package is rebuilt directly from the global odd branches.
  let F : ℂ → ℂ := cassiniGlobalForward a r
  let G : ℂ → ℂ := cassiniGlobalInverse a r
  have hF_analytic : AnalyticOnNhd ℂ F (cassiniOvalInterior a r) := by
    simpa [F] using cassiniGlobalForward_analyticOnNhd (a := a) (r := r) ha har
  have hG_analytic : AnalyticOnNhd ℂ G (ball (0 : ℂ) 1) := by
    simpa [G] using cassiniGlobalInverse_analyticOnNhd (a := a) (r := r) ha har
  have hF_maps : Set.MapsTo F (cassiniOvalInterior a r) (ball (0 : ℂ) 1) := by
    intro z hz
    have hbranch_ball :
        cassiniOvalToUnitDisc a r z ∈ ball (0 : ℂ) 1 :=
      cassiniOvalToUnitDisc_mem_ball_of_mem_cassiniOvalInterior ha har hz
    have hmobius_ball :
        cassiniOvalMobius a r (z ^ 2) ∈ ball (0 : ℂ) 1 := by
      -- Squaring the right-half branch recovers the auxiliary Möbius term inside the unit disc.
      simpa [cassiniOvalToUnitDisc_sq hz] using square_mem_ball_of_mem_ball hbranch_ball
    rw [mem_ball_zero_iff] at hmobius_ball ⊢
    have hnorm_sq : ‖F z‖ ^ 2 = ‖cassiniOvalMobius a r (z ^ 2)‖ := by
      simpa [F, norm_pow] using congrArg norm (cassiniGlobalForward_sq (a := a) (r := r) z)
    nlinarith [norm_nonneg (F z), hmobius_ball, hnorm_sq]
  have hG_maps : Set.MapsTo G (ball (0 : ℂ) 1) (cassiniOvalInterior a r) := by
    intro w hw
    have hbranch_mem :
        unitDiscToCassiniOval a r w ∈ cassiniOvalInterior a r :=
      unitDiscToCassiniOval_mem_cassiniOvalInterior_of_mem_ball ha har hw
    rw [mem_cassiniOvalInterior] at hbranch_mem ⊢
    have hsq_eq₁ :
        G w ^ 2 =
          ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) /
            (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)) := by
      simpa [G] using cassiniGlobalInverse_sq (a := a) (r := r) w
    have hsq_eq₂ :
        unitDiscToCassiniOval a r w ^ 2 =
          ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) * w ^ 2) /
            (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)) := by
      simpa using unitDiscToCassiniOval_sq (a := a) (r := r) (w := w) hw
    have hsq_eq : G w ^ 2 = unitDiscToCassiniOval a r w ^ 2 := hsq_eq₁.trans hsq_eq₂.symm
    simpa [hsq_eq] using hbranch_mem
  have hGF : Set.EqOn (G ∘ F) id (cassiniOvalInterior a r) := by
    intro z hz
    let A : ℂ := (((r : ℂ) ^ 2) /
      (((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ)))
    have hfactor_slit :
        A ∈ Complex.slitPlane := by
      simpa [A] using cassiniGlobalForwardFactor_mem_slitPlane (a := a) (r := r) ha har hz
    have hsqrt_ne : Complex.sqrt A ≠ 0 := by
      -- A slit-plane factor is nonzero, so its principal square root is nonzero.
      have hfactor_ne : A ≠ 0 := Complex.slitPlane_ne_zero hfactor_slit
      intro hsqrt_zero
      apply hfactor_ne
      calc
        A = (Complex.sqrt A) ^ 2 := by
          symm
          exact sq_sqrt_of_mem_slitPlane_or_zero (Or.inr hfactor_slit)
        _ = 0 := by simp [hsqrt_zero]
    -- The reciprocal identity for the even factor makes the two principal square roots cancel.
    have hcomp :
        ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) /
          (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) *
            (z * Complex.sqrt A) ^ 2)) : ℂ) = A⁻¹ := by
      simpa [A, F, cassiniGlobalForward] using
        cassiniGlobalInverseFactor_comp_forward (a := a) (r := r) ha har hz
    dsimp [Function.comp, F, G, cassiniGlobalForward, cassiniGlobalInverse]
    rw [hcomp]
    rw [sqrt_inv_of_mem_slitPlane hfactor_slit]
    have hcancel : z * Complex.sqrt A * (Complex.sqrt A)⁻¹ = z := by
      calc
        z * Complex.sqrt A * (Complex.sqrt A)⁻¹ = z * (Complex.sqrt A * (Complex.sqrt A)⁻¹) := by
          ring
        _ = z * 1 := by rw [mul_inv_cancel₀ hsqrt_ne]
        _ = z := by simp
    simpa [A, mul_assoc] using hcancel
  have hFG : Set.EqOn (F ∘ G) id (ball (0 : ℂ) 1) := by
    intro w hw
    let B : ℂ := ((((r ^ 4 - a ^ 4 : ℝ) : ℂ) /
      (((r : ℂ) ^ 2) - ((a : ℂ) ^ 2) * w ^ 2)))
    have hfactor_slit :
        B ∈ Complex.slitPlane := by
      simpa [B] using cassiniGlobalInverseFactor_mem_slitPlane (a := a) (r := r) ha har hw
    have hsqrt_ne : Complex.sqrt B ≠ 0 := by
      -- The inverse slit-plane factor is also nonzero.
      have hfactor_ne : B ≠ 0 := Complex.slitPlane_ne_zero hfactor_slit
      intro hsqrt_zero
      apply hfactor_ne
      calc
        B = (Complex.sqrt B) ^ 2 := by
          symm
          exact sq_sqrt_of_mem_slitPlane_or_zero (Or.inr hfactor_slit)
        _ = 0 := by simp [hsqrt_zero]
    -- The symmetric reciprocal identity yields the other composition formula.
    have hcomp :
        ((((r : ℂ) ^ 2) /
          (((a : ℂ) ^ 2) * (w * Complex.sqrt B) ^ 2 +
            ((r ^ 4 - a ^ 4 : ℝ) : ℂ))) : ℂ) = B⁻¹ := by
      simpa [B, G, cassiniGlobalInverse] using
        cassiniGlobalForwardFactor_comp_inverse (a := a) (r := r) ha har hw
    dsimp [Function.comp, F, G, cassiniGlobalForward, cassiniGlobalInverse]
    rw [hcomp]
    rw [sqrt_inv_of_mem_slitPlane hfactor_slit]
    have hcancel : w * Complex.sqrt B * (Complex.sqrt B)⁻¹ = w := by
      calc
        w * Complex.sqrt B * (Complex.sqrt B)⁻¹ = w * (Complex.sqrt B * (Complex.sqrt B)⁻¹) := by
          ring
        _ = w * 1 := by rw [mul_inv_cancel₀ hsqrt_ne]
        _ = w := by simp
    simpa [B, mul_assoc] using hcancel
  have hreal : Set.MapsTo F (cassiniOvalInteriorRealSlice a r) openUnitDiscRealSlice := by
    intro z hz
    rcases mem_cassiniOvalInteriorRealSlice.mp hz with ⟨hzCassini, hz_im⟩
    refine ⟨hF_maps hzCassini, ?_⟩
    let D : ℂ := ((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ)
    have hD_re_pos : 0 < D.re := by
      simpa [D] using cassiniGlobalForwardDenominator_re_pos (a := a) (r := r) ha har hzCassini
    have hz_real : z = (z.re : ℂ) := by
      apply Complex.ext <;> simp [hz_im]
    have hD_im : D.im = 0 := by
      -- On the real axis the denominator is a positive real number.
      dsimp [D]
      rw [hz_real]
      simp [Complex.mul_im, Complex.mul_re, pow_two]
    have hD_eq : D = (D.re : ℂ) := by
      apply Complex.ext <;> simp [hD_im]
    have hfactor_eq :
        ((((r : ℂ) ^ 2) / D) : ℂ) = (((r ^ 2 / D.re : ℝ)) : ℂ) := by
      rw [hD_eq]
      have hDre_ne : D.re ≠ 0 := ne_of_gt hD_re_pos
      simp
    have hfactor_nonneg : 0 ≤ r ^ 2 / D.re := by
      exact div_nonneg (sq_nonneg r) hD_re_pos.le
    have hsqrt_eq :
        Complex.sqrt ((((r : ℂ) ^ 2) / D)) =
          ((Real.sqrt (r ^ 2 / D.re) : ℝ) : ℂ) := by
      have hfactor_nonnegC : 0 ≤ (((r ^ 2 / D.re : ℝ)) : ℂ) := by
        exact_mod_cast hfactor_nonneg
      rw [hfactor_eq]
      rw [Complex.sqrt_of_nonneg hfactor_nonnegC]
      have harg : (((r : ℂ) ^ 2).re / D.re) = r ^ 2 / D.re := by
        simp [pow_two]
      simp [harg]
    -- The square-root factor is a nonnegative real scalar, so it preserves the real axis.
    rw [show F z = z * Complex.sqrt ((((r : ℂ) ^ 2) / D)) by
      simp [F, D, cassiniGlobalForward]]
    rw [hz_real, hsqrt_eq]
    simp
  have himag : Set.MapsTo F (cassiniOvalImaginaryAxisSegment a r) unitDiscImaginaryAxisSegment := by
    intro z hz
    refine ⟨?_, ?_⟩
    · let y : ℝ := z.im
      let D : ℂ := ((a : ℂ) ^ 2) * z ^ 2 + ((r ^ 4 - a ^ 4 : ℝ) : ℂ)
      have hz_imag : z = Complex.I * y := by
        -- A point on the symmetry segment is exactly `I * Im z`.
        rcases mem_cassiniOvalImaginaryAxisSegment.mp hz with ⟨hz_re, _⟩
        apply Complex.ext <;> simp [y, hz_re]
      have hD_re_eq : D.re = r ^ 4 - a ^ 4 - a ^ 2 * y ^ 2 := by
        -- Along the imaginary axis the denominator becomes a real scalar.
        dsimp [D]
        rw [hz_imag]
        simp [Complex.mul_re, Complex.mul_im, y, pow_two]
        ring
      have hD_re_pos : 0 < D.re := by
        rcases mem_cassiniOvalImaginaryAxisSegment.mp hz with ⟨_, hz_bound⟩
        rw [hD_re_eq]
        have hgap2_pos : 0 < r ^ 2 - a ^ 2 := by
          nlinarith
        have hbase_pos : 0 < r ^ 2 * (r ^ 2 - a ^ 2) := by
          nlinarith [sq_pos_of_pos (lt_trans ha har), hgap2_pos]
        have hlower : r ^ 2 * (r ^ 2 - a ^ 2) ≤ r ^ 4 - a ^ 4 - a ^ 2 * z.im ^ 2 := by
          nlinarith
        nlinarith
      have hD_im : D.im = 0 := by
        dsimp [D]
        rw [hz_imag]
        simp [Complex.mul_im, Complex.mul_re, pow_two]
      have hD_eq : D = (D.re : ℂ) := by
        apply Complex.ext <;> simp [hD_im]
      have hfactor_eq :
          ((((r : ℂ) ^ 2) / D) : ℂ) = (((r ^ 2 / D.re : ℝ)) : ℂ) := by
        rw [hD_eq]
        have hDre_ne : D.re ≠ 0 := ne_of_gt hD_re_pos
        simp
      have hfactor_nonneg : 0 ≤ r ^ 2 / D.re := by
        exact div_nonneg (sq_nonneg r) hD_re_pos.le
      have hsqrt_eq :
          Complex.sqrt ((((r : ℂ) ^ 2) / D)) =
            ((Real.sqrt (r ^ 2 / D.re) : ℝ) : ℂ) := by
        have hfactor_nonnegC : 0 ≤ (((r ^ 2 / D.re : ℝ)) : ℂ) := by
          exact_mod_cast hfactor_nonneg
        rw [hfactor_eq]
        rw [Complex.sqrt_of_nonneg hfactor_nonnegC]
        have harg : (((r : ℂ) ^ 2).re / D.re) = r ^ 2 / D.re := by
          simp [pow_two]
        simp [harg]
      -- The same positive real scalar preserves the imaginary axis.
      rw [show F z = z * Complex.sqrt ((((r : ℂ) ^ 2) / D)) by
        simp [F, D, cassiniGlobalForward]]
      rw [hz_imag, hsqrt_eq]
      simp [Complex.mul_re]
    · rcases
        cassiniOvalMobius_mem_nonpos_real_unitSegment_of_mem_imaginaryAxisSegment
          (a := a) (r := r) ha har hz with
          ⟨t, ht_nonneg, ht_le_one, hsq_neg⟩
      have hF_sq : F z ^ 2 = -((t : ℂ)) := by
        calc
          F z ^ 2 = cassiniOvalMobius a r (z ^ 2) := by
            simpa [F] using cassiniGlobalForward_sq (a := a) (r := r) z
          _ = -((t : ℂ)) := hsq_neg
      have hnorm_sq : ‖F z‖ ^ 2 = t := by
        calc
          ‖F z‖ ^ 2 = ‖F z ^ 2‖ := by rw [norm_pow]
          _ = ‖-((t : ℂ))‖ := by rw [hF_sq]
          _ = t := by simp [Complex.norm_real, ht_nonneg]
      -- The squared image lies on the interval `[-1,0]`, so the norm stays at most `1`.
      nlinarith [norm_nonneg (F z), ht_le_one, hnorm_sq]
  exact ⟨F, G, hF_analytic, hF_maps, hG_analytic, hG_maps, hGF, hFG, hreal, himag⟩

/-- Helper for Cartan section26 0017_Exercise_7: package the explicit forward and inverse branches
into the chapter's `HolomorphicIsomorph` owner. -/
theorem exists_cassiniOvalInterior_iso_unitDisc_preserving_axes
    {a r : ℝ} (ha : 0 < a) (har : a < r) :
    ∃ e : HolomorphicIsomorph (cassiniOvalInterior a r) (ball (0 : ℂ) 1),
      Set.MapsTo (e : ℂ → ℂ) (cassiniOvalInteriorRealSlice a r) openUnitDiscRealSlice ∧
        Set.MapsTo (e : ℂ → ℂ)
          (cassiniOvalImaginaryAxisSegment a r) unitDiscImaginaryAxisSegment := by
  -- Package the reflected forward and inverse branches into the chapter owner.
  rcases cassini_rotated_reflection_package ha har with
    ⟨F, G, hF_analytic, hF_maps, hG_analytic, hG_maps, hGF, hFG, hreal, himag⟩
  refine ⟨⟨
    { toFun := F
      invFun := G
      source := cassiniOvalInterior a r
      target := ball (0 : ℂ) 1
      map_source' := hF_maps
      map_target' := hG_maps
      left_inv' := hGF
      right_inv' := hFG
      open_source := isOpen_cassiniOvalInterior a r
      open_target := Metric.isOpen_ball
      continuousOn_toFun := hF_analytic.continuousOn
      continuousOn_invFun := hG_analytic.continuousOn },
    { source_eq := rfl
      target_eq := rfl
      analyticOn_toFun := hF_analytic
      analyticOn_symm := hG_analytic }⟩, hreal, himag⟩

end
