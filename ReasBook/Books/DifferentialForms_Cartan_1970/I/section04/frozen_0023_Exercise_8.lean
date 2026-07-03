import Mathlib
import DifferentialForms_Cartan_1970.I.section02.«frozen_0004_Definition_I_2_extra_3»
import DifferentialForms_Cartan_1970.I.section02.«frozen_0008_Proposition_4_1»

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries
open scoped ENNReal NNReal PowerSeries

/- Source-facing layer: the recurrence and its coefficient sequence are owned by
`LinearRecurrence`. The analytic generating series is the downstream scalar-series bridge from
`exercise8Coeffs` to `FormalMultilinearSeries.ofScalars`. -/

section Algebraic

variable {R : Type*} [CommSemiring R]

/-- The order-two linear recurrence governing the coefficients in Exercise 8. -/
def exercise8Rec (α β : R) : LinearRecurrence R where
  order := 2
  coeffs := ![β, α]

/-- The recursively defined coefficients in Exercise 8, realized through the canonical solution of
the governing linear recurrence with initial values `0, 1`. -/
def exercise8Coeffs (α β : R) : ℕ → R :=
  (exercise8Rec α β).mkSol ![0, 1]

/-- The coefficient sequence in Exercise 8 is a solution of the canonical order-two linear
recurrence with coefficients `β, α`. -/
theorem exercise8Coeffs_isSolution (α β : R) :
    (exercise8Rec α β).IsSolution (exercise8Coeffs α β) := by
  simpa [exercise8Coeffs] using (exercise8Rec α β).is_sol_mkSol ![0, 1]

/-- The coefficients in Exercise 8 satisfy the stated second-order linear recurrence. -/
theorem exercise8Coeffs_succ_succ (α β : R) (n : ℕ) :
    exercise8Coeffs α β (n + 2) =
      α * exercise8Coeffs α β (n + 1) + β * exercise8Coeffs α β n := by
  have h := exercise8Coeffs_isSolution α β n
  change exercise8Coeffs α β (n + 2) =
      ∑ i : Fin 2, ![β, α] i * exercise8Coeffs α β (n + ↑i) at h
  simpa [Fin.sum_univ_two, add_comm] using h

/-- Helper for Exercise 8: the canonical recurrence solution starts with the initial values
`a₀ = 0` and `a₁ = 1`. -/
theorem exercise8_coeffs_zero_one (α β : R) :
    exercise8Coeffs α β 0 = 0 ∧ exercise8Coeffs α β 1 = 1 := by
  constructor
  · -- The zeroth coefficient is the first prescribed initial datum of `mkSol`.
    simpa [exercise8Coeffs, exercise8Rec] using
      (exercise8Rec α β).mkSol_eq_init ![0, 1] ⟨0, by simp [exercise8Rec]⟩
  · -- The first coefficient is the second prescribed initial datum of `mkSol`.
    simpa [exercise8Coeffs, exercise8Rec] using
      (exercise8Rec α β).mkSol_eq_init ![0, 1] ⟨1, by simp [exercise8Rec]⟩

end Algebraic

section CoefficientBound

variable {𝕜 : Type*} [SeminormedCommRing 𝕜] [NormOneClass 𝕜]

/-- Helper for Exercise 8: after shifting by one index, the recursive coefficients are dominated by
the geometric majorant `(2c)^n`, where `c = max (|α|, |β|, 1 / 2)`. -/
theorem exercise8_coeff_norm_succ_le_geometric (α β : 𝕜) (n : ℕ) :
    ‖exercise8Coeffs α β (n + 1)‖ ≤
      (2 * max (max ‖α‖ ‖β‖) (1 / 2 : ℝ)) ^ n := by
  let c : ℝ := max (max ‖α‖ ‖β‖) (1 / 2 : ℝ)
  have hzero : exercise8Coeffs α β 0 = 0 := (exercise8_coeffs_zero_one α β).1
  have hone : exercise8Coeffs α β 1 = 1 := (exercise8_coeffs_zero_one α β).2
  have hα : ‖α‖ ≤ c := by
    dsimp [c]
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hβ : ‖β‖ ≤ c := by
    dsimp [c]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hone_le_two_c : (1 : ℝ) ≤ 2 * c := by
    have hhalf : (1 / 2 : ℝ) ≤ c := by
      dsimp [c]
      exact le_max_right _ _
    nlinarith
  have hpair :
      ∀ m : ℕ,
        ‖exercise8Coeffs α β (m + 1)‖ ≤ (2 * c) ^ m ∧
        ‖exercise8Coeffs α β (m + 2)‖ ≤ (2 * c) ^ (m + 1) := by
    intro m
    induction m with
    | zero =>
        constructor
        · -- The first shifted coefficient is `1`, which matches the geometric majorant at `0`.
          simp [hone, c]
        · -- The recurrence at `n = 0` reduces the second shifted coefficient to `α`.
          rw [exercise8Coeffs_succ_succ α β 0, hone, hzero, mul_one, mul_zero, add_zero]
          calc
            ‖α‖ ≤ c := hα
            _ ≤ 2 * c := by nlinarith
            _ = (2 * c) ^ (0 + 1) := by ring
    | succ m ihm =>
        rcases ihm with ⟨hm, hm_succ⟩
        constructor
        · -- The first half of the next pair is exactly the second half of the previous one.
          simpa [Nat.succ_eq_add_one, add_assoc, c] using hm_succ
        · -- Apply the recurrence and estimate each term by the induction hypotheses.
          rw [show m + 1 + 2 = m + 3 by omega]
          rw [exercise8Coeffs_succ_succ α β (m + 1)]
          calc
            ‖α * exercise8Coeffs α β (m + 2) + β * exercise8Coeffs α β (m + 1)‖
                ≤ ‖α * exercise8Coeffs α β (m + 2)‖ +
                    ‖β * exercise8Coeffs α β (m + 1)‖ := norm_add_le _ _
            _ ≤ ‖α‖ * ‖exercise8Coeffs α β (m + 2)‖ +
                    ‖β‖ * ‖exercise8Coeffs α β (m + 1)‖ := by
                  gcongr
                  · exact norm_mul_le _ _
                  · exact norm_mul_le _ _
            _ ≤ c * (2 * c) ^ (m + 1) + c * (2 * c) ^ m := by
                  gcongr
            _ ≤ (2 * c) ^ m * (2 * c) ^ 2 := by
                  have hmajor : c * (2 * c) + c ≤ (2 * c) ^ 2 := by
                    nlinarith [hc_nonneg, hone_le_two_c]
                  have hpow_nonneg : 0 ≤ (2 * c) ^ m := by positivity
                  have hfactor :
                      c * (2 * c) ^ (m + 1) + c * (2 * c) ^ m =
                        (2 * c) ^ m * (c * (2 * c) + c) := by
                    rw [pow_succ', ← mul_assoc]
                    ring
                  rw [hfactor]
                  gcongr
            _ = (2 * c) ^ (m + 2) := by rw [← pow_add]
  -- The requested estimate is the first component of the paired induction.
  simpa [c] using (hpair n).1

-- Proof sketch: prove the estimate by induction on `n` using the recurrence and the choice
-- `c = max (|α|, |β|, 1 / 2)`.
/-- The coefficients of the recurrence in Exercise 8 satisfy the geometric bound from part (a). -/
theorem exercise8_coeff_norm_le (α β : 𝕜) (n : ℕ) :
    ‖exercise8Coeffs α β n‖ ≤
      (2 * max (max ‖α‖ ‖β‖) (1 / 2 : ℝ)) ^ (n - 1) := by
  rcases n with _ | n
  · -- The constant term vanishes, so the textbook bound is immediate.
    simp [(exercise8_coeffs_zero_one α β).1]
  · -- For positive indices, rewrite the statement into the stable shifted estimate.
    simpa [Nat.succ_sub_one] using exercise8_coeff_norm_succ_le_geometric α β n

end CoefficientBound

section Analytic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

open Polynomial

-- Proof sketch: use the coefficient bound from `exercise8_coeff_norm_le` together with
-- `FormalMultilinearSeries.le_radius_of_bound`.
/-- The series attached to Exercise 8 has strictly positive radius of convergence. -/
theorem exercise8_radius_pos (α β : 𝕜) :
    0 < (ofScalars 𝕜 (exercise8Coeffs α β)).radius := by
  let c : ℝ := max (max ‖α‖ ‖β‖) (1 / 2 : ℝ)
  have hc_half : (1 / 2 : ℝ) ≤ c := by
    dsimp [c]
    exact le_max_right _ _
  have h_two_c_pos : 0 < 2 * c := by
    nlinarith
  have hr_nonneg : 0 ≤ (2 * c)⁻¹ := by positivity
  let r : NNReal := ⟨(2 * c)⁻¹, hr_nonneg⟩
  have h_two_c_ne_zero : (2 * c) ≠ 0 := ne_of_gt h_two_c_pos
  have hradius :
      (r : ENNReal) ≤ (ofScalars 𝕜 (exercise8Coeffs α β)).radius := by
    -- The geometric bound makes `‖aₙ‖ rⁿ` uniformly bounded by `r`.
    refine (ofScalars 𝕜 (exercise8Coeffs α β)).le_radius_of_bound ((2 * c)⁻¹) ?_
    intro n
    rcases n with _ | n
    · -- The constant coefficient is zero, so the scaled norm is zero as well.
      simp [r, c, (exercise8_coeffs_zero_one α β).1]
    · -- For positive indices, cancel the matching geometric powers.
      calc
        ‖ofScalars 𝕜 (exercise8Coeffs α β) (n + 1)‖ * (r : ℝ) ^ (n + 1)
            = ‖exercise8Coeffs α β (n + 1)‖ * ((2 * c)⁻¹) ^ (n + 1) := by
                rw [FormalMultilinearSeries.ofScalars_norm
                  (E := 𝕜) (c := exercise8Coeffs α β) (n := n + 1)]
                rfl
        _ ≤ (2 * c) ^ n * ((2 * c)⁻¹) ^ (n + 1) := by
              have hpow_nonneg : 0 ≤ ((2 * c)⁻¹) ^ (n + 1) := by positivity
              nlinarith [exercise8_coeff_norm_succ_le_geometric α β n]
        _ = (2 * c)⁻¹ := by
              have hcancel : (2 * c) ^ n * ((2 * c)⁻¹) ^ n = 1 := by
                rw [← mul_pow, mul_inv_cancel₀ h_two_c_ne_zero, one_pow]
              rw [pow_succ']
              calc
                (2 * c) ^ n * ((2 * c)⁻¹ * ((2 * c)⁻¹) ^ n)
                    = ((2 * c) ^ n * ((2 * c)⁻¹) ^ n) * (2 * c)⁻¹ := by
                        ac_rfl
                _ = (2 * c)⁻¹ := by rw [hcancel, one_mul]
  have hrpos : (0 : ENNReal) < (r : ENNReal) := by
    exact ENNReal.coe_pos.2 (by
      change 0 < (2 * c)⁻¹
      positivity)
  exact lt_of_lt_of_le hrpos hradius

end Analytic

section AnalyticSum

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

open Polynomial

/-- Helper for Exercise 8: the recurrence denominator packaged as a scalar power series. -/
private noncomputable def exercise8DenominatorSeries (α β : 𝕜) : 𝕜⟦X⟧ :=
  (1 : 𝕜⟦X⟧) - PowerSeries.C α * PowerSeries.X - PowerSeries.C β * PowerSeries.X ^ 2

/-- Helper for Exercise 8: the recurrence coefficients packaged as a scalar power series. -/
private noncomputable def exercise8SolutionSeries (α β : 𝕜) : 𝕜⟦X⟧ :=
  PowerSeries.mk (exercise8Coeffs α β)

/-- Helper for Exercise 8: the denominator series has no coefficients above degree `2`. -/
private theorem exercise8_denominatorSeries_coeff_eq_zero_of_three_le
    (α β : 𝕜) {n : ℕ} (hn : 3 ≤ n) :
    PowerSeries.coeff n (exercise8DenominatorSeries α β) = 0 := by
  -- All three summands are supported in degrees `0`, `1`, and `2`.
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  have h2 : n ≠ 2 := by omega
  have hone : PowerSeries.coeff n (1 : 𝕜⟦X⟧) = 0 := by
    simp [PowerSeries.coeff_one, h0]
  have hαX : PowerSeries.coeff n (PowerSeries.C α * PowerSeries.X : 𝕜⟦X⟧) = 0 := by
    rw [PowerSeries.coeff_C_mul]
    simp [PowerSeries.coeff_X, h1]
  have hβX : PowerSeries.coeff n (PowerSeries.C β * PowerSeries.X ^ 2 : 𝕜⟦X⟧) = 0 := by
    rw [PowerSeries.coeff_C_mul]
    simp [PowerSeries.coeff_X_pow, h2]
  simp [exercise8DenominatorSeries, hone, hαX, hβX]

/-- Helper for Exercise 8: the formal variable has no coefficients above degree `1`. -/
private theorem exercise8_X_coeff_eq_zero_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    PowerSeries.coeff n (PowerSeries.X : 𝕜⟦X⟧) = 0 := by
  -- The series `X` is supported exactly in degree `1`.
  have h1 : n ≠ 1 := by omega
  simp [PowerSeries.coeff_X, h1]

/-- Helper for Exercise 8: multiplying the coefficient series by the recurrence polynomial gives the
formal variable `X`. -/
private theorem exercise8_formal_series_mul_identity (α β : 𝕜) :
    exercise8DenominatorSeries α β * exercise8SolutionSeries α β = PowerSeries.X := by
  let S : 𝕜⟦X⟧ := exercise8SolutionSeries α β
  ext n
  rcases n with _ | (_ | n)
  · -- The constant coefficient vanishes because the initial datum is `a₀ = 0`.
    have hzero : exercise8Coeffs α β 0 = 0 := (exercise8_coeffs_zero_one α β).1
    simp [exercise8DenominatorSeries, exercise8SolutionSeries, hzero]
  · -- The linear coefficient is `a₁ = 1`, and the shifted terms still vanish at this degree.
    have hzero : exercise8Coeffs α β 0 = 0 := (exercise8_coeffs_zero_one α β).1
    have hone : exercise8Coeffs α β 1 = 1 := (exercise8_coeffs_zero_one α β).2
    have hα :
        PowerSeries.coeff 1 ((PowerSeries.C α * PowerSeries.X) * S) = α * exercise8Coeffs α β 0 := by
      rw [mul_assoc, PowerSeries.coeff_C_mul]
      simpa [pow_one, S, exercise8SolutionSeries] using
        congrArg (fun x ↦ α * x) (PowerSeries.coeff_X_pow_mul S 1 0)
    have hβ :
        PowerSeries.coeff 1 ((PowerSeries.C β * PowerSeries.X ^ 2) * S) = 0 := by
      rw [mul_assoc, PowerSeries.coeff_C_mul]
      have hcoeff : PowerSeries.coeff 1 (PowerSeries.X ^ 2 * S) = 0 := by
        rw [PowerSeries.coeff_X_pow_mul']
        norm_num
      rw [hcoeff]
      simp
    have hα' :
        PowerSeries.coeff 1
            (PowerSeries.C α * PowerSeries.X * PowerSeries.mk (exercise8Coeffs α β)) =
          α * exercise8Coeffs α β 0 := by
      simpa [S, exercise8SolutionSeries] using hα
    have hβ' :
        PowerSeries.coeff 1
            (PowerSeries.C β * PowerSeries.X ^ 2 * PowerSeries.mk (exercise8Coeffs α β)) = 0 := by
      simpa [S, exercise8SolutionSeries] using hβ
    rw [exercise8DenominatorSeries, sub_mul, sub_mul, one_mul]
    simp [sub_eq_add_neg, S, exercise8SolutionSeries]
    rw [hα', hβ', hzero]
    simp [hone]
  · -- Route correction: for degrees `n + 2`, the coefficient identity is exactly the recurrence.
    have hα :
        PowerSeries.coeff (n + 2) ((PowerSeries.C α * PowerSeries.X) * S) =
          α * exercise8Coeffs α β (n + 1) := by
      rw [mul_assoc, PowerSeries.coeff_C_mul]
      simpa [pow_one, S, exercise8SolutionSeries, Nat.add_comm] using
        congrArg (fun x ↦ α * x) (PowerSeries.coeff_X_pow_mul S 1 (n + 1))
    have hβ :
        PowerSeries.coeff (n + 2) ((PowerSeries.C β * PowerSeries.X ^ 2) * S) =
          β * exercise8Coeffs α β n := by
      rw [mul_assoc, PowerSeries.coeff_C_mul]
      simpa [S, exercise8SolutionSeries, Nat.add_comm] using
        congrArg (fun x ↦ β * x) (PowerSeries.coeff_X_pow_mul S 2 n)
    have hrec := exercise8Coeffs_succ_succ α β n
    have hα' :
        PowerSeries.coeff (n + 2)
            (PowerSeries.C α * PowerSeries.X * PowerSeries.mk (exercise8Coeffs α β)) =
          α * exercise8Coeffs α β (n + 1) := by
      simpa [S, exercise8SolutionSeries] using hα
    have hβ' :
        PowerSeries.coeff (n + 2)
            (PowerSeries.C β * PowerSeries.X ^ 2 * PowerSeries.mk (exercise8Coeffs α β)) =
          β * exercise8Coeffs α β n := by
      simpa [S, exercise8SolutionSeries] using hβ
    rw [exercise8DenominatorSeries, sub_mul, sub_mul, one_mul]
    simp [sub_eq_add_neg, S, exercise8SolutionSeries]
    rw [hα', hβ', hrec]
    ring_nf
    have hneq : 2 + n ≠ 1 := by omega
    simp [PowerSeries.coeff_X, hneq]

/-- Helper for Exercise 8: the denominator power series has infinite radius because it is a
quadratic polynomial. -/
private theorem exercise8_denominatorSeries_radius_eq_top (α β : 𝕜) :
    (exercise8DenominatorSeries α β).radius = ⊤ := by
  -- The denominator coefficients are eventually zero above degree `2`.
  rw [PowerSeries.radius]
  apply (ofScalars 𝕜
    (fun n ↦ PowerSeries.coeff n (exercise8DenominatorSeries α β))).radius_eq_top_of_eventually_eq_zero
  refine Filter.eventually_atTop.2 ?_
  refine ⟨3, fun n hn ↦ ?_⟩
  exact FormalMultilinearSeries.ofScalars_eq_zero_of_scalar_zero (E := 𝕜)
    (c := fun m ↦ PowerSeries.coeff m (exercise8DenominatorSeries α β))
    (hc := exercise8_denominatorSeries_coeff_eq_zero_of_three_le α β hn)

/-- Helper for Exercise 8: the formal variable `X` has infinite radius because it is a polynomial
of degree `1`. -/
private theorem exercise8_X_radius_eq_top :
    (PowerSeries.X : 𝕜⟦X⟧).radius = ⊤ := by
  -- The coefficient sequence of `X` vanishes above degree `1`.
  rw [PowerSeries.radius]
  apply (ofScalars 𝕜 fun n ↦ PowerSeries.coeff n (PowerSeries.X : 𝕜⟦X⟧)).radius_eq_top_of_eventually_eq_zero
  refine Filter.eventually_atTop.2 ?_
  refine ⟨2, fun n hn ↦ ?_⟩
  exact FormalMultilinearSeries.ofScalars_eq_zero_of_scalar_zero (E := 𝕜)
    (c := fun m ↦ PowerSeries.coeff m (PowerSeries.X : 𝕜⟦X⟧))
    (hc := exercise8_X_coeff_eq_zero_of_two_le hn)

/-- Helper for Exercise 8: evaluating the denominator polynomial series recovers
`1 - α z - β z^2`. -/
private theorem exercise8_denominatorSeries_sum (α β z : 𝕜) :
    PowerSeries.sum (exercise8DenominatorSeries α β) z = (1 : 𝕜) - α * z - β * z ^ 2 := by
  -- Finite support reduces the scalar series to the first three coefficients.
  rw [PowerSeries.sum, FormalMultilinearSeries.ofScalars_sum_eq]
  rw [tsum_eq_sum (s := Finset.range 3)]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [exercise8DenominatorSeries, pow_two]
    ring
  · intro n hn
    have hthree : 3 ≤ n := by simpa [Finset.mem_range] using hn
    have hcoeff : PowerSeries.coeff n (exercise8DenominatorSeries α β) = 0 :=
      exercise8_denominatorSeries_coeff_eq_zero_of_three_le α β hthree
    simp [hcoeff]

/-- Helper for Exercise 8: evaluating the formal variable `X` at `z` gives `z`. -/
private theorem exercise8_X_sum (z : 𝕜) :
    PowerSeries.sum (PowerSeries.X : 𝕜⟦X⟧) z = z := by
  -- Finite support reduces the scalar series to the constant and linear terms.
  rw [PowerSeries.sum, FormalMultilinearSeries.ofScalars_sum_eq]
  rw [tsum_eq_sum (s := Finset.range 2)]
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [PowerSeries.coeff_X]
  · intro n hn
    have htwo : 2 ≤ n := by simpa [Finset.mem_range] using hn
    have hcoeff : PowerSeries.coeff n (PowerSeries.X : 𝕜⟦X⟧) = 0 :=
      exercise8_X_coeff_eq_zero_of_two_le htwo
    simp [hcoeff]

-- Proof sketch: compare coefficients after multiplying the series by `1 - α z - β z^2`;
-- the recurrence makes every coefficient vanish except the linear term.
/-- Multiplying the sum of the Exercise 8 series by `1 - α z - β z^2` gives `z` on the disk of
convergence. -/
theorem exercise8_recurrence_polynomial_mul_sum
    {α β z : 𝕜}
    (hz : z ∈ Metric.eball (0 : 𝕜) (ofScalars 𝕜 (exercise8Coeffs α β)).radius) :
    ((1 : 𝕜) - α * z - β * z ^ 2) * ofScalarsSum (exercise8Coeffs α β) z = z := by
  -- Route correction: package the recurrence as a formal identity and then evaluate it through the
  -- chapter Cauchy-product theorem on a finite radius strictly between `‖z‖₊` and the radius.
  let D : 𝕜⟦X⟧ := exercise8DenominatorSeries α β
  let S : 𝕜⟦X⟧ := exercise8SolutionSeries α β
  have hz' : (‖z‖₊ : ℝ≥0∞) < (ofScalars 𝕜 (exercise8Coeffs α β)).radius := by
    exact (mem_scalarSeriesDiscOfConvergence_iff (𝕜 := 𝕜) (a := exercise8Coeffs α β)).1 hz
  obtain ⟨ρ, hzρ, hρS_lt⟩ :
      ∃ ρ : ℝ≥0, ‖z‖₊ < ρ ∧ (ρ : ℝ≥0∞) < S.radius := by
    simpa [S, exercise8SolutionSeries, PowerSeries.radius] using
      ENNReal.lt_iff_exists_nnreal_btwn.1 hz'
  have hρD : (ρ : ℝ≥0∞) ≤ D.radius := by
    have hDtop : D.radius = ⊤ := by
      simpa [D] using exercise8_denominatorSeries_radius_eq_top (α := α) (β := β)
    rw [hDtop]
    exact le_top
  have hρS : (ρ : ℝ≥0∞) ≤ S.radius := hρS_lt.le
  have hmul :
      PowerSeries.sum (D * S) z = PowerSeries.sum D z * PowerSeries.sum S z :=
    scalar_series_cauchy_product_eval_eq_mul D S ρ hρD hρS hzρ
  have hDsum : PowerSeries.sum D z = (1 : 𝕜) - α * z - β * z ^ 2 := by
    simpa [D] using exercise8_denominatorSeries_sum α β z
  have hSsum : PowerSeries.sum S z = ofScalarsSum (exercise8Coeffs α β) z := by
    simpa [S, exercise8SolutionSeries, PowerSeries.sum]
  have hformal : D * S = (PowerSeries.X : 𝕜⟦X⟧) := by
    simpa [D, S] using exercise8_formal_series_mul_identity (α := α) (β := β)
  -- Rewrite both sides using the formal identity and the explicit polynomial evaluations.
  calc
    ((1 : 𝕜) - α * z - β * z ^ 2) * ofScalarsSum (exercise8Coeffs α β) z
        = PowerSeries.sum D z * PowerSeries.sum S z := by
            rw [hDsum, hSsum]
    _ = PowerSeries.sum (D * S) z := by rw [hmul]
    _ = PowerSeries.sum (PowerSeries.X : 𝕜⟦X⟧) z := by rw [hformal]
    _ = z := exercise8_X_sum z

/-- Helper for Exercise 8: the quadratic denominator does not vanish inside the convergence disc of
the coefficient series. -/
private theorem exercise8_denominator_ne_zero_of_mem_radius
    {α β z : 𝕜}
    (hz : z ∈ Metric.eball (0 : 𝕜) (ofScalars 𝕜 (exercise8Coeffs α β)).radius) :
    ((1 : 𝕜) - α * z - β * z ^ 2) ≠ 0 := by
  -- The evaluated formal identity would force `z = 0`, contradicting the denominator value there.
  intro hden
  have hmul := exercise8_recurrence_polynomial_mul_sum (α := α) (β := β) hz
  rw [hden, zero_mul] at hmul
  have hz0 : z = 0 := by simpa using hmul.symm
  have hone_zero : (1 : 𝕜) = 0 := by simpa [hz0] using hden
  exact one_ne_zero hone_zero

-- Proof sketch: combine the previous identity with the fact that the denominator does not vanish
-- on the open disk of convergence.
/-- Exercise 8: on the open disk of convergence, the sum of the recursive power series is
`z / (1 - α z - β z^2)`. -/
theorem exercise8_sum_eq_rational_function
    {α β z : 𝕜}
    (hz : z ∈ Metric.eball (0 : 𝕜) (ofScalars 𝕜 (exercise8Coeffs α β)).radius) :
    ofScalarsSum (exercise8Coeffs α β) z = z / ((1 : 𝕜) - α * z - β * z ^ 2) := by
  -- Divide the evaluated recurrence identity by the nonvanishing quadratic denominator.
  have hden :
      ((1 : 𝕜) - α * z - β * z ^ 2) ≠ 0 :=
    exercise8_denominator_ne_zero_of_mem_radius (α := α) (β := β) hz
  have hmul := exercise8_recurrence_polynomial_mul_sum (α := α) (β := β) hz
  exact (eq_div_iff hden).2 (by simpa [mul_comm] using hmul)

-- Proof sketch: use the rational expression of the sum and compare the singularities coming from
-- the two roots of `β X^2 + α X - 1`.
/-- The radius of convergence in Exercise 8 is the minimum of the norms of the two roots of
`β X^2 + α X - 1`, when `z₁, z₂` are the full quadratic root pair. -/
theorem exercise8_radius_eq_min_root_norm
    {α β z₁ z₂ : 𝕜}
    (hroots : (C β * X ^ 2 + C α * X - 1).roots = {z₁, z₂}) :
    (ofScalars 𝕜 (exercise8Coeffs α β)).radius = ↑(min ‖z₁‖₊ ‖z₂‖₊) := by
  -- TODO: use the formal denominator identity to exclude any root of
  -- `β X^2 + α X - 1` from the open convergence disk, and combine that upper bound with the
  -- partial-fraction decomposition coming from the two roots to produce the matching lower bound.
  sorry

end AnalyticSum

section ClosedForm

variable {K : Type*} [Field K]

-- Proof sketch: factor the denominator with the two distinct roots and read off the coefficients
-- from the partial fraction decomposition.
/-- Distinct roots of `β X^2 + α X - 1` give the closed formula for the coefficients from part
(c). -/
theorem exercise8_coeff_closed_form_of_distinct_roots
    {α β z₁ z₂ : K}
    (hz₁ : β * z₁ ^ 2 + α * z₁ - 1 = 0)
    (hz₂ : β * z₂ ^ 2 + α * z₂ - 1 = 0)
    (hneq : z₁ ≠ z₂) (n : ℕ) :
    exercise8Coeffs α β n = (z₁ * z₂ / (z₂ - z₁)) * (z₁⁻¹ ^ n - z₂⁻¹ ^ n) := by
  -- TODO: translate `hz₁` and `hz₂` into characteristic-polynomial roots of `exercise8Rec α β`,
  -- show the right-hand side is a solution of the same recurrence with the same initial values,
  -- and conclude by uniqueness of `LinearRecurrence.mkSol`.
  sorry

end ClosedForm
