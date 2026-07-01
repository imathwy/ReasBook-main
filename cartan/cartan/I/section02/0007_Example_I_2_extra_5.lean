import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.RCLike.Basic
import cartan.I.section02.«0004_Definition_I_2_extra_3»

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open FormalMultilinearSeries
open PowerSeries
open scoped PowerSeries

universe u

variable {𝕜 : Type u}

/-- Example I.2-extra-5 (1): the scalar power series `∑ n! z^n` has radius of convergence `0`. -/
theorem radius_factorial_eq_zero [RCLike 𝕜] :
    (mk fun n ↦ (n.factorial : 𝕜)).radius = 0 := by
  simpa [PowerSeries.radius, PowerSeries.coeff_mk] using
    (by
      apply ofScalars_radius_eq_zero_of_tendsto 𝕜
      refine Tendsto.congr' ?_ ((tendsto_add_atTop_iff_nat 1).2 tendsto_natCast_atTop_atTop)
      refine Eventually.of_forall fun n ↦ ?_
      change (n.succ : ℝ) = ‖((n.succ.factorial : ℕ) : 𝕜)‖ / ‖((n.factorial : ℕ) : 𝕜)‖
      calc
        (n.succ : ℝ) = ‖((n.succ : ℕ) : 𝕜)‖ := by
          simpa using (RCLike.norm_natCast n.succ).symm
        _ = ‖((n.succ.factorial : ℕ) : 𝕜)‖ / ‖((n.factorial : ℕ) : 𝕜)‖ := by
          symm
          rw [Nat.factorial_succ, Nat.cast_mul, norm_mul, RCLike.norm_natCast]
          have hfac : ‖((n.factorial : ℕ) : 𝕜)‖ ≠ 0 := by
            have hfac' : (n.factorial : ℝ) ≠ 0 := by
              exact_mod_cast Nat.factorial_ne_zero n
            simpa [RCLike.norm_natCast] using hfac'
          rw [mul_div_assoc, div_self hfac, mul_one] :
            (ofScalars 𝕜 fun n ↦ (n.factorial : 𝕜)).radius = 0)

/-- Example I.2-extra-5 (2): the scalar power series `∑ z^n / n!` has infinite radius of
convergence. -/
theorem radius_inv_factorial_eq_top [NontriviallyNormedField 𝕜] [CharZero 𝕜]
    [ContinuousSMul ℚ 𝕜] :
    (mk fun n ↦ ((n.factorial : 𝕜)⁻¹)).radius = ⊤ := by
  simpa [PowerSeries.radius, PowerSeries.coeff_mk, NormedSpace.expSeries_eq_ofScalars] using
    NormedSpace.expSeries_radius_eq_top 𝕜 𝕜

/-- Example I.2-extra-5 (3): the geometric scalar power series `∑ z^n` has radius of convergence
`1`. -/
theorem radius_one_eq_one [NontriviallyNormedField 𝕜] :
    (mk fun _ ↦ (1 : 𝕜)).radius = 1 := by
  simpa [PowerSeries.radius, PowerSeries.coeff_mk] using
    (ofScalars_radius_eq_of_tendsto 𝕜 (fun _ ↦ (1 : 𝕜)) one_ne_zero (by simp))

/-- Example I.2-extra-5 (4): the scalar power series `∑ (1 / n) z^n`, interpreted with coefficient
`0` at `n = 0`, has radius of convergence `1`. -/
theorem radius_harmonic_eq_one [RCLike 𝕜] :
    (mk fun n ↦ if n = 0 then 0 else (n : 𝕜)⁻¹).radius = 1 := by
  simpa [PowerSeries.radius, PowerSeries.coeff_mk] using
    (by
      apply ofScalars_radius_eq_of_tendsto 𝕜 (fun n ↦ if n = 0 then 0 else (n : 𝕜)⁻¹) one_ne_zero
      have hlim : Tendsto (fun n : ℕ ↦ (1 : ℝ) + (n : ℝ)⁻¹) atTop (nhds 1) := by
        simpa using
          (tendsto_const_nhds.add tendsto_inv_atTop_nhds_zero_nat :
            Tendsto (fun n : ℕ ↦ (1 : ℝ) + (n : ℝ)⁻¹) atTop (nhds ((1 : ℝ) + 0)))
      refine Tendsto.congr' ?_ hlim
      refine Filter.eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩
      have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
      have hnR : (n : ℝ) ≠ 0 := by
        exact_mod_cast hn0
      symm
      change ‖if n = 0 then 0 else (n : 𝕜)⁻¹‖ / ‖if n.succ = 0 then 0 else (n.succ : 𝕜)⁻¹‖ =
        1 + (n : ℝ)⁻¹
      rw [if_neg hn0, if_neg (Nat.succ_ne_zero n), norm_inv, norm_inv, RCLike.norm_natCast,
        RCLike.norm_natCast]
      field_simp [hnR]
      simp [Nat.cast_add] :
      (ofScalars 𝕜 (fun n ↦ if n = 0 then 0 else (n : 𝕜)⁻¹)).radius = 1)

/-- Example I.2-extra-5 (5): the scalar power series `∑ (1 / n²) z^n`, interpreted with
coefficient `0` at `n = 0`, has radius of convergence `1`. -/
theorem radius_harmonicSquare_eq_one [RCLike 𝕜] :
    (mk fun n ↦ if n = 0 then 0 else ((n : 𝕜) ^ 2)⁻¹).radius = 1 := by
  simpa [PowerSeries.radius, PowerSeries.coeff_mk] using
    (by
      apply ofScalars_radius_eq_of_tendsto 𝕜
        (fun n ↦ if n = 0 then 0 else ((n : 𝕜) ^ 2)⁻¹) one_ne_zero
      have hlim : Tendsto (fun n : ℕ ↦ ((1 : ℝ) + (n : ℝ)⁻¹) ^ 2) atTop (nhds 1) := by
        simpa using
          ((tendsto_const_nhds.add tendsto_inv_atTop_nhds_zero_nat :
              Tendsto (fun n : ℕ ↦ (1 : ℝ) + (n : ℝ)⁻¹) atTop (nhds ((1 : ℝ) + 0))).pow 2)
      refine Tendsto.congr' ?_ hlim
      refine Filter.eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩
      have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
      have hnR : (n : ℝ) ≠ 0 := by
        exact_mod_cast hn0
      symm
      change ‖if n = 0 then 0 else ((n : 𝕜) ^ 2)⁻¹‖ /
          ‖if n.succ = 0 then 0 else ((n.succ : 𝕜) ^ 2)⁻¹‖ =
        ((1 : ℝ) + (n : ℝ)⁻¹) ^ 2
      rw [if_neg hn0, if_neg (Nat.succ_ne_zero n), norm_inv, norm_inv, norm_pow, norm_pow,
        RCLike.norm_natCast, RCLike.norm_natCast]
      field_simp [hnR]
      simp [Nat.cast_add] :
      (ofScalars 𝕜 (fun n ↦ if n = 0 then 0 else ((n : 𝕜) ^ 2)⁻¹)).radius = 1)
