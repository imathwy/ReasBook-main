import Mathlib
import cartan.I.section02.«frozen_0004_Definition_I_2_extra_3»
import cartan.I.section02.«frozen_0007_Example_I_2_extra_5»
import cartan.I.section02.«frozen_0008_Proposition_4_1»
import cartan.I.section04.«0020_Exercise_5»

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries
open PowerSeries Filter
open scoped BigOperators
open scoped ENNReal NNReal PowerSeries

universe u

variable {R : Type*}
variable {K : Type*}

/-- The coefficients `s_n = a_0 + ⋯ + a_n` attached to a scalar power series. -/
def summatory_coefficients [AddCommMonoid R] (a : ℕ → R) : ℕ → R :=
  fun n ↦ Finset.sum (Finset.range (n + 1)) fun k ↦ a k

/-- The first summatory coefficient is the constant coefficient. -/
-- Proof sketch: unfold `summatory_coefficients` and evaluate the finite sum over `range 1`.
theorem summatory_coefficients_zero [AddCommMonoid R] (a : ℕ → R) :
    summatory_coefficients a 0 = a 0 := by
  -- Reduce to the single term in `range 1`.
  simp [summatory_coefficients]

/-- Over a characteristic-zero division ring, the coefficients
`t_n = (n + 1)⁻¹ (s_0 + ⋯ + s_n)` obtained from Cesàro averaging the summatory coefficients. -/
def cesaro_mean_coefficients [DivisionRing K] [CharZero K] (a : ℕ → K) : ℕ → K :=
  fun n ↦ ((n + 1 : K)⁻¹) *
    Finset.sum (Finset.range (n + 1)) fun k ↦ summatory_coefficients a k

/-- The first Cesàro mean coefficient agrees with the constant coefficient. -/
-- Proof sketch: unfold `cesaro_mean_coefficients`, use `summatory_coefficients_zero`, and simplify
-- the factor `(1 : K)⁻¹`.
theorem cesaro_mean_coefficients_zero [DivisionRing K] [CharZero K] (a : ℕ → K) :
    cesaro_mean_coefficients a 0 = a 0 := by
  -- Unfold the Cesàro average at `n = 0` and simplify the unique summand.
  simp [cesaro_mean_coefficients, summatory_coefficients_zero]

section NormedField

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {a : ℕ → 𝕜}

/-- Helper for Exercise I.4-extra-7: the summatory coefficients are the Cauchy-product
coefficients of the original series with the geometric series. -/
theorem summatory_coefficients_eq_geometric_cauchy_product (a : ℕ → 𝕜) :
    (fun n ↦ PowerSeries.coeff n (PowerSeries.mk a * PowerSeries.mk (fun _ ↦ (1 : 𝕜)))) =
      summatory_coefficients a := by
  funext n
  -- Compare the product coefficient with the textbook partial sum.
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun k l ↦ PowerSeries.coeff k (PowerSeries.mk a) *
        PowerSeries.coeff l (PowerSeries.mk (fun _ ↦ (1 : 𝕜))))]
  simp [summatory_coefficients]

/-- Helper for Exercise I.4-extra-7: the inverse-succ ratio appearing in the ratio test is the
norm of `1 + 1 / (n + 1)`. -/
theorem inverse_succ_norm_ratio_eq_norm_one_add_inv_succ [CharZero 𝕜] (n : ℕ) :
    ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ / ‖(((n + 2 : ℕ) : 𝕜)⁻¹ : 𝕜)‖ =
      ‖(1 : 𝕜) + ((n.succ : 𝕜)⁻¹)‖ := by
  calc
    ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ / ‖(((n + 2 : ℕ) : 𝕜)⁻¹ : 𝕜)‖ =
        ‖(((n.succ : 𝕜)⁻¹ : 𝕜))‖ * ‖(((n + 2 : ℕ) : 𝕜))‖ := by
          rw [norm_inv, norm_inv, div_eq_mul_inv, inv_inv]
    _ = ‖((((n.succ : 𝕜))⁻¹ : 𝕜) * (((n + 2 : ℕ) : 𝕜)) )‖ := by
      rw [norm_mul]
    _ = ‖(1 : 𝕜) + ((n.succ : 𝕜)⁻¹)‖ := by
      have hcast : (((n + 2 : ℕ) : 𝕜)) = (n.succ : 𝕜) + 1 := by
        calc
          (((n + 2 : ℕ) : 𝕜)) = (n : 𝕜) + 2 := by
            simp [Nat.cast_add]
          _ = (n.succ : 𝕜) + 1 := by
            norm_num [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_assoc]
      rw [hcast]
      congr 1
      field_simp [Nat.cast_add, Nat.cast_one]

/-- Helper for Exercise I.4-extra-7: the field norm on `𝕜` restricted to the rational scalars. -/
def rational_norm_absolute_value [CharZero 𝕜] : AbsoluteValue ℚ ℝ :=
  AbsoluteValue.comp (NormedField.toAbsoluteValue 𝕜) (f := Rat.castHom 𝕜)
    (Rat.cast_injective (α := 𝕜))

/-- Helper for Exercise I.4-extra-7: the root sequence appearing in Hadamard's formula for the
coefficients `((n + 1 : 𝕜)⁻¹)`. -/
def inverse_succ_root_sequence [CharZero 𝕜] : ℕ → ℝ≥0∞ :=
  fun n ↦ ENNReal.ofReal (‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ (1 / (n : ℝ)))

/-- Helper for Exercise I.4-extra-7: the `p`-adic absolute value of a positive integer is bounded
below by its reciprocal. -/
theorem padic_nat_recip_le (p n : ℕ) [Fact p.Prime] :
    ((n.succ : ℝ)⁻¹) ≤ Rat.AbsoluteValue.padic p n.succ := by
  -- Compare the inverse of `n + 1` with the inverse of the largest `p`-power dividing it.
  have hpow_le : ((p : ℚ) ^ padicValNat p n.succ) ≤ n.succ := by
    exact_mod_cast
      (le_trans
        (Nat.pow_le_pow_left Fact.out.one_le (padicValNat_le_nat_log (p := p) n.succ))
        (Nat.pow_log_le_self p n.succ_ne_zero))
  have hpow_inv :
      ((n.succ : ℚ)⁻¹) ≤ (((p : ℚ) ^ padicValNat p n.succ)⁻¹) := by
    -- Inverting reverses the inequality because both sides are positive.
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 hpow_le
  have hpadic :
      (((p : ℚ) ^ padicValNat p n.succ)⁻¹ : ℚ) = padicNorm p n.succ := by
    -- Rewrite the `p`-adic norm through its valuation formula on the nonzero natural number.
    rw [padicNorm.eq_zpow_of_nonzero (p := p)]
    · rw [padicValRat.of_nat]
      simp [zpow_neg, Rat.cast_natCast]
    · exact_mod_cast n.succ_ne_zero
  -- Cast the rational comparison to the real-valued absolute value used in Ostrowski's theorem.
  have hpow_inv_real :
      ((n.succ : ℚ)⁻¹ : ℝ) ≤ (padicNorm p n.succ : ℝ) := by
    exact_mod_cast hpow_inv.trans_eq hpadic
  simpa [Rat.AbsoluteValue.padic_eq_padicNorm] using hpow_inv_real

/-- Helper for Exercise I.4-extra-7: if the restricted rational norm is trivial, the reciprocal
root sequence is constantly `1`. -/
theorem inverse_succ_root_tendsto_one_of_trivial [CharZero 𝕜]
    (hvQ : ¬ (rational_norm_absolute_value (𝕜 := 𝕜)).IsNontrivial) :
    Tendsto (inverse_succ_root_sequence (𝕜 := 𝕜)) atTop (𝓝 1) := by
  -- Every nonzero rational then has absolute value `1`, so each root term is exactly `1`.
  have hseq : inverse_succ_root_sequence (𝕜 := 𝕜) = fun _ ↦ (1 : ℝ≥0∞) := by
    funext n
    have hnorm : ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ = 1 := by
      simpa [rational_norm_absolute_value] using
        (AbsoluteValue.not_isNontrivial_apply hvQ
          (x := ((n.succ : ℚ)⁻¹)) (by norm_num : ((n.succ : ℚ)⁻¹) ≠ 0))
    simp [inverse_succ_root_sequence, hnorm]
  simpa [hseq] using tendsto_const_nhds

/-- Helper for Exercise I.4-extra-7: in the real-equivalent case, the reciprocal root sequence
tends to `1`. -/
theorem inverse_succ_root_tendsto_one_of_real_equiv [CharZero 𝕜]
    (hreal : (rational_norm_absolute_value (𝕜 := 𝕜)).IsEquiv Rat.AbsoluteValue.real) :
    Tendsto (inverse_succ_root_sequence (𝕜 := 𝕜)) atTop (𝓝 1) := by
  -- Express the restricted norm on naturals as a fixed real power of the standard absolute value.
  obtain ⟨c, hc, hnat⟩ :=
    (Rat.AbsoluteValue.exists_nat_rpow_iff_isEquiv
      (f := Rat.AbsoluteValue.real) (g := rational_norm_absolute_value (𝕜 := 𝕜))).2 hreal.symm
  have hcoeff : ∀ n : ℕ, ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ = (n.succ : ℝ) ^ (-c) := by
    intro n
    have hnat' :
        rational_norm_absolute_value (𝕜 := 𝕜) n.succ = (n.succ : ℝ) ^ c := by
      simpa [Rat.AbsoluteValue.real_eq_abs] using (hnat n.succ).symm
    -- Rewrite the reciprocal coefficient norm through the restricted rational absolute value.
    calc
      ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ =
          rational_norm_absolute_value (𝕜 := 𝕜) ((n.succ : ℚ)⁻¹) := by
            simp [rational_norm_absolute_value]
      _ = (rational_norm_absolute_value (𝕜 := 𝕜) n.succ)⁻¹ := by
        rw [map_inv₀]
      _ = ((n.succ : ℝ) ^ c)⁻¹ := by rw [hnat']
      _ = (n.succ : ℝ) ^ (-c) := by
        rw [Real.rpow_neg (by positivity)]
  have hroot :
      ∀ n : ℕ,
        ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ (1 / (n : ℝ)) = (n.succ : ℝ) ^ (-c / (n : ℝ)) := by
    intro n
    -- Move the `1 / n` exponent into the single real-power exponent.
    rw [hcoeff n, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  have hreal_tendsto :
      Tendsto (fun n : ℕ ↦ (n.succ : ℝ) ^ (-c / (n : ℝ))) atTop (𝓝 1) := by
    -- The explicit model sequence is an `x ^ (a / (x - 1))` asymptotic with `x = n + 1`.
    refine
      (tendsto_rpow_div_mul_add (-c) 1 (-1) zero_ne_one).comp
        (tendsto_add_atTop_nat 1).cast_real
  -- Transfer the real convergence through `ENNReal.ofReal`.
  have henn :
      Tendsto
        (fun n : ℕ ↦ ENNReal.ofReal ((n.succ : ℝ) ^ (-c / (n : ℝ))))
        atTop (𝓝 1) := by
    simpa using (ENNReal.continuous_ofReal.tendsto 1).comp hreal_tendsto
  simpa [inverse_succ_root_sequence, hroot] using henn

/-- Helper for Exercise I.4-extra-7: in the `p`-adic-equivalent case, the reciprocal root sequence
tends to `1`. -/
theorem inverse_succ_root_tendsto_one_of_padic_equiv [CharZero 𝕜]
    (p : ℕ) [Fact p.Prime]
    (hpadic : (rational_norm_absolute_value (𝕜 := 𝕜)).IsEquiv (Rat.AbsoluteValue.padic p)) :
    Tendsto (inverse_succ_root_sequence (𝕜 := 𝕜)) atTop (𝓝 1) := by
  -- Express the restricted norm on naturals as a fixed positive power of the model `p`-adic norm.
  obtain ⟨c, hc, hnat⟩ :=
    (Rat.AbsoluteValue.exists_nat_rpow_iff_isEquiv
      (f := Rat.AbsoluteValue.padic p) (g := rational_norm_absolute_value (𝕜 := 𝕜))).2
      hpadic.symm
  have hcoeff_le_one :
      ∀ n : ℕ, rational_norm_absolute_value (𝕜 := 𝕜) n.succ ≤ 1 := by
    intro n
    have hpad_le : Rat.AbsoluteValue.padic p n.succ ≤ 1 := by
      simpa using Rat.AbsoluteValue.padic_le_one p (n.succ : ℤ)
    -- Raise the `p`-adic upper bound to the positive equivalence exponent.
    calc
      rational_norm_absolute_value (𝕜 := 𝕜) n.succ =
          Rat.AbsoluteValue.padic p n.succ ^ c := by
            simpa using (hnat n.succ).symm
      _ ≤ 1 ^ c := by
        gcongr
      _ = 1 := one_rpow c
  have hcoeff_ge :
      ∀ n : ℕ, (n.succ : ℝ) ^ (-c) ≤ rational_norm_absolute_value (𝕜 := 𝕜) n.succ := by
    intro n
    have hpad_ge : ((n.succ : ℝ)⁻¹) ≤ Rat.AbsoluteValue.padic p n.succ :=
      padic_nat_recip_le p n
    -- The positive equivalence exponent preserves the lower bound.
    calc
      (n.succ : ℝ) ^ (-c) = (((n.succ : ℝ)⁻¹) ^ c) := by
        rw [inv_rpow]
        · congr 1
          ring
        · positivity
      _ ≤ Rat.AbsoluteValue.padic p n.succ ^ c := by
        gcongr
      _ = rational_norm_absolute_value (𝕜 := 𝕜) n.succ := by
        simpa using hnat n.succ
  have hreal_upper :
      Tendsto (fun n : ℕ ↦ (n.succ : ℝ) ^ (c / (n : ℝ))) atTop (𝓝 1) := by
    -- The explicit polynomial upper envelope has trivial Hadamard limsup.
    refine
      (tendsto_rpow_div_mul_add c 1 (-1) zero_ne_one).comp
        (tendsto_add_atTop_nat 1).cast_real
  have hreal_lower :
      Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hreal_sandwich :
      Tendsto (fun n : ℕ ↦ ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ (1 / (n : ℝ))) atTop (𝓝 1) := by
    -- Squeeze the reciprocal-root sequence between `1` and the explicit upper model.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hreal_lower hreal_upper ?_ ?_
    · filter_upwards with n
      have hvQ_pos :
          0 < rational_norm_absolute_value (𝕜 := 𝕜) n.succ := by
        exact map_pos_of_ne_zero _ (Nat.cast_ne_zero.mpr n.succ_ne_zero)
      have hnorm_ge_one :
          1 ≤ ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ := by
        have hnorm_eq :
            ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ =
              (rational_norm_absolute_value (𝕜 := 𝕜) n.succ)⁻¹ := by
          calc
            ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ =
                rational_norm_absolute_value (𝕜 := 𝕜) ((n.succ : ℚ)⁻¹) := by
                  simp [rational_norm_absolute_value]
            _ = (rational_norm_absolute_value (𝕜 := 𝕜) n.succ)⁻¹ := by
              rw [map_inv₀]
        rw [hnorm_eq]
        exact (one_le_inv₀ hvQ_pos).2 (hcoeff_le_one n)
      calc
        (1 : ℝ) = 1 ^ (1 / (n : ℝ)) := by simp
        _ ≤ ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ (1 / (n : ℝ)) := by
          exact Real.rpow_le_rpow (by positivity) hnorm_ge_one (by positivity)
    · filter_upwards with n
      have hvQ_pos :
          0 < rational_norm_absolute_value (𝕜 := 𝕜) n.succ := by
        exact map_pos_of_ne_zero _ (Nat.cast_ne_zero.mpr n.succ_ne_zero)
      have hnorm_eq :
          ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ =
            (rational_norm_absolute_value (𝕜 := 𝕜) n.succ)⁻¹ := by
        calc
          ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ =
              rational_norm_absolute_value (𝕜 := 𝕜) ((n.succ : ℚ)⁻¹) := by
                simp [rational_norm_absolute_value]
          _ = (rational_norm_absolute_value (𝕜 := 𝕜) n.succ)⁻¹ := by
            rw [map_inv₀]
      have hnorm_le : ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ≤ (n.succ : ℝ) ^ c := by
        have :
            (rational_norm_absolute_value (𝕜 := 𝕜) n.succ)⁻¹ ≤
              (((n.succ : ℝ) ^ (-c))⁻¹) := by
          exact (inv_le_inv₀ hvQ_pos (by positivity)).2 (hcoeff_ge n)
        simpa [hnorm_eq, Real.rpow_neg (by positivity)] using this
      calc
        ‖(((n.succ : 𝕜))⁻¹ : 𝕜)‖ ^ (1 / (n : ℝ))
            ≤ ((n.succ : ℝ) ^ c) ^ (1 / (n : ℝ)) := by
              exact Real.rpow_le_rpow (norm_nonneg _) hnorm_le (by positivity)
        _ = (n.succ : ℝ) ^ (c / (n : ℝ)) := by
          rw [← Real.rpow_mul (by positivity)]
          congr 1
          ring
  -- Transfer the real squeeze limit through `ENNReal.ofReal`.
  have henn :
      Tendsto (inverse_succ_root_sequence (𝕜 := 𝕜)) atTop (𝓝 1) := by
    simpa [inverse_succ_root_sequence] using
      (ENNReal.continuous_ofReal.tendsto 1).comp hreal_sandwich
  exact henn

/-- Helper for Exercise I.4-extra-7: the reciprocal-succ scalar series has radius `1`. -/
theorem inverse_succ_coefficients_radius_eq_one [CharZero 𝕜] :
    (ofScalars 𝕜 (fun n ↦ ((n.succ : 𝕜)⁻¹))).radius = 1 := by
  -- Route correction: the naive proof route `((n + 1 : 𝕜)⁻¹) → 0` is not available in general
  -- nonarchimedean normed fields, so the correct closure should use the Cauchy-Hadamard limsup
  -- formula for the roots `‖(n + 1 : 𝕜)⁻¹‖^(1 / n)`.
  set vQ : AbsoluteValue ℚ ℝ := rational_norm_absolute_value (𝕜 := 𝕜)
  have hlim :
      Tendsto (inverse_succ_root_sequence (𝕜 := 𝕜)) atTop (𝓝 1) := by
    by_cases hvQ : vQ.IsNontrivial
    · obtain hreal | ⟨p, hp⟩ := Rat.AbsoluteValue.equiv_real_or_padic vQ hvQ
      · -- The real-equivalent branch is the classical polynomial-growth case.
        simpa [vQ] using inverse_succ_root_tendsto_one_of_real_equiv (𝕜 := 𝕜) hreal
      · rcases hp with ⟨hpPrime, hpadic⟩
        letI : Fact p.Prime := hpPrime
        -- The `p`-adic branch is controlled by the subexponential bound `‖n⁻¹‖ ≤ n^c`.
        simpa [vQ] using inverse_succ_root_tendsto_one_of_padic_equiv (𝕜 := 𝕜) p hpadic
    · -- The remaining case is the trivial restriction of the norm to `ℚ`.
      simpa [vQ] using inverse_succ_root_tendsto_one_of_trivial (𝕜 := 𝕜) hvQ
  have hroot_limsup :
      limsup (inverse_succ_root_sequence (𝕜 := 𝕜)) atTop = 1 :=
    hlim.limsup_eq
  have hradius_inv :
      (ofScalars 𝕜 (fun n ↦ ((n.succ : 𝕜)⁻¹))).radius⁻¹ = 1 := by
    -- Rewrite Hadamard's limsup formula through the explicit reciprocal root sequence.
    simpa [inverse_succ_root_sequence] using
      (ofScalars_radius_inv_eq_limsup (𝕜 := 𝕜) (fun n ↦ ((n.succ : 𝕜)⁻¹))).trans hroot_limsup
  -- Inverting the radius once more finishes the Hadamard argument.
  calc
    (ofScalars 𝕜 (fun n ↦ ((n.succ : 𝕜)⁻¹))).radius =
        ((ofScalars 𝕜 (fun n ↦ ((n.succ : 𝕜)⁻¹))).radius⁻¹)⁻¹ := by
          rw [ENNReal.inv_inv]
    _ = 1 := by simpa [hradius_inv]

/-- Helper for Exercise I.4-extra-7: the Cesàro coefficients split as reciprocal-succ weights
times the double summatory sequence. -/
theorem cesaro_mean_coefficients_eq_inverse_succ_mul_double_summatory [CharZero 𝕜]
    (a : ℕ → 𝕜) (n : ℕ) :
    cesaro_mean_coefficients a n =
      ((n.succ : 𝕜)⁻¹) * summatory_coefficients (summatory_coefficients a) n := by
  -- Unfold both definitions and identify the inner finite sum.
  simp [cesaro_mean_coefficients, summatory_coefficients]

/-- If the original scalar power series has radius of convergence at least `1`, then the power
series with coefficients `s_n = a_0 + ⋯ + a_n` also has radius of convergence at least `1`. -/
-- Proof sketch: identify the new series with the original one multiplied by the geometric series
-- `(1 - z)⁻¹` on the open unit disk, then compare radii of convergence.
theorem summatory_power_series_radius_ge_one
    (hS : 1 ≤ (ofScalars 𝕜 a).radius) :
    1 ≤ (ofScalars 𝕜 (summatory_coefficients a)).radius := by
  let S : 𝕜⟦X⟧ := PowerSeries.mk a
  let G : 𝕜⟦X⟧ := PowerSeries.mk (fun _ ↦ (1 : 𝕜))
  have hgeom : (1 : ℝ≥0∞) ≤ G.radius := by
    -- The geometric series already has radius exactly `1`.
    simpa [G, PowerSeries.radius] using
      (geometric_series_radius_eq_one (𝕜 := 𝕜)).ge
  have hprod :
      (1 : ℝ≥0∞) ≤ (S * G).radius :=
    scalar_series_cauchy_product_radius_ge S G 1 (by simpa [S, PowerSeries.radius] using hS) hgeom
  have hprod' : (1 : ℝ≥0∞) ≤ (PowerSeries.mk (summatory_coefficients a)).radius := by
    -- Rewrite the product coefficients as the summatory sequence.
    simpa [PowerSeries.radius, S, G, summatory_coefficients_eq_geometric_cauchy_product] using hprod
  -- Replace the product series by its coefficientwise summatory description.
  simpa [PowerSeries.radius] using hprod'

/-- If the original scalar power series has radius of convergence at least `1`, then the power
series with coefficients `t_n = (n + 1)⁻¹ (s_0 + ⋯ + s_n)` also has radius of convergence at
least `1`. -/
-- Proof sketch: use the first part together with the standard Cesàro-averaging effect on
-- coefficients, which preserves the unit radius in this characteristic-zero setting.
theorem cesaro_power_series_radius_ge_one
    [CharZero 𝕜]
    (hS : 1 ≤ (ofScalars 𝕜 a).radius) :
    1 ≤ (ofScalars 𝕜 (cesaro_mean_coefficients a)).radius := by
  let b : ℕ → 𝕜 := fun n ↦ ((n.succ : 𝕜)⁻¹)
  let s : ℕ → 𝕜 := summatory_coefficients (summatory_coefficients a)
  have hb : 1 ≤ (ofScalars 𝕜 b).radius := by
    simpa [b] using (inverse_succ_coefficients_radius_eq_one (𝕜 := 𝕜)).ge
  have hs₁ : 1 ≤ (ofScalars 𝕜 (summatory_coefficients a)).radius :=
    summatory_power_series_radius_ge_one (𝕜 := 𝕜) hS
  have hs₂ : 1 ≤ (ofScalars 𝕜 s).radius := by
    simpa [s] using summatory_power_series_radius_ge_one (𝕜 := 𝕜) hs₁
  have hhad :
      (ofScalars 𝕜 b).radius * (ofScalars 𝕜 s).radius ≤
        (ofScalars 𝕜 (b * s)).radius :=
    ofScalars_radius_hadamardMul_ge (𝕜 := 𝕜) b s
  have hone : (1 : ℝ≥0∞) ≤ (ofScalars 𝕜 b).radius * (ofScalars 𝕜 s).radius := by
    calc
      (1 : ℝ≥0∞) = 1 * 1 := by simp
      _ ≤ (ofScalars 𝕜 b).radius * (ofScalars 𝕜 s).radius := by
        gcongr
  have hcesaro : (1 : ℝ≥0∞) ≤ (ofScalars 𝕜 (b * s)).radius := le_trans hone hhad
  have hcoeff : cesaro_mean_coefficients a = b * s := by
    funext n
    -- Rewrite the Cesàro coefficient in its pointwise-product form.
    simpa [b, s, Pi.mul_apply] using
      cesaro_mean_coefficients_eq_inverse_succ_mul_double_summatory (a := a) n
  simpa [hcoeff] using hcesaro

section Complete

variable [CompleteSpace 𝕜]

/-- Helper for Exercise I.4-extra-7: the geometric scalar series sums to `(1 - z)⁻¹` on the open
unit ball. -/
theorem geometric_ofScalarsSum_eq_inv_one_sub {z : 𝕜} (hz : ‖z‖ < 1) :
    ofScalarsSum (fun _ ↦ (1 : 𝕜)) z = (1 - z)⁻¹ := by
  -- Identify `ofScalarsSum` with the geometric `tsum`.
  rw [ofScalars_sum_eq]
  simpa using tsum_geometric_of_norm_lt_one hz

/--
Exercise I.4-extra-7: if the original scalar power series has radius of convergence at least `1`,
then for `‖z‖ < 1` multiplying the sum of `∑ a_n z^n` by `(1 - z)⁻¹` gives the sum of the power
series with coefficients `s_n = a_0 + ⋯ + a_n`. -/
-- Proof sketch: identify the geometric factor with the canonical geometric power series, apply the
-- chapter-level Cauchy-product evaluation theorem to the product with `ofScalars 𝕜 a`, identify
-- the resulting coefficients with `s_n`, and use `‖z‖ < 1` to evaluate the geometric series as
-- `(1 - z)⁻¹`.
theorem summatory_power_series_sum_eq_geometric_mul
    (hS : 1 ≤ (ofScalars 𝕜 a).radius) {z : 𝕜} (hz : ‖z‖ < 1) :
    (1 - z)⁻¹ * ofScalarsSum a z = ofScalarsSum (summatory_coefficients a) z := by
  let S : 𝕜⟦X⟧ := PowerSeries.mk a
  let G : 𝕜⟦X⟧ := PowerSeries.mk (fun _ ↦ (1 : 𝕜))
  have hgeom : (1 : ℝ≥0∞) ≤ G.radius := by
    -- The geometric factor converges on the whole open unit ball.
    simpa [G, PowerSeries.radius] using
      (geometric_series_radius_eq_one (𝕜 := 𝕜)).ge
  have hz' : ‖z‖₊ < (1 : ℝ≥0) := by
    simpa using hz
  have hmul :
      PowerSeries.sum (S * G) z = PowerSeries.sum S z * PowerSeries.sum G z :=
    scalar_series_cauchy_product_eval_eq_mul S G 1
      (by simpa [S, PowerSeries.radius] using hS) hgeom hz'
  have hsum :
      ofScalarsSum (summatory_coefficients a) z =
        ofScalarsSum a z * ofScalarsSum (fun _ ↦ (1 : 𝕜)) z := by
    -- Convert the chapter-level product evaluation to the specific coefficient sequence.
    simpa [PowerSeries.sum, S, G, summatory_coefficients_eq_geometric_cauchy_product] using hmul
  calc
    (1 - z)⁻¹ * ofScalarsSum a z = ofScalarsSum (fun _ ↦ (1 : 𝕜)) z * ofScalarsSum a z := by
      rw [geometric_ofScalarsSum_eq_inv_one_sub hz]
    _ = ofScalarsSum a z * ofScalarsSum (fun _ ↦ (1 : 𝕜)) z := by
      rw [mul_comm]
    _ = ofScalarsSum (summatory_coefficients a) z := by
      rw [hsum]

end Complete

end NormedField
