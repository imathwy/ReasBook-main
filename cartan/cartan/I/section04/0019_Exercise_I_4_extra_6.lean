import cartan.I.section02.«0006_Proposition_I_2_extra_4»

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries
open Filter
open scoped NNReal ENNReal Topology

/-
Source-facing exercise statements in the scalar power-series radius domain.
Core owner: `FormalMultilinearSeries.ofScalars`.
Bridge used for the root-test statements below: the chapter theorem
`ofScalars_radius_inv_eq_limsup`.
-/

universe u

variable {𝕜 : Type u}

/-- Helper for Exercise I.4-extra-6: the shifted root sequence for the coefficients `n^p`. -/
noncomputable def polynomial_root_sequence [RCLike 𝕜] (p : ℕ) : ℕ → ℝ≥0∞ :=
  fun n ↦ ((‖((n.succ : 𝕜) ^ p)‖₊ ^ (1 / (n.succ : ℝ)) : ℝ≥0) : ℝ≥0∞)

/-- Helper for Exercise I.4-extra-6: the shifted root sequence for the alternating geometric
coefficients. -/
noncomputable def alternating_root_sequence [NontriviallyNormedField 𝕜] (a b : 𝕜) : ℕ → ℝ≥0∞ :=
  fun n ↦ ((‖if Even n.succ then b ^ n.succ else a ^ n.succ‖₊ ^ (1 / (n.succ : ℝ)) : ℝ≥0) : ℝ≥0∞)

/-- Helper for Exercise I.4-extra-6: taking the `n`th root of an `n`th power in `ℝ≥0∞`
recovers the original value. -/
lemma ennreal_rpow_nat_root (x : ℝ≥0) {n : ℕ} (hn : n ≠ 0) :
    (((x ^ n) ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞) = x := by
  -- First compute the root in `ℝ≥0`, then coerce the identity to `ℝ≥0∞`.
  simpa [one_div] using
    congrArg (fun y : ℝ≥0 ↦ (y : ℝ≥0∞)) (NNReal.pow_rpow_inv_natCast x hn)

/-- Helper for Exercise I.4-extra-6: the quadratic-geometric norm ratio tends to `0` when
`‖q‖ < 1`. -/
lemma quadratic_geometric_ratio_tendsto_zero [NontriviallyNormedField 𝕜] {q : 𝕜}
    (hq0 : q ≠ 0) (hq : ‖q‖ < 1) :
    Tendsto (fun n ↦ ‖q ^ (n.succ ^ 2)‖ / ‖q ^ (n ^ 2)‖) atTop (𝓝 0) := by
  have hqnorm0 : ‖q‖ ≠ 0 := by
    simpa [norm_eq_zero] using hq0
  have hratio :
      ∀ n : ℕ, ‖q ^ (n.succ ^ 2)‖ / ‖q ^ (n ^ 2)‖ = ‖q‖ ^ (2 * n + 1) := by
    intro n
    have hsq : n.succ ^ 2 = n ^ 2 + (2 * n + 1) := by
      rw [Nat.succ_eq_add_one, pow_two, pow_two]
      ring
    have hden : ‖q‖ ^ (n ^ 2) ≠ 0 := pow_ne_zero _ hqnorm0
    -- Rewrite the quotient by separating off the extra factor `‖q‖^(2n+1)`.
    calc
      ‖q ^ (n.succ ^ 2)‖ / ‖q ^ (n ^ 2)‖
          = ‖q‖ ^ (n ^ 2 + (2 * n + 1)) / ‖q‖ ^ (n ^ 2) := by
              rw [norm_pow, norm_pow, hsq]
      _ = (‖q‖ ^ (n ^ 2) * ‖q‖ ^ (2 * n + 1)) / ‖q‖ ^ (n ^ 2) := by
            rw [pow_add]
      _ = (‖q‖ ^ (2 * n + 1) * ‖q‖ ^ (n ^ 2)) / ‖q‖ ^ (n ^ 2) := by
            ring
      _ = ‖q‖ ^ (2 * n + 1) := by
            rw [mul_div_assoc, div_self hden, mul_one]
  have hpow_sq :
      Tendsto (fun n : ℕ ↦ (‖q‖ ^ 2) ^ n) atTop (𝓝 0) := by
    have hsq_lt_one : ‖q‖ ^ 2 < 1 := by
      nlinarith [norm_nonneg q, hq]
    -- The geometric factor `(‖q‖^2)^n` decays exponentially.
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hsq_lt_one
  have hpow :
      Tendsto (fun n : ℕ ↦ ‖q‖ ^ (2 * n + 1)) atTop (𝓝 0) := by
    have hrewrite :
        (fun n : ℕ ↦ ‖q‖ ^ (2 * n + 1)) =
          fun n : ℕ ↦ ‖q‖ * (‖q‖ ^ 2) ^ n := by
      funext n
      -- Factor one copy of `‖q‖` from the odd power.
      calc
        ‖q‖ ^ (2 * n + 1) = ‖q‖ ^ (2 * n) * ‖q‖ := by
          rw [pow_add]
          simp
        _ = (‖q‖ ^ 2) ^ n * ‖q‖ := by
          rw [pow_mul]
        _ = ‖q‖ * (‖q‖ ^ 2) ^ n := by
          ring
    rw [hrewrite]
    simpa using (tendsto_const_nhds.mul hpow_sq)
  exact Tendsto.congr' (Eventually.of_forall fun n ↦ (hratio n).symm) hpow

/-- Helper for Exercise I.4-extra-6: the shifted polynomial root sequence tends to `1`. -/
lemma polynomial_root_sequence_tendsto_one [RCLike 𝕜] (p : ℕ) :
    Tendsto (polynomial_root_sequence (𝕜 := 𝕜) p) atTop (𝓝 1) := by
  have hreal :
      Tendsto (fun n : ℕ ↦ ((n.succ : ℝ) ^ p) ^ (1 / (n.succ : ℝ))) atTop (𝓝 1) := by
    have hrewrite :
        (fun n : ℕ ↦ ((n.succ : ℝ) ^ p) ^ (1 / (n.succ : ℝ))) =
          fun n : ℕ ↦ (n.succ : ℝ) ^ ((p : ℝ) / (n.succ : ℝ)) := by
      funext n
      -- Convert the natural power to a real power and combine exponents.
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      ring
    rw [hrewrite]
    have hsucc_real : Tendsto (fun n : ℕ ↦ (n.succ : ℝ)) atTop atTop := by
      simpa [Nat.succ_eq_add_one] using
        (Filter.tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ)))
    simpa using (tendsto_rpow_div_mul_add (p : ℝ) 1 0 zero_ne_one).comp hsucc_real
  -- Transfer the real convergence through `ENNReal.ofReal`.
  have hcoeff :
      polynomial_root_sequence (𝕜 := 𝕜) p =
        fun n ↦ ENNReal.ofReal (((n.succ : ℝ) ^ p) ^ (1 / (n.succ : ℝ))) := by
    funext n
    rw [polynomial_root_sequence, nnnorm_pow, ENNReal.coe_nnreal_eq]
    congr 1
    rw [NNReal.coe_rpow, NNReal.coe_pow, RCLike.nnnorm_natCast]
    change (((n.succ : ℝ) ^ p) ^ (1 / (n.succ : ℝ))) =
      (((n.succ : ℝ) ^ p) ^ (1 / (n.succ : ℝ)))
    rfl
  rw [hcoeff]
  simpa using (ENNReal.continuous_ofReal.tendsto 1).comp hreal

/-- Helper for Exercise I.4-extra-6: on the even positive indices, the alternating root sequence
is exactly `‖b‖`. -/
lemma alternating_root_sequence_eq_even [NontriviallyNormedField 𝕜] (a b : 𝕜) (n : ℕ)
    (hEven : Even n.succ) :
    alternating_root_sequence a b n = ENNReal.ofReal ‖b‖ := by
  -- The coefficient is `b^(n+1)`, and the `(n+1)`st root cancels that power.
  rw [alternating_root_sequence, if_pos hEven, nnnorm_pow]
  simpa [one_div, ENNReal.ofReal_eq_coe_nnreal] using congrArg (fun y : ℝ≥0 ↦ (y : ℝ≥0∞))
    (NNReal.pow_rpow_inv_natCast ‖b‖₊ n.succ_ne_zero)

/-- Helper for Exercise I.4-extra-6: on the odd positive indices, the alternating root sequence
is exactly `‖a‖`. -/
lemma alternating_root_sequence_eq_odd [NontriviallyNormedField 𝕜] (a b : 𝕜) (n : ℕ)
    (hOdd : ¬ Even n.succ) :
    alternating_root_sequence a b n = ENNReal.ofReal ‖a‖ := by
  -- The coefficient is `a^(n+1)`, and the `(n+1)`st root cancels that power.
  rw [alternating_root_sequence, if_neg hOdd, nnnorm_pow]
  simpa [one_div, ENNReal.ofReal_eq_coe_nnreal] using congrArg (fun y : ℝ≥0 ↦ (y : ℝ≥0∞))
    (NNReal.pow_rpow_inv_natCast ‖a‖₊ n.succ_ne_zero)

/-- Helper for Exercise I.4-extra-6: every term of the shifted alternating root sequence is bounded
by `max ‖a‖ ‖b‖`. -/
lemma alternating_root_sequence_le_max [NontriviallyNormedField 𝕜] (a b : 𝕜) (n : ℕ) :
    alternating_root_sequence a b n ≤ ENNReal.ofReal (max ‖a‖ ‖b‖) := by
  by_cases hEven : Even n.succ
  · -- On an even successor index, the exact value is `‖b‖`.
    rw [alternating_root_sequence_eq_even (a := a) (b := b) n hEven]
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  · -- On an odd successor index, the exact value is `‖a‖`.
    rw [alternating_root_sequence_eq_odd (a := a) (b := b) n hEven]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)

/-- Helper for Exercise I.4-extra-6: the shifted alternating root sequence attains `‖a‖`
frequently. -/
lemma frequently_le_alternating_root_sequence_left [NontriviallyNormedField 𝕜] (a b : 𝕜) :
    ∃ᶠ n in atTop, ENNReal.ofReal ‖a‖ ≤ alternating_root_sequence a b n := by
  refine Filter.frequently_atTop.2 ?_
  intro N
  refine ⟨2 * N, by omega, ?_⟩
  have hOdd : ¬ Even (2 * N).succ := by
    simpa [Nat.succ_eq_add_one, parity_simps]
  simpa [alternating_root_sequence_eq_odd (a := a) (b := b) (n := 2 * N) hOdd]

/-- Helper for Exercise I.4-extra-6: the shifted alternating root sequence attains `‖b‖`
frequently. -/
lemma frequently_le_alternating_root_sequence_right [NontriviallyNormedField 𝕜] (a b : 𝕜) :
    ∃ᶠ n in atTop, ENNReal.ofReal ‖b‖ ≤ alternating_root_sequence a b n := by
  refine Filter.frequently_atTop.2 ?_
  intro N
  refine ⟨2 * N + 1, by omega, ?_⟩
  have hEven : Even (2 * N + 1).succ := by
    simpa [Nat.succ_eq_add_one, parity_simps]
  simpa [alternating_root_sequence_eq_even (a := a) (b := b) (n := 2 * N + 1) hEven]

/-- Helper for Exercise I.4-extra-6: the limsup of the alternating root sequence is the larger of
`‖a‖` and `‖b‖`. -/
lemma alternating_root_limsup_eq_max [NontriviallyNormedField 𝕜] (a b : 𝕜) :
    limsup (alternating_root_sequence a b) atTop = ENNReal.ofReal (max ‖a‖ ‖b‖) := by
  apply le_antisymm
  · -- The uniform bound gives the limsup upper bound.
    exact limsup_le_of_le (h := Eventually.of_forall fun n ↦ alternating_root_sequence_le_max a b n)
  · -- Each of the two parity values appears frequently, so their maximum is below the limsup.
    have ha :
        ENNReal.ofReal ‖a‖ ≤ limsup (alternating_root_sequence a b) atTop :=
      le_limsup_of_frequently_le (frequently_le_alternating_root_sequence_left a b)
    have hb :
        ENNReal.ofReal ‖b‖ ≤ limsup (alternating_root_sequence a b) atTop :=
      le_limsup_of_frequently_le (frequently_le_alternating_root_sequence_right a b)
    have hmax :
        max (ENNReal.ofReal ‖a‖) (ENNReal.ofReal ‖b‖) ≤ limsup (alternating_root_sequence a b) atTop :=
      max_le_iff.mpr ⟨ha, hb⟩
    simpa [ENNReal.ofReal_max] using hmax

/-- Exercise I.4-extra-6 (1): If `‖q‖ < 1`, then the power series
`∑_{n ≥ 0} q^(n^2) z^n` has infinite radius of convergence. -/
-- Proof sketch: apply the canonical ratio-test lemma `ofScalars_radius_eq_top_of_tendsto` to the
-- coefficients `q^(n^2)`; their successive norm ratios are `‖q‖^(2 * n + 1)`, which tend to `0`.
theorem quadratic_geometric_radius_eq_top [NontriviallyNormedField 𝕜] {q : 𝕜} (hq : ‖q‖ < 1) :
    (ofScalars 𝕜 (fun n ↦ q ^ (n ^ 2))).radius = ⊤ := by
  by_cases hq0 : q = 0
  · -- If `q = 0`, all coefficients after the constant term vanish.
    refine (ofScalars 𝕜 (fun n ↦ q ^ (n ^ 2))).radius_eq_top_of_eventually_eq_zero ?_
    refine Filter.eventually_atTop.2 ?_
    refine ⟨1, ?_⟩
    intro n hn
    have hn0 : n ≠ 0 := by
      omega
    simp [hq0, hn0]
  · -- Otherwise the ratio test applies directly to the nonvanishing coefficients.
    apply ofScalars_radius_eq_top_of_tendsto (E := 𝕜) (c := fun n ↦ q ^ (n ^ 2))
    · exact Eventually.of_forall fun n ↦ pow_ne_zero _ hq0
    · simpa using quadratic_geometric_ratio_tendsto_zero (q := q) hq0 hq

/-- Exercise I.4-extra-6 (2): For every natural number `p`, the power series
`∑_{n ≥ 0} n^p z^n` has radius of convergence `1`. -/
-- Proof sketch: rewrite the radius through the chapter bridge `ofScalars_radius_inv_eq_limsup`
-- for the coefficients `(n : 𝕜)^p`; the
-- limsup of their `n`th roots is `1`.
theorem polynomial_coefficients_radius_eq_one [RCLike 𝕜] (p : ℕ) :
    (ofScalars 𝕜 (fun n ↦ (n : 𝕜) ^ p)).radius = 1 := by
  let u : ℕ → ℝ≥0∞ :=
    fun n ↦ ((‖((n : 𝕜) ^ p)‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)
  have hroot_limsup :
      limsup u atTop = 1 := by
    -- Drop the initial `n = 0` term and identify the shifted sequence with the explicit model.
    have hshift : (fun n ↦ u (n + 1)) = polynomial_root_sequence (𝕜 := 𝕜) p := by
      funext n
      simp only [u, polynomial_root_sequence, Nat.succ_eq_add_one, nnnorm_pow]
    rw [← limsup_nat_add u 1, hshift]
    exact (polynomial_root_sequence_tendsto_one (𝕜 := 𝕜) p).limsup_eq
  have hradius_inv :
      (ofScalars 𝕜 (fun n ↦ (n : 𝕜) ^ p)).radius⁻¹ = 1 := by
    -- Rewrite Hadamard's formula through the computed limsup.
    simpa using
      (ofScalars_radius_inv_eq_limsup (𝕜 := 𝕜) (fun n ↦ (n : 𝕜) ^ p)).trans hroot_limsup
  -- Invert once more to recover the radius itself.
  calc
    (ofScalars 𝕜 (fun n ↦ (n : 𝕜) ^ p)).radius =
        ((ofScalars 𝕜 (fun n ↦ (n : 𝕜) ^ p)).radius⁻¹)⁻¹ := by
          simpa using inv_inv ((ofScalars 𝕜 (fun n ↦ (n : 𝕜) ^ p)).radius)
    _ = 1 := by
          simpa [hradius_inv]

/-- Exercise I.4-extra-6 (3): The series whose even coefficients are `b^(2n)` and whose odd
coefficients are `a^(2n + 1)` has radius of convergence `(max ‖a‖ ‖b‖)⁻¹`. -/
-- Proof sketch: rewrite the radius through `ofScalars_radius_inv_eq_limsup` for the parity-defined
-- coefficients. Along
-- the even subsequence the `n`th roots tend to `‖b‖`, and along the odd subsequence they tend to
-- `‖a‖`; hence the limsup is `max ‖a‖ ‖b‖`.
theorem alternating_geometric_radius_eq_inv_max [NontriviallyNormedField 𝕜] (a b : 𝕜) :
    (ofScalars 𝕜
      (fun n ↦ if Even n then b ^ n else a ^ n)).radius =
      (ENNReal.ofReal (max ‖a‖ ‖b‖))⁻¹ := by
  let u : ℕ → ℝ≥0∞ :=
    fun n ↦ ((‖if Even n then b ^ n else a ^ n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)
  have hroot_limsup :
      limsup u atTop = ENNReal.ofReal (max ‖a‖ ‖b‖) := by
    -- As in the polynomial case, discard the initial `n = 0` term and work with the positive tail.
    have hshift : (fun n ↦ u (n + 1)) = alternating_root_sequence a b := by
      funext n
      simp [u, alternating_root_sequence, Nat.succ_eq_add_one]
    rw [← limsup_nat_add u 1, hshift]
    exact alternating_root_limsup_eq_max (a := a) (b := b)
  have hradius_inv :
      (ofScalars 𝕜 (fun n ↦ if Even n then b ^ n else a ^ n)).radius⁻¹ =
        ENNReal.ofReal (max ‖a‖ ‖b‖) := by
    -- Rewrite Hadamard's formula through the explicit limsup computation.
    simpa using
      (ofScalars_radius_inv_eq_limsup (𝕜 := 𝕜) (fun n ↦ if Even n then b ^ n else a ^ n)).trans
        hroot_limsup
  -- One final inversion converts the inverse-radius identity into the stated radius formula.
  calc
    (ofScalars 𝕜 (fun n ↦ if Even n then b ^ n else a ^ n)).radius =
        ((ofScalars 𝕜 (fun n ↦ if Even n then b ^ n else a ^ n)).radius⁻¹)⁻¹ := by
          simpa using inv_inv ((ofScalars 𝕜 (fun n ↦ if Even n then b ^ n else a ^ n)).radius)
    _ = (ENNReal.ofReal (max ‖a‖ ‖b‖))⁻¹ := by
          simp [hradius_inv]
