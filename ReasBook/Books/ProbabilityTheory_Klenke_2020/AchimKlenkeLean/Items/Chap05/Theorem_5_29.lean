import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap05.Theorem_5_28

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Theorem 5.29: each finite partial sum has variance bounded by the variance supremum
times the number of summands. -/
private lemma partialSum_variance_le_sSup_mul
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_memLp : ∀ n, MemLp (X n) 2 P)
    (hX_var_bdd : BddAbove (Set.range fun n ↦ Var[X n; P]))
    (N : ℕ) :
    Var[partialSum X N; P] ≤ sSup (Set.range fun n ↦ Var[X n; P]) * (N : ℝ) := by
  -- Proof comment: restrict the independent sequence to the first `N` coordinates, rewrite the
  -- partial sum as a `Fin N`-indexed sum, and then use additivity of variance for finite
  -- independent sums.
  let Y : Fin N → Ω → ℝ := fun i ↦ X i.1
  have hY_memLp : ∀ i, MemLp (Y i) 2 P := by
    intro i
    exact hX_memLp i.1
  have hY_pairwise :
      ((Finset.univ : Finset (Fin N)) : Set (Fin N)).Pairwise fun i j ↦ IndepFun (Y i) (Y j) P :=
    by
      intro i _ j _ hij
      exact (hX_indep.precomp Fin.val_injective).indepFun hij
  have hpartial_eq : partialSum X N = fun ω ↦ ∑ i : Fin N, Y i ω := by
    -- Proof comment: the chapter's `partialSum` is exactly the sum over `Fin.range N`.
    ext ω
    simpa [partialSum, Y] using (Fin.sum_univ_eq_sum_range (fun i ↦ X i ω) N).symm
  have hsum_fun_eq : (∑ i : Fin N, Y i) = fun ω ↦ ∑ i : Fin N, Y i ω := by
    -- Proof comment: rewrite the sum of functions in explicit pointwise form.
    funext ω
    simp [Finset.sum_apply]
  have hsum_var : Var[partialSum X N; P] = ∑ i : Fin N, Var[Y i; P] := by
    -- Proof comment: variance additivity is available once the finite family is pairwise
    -- independent and square-integrable.
    rw [hpartial_eq, ← hsum_fun_eq]
    simpa using IndepFun.variance_sum (fun i _ ↦ hY_memLp i) hY_pairwise
  have hvar_le : ∀ i : Fin N, Var[Y i; P] ≤ sSup (Set.range fun n ↦ Var[X n; P]) := by
    intro i
    exact le_csSup hX_var_bdd (Set.mem_range_self i.1)
  have hsum_le :
      ∑ i : Fin N, Var[Y i; P] ≤ N * sSup (Set.range fun n ↦ Var[X n; P]) := by
    -- Proof comment: each summand is bounded by the common variance supremum.
    simpa [Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_card_nsmul Finset.univ (fun i : Fin N ↦ Var[Y i; P])
        (sSup (Set.range fun n ↦ Var[X n; P])) (fun i _ ↦ hvar_le i)
  rw [hsum_var]
  simpa [mul_comm] using hsum_le

/-- Helper for Theorem 5.29: logarithms of dyadic powers linearize exactly. -/
private lemma dyadic_log_pow_eq
    (k : ℕ) :
    Real.log ((2 ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log 2 := by
  -- Proof comment: `Real.log_pow` applies directly once the dyadic natural power is cast to `ℝ`.
  rw [Nat.cast_pow]
  exact Real.log_pow (2 : ℝ) k

/-- Helper for Theorem 5.29: the shifted dyadic logarithm is the `k = m + 1` case of the general
dyadic logarithm identity. -/
private lemma dyadic_log_eq
    (m : ℕ) :
    Real.log ((2 ^ (m + 1) : ℕ) : ℝ) = (m + 1 : ℝ) * Real.log 2 := by
  -- Proof comment: specialize the general dyadic logarithm identity to the shifted block index.
  rw [dyadic_log_pow_eq]
  norm_num

/-- Helper for Theorem 5.29: the dyadic normalization square expands into the exact p-series
denominator used in the Kolmogorov bound. -/
private lemma dyadic_normalization_sq
    {ε δ : ℝ} (m : ℕ) :
    (δ *
      (Real.sqrt (((2 ^ (m + 1) : ℕ) : ℝ)) *
        Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 / 2 + ε))) ^ 2 =
      δ ^ 2 * ((((2 ^ (m + 1) : ℕ) : ℝ)) *
        (((m + 1 : ℝ) ^ (1 + 2 * ε)) * Real.rpow (Real.log 2) (1 + 2 * ε))) := by
  have hlog_nonneg : 0 ≤ Real.log (((2 ^ (m + 1) : ℕ) : ℝ)) := by
    -- Proof comment: on a shifted dyadic block the logarithm is positive, hence nonnegative.
    rw [dyadic_log_eq]
    positivity
  have hrpow_sq :
      (Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 / 2 + ε)) ^ 2 =
        Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 + 2 * ε) := by
    -- Proof comment: multiply the exponent `1 / 2 + ε` by `2` to recover `1 + 2 * ε`.
    calc
      (Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 / 2 + ε)) ^ 2 =
          (Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 / 2 + ε)) ^ (2 : ℝ) := by
        rw [← Real.rpow_natCast]
        norm_num
      _ = Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) ((1 / 2 + ε) * 2) := by
        symm
        exact Real.rpow_mul hlog_nonneg (1 / 2 + ε) (2 : ℝ)
      _ = Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 + 2 * ε) := by
        congr 1
        ring
  have hscale_sq :
      (Real.sqrt (((2 ^ (m + 1) : ℕ) : ℝ)) *
          Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 / 2 + ε)) ^ 2 =
        (((2 ^ (m + 1) : ℕ) : ℝ)) *
          (((m + 1 : ℝ) ^ (1 + 2 * ε)) * Real.rpow (Real.log 2) (1 + 2 * ε)) := by
    -- Proof comment: square the `sqrt` and `rpow` factors separately and then linearize the
    -- dyadic logarithm.
    rw [mul_pow, Real.sq_sqrt (by positivity), hrpow_sq, dyadic_log_eq]
    have hmul :
        (((m + 1 : ℝ) * Real.log 2) ^ (1 + 2 * ε)) =
          (m + 1 : ℝ) ^ (1 + 2 * ε) * (Real.log 2) ^ (1 + 2 * ε) := by
      simpa using (Real.mul_rpow (by positivity) (by positivity) : 
        (((m + 1 : ℝ) * Real.log 2) ^ (1 + 2 * ε)) =
          (m + 1 : ℝ) ^ (1 + 2 * ε) * (Real.log 2) ^ (1 + 2 * ε))
    exact congrArg (fun t : ℝ ↦ (((2 ^ (m + 1) : ℕ) : ℝ)) * t) hmul
  -- Proof comment: the threshold factor `δ` now contributes only the scalar square `δ ^ 2`.
  rw [mul_pow, hscale_sq]

/-- Helper for Theorem 5.29: the shifted p-series coming from the dyadic maximal inequality is
summable as soon as `ε > 0`. -/
private lemma shifted_p_series_summable
    {ε C : ℝ} (hε : 0 < ε) :
    Summable (fun m : ℕ ↦ C / ((m + 1 : ℝ) ^ (1 + 2 * ε))) := by
  have hs :
      Summable (fun m : ℕ ↦ 1 / ((m + 1 : ℝ) ^ (1 + 2 * ε))) := by
    -- Proof comment: this is the textbook `p`-series with exponent `1 + 2 * ε > 1`.
    refine
      ((Real.summable_one_div_nat_add_rpow 1 (1 + 2 * ε)).2 (by linarith)).congr ?_
    intro m
    rw [abs_of_nonneg]
    positivity
  -- Proof comment: multiplying a summable series by the constant prefactor preserves summability.
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hs.mul_left C

/-- Helper for Theorem 5.29: on each dyadic block, the dyadic normalization is controlled by the
normalization at any interior index up to an explicit `ε`-dependent constant. -/
private lemma dyadic_scale_le_block_scale
    {ε : ℝ} (hε : 0 < ε) {m n : ℕ}
    (hm : 1 ≤ m) (h_lower : 2 ^ m ≤ n + 1) (h_upper : n + 1 ≤ 2 ^ (m + 1)) :
    Real.sqrt (((2 ^ (m + 1) : ℕ) : ℝ)) *
        Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 / 2 + ε) ≤
      (Real.sqrt 2 * 2 ^ (1 / 2 + ε)) *
        (Real.sqrt (n + 1) * Real.rpow (Real.log (n + 1)) (1 / 2 + ε)) := by
  have hp_pos : 0 < (1 / 2 + ε : ℝ) := by
    linarith
  have hsqrt :
      Real.sqrt (((2 ^ (m + 1) : ℕ) : ℝ)) ≤ Real.sqrt 2 * Real.sqrt (n + 1) := by
    have h_cast : (((2 ^ (m + 1) : ℕ) : ℝ)) ≤ 2 * (n + 1 : ℝ) := by
      -- Proof comment: the upper dyadic endpoint is at most twice any index in the same dyadic
      -- block.
      calc
        (((2 ^ (m + 1) : ℕ) : ℝ)) = 2 * ((2 ^ m : ℕ) : ℝ) := by
          rw [pow_succ, Nat.cast_mul]
          ring
        _ ≤ 2 * (n + 1 : ℝ) := by
          gcongr
          exact_mod_cast h_lower
    calc
      Real.sqrt (((2 ^ (m + 1) : ℕ) : ℝ)) ≤ Real.sqrt (2 * (n + 1 : ℝ)) := Real.sqrt_le_sqrt h_cast
      _ = Real.sqrt 2 * Real.sqrt (n + 1) := by
        rw [Real.sqrt_mul (by positivity)]
  have hlog_nonneg : 0 ≤ Real.log (n + 1 : ℝ) := by
    have hpow_two : (2 : ℕ) ≤ 2 ^ m := by
      rcases Nat.exists_eq_add_of_le hm with ⟨k, rfl⟩
      have hk : 1 ≤ 2 ^ k := Nat.succ_le_of_lt (pow_pos (by decide : 0 < 2) k)
      calc
        2 = 2 * 1 := by ring
        _ ≤ 2 * 2 ^ k := by gcongr
        _ = 2 ^ (1 + k) := by simp [pow_succ, Nat.mul_comm, Nat.add_comm]
    have h_lower_two : (2 : ℕ) ≤ n + 1 := le_trans hpow_two h_lower
    -- Proof comment: every index in a shifted dyadic block is at least `2`, so its logarithm is
    -- nonnegative.
    exact le_of_lt (Real.log_pos (by exact_mod_cast h_lower_two))
  have hlog_upper_bound :
      Real.log (((2 ^ (m + 1) : ℕ) : ℝ)) ≤ 2 * Real.log (n + 1 : ℝ) := by
    have hm_cast : (1 : ℝ) ≤ m := by
      exact_mod_cast hm
    have hm_succ_le : (m + 1 : ℝ) ≤ 2 * m := by
      linarith
    have hlog_lower : (m : ℝ) * Real.log 2 ≤ Real.log (n + 1 : ℝ) := by
      -- Proof comment: the lower dyadic endpoint lies below `n + 1`, so its logarithm does too.
      rw [← dyadic_log_pow_eq m]
      exact Real.log_le_log (by positivity) (by exact_mod_cast h_lower)
    rw [dyadic_log_eq]
    calc
      (m + 1 : ℝ) * Real.log 2 ≤ (2 * m : ℝ) * Real.log 2 := by
        exact mul_le_mul_of_nonneg_right hm_succ_le (le_of_lt (Real.log_pos one_lt_two))
      _ = 2 * ((m : ℝ) * Real.log 2) := by
        ring
      _ ≤ 2 * Real.log (n + 1 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hlog_lower (by positivity)
  have hrpow :
      Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 / 2 + ε) ≤
        2 ^ (1 / 2 + ε) * Real.rpow (Real.log (n + 1 : ℝ)) (1 / 2 + ε) := by
    -- Proof comment: monotonicity of `x ↦ x^(1 / 2 + ε)` on `[0, ∞)` upgrades the logarithmic
    -- block comparison to the normalization factor.
    calc
      Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 / 2 + ε) ≤
          Real.rpow (2 * Real.log (n + 1 : ℝ)) (1 / 2 + ε) := by
        exact Real.rpow_le_rpow (by positivity) hlog_upper_bound hp_pos.le
      _ = 2 ^ (1 / 2 + ε) * Real.rpow (Real.log (n + 1 : ℝ)) (1 / 2 + ε) := by
        have hmul :
            ((2 * Real.log (n + 1 : ℝ)) ^ (1 / 2 + ε)) =
              2 ^ (1 / 2 + ε) * (Real.log (n + 1 : ℝ)) ^ (1 / 2 + ε) := by
          simpa using (Real.mul_rpow (by positivity) hlog_nonneg :
            ((2 * Real.log (n + 1 : ℝ)) ^ (1 / 2 + ε)) =
              2 ^ (1 / 2 + ε) * (Real.log (n + 1 : ℝ)) ^ (1 / 2 + ε))
        exact hmul
  have hdyadic_log_nonneg : 0 ≤ Real.log (((2 ^ (m + 1) : ℕ) : ℝ)) := by
    rw [dyadic_log_eq]
    positivity
  have hdyadic_rpow_nonneg :
      0 ≤ Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 / 2 + ε) := by
    exact Real.rpow_nonneg hdyadic_log_nonneg _
  have hblock_nonneg : 0 ≤ Real.sqrt 2 * Real.sqrt (n + 1) := by
    positivity
  -- Proof comment: combine the square-root control and the logarithmic control, then regroup the
  -- scalar constants.
  calc
    Real.sqrt (((2 ^ (m + 1) : ℕ) : ℝ)) *
        Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 / 2 + ε) ≤
      (Real.sqrt 2 * Real.sqrt (n + 1)) *
        Real.rpow (Real.log (((2 ^ (m + 1) : ℕ) : ℝ))) (1 / 2 + ε) := by
      exact mul_le_mul_of_nonneg_right hsqrt hdyadic_rpow_nonneg
    _ ≤ (Real.sqrt 2 * Real.sqrt (n + 1)) *
        (2 ^ (1 / 2 + ε) * Real.rpow (Real.log (n + 1 : ℝ)) (1 / 2 + ε)) := by
      exact mul_le_mul_of_nonneg_left hrpow hblock_nonneg
    _ = (Real.sqrt 2 * 2 ^ (1 / 2 + ε)) *
          (Real.sqrt (n + 1) * Real.rpow (Real.log (n + 1)) (1 / 2 + ε)) := by
      ring

-- Proof sketch: pass to the dyadic subsequence `2^k`, apply Kolmogorov's maximal inequality to
-- the centered partial sums using the uniform variance bound, show the resulting probabilities are
-- summable, and conclude from Borel--Cantelli. A comparison between arbitrary `n` and the
-- neighboring dyadic block then gives the full limsup statement.
/-- Theorem 5.29: if the real random variables `X₀, X₁, …` are independent, have mean `0`, and
have uniformly bounded variances, then for every `ε > 0` the normalized partial sums
`Sₙ = X₀ + ⋯ + Xₙ₋₁` satisfy
`limsup |Sₙ| / (sqrt n * (log n)^(1 / 2 + ε)) = 0` almost surely. For the textbook indexing
`X₁, X₂, …`, apply this statement to `fun k ↦ X (k + 1)`. -/
theorem ae_limsup_partial_sum_div_sqrt_log_rpow_eq_zero
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun X P)
    (hX_memLp : ∀ n, MemLp (X n) 2 P)
    (hX_mean_zero : ∀ n, P[X n] = 0)
    (hX_var_bdd : BddAbove (Set.range fun n ↦ Var[X n; P]))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P,
      limsup
        (fun n ↦
          |partialSum X (n + 1) ω| /
            (Real.sqrt (n + 1) *
              Real.rpow (Real.log (n + 1)) (1 / 2 + ε))) atTop = 0 := by
  let V : ℝ := sSup (Set.range fun n ↦ Var[X n; P])
  let L : ℕ → ℝ := fun n ↦ Real.sqrt n * Real.rpow (Real.log n) (1 / 2 + ε)
  have hvariance : ∀ N, Var[partialSum X N; P] ≤ V * (N : ℝ) := by
    intro N
    simpa [V] using partialSum_variance_le_sSup_mul P X hX_indep hX_memLp hX_var_bdd N
  have hp_pos : 0 < (1 / 2 + ε : ℝ) := by
    linarith
  -- Route correction: the previous attempt confirmed the correct dyadic skeleton and isolated the
  -- exact algebraic bottleneck in Lean. The file now contains the closed normalization identity
  -- `dyadic_normalization_sq`, the p-series helper `shifted_p_series_summable`, and the
  -- deterministic block comparison `dyadic_scale_le_block_scale`.
  -- TODO: assemble these helpers with `kolmogorov_inequality_abs_partial_sums` into the concrete
  -- summable majorant for
  -- `P (absHitEvent X (2 ^ (m + 1)) (δ * L (2 ^ (m + 1))))`, apply
  -- `MeasureTheory.ae_eventually_notMem` to that canonical dyadic event family for the reciprocal
  -- thresholds `δ_j = (j + 1)⁻¹`, and then convert the resulting eventual dyadic control into the
  -- almost sure `limsup = 0` conclusion.
  sorry
