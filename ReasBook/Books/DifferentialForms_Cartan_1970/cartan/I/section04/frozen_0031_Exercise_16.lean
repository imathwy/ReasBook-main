import Mathlib
import DifferentialForms_Cartan_1970.I.section02.«frozen_0007_Example_I_2_extra_5»
import DifferentialForms_Cartan_1970.I.section02.«0013_Proposition_7_1»
import DifferentialForms_Cartan_1970.I.section03.«0011_Proposition_6_1»

-- Declarations for this item will be appended below by the statement pipeline.

open FormalMultilinearSeries
open scoped Topology

/-- The domain `D = {z : ℂ | ‖z‖ < 1 and ‖z - 1‖ < 1}` from Exercise 16. -/
def exercise16Domain : Set ℂ :=
  Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) 1

namespace Complex

/-- The textbook dilogarithm-type power series
`S(z) = ∑_{n ≥ 1} z^n / n^2`, realized as a thin source-facing bridge over the scalar-series
owner `FormalMultilinearSeries.ofScalarsSum`. -/
noncomputable def dilogarithmPowerSeries (z : ℂ) : ℂ :=
  z * ofScalarsSum (fun n ↦ (1 : ℂ) / ((n + 1 : ℂ) ^ 2)) z

/-- The source-facing dilogarithm-type series agrees with its textbook `tsum` expansion. -/
theorem dilogarithmPowerSeries_eq_tsum (z : ℂ) :
    dilogarithmPowerSeries z = ∑' n : ℕ, z ^ (n + 1) / ((n + 1 : ℂ) ^ 2) := by
  rw [dilogarithmPowerSeries, ofScalars_sum_eq]
  rw [← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  calc
    z * (((1 : ℂ) / ((n + 1 : ℂ) ^ 2)) • z ^ n)
        = ((1 : ℂ) / ((n + 1 : ℂ) ^ 2)) * z ^ (n + 1) := by
            simp [smul_eq_mul, pow_succ', mul_assoc, mul_comm]
    _ = z ^ (n + 1) / ((n + 1 : ℂ) ^ 2) := by
          simp [div_eq_mul_inv, mul_comm]

end Complex

/-- A constant satisfying the reflection identity for the dilogarithm-type series on
`exercise16Domain`. -/
def Exercise16ReflectionConstant (a : ℂ) : Prop :=
  ∀ z ∈ exercise16Domain,
    Complex.dilogarithmPowerSeries z + Complex.dilogarithmPowerSeries (1 - z) =
      a - Complex.log z * Complex.log (1 - z)

section AbelSummation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Helper for Exercise 16: Abel's finite summation-by-parts identity rewritten in terms of the
partial sums `s_i = ∑_{k ≤ i} α_k`. -/
theorem weighted_sum_eq_partial_sums_abel
    (α : ℕ → E) (β : ℕ → ℝ) (n : ℕ) :
    (Finset.range (n + 1)).sum (fun i ↦ β i • α i) =
      (Finset.range n).sum (fun i ↦ (β i - β (i + 1)) • (Finset.range (i + 1)).sum α) +
        β n • (Finset.range (n + 1)).sum α := by
  -- Rewrite the weighted sum using the finite summation-by-parts formula from `Finset`.
  calc
    (Finset.range (n + 1)).sum (fun i ↦ β i • α i) =
        β n • (Finset.range (n + 1)).sum α -
          (Finset.range n).sum (fun i ↦ (β (i + 1) - β i) • (Finset.range (i + 1)).sum α) := by
      simpa [Nat.add_comm] using Finset.sum_range_by_parts β α (n + 1)
    _ =
        (Finset.range n).sum (fun i ↦ (β i - β (i + 1)) • (Finset.range (i + 1)).sum α) +
          β n • (Finset.range (n + 1)).sum α := by
      -- Move the correction term to the right and flip the scalar difference.
      rw [sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
      have hterm :
          (fun i ↦ -((β (i + 1) - β i) • (Finset.range (i + 1)).sum α)) =
            fun i ↦ (β i - β (i + 1)) • (Finset.range (i + 1)).sum α := by
        funext i
        calc
          -((β (i + 1) - β i) • (Finset.range (i + 1)).sum α) =
              (-(β (i + 1) - β i)) • (Finset.range (i + 1)).sum α := by
                rw [neg_smul]
          _ = (β i - β (i + 1)) • (Finset.range (i + 1)).sum α := by
                congr 1
                ring
      rw [hterm]

/-- Helper for Exercise 16: the Abel coefficients telescope to the first weight. -/
theorem sum_range_beta_diff_add (β : ℕ → ℝ) (n : ℕ) :
    (Finset.range n).sum (fun i ↦ β i - β (i + 1)) + β n = β 0 := by
  -- The finite difference sum telescopes.
  have h := Finset.sum_range_sub β n
  have h' := congrArg (fun t : ℝ => -t + β n) h
  have h'' : β n + (Finset.range n).sum (fun i ↦ β i - β (i + 1)) = β 0 := by
    calc
      β n + (Finset.range n).sum (fun i ↦ β i - β (i + 1)) =
          β n + -∑ x ∈ Finset.range n, (-β x + β (x + 1)) := by
            congr 1
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = β 0 := by
        simpa [Finset.sum_sub_distrib, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
  simpa [add_comm] using h''

-- Proof sketch: apply Abel summation to the partial sums `s_n = ∑_{k ≤ n} α_k` and the
-- monotone nonnegative weights `β_n`, then use the identity from the hint to rewrite the
-- weighted sum in terms of the bounded partial sums.
/-- Exercise 16 (1): if the partial sums of a sequence in a real normed space are uniformly
bounded by `M`
and `β` is a nonnegative decreasing real sequence, then every finite weighted sum
`∑_{k ≤ n} α_k β_k` has norm at most `M * β₀`. -/
theorem abel_summation_norm_le_of_bounded_partial_sums
    (α : ℕ → E) (β : ℕ → ℝ) (M : ℝ)
    (hpartial : ∀ n : ℕ, ‖(Finset.range (n + 1)).sum α‖ ≤ M)
    (hβ_nonneg : ∀ n : ℕ, 0 ≤ β n) (hβ_antitone : Antitone β) (n : ℕ) :
    ‖(Finset.range (n + 1)).sum (fun i ↦ β i • α i)‖ ≤ M * β 0 := by
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hpartial 0)
  -- Rewrite the weighted sum in Abel form so that the bounded partial sums appear explicitly.
  rw [weighted_sum_eq_partial_sums_abel α β n]
  calc
    ‖(Finset.range n).sum
        (fun i ↦ (β i - β (i + 1)) • (Finset.range (i + 1)).sum α) +
        β n • (Finset.range (n + 1)).sum α‖
      ≤ ‖(Finset.range n).sum
          (fun i ↦ (β i - β (i + 1)) • (Finset.range (i + 1)).sum α)‖ +
        ‖β n • (Finset.range (n + 1)).sum α‖ := norm_add_le _ _
    _ ≤
        (Finset.range n).sum
            (fun i ↦ ‖(β i - β (i + 1)) • (Finset.range (i + 1)).sum α‖) +
          ‖β n • (Finset.range (n + 1)).sum α‖ := by
        gcongr
        exact norm_sum_le _ _
    _ ≤ (Finset.range n).sum (fun i ↦ (β i - β (i + 1)) * M) + β n * M := by
      refine add_le_add ?_ ?_
      · refine Finset.sum_le_sum fun i hi ↦ ?_
        have hβmono : β (i + 1) ≤ β i := hβ_antitone (Nat.le_succ i)
        have hβdiff : 0 ≤ β i - β (i + 1) := sub_nonneg.mpr hβmono
        rw [norm_smul, Real.norm_of_nonneg hβdiff]
        exact mul_le_mul_of_nonneg_left (hpartial i) hβdiff
      · have hβn : 0 ≤ β n := hβ_nonneg n
        rw [norm_smul, Real.norm_of_nonneg hβn]
        exact mul_le_mul_of_nonneg_left (hpartial n) hβn
    _ = ((Finset.range n).sum (fun i ↦ β i - β (i + 1))) * M + β n * M := by
      rw [Finset.sum_mul]
    _ = ((Finset.range n).sum (fun i ↦ β i - β (i + 1)) + β n) * M := by
      ring
    _ = β 0 * M := by rw [sum_range_beta_diff_add β n]
    _ = M * β 0 := by ring

end AbelSummation

section RealAbelPowerSeries

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Helper for Exercise 16: every sufficiently deep tail of a convergent series has uniformly
small finite partial sums. -/
theorem summable_tail_partial_sums_norm_lt
    (a : ℕ → 𝕜) (ha : Summable a) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, ∀ m, ‖(Finset.range m).sum (fun i ↦ a (n + i))‖ < ε := by
  let s : ℕ → 𝕜 := fun n ↦ (Finset.range n).sum a
  have hs : CauchySeq s := (ha.hasSum.tendsto_sum_nat).cauchySeq
  rcases Metric.cauchySeq_iff.1 hs ε hε with ⟨N, hN⟩
  refine ⟨N, fun n hn m ↦ ?_⟩
  have hdist := hN (n + m) (le_trans hn (Nat.le_add_right n m)) n hn
  have hsplit : s (n + m) = s n + (Finset.range m).sum (fun i ↦ a (n + i)) := by
    simp [s, Finset.sum_range_add]
  -- Interpret the Cauchy estimate as a norm estimate on the shifted tail sum.
  simpa [s, hsplit, dist_eq_norm] using hdist

/-- Helper for Exercise 16: splitting a longer power-series partial sum at a smaller index factors
out the initial power. -/
theorem weighted_partial_sum_split
    (a : ℕ → 𝕜) (x : ℝ) (m k : ℕ) :
    (Finset.range (m + k)).sum (fun i ↦ a i * (x : 𝕜) ^ i) =
      (Finset.range m).sum (fun i ↦ a i * (x : 𝕜) ^ i) +
        (x : 𝕜) ^ m * (Finset.range k).sum (fun i ↦ a (m + i) * (x : 𝕜) ^ i) := by
  -- Split the range sum and factor the common power `x^m` out of the tail block.
  calc
    (Finset.range (m + k)).sum (fun i ↦ a i * (x : 𝕜) ^ i) =
        (Finset.range m).sum (fun i ↦ a i * (x : 𝕜) ^ i) +
          (Finset.range k).sum (fun i ↦ a (m + i) * (x : 𝕜) ^ (m + i)) := by
      rw [Finset.sum_range_add]
    _ =
        (Finset.range m).sum (fun i ↦ a i * (x : 𝕜) ^ i) +
          (Finset.range k).sum
            (fun i ↦ (x : 𝕜) ^ m * (a (m + i) * (x : 𝕜) ^ i)) := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [pow_add]
      ring
    _ =
        (Finset.range m).sum (fun i ↦ a i * (x : 𝕜) ^ i) +
          (x : 𝕜) ^ m * (Finset.range k).sum (fun i ↦ a (m + i) * (x : 𝕜) ^ i) := by
      rw [← Finset.mul_sum]

-- Proof sketch: use part (1) with `α_n = a_n` and `β_n = x^n` for `x ∈ [0, 1]`; the convergence
-- of `∑ a_n` gives bounded partial sums, and the uniform bound
-- `‖a n * x^n‖ ≤ ‖a n‖` yields a summable majorant on `[0, 1]`.
/-- Helper for Exercise 16: on the closed unit interval, each power-series term is bounded in norm
by the norm of its coefficient. -/
theorem exercise16_term_norm_le_coeff_norm_on_unitInterval
    (a : ℕ → 𝕜) (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ‖a n * (x : 𝕜) ^ n‖ ≤ ‖a n‖ := by
  -- Separate the coefficient norm from the scalar power and bound the latter by `1`.
  rw [norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  calc
    ‖((x : 𝕜) ^ n)‖ ≤ ‖(x : 𝕜)‖ ^ n := norm_pow_le _ _
    _ = |x| ^ n := by rw [RCLike.norm_ofReal]
    _ = x ^ n := by rw [abs_of_nonneg hx.1]
    _ ≤ 1 := pow_le_one₀ hx.1 hx.2

/-- Exercise 16 (2): if the coefficient series `∑ a_n` converges, then the series
`∑ a_n x^n` is uniformly convergent on the closed interval `[0, 1]`. -/
theorem exercise16_uniform_hasSumOn_unitInterval
    (a : ℕ → 𝕜) (ha : Summable a) :
    HasSumUniformlyOn (fun n (x : ℝ) ↦ a n * (x : 𝕜) ^ n)
      (fun x : ℝ ↦ ofScalarsSum a (x : 𝕜)) (Set.Icc (0 : ℝ) 1) := by
  -- Route correction: for Lean's stronger `HasSumUniformlyOn`, use the summable norm majorant
  -- directly instead of trying to upgrade the Abel `Finset.range` estimates.
  simpa [ofScalars_sum_eq, smul_eq_mul] using
    (HasSumUniformlyOn.of_norm_le_summable ha.norm
      (fun n x hx ↦ by
        simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
          exercise16_term_norm_le_coeff_norm_on_unitInterval a n hx))

-- Proof sketch: combine the uniform convergence on `[0, 1]` from part (2) with the equality
-- `ofScalarsSum a 1 = ∑' n, a n`, then restrict to the approach to `1`
-- through `0 < x < 1`.
/-- Exercise 16 (3): under the hypothesis of part (2), the Abel sums tend to `∑ a_n`
when `x → 1` with `0 < x < 1`. -/
theorem exercise16_tendsto_realAbelPowerSeriesSum_at_one
    (a : ℕ → 𝕜) (ha : Summable a) :
    Filter.Tendsto (fun x : ℝ ↦ ofScalarsSum a (x : 𝕜)) (𝓝[Set.Ioo (0 : ℝ) 1] 1)
      (𝓝 (∑' n : ℕ, a n)) := by
  have hnorm : Summable (fun n : ℕ ↦ ‖a n‖) := ha.norm
  have hcont :
      ContinuousOn (fun x : ℝ ↦ ∑' n : ℕ, a n * (x : 𝕜) ^ n) (Set.Icc (0 : ℝ) 1) := by
    -- Control the series by the coefficient norms on the closed interval.
    refine continuousOn_tsum (fun n ↦ ?_) hnorm fun n x hx ↦ ?_
    · exact (continuous_const.mul <| (RCLike.continuous_ofReal.pow n)).continuousOn
    · have hx_norm_le : ‖(x : 𝕜)‖ ≤ 1 := by
        simpa [RCLike.norm_ofReal, abs_of_nonneg hx.1] using hx.2
      calc
        ‖a n * (x : 𝕜) ^ n‖ = ‖a n‖ * ‖(x : 𝕜) ^ n‖ := norm_mul _ _
        _ ≤ ‖a n‖ * 1 := by
            gcongr
            simpa [norm_pow] using pow_le_one₀ (norm_nonneg ((x : 𝕜))) hx_norm_le
        _ = ‖a n‖ := by
            ring
  have hwithin :
      ContinuousWithinAt (fun x : ℝ ↦ ofScalarsSum a (x : 𝕜)) (Set.Ioo (0 : ℝ) 1) 1 := by
    -- Restrict continuity from `[0,1]` to the left approach through `(0,1)`.
    have hIcc :
        ContinuousWithinAt (fun x : ℝ ↦ ofScalarsSum a (x : 𝕜)) (Set.Icc (0 : ℝ) 1) 1 := by
      simpa [FormalMultilinearSeries.ofScalarsSum_eq_tsum, smul_eq_mul] using
        hcont.continuousWithinAt (by simp : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    exact hIcc.mono (Set.Ioo_subset_Icc_self)
  simpa [FormalMultilinearSeries.ofScalarsSum_eq_tsum, smul_eq_mul] using hwithin.tendsto

end RealAbelPowerSeries

/-- Helper for Cartan section04 frozen_0031_Exercise_16: the scalar coefficients of the
dilogarithm series before the leading shift. -/
noncomputable def exercise16Coeffs : ℕ → ℂ :=
  fun n ↦ (1 : ℂ) / ((n + 1 : ℂ) ^ 2)

/-- Helper for Cartan section04 frozen_0031_Exercise_16: the coefficient sequence
`1 / (n + 1)^2` is summable. -/
lemma summable_exercise16Coeffs : Summable exercise16Coeffs := by
  -- Compare the complex coefficients with the shifted real `p`-series `∑ 1 / (n + 1)^2`.
  refine Summable.of_norm ?_
  rw [show (fun n : ℕ ↦ ‖exercise16Coeffs n‖) =
      (fun n : ℕ ↦ (1 : ℝ) / ((n + 1 : ℝ) ^ 2)) by
        funext n
        calc
          ‖exercise16Coeffs n‖ = ‖(1 : ℂ) / ((n + 1 : ℂ) ^ 2)‖ := by
            rfl
          _ = (1 : ℝ) / ‖((n + 1 : ℂ) ^ 2)‖ := by
            simp
          _ = (1 : ℝ) / ((n + 1 : ℝ) ^ 2) := by
            rw [norm_pow]
            have habs : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
              simpa [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n + 1)
            have habs_sq : ‖(n : ℂ) + 1‖ ^ 2 = ((n : ℝ) + 1) ^ 2 := by
              exact congrArg (fun t : ℝ ↦ t ^ 2) habs
            rw [one_div, one_div]
            exact congrArg Inv.inv habs_sq]
  have hbase : Summable (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) ^ 2)) := by
    have hlt : (1 : ℝ) < 2 := by
      norm_num
    have hbase' : Summable (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ (2 : ℝ)) :=
      (Real.summable_one_div_nat_rpow (p := (2 : ℝ))).2 hlt
    convert hbase' using 1 with n
    simp
  have hshift : Summable (fun n : ℕ ↦ (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2)) :=
    (summable_nat_add_iff 1).2 hbase
  convert hshift using 1 with n
  simp [Nat.cast_add, Nat.cast_one]

namespace Complex

/-- Helper for Cartan section04 frozen_0031_Exercise_16: the source-facing dilogarithm series is
the shifted scalar owner series obtained by prepending a zero coefficient. -/
lemma dilogarithmPowerSeries_eq_ofScalarsSum_prependZero (z : ℂ) :
    dilogarithmPowerSeries z = ofScalarsSum (prependZero exercise16Coeffs) z := by
  -- Route correction: replace the ad hoc product view by the canonical shifted owner series.
  rw [Complex.dilogarithmPowerSeries_eq_tsum, FormalMultilinearSeries.ofScalarsSum_eq_tsum]
  let f : ℕ → ℂ := fun n ↦ z ^ (n + 1) / ((n + 1 : ℂ) ^ 2)
  let g : ℕ → ℂ := fun n ↦ prependZero exercise16Coeffs n • z ^ n
  change ∑' n : ℕ, f n = ∑' n : ℕ, g n
  have hg0 : g 0 = 0 := by
    simp [g, prependZero]
  have hsucc : ∀ n : ℕ, g (n + 1) = f n := by
    intro n
    simp [f, g, prependZero, exercise16Coeffs, smul_eq_mul, div_eq_mul_inv, mul_comm]
  by_cases hf : Summable f
  · have hg : Summable g := by
      -- Summability is unchanged by adjoining the initial zero term.
      refine (summable_nat_add_iff 1).1 ?_
      simpa [hsucc] using hf
    rw [hg.tsum_eq_zero_add, hg0, zero_add]
    exact tsum_congr (fun n ↦ (hsucc n).symm)
  · have hg : ¬ Summable g := by
      intro hg
      apply hf
      -- If the prepended series were summable, then so would its shifted tail be.
      simpa [hsucc] using (summable_nat_add_iff 1).2 hg
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hg]

end Complex

/-- Helper for Cartan section04 frozen_0031_Exercise_16: points of norm `< 1` lie inside the
convergence radius of the prepended-zero owner series. -/
lemma exercise16_prependZero_mem_radius {z : ℂ} (hz : ‖z‖ < 1) :
    ENNReal.ofReal ‖z‖ < (ofScalars ℂ (prependZero exercise16Coeffs)).radius := by
  have hs_norm :
      Summable (fun n : ℕ ↦ ‖ofScalars ℂ exercise16Coeffs n‖ * (1 : ℝ) ^ n) := by
    convert summable_exercise16Coeffs.norm using 1 with n
    simp
  have hradius :
      (1 : ENNReal) ≤ (ofScalars ℂ exercise16Coeffs).radius := by
    -- Summability at `r = 1` gives the source radius lower bound directly.
    exact FormalMultilinearSeries.le_radius_of_summable_norm
      (p := ofScalars ℂ exercise16Coeffs) (r := (1 : NNReal)) hs_norm
  have hzENN : ENNReal.ofReal ‖z‖ < (1 : ENNReal) := by
    simpa using (ENNReal.ofReal_lt_ofReal_iff (by positivity : (0 : ℝ) < 1)).2 hz
  calc
    ENNReal.ofReal ‖z‖ < (1 : ENNReal) := hzENN
    _ ≤ (ofScalars ℂ exercise16Coeffs).radius := hradius
    _ = (ofScalars ℂ (prependZero exercise16Coeffs)).radius := by
      rw [radius_prependZero_eq_radius (𝕜 := ℂ) exercise16Coeffs]

/-- Helper for Cartan section04 frozen_0031_Exercise_16: differentiating the prepended-zero
coefficient sequence yields the harmonic coefficients `1 / (n + 1)`. -/
lemma exercise16_derivCoeff_prependZero :
    ofScalarsDerivCoeff (prependZero exercise16Coeffs) = fun n : ℕ ↦ (1 : ℂ) / (n + 1 : ℂ) := by
  -- The leading zero is exactly what turns the derived coefficients into the harmonic sequence.
  funext n
  have hn : (n + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero n
  calc
    ofScalarsDerivCoeff (prependZero exercise16Coeffs) n
        = (n + 1 : ℂ) * ((1 : ℂ) / ((n + 1 : ℂ) ^ 2)) := by
            simp [ofScalarsDerivCoeff, prependZero, exercise16Coeffs]
    _ = (1 : ℂ) / (n + 1 : ℂ) := by
      field_simp [hn, pow_two]

/-- Helper for Cartan section04 frozen_0031_Exercise_16: the differentiated dilogarithm series
sums to `-log (1 - z) / z` on the open unit disk away from `0`. -/
lemma hasSum_one_div_succ_eq_neg_log_div
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasSum (fun n : ℕ ↦ z ^ n / (n + 1 : ℂ)) (-Complex.log (1 - z) / z) := by
  have hshift :
      HasSum (fun n : ℕ ↦ z ^ (n + 1) / (n + 1 : ℂ)) (-Complex.log (1 - z)) := by
    simpa [Nat.succ_eq_add_one] using
      (hasSum_nat_add_iff' 1).mpr (Complex.hasSum_taylorSeries_neg_log hz)
  -- Divide the shifted logarithmic series by `z` to recover the desired coefficient shape.
  have hdiv := hshift.mul_right z⁻¹
  convert hdiv using 1
  · ext n
    have hz_inv_mul : z⁻¹ * z = 1 := by
      field_simp [hz0]
    calc
      z ^ n / (n + 1 : ℂ) = z ^ n / (n + 1 : ℂ) * 1 := by ring
      _ = z ^ n / (n + 1 : ℂ) * (z⁻¹ * z) := by rw [hz_inv_mul]
      _ = z⁻¹ * (z * z ^ n / (n + 1 : ℂ)) := by ring
      _ = z ^ (n + 1) / (n + 1 : ℂ) * z⁻¹ := by
          rw [pow_succ]
          ring

/-- Helper for Cartan section04 frozen_0031_Exercise_16: points of the lens domain and their
complements `1 - z` both lie in the complex slit plane. -/
lemma exercise16Domain_mem_slitPlane {z : ℂ} (hz : z ∈ exercise16Domain) :
    z ∈ Complex.slitPlane ∧ (1 - z) ∈ Complex.slitPlane := by
  rcases hz with ⟨hz0, hz1⟩
  refine ⟨Complex.ball_one_subset_slitPlane hz1, ?_⟩
  -- Recenter the unit-disk condition at `1` to place `1 - z` in the slit plane.
  simpa [sub_eq_add_neg] using
    (Complex.mem_slitPlane_of_norm_lt_one (z := -z) <|
      by simpa [Metric.mem_ball, norm_neg] using hz0)

/-- Helper for Cartan section04 frozen_0031_Exercise_16: on the open unit disk away from `0`,
the dilogarithm series has derivative `-log (1-z) / z`. -/
lemma hasDerivAt_dilogarithmPowerSeries
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasDerivAt Complex.dilogarithmPowerSeries (-Complex.log (1 - z) / z) z := by
  -- Route correction: differentiate the shifted owner series directly instead of the product form.
  have hzrad :
      ENNReal.ofReal ‖z‖ < (ofScalars ℂ (prependZero exercise16Coeffs)).radius :=
    exercise16_prependZero_mem_radius hz
  have howner :
      HasDerivAt (ofScalarsSum (prependZero exercise16Coeffs))
        (ofScalarsSum (ofScalarsDerivCoeff (prependZero exercise16Coeffs)) z) z := by
    simpa using
      hasDerivAt_ofScalarsSum_eq_ofScalarsSum_derivCoeff
        (a := prependZero exercise16Coeffs) hzrad
  have hvalue :
      ofScalarsSum (ofScalarsDerivCoeff (prependZero exercise16Coeffs)) z =
        -Complex.log (1 - z) / z := by
    -- Rewrite the derivative sum to the textbook harmonic series and invoke the logarithmic sum.
    rw [exercise16_derivCoeff_prependZero, FormalMultilinearSeries.ofScalarsSum_eq_tsum]
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (hasSum_one_div_succ_eq_neg_log_div hz hz0).tsum_eq
  have hfun :
      Complex.dilogarithmPowerSeries = ofScalarsSum (prependZero exercise16Coeffs) :=
    funext Complex.dilogarithmPowerSeries_eq_ofScalarsSum_prependZero
  simpa [hfun, hvalue] using howner

namespace Complex

/-- Helper for Cartan section04 frozen_0031_Exercise_16: on the lens domain, differentiating the
dilogarithm-type series termwise yields `-log (1 - z) / z`. -/
theorem dilogarithmPowerSeries_hasDerivAt_on_domain {z : ℂ} (hz : z ∈ exercise16Domain) :
    HasDerivAt dilogarithmPowerSeries (-Complex.log (1 - z) / z) z := by
  have hz_norm : ‖z‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz.1
  have hz_ne : z ≠ 0 := Complex.slitPlane_ne_zero (exercise16Domain_mem_slitPlane hz).1
  exact hasDerivAt_dilogarithmPowerSeries hz_norm hz_ne

end Complex

/-- Helper for Cartan section04 frozen_0031_Exercise_16: the reflection function has derivative
`0` throughout the lens domain. -/
lemma hasDerivAt_reflection_function_zero
    {z : ℂ} (hz : z ∈ exercise16Domain) :
    HasDerivAt
      (fun w ↦
        Complex.dilogarithmPowerSeries w + Complex.dilogarithmPowerSeries (1 - w) +
          Complex.log w * Complex.log (1 - w))
      0 z := by
  rcases hz with ⟨hz_ball0, hz_ball1⟩
  have hz_norm : ‖z‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz_ball0
  have h1z_norm : ‖1 - z‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hz_ball1
  have hslit := exercise16Domain_mem_slitPlane ⟨hz_ball0, hz_ball1⟩
  rcases hslit with ⟨hz_slit, h1z_slit⟩
  have hz_ne : z ≠ 0 := Complex.slitPlane_ne_zero hz_slit
  have h1z_ne : 1 - z ≠ 0 := Complex.slitPlane_ne_zero h1z_slit
  have hdilog :
      HasDerivAt Complex.dilogarithmPowerSeries (-Complex.log (1 - z) / z) z :=
    hasDerivAt_dilogarithmPowerSeries hz_norm hz_ne
  have hdilog_comp :
      HasDerivAt (fun w ↦ Complex.dilogarithmPowerSeries (1 - w)) (Complex.log z / (1 - z)) z := by
    -- Differentiate the reflected dilogarithm by transporting through `w ↦ 1 - w`.
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_dilogarithmPowerSeries h1z_norm h1z_ne).comp_const_sub 1 z
  have hlog :
      HasDerivAt Complex.log z⁻¹ z :=
    Complex.hasDerivAt_log hz_slit
  have hlog_comp :
      HasDerivAt (fun w ↦ Complex.log (1 - w)) (-(1 - z)⁻¹) z := by
    -- Differentiate the second logarithm through the same affine involution.
    simpa using (Complex.hasDerivAt_log h1z_slit).comp_const_sub 1 z
  have hlog_mul :
      HasDerivAt (fun w ↦ Complex.log w * Complex.log (1 - w))
        (z⁻¹ * Complex.log (1 - z) + Complex.log z * (-(1 - z)⁻¹)) z :=
    hlog.mul hlog_comp
  have hsum :=
    hdilog.add hdilog_comp |>.add hlog_mul
  have hderiv_zero :
      -Complex.log (1 - z) / z + Complex.log z / (1 - z)
        + (z⁻¹ * Complex.log (1 - z) + -(Complex.log z * (1 - z)⁻¹)) = 0 := by
    -- After rewriting divisions as multiplications by inverses, the two pairs cancel.
    field_simp [div_eq_mul_inv, hz_ne, h1z_ne]
    ring
  have hsum' :
      HasDerivAt
        (fun w ↦
          Complex.dilogarithmPowerSeries w + Complex.dilogarithmPowerSeries (1 - w) +
            Complex.log w * Complex.log (1 - w))
        (-Complex.log (1 - z) / z + Complex.log z / (1 - z) +
          (z⁻¹ * Complex.log (1 - z) + -(Complex.log z * (1 - z)⁻¹))) z := by
    simpa using hsum
  simpa [hderiv_zero] using hsum'

/-- Exercise 16 (4): there exists a constant `a` such that on the lens-shaped domain
`D = {z : ℂ | ‖z‖ < 1 and ‖z - 1‖ < 1}` one has
`S(z) + S(1 - z) = a - log z log (1 - z)` for
`S = Complex.dilogarithmPowerSeries`. -/
theorem exercise16_exists_reflection_constant :
    ∃ a : ℂ, Exercise16ReflectionConstant a := by
  let F : ℂ → ℂ := fun w ↦
    Complex.dilogarithmPowerSeries w + Complex.dilogarithmPowerSeries (1 - w) +
      Complex.log w * Complex.log (1 - w)
  have hopen : IsOpen exercise16Domain := by
    -- The lens domain is the intersection of the two open unit balls centered at `0` and `1`.
    simpa [exercise16Domain] using
      (Metric.isOpen_ball.inter Metric.isOpen_ball :
        IsOpen (Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) 1))
  have hpreconnected : IsPreconnected exercise16Domain := by
    -- Convexity of the two balls gives preconnectedness of their intersection.
    simpa [exercise16Domain] using
      ((convex_ball (0 : ℂ) 1).inter (convex_ball (1 : ℂ) 1)).isPreconnected
  have hdiff : DifferentiableOn ℂ F exercise16Domain := by
    intro z hz
    exact (hasDerivAt_reflection_function_zero hz).differentiableAt.differentiableWithinAt
  have hfderiv : exercise16Domain.EqOn (fderiv ℂ F) 0 := by
    intro z hz
    simpa using (hasDerivAt_reflection_function_zero hz).hasFDerivAt.fderiv
  obtain ⟨a, ha⟩ := hopen.exists_is_const_of_fderiv_eq_zero hpreconnected hdiff hfderiv
  refine ⟨a, ?_⟩
  intro z hz
  -- Rearrange the constant value of the reflection function into the textbook identity.
  exact (eq_sub_iff_add_eq).2 <| by simpa [F] using ha z hz

/-- Helper for Cartan section04 frozen_0031_Exercise_16: the involution `x ↦ 1 - x` transports
the right-hand approach to `0` inside `(0,1)` to the left-hand approach to `1` inside `(0,1)`. -/
lemma exercise16_tendsto_one_sub_within_at_zero_to_one :
    Filter.Tendsto (fun x : ℝ ↦ 1 - x) (𝓝[Set.Ioo (0 : ℝ) 1] 0) (𝓝[Set.Ioo (0 : ℝ) 1] 1) := by
  -- Keep the source route: transport the Abel-limit term through the affine involution.
  have hid : Filter.Tendsto id (𝓝[Set.Ioo (0 : ℝ) 1] 0) (𝓝 0) :=
    tendsto_nhds_of_tendsto_nhdsWithin Filter.tendsto_id
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · simpa using (tendsto_const_nhds.sub hid)
  · refine eventually_nhdsWithin_of_forall fun x hx ↦ ?_
    exact ⟨sub_pos.2 hx.2, by linarith [hx.1]⟩

/-- Helper for Cartan section04 frozen_0031_Exercise_16: the real quotient `log (1 - x) / x`
tends to `-1` as `x → 0+` inside `(0,1)`. -/
lemma real_tendsto_log_one_sub_div_at_zero :
    Filter.Tendsto
      (fun x : ℝ ↦ Real.log (1 - x) / x)
      (𝓝[Set.Ioo (0 : ℝ) 1] 0)
      (𝓝 (-1)) := by
  -- Use the derivative of `x ↦ log (1 - x)` at `0` and read the quotient as the right slope.
  have hlog : HasDerivAt Real.log 1 1 := by
    simpa using Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
  have hderiv : HasDerivAt (fun x : ℝ ↦ Real.log (1 - x)) (-1) 0 := by
    have hlog' : HasDerivAt Real.log 1 (1 - 0 : ℝ) := by
      simpa using hlog
    simpa using HasDerivAt.comp_const_sub (a := (1 : ℝ)) (x := 0) hlog'
  rw [nhdsWithin_Ioo_eq_nhdsGT zero_lt_one]
  simpa [Real.log_one, div_eq_mul_inv, sub_eq_add_neg, mul_comm] using
    hderiv.tendsto_slope_zero_right

/-- Helper for Cartan section04 frozen_0031_Exercise_16: the complex quotient in the logarithmic
correction has the same endpoint limit `-1`. -/
lemma complex_tendsto_log_one_sub_div_at_zero :
    Filter.Tendsto
      (fun x : ℝ ↦ Complex.log ((1 - x : ℝ) : ℂ) / (x : ℂ))
      (𝓝[Set.Ioo (0 : ℝ) 1] 0)
      (𝓝 (-1)) := by
  -- This is just the real slope limit transported through `Complex.ofReal`.
  rw [nhdsWithin_Ioo_eq_nhdsGT zero_lt_one]
  have hreal :
      Filter.Tendsto (fun x : ℝ ↦ Real.log (1 - x) / x) (𝓝[>] (0 : ℝ)) (𝓝 (-1)) := by
    simpa [nhdsWithin_Ioo_eq_nhdsGT zero_lt_one] using real_tendsto_log_one_sub_div_at_zero
  have hofReal :
      Filter.Tendsto
        (Complex.ofReal ∘ fun x : ℝ ↦ Real.log (1 - x) / x)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.ofReal (-1 : ℝ))) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hcomplex :
      Filter.Tendsto
        (fun x : ℝ ↦ Complex.log ((1 - x : ℝ) : ℂ) / (x : ℂ))
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.ofReal (-1 : ℝ))) := by
    refine Filter.Tendsto.congr' ?_ hofReal
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
    calc
      (Complex.ofReal ∘ fun y : ℝ ↦ Real.log (1 - y) / y) x
          = Complex.ofReal (Real.log (1 - x) / x) := by
              rfl
      _ = ((Real.log (1 - x) : ℝ) : ℂ) / (x : ℂ) := by
            rw [Complex.ofReal_div]
      _ = Complex.log ((1 - x : ℝ) : ℂ) / (x : ℂ) := by
            rw [Complex.ofReal_log (sub_nonneg.mpr hx.2.le)]
  simpa using hcomplex

/-- Helper for Cartan section04 frozen_0031_Exercise_16: the shifted owner series extends
continuously to `0` from within `(0,1)`, where its value is `0` because of the prepended zero
coefficient. -/
lemma tendsto_ofScalarsSum_prependZero_real_within_at_zero :
    Filter.Tendsto
      (fun x : ℝ ↦ ofScalarsSum (prependZero exercise16Coeffs) (x : ℂ))
      (𝓝[Set.Ioo (0 : ℝ) 1] 0)
      (𝓝 0) := by
  have hprepend : Summable (prependZero exercise16Coeffs) := by
    -- Adjoining the initial zero term preserves summability of the coefficient sequence.
    have htail : Summable (fun n : ℕ ↦ prependZero exercise16Coeffs (n + 1)) := by
      simpa [prependZero] using summable_exercise16Coeffs
    exact (summable_nat_add_iff 1).1 htail
  have hnorm : Summable (fun n : ℕ ↦ ‖prependZero exercise16Coeffs n‖) := hprepend.norm
  have hcont :
      ContinuousOn
        (fun x : ℝ ↦ ∑' n : ℕ, prependZero exercise16Coeffs n * (x : ℂ) ^ n)
        (Set.Icc (0 : ℝ) 1) := by
    -- Use the same closed-interval `continuousOn_tsum` architecture as the Abel-limit proof.
    refine continuousOn_tsum (fun n ↦ ?_) hnorm fun n x hx ↦ ?_
    · exact (continuous_const.mul <| Complex.continuous_ofReal.pow n).continuousOn
    · have hx_norm_le : ‖(x : ℂ)‖ ≤ 1 := by
        simpa [RCLike.norm_ofReal, abs_of_nonneg hx.1] using hx.2
      calc
        ‖prependZero exercise16Coeffs n * (x : ℂ) ^ n‖
            = ‖prependZero exercise16Coeffs n‖ * ‖(x : ℂ) ^ n‖ := norm_mul _ _
        _ ≤ ‖prependZero exercise16Coeffs n‖ * 1 := by
            gcongr
            simpa [norm_pow] using pow_le_one₀ (norm_nonneg ((x : ℂ))) hx_norm_le
        _ = ‖prependZero exercise16Coeffs n‖ := by ring
  have hwithin :
      ContinuousWithinAt
        (fun x : ℝ ↦ ofScalarsSum (prependZero exercise16Coeffs) (x : ℂ))
        (Set.Ioo (0 : ℝ) 1) 0 := by
    -- Restrict the closed-interval continuity to the one-sided punctured approach to `0`.
    have hIcc :
        ContinuousWithinAt
          (fun x : ℝ ↦ ofScalarsSum (prependZero exercise16Coeffs) (x : ℂ))
          (Set.Icc (0 : ℝ) 1) 0 := by
      simpa [FormalMultilinearSeries.ofScalarsSum_eq_tsum, smul_eq_mul] using
        hcont.continuousWithinAt (by simp : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    exact hIcc.mono (Set.Ioo_subset_Icc_self)
  simpa [prependZero] using hwithin.tendsto

/-- Helper for Cartan section04 frozen_0031_Exercise_16: the first dilogarithm term tends to `0`
as `x → 0+` inside `(0,1)`. -/
lemma tendsto_dilogarithmPowerSeries_real_within_at_zero :
    Filter.Tendsto
      (fun x : ℝ ↦ Complex.dilogarithmPowerSeries (x : ℂ))
      (𝓝[Set.Ioo (0 : ℝ) 1] 0)
      (𝓝 0) := by
  -- Route correction: transfer the endpoint limit through the canonical shifted owner series.
  refine tendsto_nhdsWithin_congr ?_ tendsto_ofScalarsSum_prependZero_real_within_at_zero
  intro x hx
  rw [Complex.dilogarithmPowerSeries_eq_ofScalarsSum_prependZero]

/-- Helper for Cartan section04 frozen_0031_Exercise_16: the factor `log x * x` tends to `0`
for real `x → 0+`, viewed in `ℂ`. -/
lemma complex_tendsto_log_mul_real_at_zero :
    Filter.Tendsto
      (fun x : ℝ ↦ Complex.log (x : ℂ) * (x : ℂ))
      (𝓝[Set.Ioo (0 : ℝ) 1] 0)
      (𝓝 0) := by
  rw [nhdsWithin_Ioo_eq_nhdsGT zero_lt_one]
  have hreal :
      Filter.Tendsto (fun x : ℝ ↦ Real.log x * x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    -- This is the standard `x log x → 0` estimate on the positive side.
    simpa only [Real.rpow_one] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  have hofReal :
      Filter.Tendsto
        (fun x : ℝ ↦ ((Real.log x * x : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ))
        (𝓝 0) := by
    simpa only [Function.comp_apply] using
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hreal)
  refine tendsto_nhdsWithin_congr ?_ hofReal
  intro x hx
  calc
    (((Real.log x * x : ℝ)) : ℂ) = Complex.ofReal (Real.log x) * (x : ℂ) := by simp
    _ = Complex.log (x : ℂ) * (x : ℂ) := by rw [Complex.ofReal_log hx.le]

/-- Helper for Cartan section04 frozen_0031_Exercise_16: the logarithmic correction term tends
to `0` along `x → 0+`. -/
lemma tendsto_log_mul_log_one_sub_within_at_zero :
    Filter.Tendsto
      (fun x : ℝ ↦ Complex.log (x : ℂ) * Complex.log ((1 - x : ℝ) : ℂ))
      (𝓝[Set.Ioo (0 : ℝ) 1] 0)
      (𝓝 0) := by
  have hfactorized :
      Filter.Tendsto
        (fun x : ℝ ↦
          (Complex.log (x : ℂ) * (x : ℂ))
            * (Complex.log ((1 - x : ℝ) : ℂ) / (x : ℂ)))
        (𝓝[Set.Ioo (0 : ℝ) 1] 0)
        (𝓝 0) := by
    -- Separate the vanishing `x log x` factor from the bounded logarithmic quotient.
    simpa using complex_tendsto_log_mul_real_at_zero.mul complex_tendsto_log_one_sub_div_at_zero
  refine tendsto_nhdsWithin_congr ?_ hfactorized
  intro x hx
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.1.ne'
  calc
    (Complex.log (x : ℂ) * (x : ℂ)) * (Complex.log ((1 - x : ℝ) : ℂ) / (x : ℂ))
        = Complex.log (x : ℂ)
            * (((x : ℂ) * (x : ℂ)⁻¹) * Complex.log ((1 - x : ℝ) : ℂ)) := by
              rw [div_eq_mul_inv]
              ring
    _ = Complex.log (x : ℂ) * (1 * Complex.log ((1 - x : ℝ) : ℂ)) := by
          congr 1
          rw [mul_inv_cancel₀ hx0]
    _ = Complex.log (x : ℂ) * Complex.log ((1 - x : ℝ) : ℂ) := by simp

/-- Cartan section04 frozen_0031_Exercise_16: Exercise 16 (5) shows that every reflection
constant from part (4) is equal to `∑_{n ≥ 1} 1 / n^2`, written in Lean as
`∑_{n ≥ 0} 1 / (n + 1)^2`. -/
theorem exercise16_reflection_constant_eq_zeta_two
    {a : ℂ} (ha : Exercise16ReflectionConstant a) :
    a = ∑' n : ℕ, (1 : ℂ) / ((n + 1 : ℂ) ^ 2) := by
  have hprepend : Summable (prependZero exercise16Coeffs) := by
    -- The reflected endpoint term is still governed by the same shifted coefficient series.
    have htail : Summable (fun n : ℕ ↦ prependZero exercise16Coeffs (n + 1)) := by
      simpa [prependZero] using summable_exercise16Coeffs
    exact (summable_nat_add_iff 1).1 htail
  have hdomain :
      ∀ x ∈ Set.Ioo (0 : ℝ) 1, (x : ℂ) ∈ exercise16Domain := by
    intro x hx
    refine ⟨?_, ?_⟩
    · -- Real points with `0 < x < 1` lie in the first unit ball centered at `0`.
      simpa [Metric.mem_ball, dist_eq_norm, RCLike.norm_ofReal, abs_of_pos hx.1] using hx.2
    · -- The same interval condition gives `‖1 - x‖ < 1`, hence membership in the second ball.
      have hsub_lt : 1 - x < 1 := by linarith [hx.1]
      have hx_sub_neg : x - 1 < 0 := sub_neg.mpr hx.2
      have hnorm_ofReal : ‖((x - 1 : ℝ) : ℂ)‖ = |x - 1| := by
        simpa using (RCLike.norm_ofReal (K := ℂ) (x - 1))
      have hdist : ‖(x : ℂ) - 1‖ < 1 := by
        calc
          ‖(x : ℂ) - 1‖ = ‖((x - 1 : ℝ) : ℂ)‖ := by norm_num
          _ = |x - 1| := hnorm_ofReal
          _ = 1 - x := by
            rw [abs_of_neg hx_sub_neg]
            ring
          _ < 1 := hsub_lt
      simpa [Metric.mem_ball, dist_eq_norm] using hdist
  have hsecond_owner :
      Filter.Tendsto
        (fun x : ℝ ↦ ofScalarsSum (prependZero exercise16Coeffs) ((1 - x : ℝ) : ℂ))
        (𝓝[Set.Ioo (0 : ℝ) 1] 0)
        (𝓝 (∑' n : ℕ, prependZero exercise16Coeffs n)) := by
    -- Transport the Abel limit for the shifted owner series through `x ↦ 1 - x`.
    simpa only [Function.comp_apply] using
      (exercise16_tendsto_realAbelPowerSeriesSum_at_one
        (prependZero exercise16Coeffs) hprepend).comp
        exercise16_tendsto_one_sub_within_at_zero_to_one
  have hsecond :
      Filter.Tendsto
        (fun x : ℝ ↦ Complex.dilogarithmPowerSeries ((1 - x : ℝ) : ℂ))
        (𝓝[Set.Ioo (0 : ℝ) 1] 0)
        (𝓝 (∑' n : ℕ, prependZero exercise16Coeffs n)) := by
    -- Rewrite the reflected term back to the source-facing dilogarithm notation only once.
    refine tendsto_nhdsWithin_congr ?_ hsecond_owner
    intro x hx
    rw [Complex.dilogarithmPowerSeries_eq_ofScalarsSum_prependZero]
  have htotal :
      Filter.Tendsto
        (fun x : ℝ ↦
          Complex.dilogarithmPowerSeries (x : ℂ)
            + Complex.dilogarithmPowerSeries ((1 - x : ℝ) : ℂ)
            + Complex.log (x : ℂ) * Complex.log ((1 - x : ℝ) : ℂ))
        (𝓝[Set.Ioo (0 : ℝ) 1] 0)
        (𝓝 (∑' n : ℕ, prependZero exercise16Coeffs n)) := by
    -- The first term vanishes, the second tends to the coefficient sum, and the log correction
    -- disappears at the endpoint.
    simpa [add_assoc] using
      (tendsto_dilogarithmPowerSeries_real_within_at_zero.add hsecond).add
        tendsto_log_mul_log_one_sub_within_at_zero
  have hconst :
      Filter.Tendsto
        (fun _ : ℝ ↦ a)
        (𝓝[Set.Ioo (0 : ℝ) 1] 0)
        (𝓝 (∑' n : ℕ, prependZero exercise16Coeffs n)) := by
    -- On `(0,1)`, the reflection identity identifies the constant with the limiting expression.
    refine tendsto_nhdsWithin_congr ?_ htotal
    intro x hx
    have hx_reflection := ha (x : ℂ) (hdomain x hx)
    simpa [add_assoc] using (sub_eq_iff_eq_add.mp hx_reflection.symm).symm
  have hne : Filter.NeBot (𝓝[Set.Ioo (0 : ℝ) 1] 0) := by
    rw [nhdsWithin_Ioo_eq_nhdsGT zero_lt_one]
    infer_instance
  have ha_prepend :
      a = ∑' n : ℕ, prependZero exercise16Coeffs n := by
    exact tendsto_nhds_unique' hne tendsto_const_nhds hconst
  calc
    a = ∑' n : ℕ, prependZero exercise16Coeffs n := ha_prepend
    _ = ∑' n : ℕ, (1 : ℂ) / ((n + 1 : ℂ) ^ 2) := by
      -- Remove the prepended zero coefficient to recover the textbook zeta-value series.
      rw [hprepend.tsum_eq_zero_add]
      simp [prependZero, exercise16Coeffs]

-- Proof sketch: specialize the reflection identity at `z = 1 / 2`, rewrite both series terms as
-- the same value `S(1 / 2)`, and use part (5) together with `Complex.log (1 / 2) = - Complex.log 2`
-- on the principal branch.
/-- Helper for Exercise 16: the midpoint `1 / 2` belongs to the lens domain. -/
theorem exercise16_half_mem_domain : ((1 : ℂ) / 2) ∈ exercise16Domain := by
  constructor
  · -- The midpoint lies in the unit disk centered at `0`.
    norm_num [exercise16Domain, Metric.mem_ball, dist_eq_norm]
  · -- The same midpoint is also in the unit disk centered at `1`.
    norm_num [exercise16Domain, Metric.mem_ball, dist_eq_norm]

/-- Exercise 16 (6): every reflection constant from part (4) satisfies
`a - (log 2)^2 = ∑_{n ≥ 1} 1 / (n^2 2^(n - 1))`, reindexed over `ℕ`. -/
theorem exercise16_reflection_constant_sub_log_two_sq
    {a : ℂ} (ha : Exercise16ReflectionConstant a) :
    a - Complex.log 2 ^ 2 =
      ∑' n : ℕ, (1 : ℂ) / (((n + 1 : ℂ) ^ 2) * (2 : ℂ) ^ n) := by
  have hhalf := ha ((1 : ℂ) / 2) exercise16_half_mem_domain
  have hlog_half : Complex.log ((1 : ℂ) / 2) = -Complex.log (2 : ℂ) := by
    -- Rewrite the midpoint logarithm through the real identity `log (1/2) = -log 2`.
    calc
      Complex.log ((1 : ℂ) / 2) = (Real.log ((2 : ℝ)⁻¹) : ℂ) := by
        rw [show ((1 : ℂ) / 2) = (((2 : ℝ)⁻¹ : ℝ) : ℂ) by norm_num]
        rw [← Complex.ofReal_log (by positivity : 0 ≤ (2 : ℝ)⁻¹)]
      _ = -(Real.log (2 : ℝ) : ℂ) := by
        rw [Real.log_inv]
        simp
      _ = -Complex.log (2 : ℂ) := by
        have hlog_two : (Real.log (2 : ℝ) : ℂ) = Complex.log (2 : ℂ) := by
          rw [Complex.ofReal_log (by positivity : 0 ≤ (2 : ℝ))]
          norm_num
        simp [hlog_two]
  have hreflection' :
      (2 : ℂ) * Complex.dilogarithmPowerSeries ((1 : ℂ) / 2) = a - Complex.log (2 : ℂ) ^ 2 := by
    -- At the midpoint both dilogarithm terms coincide, and the logarithm square simplifies.
    rw [show (1 : ℂ) - (1 : ℂ) / 2 = (1 : ℂ) / 2 by norm_num, hlog_half] at hhalf
    simpa [pow_two, ← two_mul] using hhalf
  have htsum :
      (2 : ℂ) * Complex.dilogarithmPowerSeries ((1 : ℂ) / 2) =
        ∑' n : ℕ, (1 : ℂ) / (((n + 1 : ℂ) ^ 2) * (2 : ℂ) ^ n) := by
    -- Expand the midpoint dilogarithm series and simplify each coefficient.
    rw [Complex.dilogarithmPowerSeries_eq_tsum]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    have htwo : (2 : ℂ) ≠ 0 := by norm_num
    have hn : ((n + 1 : ℂ) ^ 2) ≠ 0 := by
      exact pow_ne_zero 2 (Nat.cast_add_one_ne_zero n)
    have hpow : ((1 : ℂ) / 2) ^ n * (2 : ℂ) ^ n = 1 := by
      rw [← mul_pow, show ((1 : ℂ) / 2 * 2) = 1 by field_simp [htwo], one_pow]
    field_simp [pow_succ, htwo, hn]
    rw [pow_succ]
    ring_nf
    exact hpow
  calc
    a - Complex.log (2 : ℂ) ^ 2 = (2 : ℂ) * Complex.dilogarithmPowerSeries ((1 : ℂ) / 2) :=
      hreflection'.symm
    _ = ∑' n : ℕ, (1 : ℂ) / (((n + 1 : ℂ) ^ 2) * (2 : ℂ) ^ n) := htsum

/-- Entry-point alias for the existence statement proved in this file. The surrounding file also
contains the Abel-summation and endpoint-limit ingredients used later in Exercise 16. -/
theorem cartan_section04_frozen_0031_Exercise_16 :
    ∃ a : ℂ, Exercise16ReflectionConstant a :=
  exercise16_exists_reflection_constant
