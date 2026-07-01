import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import cartan.I.section02.«0013_Proposition_7_1»

-- Declarations for this item will be appended below by the statement pipeline.

-- Owner triage:
-- * core/canonical: `FormalMultilinearSeries.ofScalarsSum`,
--   `FormalMultilinearSeries.ofScalarsSum_eq_tsum`,
--   `HasSumUniformlyOn.of_norm_le_summable`,
--   `Real.tendsto_tsum_powerSeries_nhdsWithin_lt`
-- * source-facing bridge: `Complex.dilogarithmPowerSeries`
-- * bridge/view predicate: `Exercise16ReflectionConstant`

noncomputable section

open Filter
open FormalMultilinearSeries
open scoped BigOperators Topology

/-- The domain `D = {z : ℂ | ‖z‖ < 1 and ‖z - 1‖ < 1}` from Exercise 16. -/
def exercise16Domain : Set ℂ :=
  Metric.ball (0 : ℂ) 1 ∩ Metric.ball (1 : ℂ) 1

namespace Complex

/-- The textbook dilogarithm-type series
`S(z) = ∑_{n ≥ 1} z^n / n^2`, realized as a thin source-facing bridge over the scalar-series
owner `FormalMultilinearSeries.ofScalarsSum`. -/
def dilogarithmPowerSeries (z : ℂ) : ℂ :=
  z * ofScalarsSum (fun n ↦ (1 : ℂ) / ((n + 1 : ℂ) ^ 2)) z

/-- The source-facing dilogarithm-type series agrees with its textbook `tsum` expansion. -/
theorem dilogarithmPowerSeries_eq_tsum (z : ℂ) :
    dilogarithmPowerSeries z = ∑' n : ℕ, z ^ (n + 1) / ((n + 1 : ℂ) ^ 2) := by
  -- Expand the owner series and absorb the front factor `z` into each term.
  rw [dilogarithmPowerSeries, FormalMultilinearSeries.ofScalarsSum_eq_tsum]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp [smul_eq_mul, div_eq_mul_inv, pow_succ, mul_assoc, mul_comm]

end Complex

open Complex

/-- A constant satisfying the reflection identity from Exercise 16 on `exercise16Domain`. -/
def Exercise16ReflectionConstant (a : ℂ) : Prop :=
  ∀ z ∈ exercise16Domain,
    dilogarithmPowerSeries z + dilogarithmPowerSeries (1 - z) = a - log z * log (1 - z)

/-- Helper for Exercise 16: the scalar coefficients of the dilogarithm series before the leading
shift. -/
def exercise16Coeffs : ℕ → ℂ :=
  fun n ↦ (1 : ℂ) / ((n + 1 : ℂ) ^ 2)

/-- Helper for Exercise 16: the coefficient sequence `1 / (n + 1)^2` is summable. -/
lemma summable_exercise16Coeffs : Summable exercise16Coeffs := by
  -- Compare the complex coefficients with the shifted real `p`-series `∑ 1 / (n + 1)^2`.
  refine Summable.of_norm ?_
  rw [show (fun n : ℕ ↦ ‖exercise16Coeffs n‖) =
      (fun n : ℕ ↦ (1 : ℝ) / ((n + 1 : ℝ) ^ 2)) by
        funext n
        calc
          ‖exercise16Coeffs n‖ = ‖(1 : ℂ) / ((n + 1 : ℂ) ^ 2)‖ := by
            rfl
          _ = (1 : ℝ) / ‖((n + 1 : ℂ) ^ 2)‖ := by simp
          _ = (1 : ℝ) / ((n + 1 : ℝ) ^ 2) := by
            rw [norm_pow]
            have habs : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
              simpa [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n + 1)
            have habs_sq : ‖(n : ℂ) + 1‖ ^ 2 = ((n : ℝ) + 1) ^ 2 := by
              exact congrArg (fun t : ℝ ↦ t ^ 2) habs
            rw [one_div, one_div]
            exact congrArg Inv.inv habs_sq]
  have hbase : Summable (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) ^ 2)) := by
    have hlt : (1 : ℝ) < 2 := by norm_num
    have hbase' : Summable (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ (2 : ℝ)) :=
      (Real.summable_one_div_nat_rpow (p := (2 : ℝ))).2 hlt
    convert hbase' using 1 with n
    simp
  have hshift : Summable (fun n : ℕ ↦ (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2)) :=
    (summable_nat_add_iff 1).2 hbase
  convert hshift using 1 with n
  simp [Nat.cast_add, Nat.cast_one]

/-- Helper for Exercise 16: the source-facing dilogarithm series is the shifted scalar owner
series obtained by prepending a zero coefficient. -/
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

/-- Helper for Exercise 16: points of norm `< 1` lie inside the convergence radius of the
prepended-zero owner series. -/
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

/-- Helper for Exercise 16: differentiating the prepended-zero coefficient sequence yields the
harmonic coefficients `1 / (n + 1)`. -/
lemma exercise16_derivCoeff_prependZero :
    ofScalarsDerivCoeff (prependZero exercise16Coeffs) = fun n : ℕ ↦ (1 : ℂ) / (n + 1 : ℂ) := by
  -- The leading zero is exactly what turns the derived coefficients into the harmonic sequence.
  funext n
  have hn : ((n + 1 : ℂ)) ≠ 0 := Nat.cast_add_one_ne_zero n
  calc
    ofScalarsDerivCoeff (prependZero exercise16Coeffs) n
        = (n + 1 : ℂ) * ((1 : ℂ) / ((n + 1 : ℂ) ^ 2)) := by
            simp [ofScalarsDerivCoeff, prependZero, exercise16Coeffs]
    _ = (1 : ℂ) / (n + 1 : ℂ) := by
      field_simp [hn, pow_two]

/-- Helper for Exercise 16: the differentiated dilogarithm series sums to
`-log (1 - z) / z` on the open unit disk away from `0`. -/
lemma hasSum_one_div_succ_eq_neg_log_div
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasSum (fun n : ℕ ↦ z ^ n / (n + 1 : ℂ)) (-log (1 - z) / z) := by
  have hshift :
      HasSum (fun n : ℕ ↦ z ^ (n + 1) / ((n + 1 : ℂ))) (-log (1 - z)) := by
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

section AbelSummation

variable {E : Type*} [NormedAddCommGroup E]

/-- Helper for Exercise 16: shifting a `range` sum by one rewrites it as the corresponding `Icc`
sum starting at `1`. -/
lemma sum_range_succ_eq_sum_Icc (f : ℕ → E) :
    ∀ n : ℕ, Finset.sum (Finset.range n) (fun i ↦ f (i + 1)) = Finset.sum (Finset.Icc 1 n) f
  | 0 => by
      -- Both indexing conventions are empty at the bottom.
      simp
  | n + 1 => by
      -- Peel off the last term on both sides and use the induction hypothesis on the prefix.
      rw [Finset.sum_range_succ, sum_range_succ_eq_sum_Icc]
      rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n))]

variable [NormedSpace ℝ E]

/-- Helper for Exercise 16: the zero-based Abel estimate follows from summation by parts on
`Finset.range`. -/
lemma norm_sum_range_smul_le_of_bdd_partial_sums
    (α : ℕ → E) (β : ℕ → ℝ) {M : ℝ}
    (hs : ∀ n : ℕ, ‖Finset.sum (Finset.range n) α‖ ≤ M)
    (hβ_nonneg : ∀ n : ℕ, 0 ≤ β n)
    (hβ_step : ∀ n : ℕ, β (n + 1) ≤ β n)
    (n : ℕ) :
    ‖Finset.sum (Finset.range n) (fun i ↦ β i • α i)‖ ≤ M * β 0 := by
  have hM : 0 ≤ M := by
    -- The empty partial sum already forces the ambient bound `M` to be nonnegative.
    simpa using hs 0
  have hneg :
      -∑ i ∈ Finset.range (n - 1), (β (i + 1) - β i) • ∑ j ∈ Finset.range (i + 1), α j
        = ∑ i ∈ Finset.range (n - 1), (β i - β (i + 1)) • ∑ j ∈ Finset.range (i + 1), α j := by
    -- Negating the Abel correction term flips each scalar difference.
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← neg_smul]
    ring
  calc
    ‖Finset.sum (Finset.range n) (fun i ↦ β i • α i)‖
        = ‖β (n - 1) • Finset.sum (Finset.range n) α
            + Finset.sum (Finset.range (n - 1))
                (fun i ↦ (β i - β (i + 1)) • Finset.sum (Finset.range (i + 1)) α)‖ := by
            -- Abel's finite summation-by-parts identity is the source decomposition here.
            rw [Finset.sum_range_by_parts β α n, sub_eq_add_neg, hneg]
    _ ≤ ‖β (n - 1) • Finset.sum (Finset.range n) α‖
        + ‖Finset.sum (Finset.range (n - 1))
            (fun i ↦ (β i - β (i + 1)) • Finset.sum (Finset.range (i + 1)) α)‖ := by
          exact norm_add_le _ _
    _ ≤ β (n - 1) * M
        + Finset.sum (Finset.range (n - 1)) (fun i ↦ (β i - β (i + 1)) * M) := by
          -- Each coefficient difference is nonnegative, so the triangle inequality gives the bound.
          refine add_le_add ?_ ?_
          · rw [norm_smul, Real.norm_of_nonneg (hβ_nonneg (n - 1))]
            exact mul_le_mul_of_nonneg_left (hs n) (hβ_nonneg (n - 1))
          · refine (norm_sum_le _ _).trans ?_
            refine Finset.sum_le_sum fun i hi ↦ ?_
            have hdiff_nonneg : 0 ≤ β i - β (i + 1) := sub_nonneg.mpr (hβ_step i)
            rw [norm_smul, Real.norm_of_nonneg hdiff_nonneg]
            exact mul_le_mul_of_nonneg_left (hs (i + 1)) hdiff_nonneg
    _ = M * (β (n - 1) + Finset.sum (Finset.range (n - 1)) (fun i ↦ (β i - β (i + 1)))) := by
          rw [← Finset.sum_mul]
          ring
    _ = M * β 0 := by
          -- The coefficients telescope exactly as in the textbook proof.
          rw [Finset.sum_range_sub' β (n - 1)]
          ring

/-- Exercise 16 (1): if the partial sums `∑_{i=1}^n α_i` are uniformly bounded by `M` and
`(β_n)` is a nonnegative decreasing real sequence, then
`‖∑_{i=1}^n β_i • α_i‖ ≤ M β₁` for every `n ≥ 1`. -/
theorem norm_sum_Icc_smul_le_of_bdd_partial_sums
    (α : ℕ → E) (β : ℕ → ℝ) {M : ℝ}
    (hs : ∀ n : ℕ, 1 ≤ n → ‖Finset.sum (Finset.Icc 1 n) α‖ ≤ M)
    (hβ_nonneg : ∀ n : ℕ, 1 ≤ n → 0 ≤ β n)
    (hβ_antitone : ∀ ⦃m n : ℕ⦄, 1 ≤ m → m ≤ n → β n ≤ β m)
    (n : ℕ) (_hn : 1 ≤ n) :
    ‖Finset.sum (Finset.Icc 1 n) (fun i ↦ β i • α i)‖ ≤ M * β 1 := by
  let α' : ℕ → E := fun i ↦ α (i + 1)
  let β' : ℕ → ℝ := fun i ↦ β (i + 1)
  have hM : 0 ≤ M := by
    -- The first partial sum already shows that `M` cannot be negative.
    exact (norm_nonneg _).trans (hs 1 (by omega))
  have hs' : ∀ k : ℕ, ‖Finset.sum (Finset.range k) α'‖ ≤ M := by
    intro k
    cases k with
    | zero =>
        simpa [α'] using hM
    | succ k =>
        -- Translate the shifted `range` partial sum back to the original `Icc` partial sum.
        simpa [α', sum_range_succ_eq_sum_Icc] using hs (k + 1) (by omega)
  have hβ_nonneg' : ∀ k : ℕ, 0 ≤ β' k := by
    intro k
    exact hβ_nonneg (k + 1) (by omega)
  have hβ_step' : ∀ k : ℕ, β' (k + 1) ≤ β' k := by
    intro k
    exact hβ_antitone (by omega) (by omega)
  -- Apply the zero-based Abel estimate to the shifted sequences.
  rw [← sum_range_succ_eq_sum_Icc (fun i ↦ β i • α i) n]
  simpa [α', β'] using
    norm_sum_range_smul_le_of_bdd_partial_sums α' β' hs' hβ_nonneg' hβ_step' n

end AbelSummation

section RealAbelPowerSeries

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Helper for Exercise 16: after a large index, every coefficient-tail partial sum is small,
uniformly in the starting point of the tail. -/
lemma tail_partial_sum_norm_lt_of_summable
    (a : ℕ → 𝕜) (ha : Summable a) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ p : ℕ, ‖Finset.sum (Finset.range p) (fun i ↦ a (m + i))‖ < ε := by
  have hnorm : Summable (fun n : ℕ ↦ ‖a n‖) := ha.norm
  have htail :
      Tendsto (fun m : ℕ ↦ ∑' i : ℕ, ‖a (m + i)‖) atTop (𝓝 0) := by
    simpa [add_comm] using (tendsto_sum_nat_add (fun n : ℕ ↦ ‖a n‖))
  -- Use the absolute tail to dominate every finite partial sum in the shifted series.
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 htail ε hε
  refine ⟨N, fun m hm p ↦ ?_⟩
  have hnorm_shift : Summable (fun i : ℕ ↦ ‖a (m + i)‖) := by
    simpa [add_comm] using ((summable_nat_add_iff m).2 hnorm)
  calc
    ‖Finset.sum (Finset.range p) (fun i ↦ a (m + i))‖
        ≤ ∑ i ∈ Finset.range p, ‖a (m + i)‖ := norm_sum_le _ _
    _ ≤ ∑' i : ℕ, ‖a (m + i)‖ := by
      exact hnorm_shift.sum_le_tsum (Finset.range p) (fun i _ ↦ norm_nonneg _)
    _ < ε := by
      simpa
        [Real.dist_eq, abs_of_nonneg (tsum_nonneg fun i ↦ norm_nonneg (a (m + i)))]
        using hN m hm

/-- Helper for Exercise 16: for `x ∈ [0,1]`, the scalar power series with coefficients `a n`
defines a summable sequence. -/
lemma summable_mul_pow_of_mem_unitInterval
    (a : ℕ → 𝕜) (ha : Summable a) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Summable (fun n : ℕ ↦ a n * (x : 𝕜) ^ n) := by
  have hnorm : Summable (fun n : ℕ ↦ ‖a n‖) := ha.norm
  have hx_norm_le : ‖(x : 𝕜)‖ ≤ 1 := by
    simpa [RCLike.norm_ofReal, abs_of_nonneg hx.1] using hx.2
  -- Compare the power-series terms with the absolutely summable coefficient norms.
  refine Summable.of_norm_bounded hnorm fun n ↦ ?_
  calc
    ‖a n * (x : 𝕜) ^ n‖ = ‖a n‖ * ‖(x : 𝕜) ^ n‖ := norm_mul _ _
    _ ≤ ‖a n‖ * 1 := by
      gcongr
      simpa [norm_pow] using pow_le_one₀ (norm_nonneg ((x : 𝕜))) hx_norm_le
    _ = ‖a n‖ := by ring

/-- Helper for Exercise 16: on `[0,1]`, the coefficient series sums to the canonical owner
`ofScalarsSum`. -/
lemma hasSum_mul_pow_of_mem_unitInterval
    (a : ℕ → 𝕜) (ha : Summable a) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ ↦ a n * (x : 𝕜) ^ n) (ofScalarsSum a (x : 𝕜)) := by
  have hs : Summable (fun n : ℕ ↦ a n * (x : 𝕜) ^ n) :=
    summable_mul_pow_of_mem_unitInterval a ha hx
  -- The owner `ofScalarsSum` is exactly the textbook scalar series on `[0,1]`.
  rw [Summable.hasSum_iff hs]
  simp [FormalMultilinearSeries.ofScalarsSum_eq_tsum, smul_eq_mul]

/-- Helper for Exercise 16: sufficiently deep power-series tails are uniformly small on `[0,1]`. -/
lemma tail_norm_le_of_summable_on_unitInterval
    (a : ℕ → 𝕜) (ha : Summable a) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖∑' i : ℕ, a (n + i) * (x : 𝕜) ^ (n + i)‖ < ε := by
  have hnorm : Summable (fun n : ℕ ↦ ‖a n‖) := ha.norm
  have htail :
      Tendsto (fun n : ℕ ↦ ∑' i : ℕ, ‖a (n + i)‖) atTop (𝓝 0) := by
    simpa [add_comm] using (tendsto_sum_nat_add (fun n : ℕ ↦ ‖a n‖))
  -- The norm of every tail is bounded by the corresponding scalar tail of `‖a n‖`.
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 htail ε hε
  refine ⟨N, fun n hn x hx ↦ ?_⟩
  have hnorm_shift : Summable (fun i : ℕ ↦ ‖a (n + i)‖) := by
    simpa [add_comm] using ((summable_nat_add_iff n).2 hnorm)
  have hs : Summable (fun i : ℕ ↦ a (n + i) * (x : 𝕜) ^ (n + i)) := by
    have hx_norm_le : ‖(x : 𝕜)‖ ≤ 1 := by
      simpa [RCLike.norm_ofReal, abs_of_nonneg hx.1] using hx.2
    -- Compare the shifted tail with the shifted coefficient norms.
    refine Summable.of_norm_bounded hnorm_shift fun i ↦ ?_
    calc
      ‖a (n + i) * (x : 𝕜) ^ (n + i)‖ = ‖a (n + i)‖ * ‖(x : 𝕜) ^ (n + i)‖ := norm_mul _ _
      _ ≤ ‖a (n + i)‖ * 1 := by
        gcongr
        simpa [norm_pow] using pow_le_one₀ (norm_nonneg ((x : 𝕜))) hx_norm_le
      _ = ‖a (n + i)‖ := by ring
  have hbound :
      ‖∑' i : ℕ, a (n + i) * (x : 𝕜) ^ (n + i)‖ ≤ ∑' i : ℕ, ‖a (n + i)‖ := by
    have hsum_terms := hs.hasSum
    have hsum_norms : HasSum (fun i : ℕ ↦ ‖a (n + i)‖) (∑' i : ℕ, ‖a (n + i)‖) :=
      hnorm_shift.hasSum
    refine hsum_terms.norm_le_of_bounded hsum_norms fun i ↦ ?_
    have hx_norm_le : ‖(x : 𝕜)‖ ≤ 1 := by
      simpa [RCLike.norm_ofReal, abs_of_nonneg hx.1] using hx.2
    calc
      ‖a (n + i) * (x : 𝕜) ^ (n + i)‖ = ‖a (n + i)‖ * ‖(x : 𝕜) ^ (n + i)‖ := norm_mul _ _
      _ ≤ ‖a (n + i)‖ * 1 := by
        gcongr
        simpa [norm_pow] using pow_le_one₀ (norm_nonneg ((x : 𝕜))) hx_norm_le
      _ = ‖a (n + i)‖ := by ring
  exact lt_of_le_of_lt hbound <|
    by
      simpa
        [Real.dist_eq, abs_of_nonneg (tsum_nonneg fun i ↦ norm_nonneg (a (n + i)))]
        using hN n hn

/-- Exercise 16 (2): if the coefficient series `∑ a_n` converges, then the series
`∑ a_n x^n` is uniformly convergent on `[0, 1]`, with sum given by the canonical scalar-series
owner `ofScalarsSum`. -/
theorem exercise16_uniform_hasSumOn_unitInterval
    (a : ℕ → 𝕜) (ha : Summable a) :
    HasSumUniformlyOn
      (fun n (x : ℝ) ↦ a n * (x : 𝕜) ^ n)
      (fun x : ℝ ↦ ofScalarsSum a (x : 𝕜))
      (Set.Icc (0 : ℝ) 1) := by
  have hnorm : Summable (fun n : ℕ ↦ ‖a n‖) := ha.norm
  -- Absolute coefficient control gives uniform convergence on the whole closed interval.
  simpa [FormalMultilinearSeries.ofScalarsSum_eq_tsum, smul_eq_mul] using
    (HasSumUniformlyOn.of_norm_le_summable (u := fun n : ℕ ↦ ‖a n‖) hnorm
      (s := Set.Icc (0 : ℝ) 1) fun n x hx ↦ by
        have hx_norm_le : ‖(x : 𝕜)‖ ≤ 1 := by
          simpa [RCLike.norm_ofReal, abs_of_nonneg hx.1] using hx.2
        calc
          ‖a n * (x : 𝕜) ^ n‖ = ‖a n‖ * ‖(x : 𝕜) ^ n‖ := norm_mul _ _
          _ ≤ ‖a n‖ * 1 := by
            gcongr
            simpa [norm_pow] using pow_le_one₀ (norm_nonneg ((x : 𝕜))) hx_norm_le
          _ = ‖a n‖ := by ring)

/-- Exercise 16 (3): under the hypotheses of part (2), the sum of the power series tends to
`∑ a_n` as `x → 1` with `0 < x < 1`. -/
theorem exercise16_tendsto_realAbelPowerSeriesSum_at_one
    (a : ℕ → 𝕜) (ha : Summable a) :
    Tendsto
      (fun x : ℝ ↦ ofScalarsSum a (x : 𝕜))
      (𝓝[Set.Ioo (0 : ℝ) 1] (1 : ℝ))
      (𝓝 (∑' n : ℕ, a n)) := by
  have hnorm : Summable (fun n : ℕ ↦ ‖a n‖) := ha.norm
  have hcont :
      ContinuousOn (fun x : ℝ ↦ ∑' n : ℕ, a n * (x : 𝕜) ^ n) (Set.Icc (0 : ℝ) 1) := by
    refine continuousOn_tsum (fun n ↦ ?_) hnorm fun n x hx ↦ ?_
    · exact (continuous_const.mul <| (RCLike.continuous_ofReal.pow n)).continuousOn
    · have hx_norm_le : ‖(x : 𝕜)‖ ≤ 1 := by
        simpa [RCLike.norm_ofReal, abs_of_nonneg hx.1] using hx.2
      calc
        ‖a n * (x : 𝕜) ^ n‖ = ‖a n‖ * ‖(x : 𝕜) ^ n‖ := norm_mul _ _
        _ ≤ ‖a n‖ * 1 := by
          gcongr
          simpa [norm_pow] using pow_le_one₀ (norm_nonneg ((x : 𝕜))) hx_norm_le
        _ = ‖a n‖ := by ring
  have hwithin :
      ContinuousWithinAt (fun x : ℝ ↦ ofScalarsSum a (x : 𝕜)) (Set.Ioo (0 : ℝ) 1) 1 := by
    -- Restrict continuity from the closed interval to the punctured one-sided approach region.
    have hIcc :
        ContinuousWithinAt (fun x : ℝ ↦ ofScalarsSum a (x : 𝕜)) (Set.Icc (0 : ℝ) 1) 1 := by
      simpa [FormalMultilinearSeries.ofScalarsSum_eq_tsum, smul_eq_mul] using
        hcont.continuousWithinAt (by simp : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    exact hIcc.mono (Set.Ioo_subset_Icc_self)
  simpa [FormalMultilinearSeries.ofScalarsSum_eq_tsum, smul_eq_mul] using hwithin.tendsto

end RealAbelPowerSeries

/-- Helper for Exercise 16: points of the lens domain and their complements `1 - z`
both lie in the complex slit plane. -/
lemma exercise16Domain_mem_slitPlane {z : ℂ} (hz : z ∈ exercise16Domain) :
    z ∈ Complex.slitPlane ∧ (1 - z) ∈ Complex.slitPlane := by
  rcases hz with ⟨hz0, hz1⟩
  refine ⟨Complex.ball_one_subset_slitPlane hz1, ?_⟩
  -- Recenter the unit-disk condition at `1` to place `1 - z` in the slit plane.
  simpa [sub_eq_add_neg] using
    (Complex.mem_slitPlane_of_norm_lt_one (z := -z) <|
      by simpa [Metric.mem_ball, norm_neg] using hz0)

/-- Helper for Exercise 16: on the open unit disk away from `0`, the dilogarithm series has
derivative `-log (1-z) / z`. -/
lemma hasDerivAt_dilogarithmPowerSeries
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasDerivAt dilogarithmPowerSeries (-log (1 - z) / z) z := by
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
        -log (1 - z) / z := by
    -- Rewrite the derivative sum to the textbook harmonic series and invoke the logarithmic sum.
    rw [exercise16_derivCoeff_prependZero, FormalMultilinearSeries.ofScalarsSum_eq_tsum]
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (hasSum_one_div_succ_eq_neg_log_div hz hz0).tsum_eq
  have hfun :
      dilogarithmPowerSeries = ofScalarsSum (prependZero exercise16Coeffs) :=
    funext dilogarithmPowerSeries_eq_ofScalarsSum_prependZero
  simpa [hfun, hvalue] using howner

/-- Helper for Exercise 16: the reflection function has derivative `0` throughout the lens
domain. -/
lemma hasDerivAt_reflection_function_zero
    {z : ℂ} (hz : z ∈ exercise16Domain) :
    HasDerivAt
      (fun w ↦ dilogarithmPowerSeries w
        + dilogarithmPowerSeries (1 - w)
        + log w * log (1 - w))
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
      HasDerivAt dilogarithmPowerSeries (-log (1 - z) / z) z :=
    hasDerivAt_dilogarithmPowerSeries hz_norm hz_ne
  have hdilog_comp :
      HasDerivAt (fun w ↦ dilogarithmPowerSeries (1 - w)) (log z / (1 - z)) z := by
    -- The second dilogarithm term is the same derivative evaluated at `1 - z`, then transported
    -- through the affine involution `w ↦ 1 - w`.
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_dilogarithmPowerSeries h1z_norm h1z_ne).comp_const_sub 1 z
  have hlog :
      HasDerivAt log z⁻¹ z :=
    Complex.hasDerivAt_log hz_slit
  have hlog_comp :
      HasDerivAt (fun w ↦ log (1 - w)) (-(1 - z)⁻¹) z := by
    -- Differentiate the logarithm on the second slit-plane factor through `1 - w`.
    simpa using (Complex.hasDerivAt_log h1z_slit).comp_const_sub 1 z
  have hlog_mul :
      HasDerivAt (fun w ↦ log w * log (1 - w))
        (z⁻¹ * log (1 - z) + log z * (-(1 - z)⁻¹)) z :=
    hlog.mul hlog_comp
  have hsum :=
    hdilog.add hdilog_comp |>.add hlog_mul
  have hderiv_zero :
      -log (1 - z) / z + log z / (1 - z)
        + (z⁻¹ * log (1 - z) + -(log z * (1 - z)⁻¹)) = 0 := by
    -- After rewriting divisions as multiplications by inverses, the two pairs cancel.
    field_simp [div_eq_mul_inv, hz_ne, h1z_ne]
    ring
  have hsum' :
      HasDerivAt
        (fun w ↦ dilogarithmPowerSeries w
          + dilogarithmPowerSeries (1 - w)
          + log w * log (1 - w))
        (-log (1 - z) / z + log z / (1 - z)
          + (z⁻¹ * log (1 - z) + -(log z * (1 - z)⁻¹))) z := by
    simpa using hsum
  simpa [hderiv_zero] using hsum'

/-- Exercise 16 (4): on `exercise16Domain`, the dilogarithm-style series satisfies the reflection
identity for some constant. -/
theorem exists_dilog_reflection_constant_on_exercise16Domain :
    ∃ a : ℂ, Exercise16ReflectionConstant a := by
  let F : ℂ → ℂ := fun w ↦
    dilogarithmPowerSeries w + dilogarithmPowerSeries (1 - w) + log w * log (1 - w)
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

/-- Helper for Exercise 16: the involution `x ↦ 1 - x` transports the right-hand approach to
`0` inside `(0,1)` to the left-hand approach to `1` inside `(0,1)`. -/
lemma exercise16_tendsto_one_sub_within_at_zero_to_one :
    Tendsto (fun x : ℝ ↦ 1 - x) (𝓝[Set.Ioo (0 : ℝ) 1] 0) (𝓝[Set.Ioo (0 : ℝ) 1] 1) := by
  -- Keep the source route: transport the Abel-limit term through the affine involution.
  have hid : Tendsto (fun x : ℝ ↦ x) (𝓝[Set.Ioo (0 : ℝ) 1] 0) (𝓝 0) :=
    tendsto_nhds_of_tendsto_nhdsWithin tendsto_id
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · simpa using (tendsto_const_nhds.sub hid)
  · refine eventually_nhdsWithin_of_forall fun x hx ↦ ?_
    exact ⟨sub_pos.2 hx.2, by linarith [hx.1]⟩

/-- Helper for Exercise 16: the real quotient `log (1 - x) / x` tends to `-1` as `x → 0+`
inside `(0,1)`. -/
lemma real_tendsto_log_one_sub_div_at_zero :
    Tendsto
      (fun x : ℝ ↦ Real.log (1 - x) / x)
      (𝓝[Set.Ioo (0 : ℝ) 1] 0)
      (𝓝 (-1)) := by
  -- Use the derivative of `x ↦ log (1 - x)` at `0` and read the quotient as the right slope.
  have hlog : HasDerivAt Real.log 1 1 := by
    simpa using Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
  have hsub : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) 0 := by
    simpa using (hasDerivAt_id 0).const_sub 1
  have hderiv : HasDerivAt (fun x : ℝ ↦ Real.log (1 - x)) (-1) 0 := by
    have hlog' : HasDerivAt Real.log 1 (1 - 0 : ℝ) := by
      simpa using hlog
    simpa using HasDerivAt.comp_const_sub (a := (1 : ℝ)) (x := 0) hlog'
  rw [nhdsWithin_Ioo_eq_nhdsGT zero_lt_one]
  simpa [Real.log_one, div_eq_mul_inv, sub_eq_add_neg, mul_comm] using
    hderiv.tendsto_slope_zero_right

/-- Helper for Exercise 16: the complex quotient in the logarithmic correction has the same
endpoint limit `-1`. -/
lemma complex_tendsto_log_one_sub_div_at_zero :
    Tendsto
      (fun x : ℝ ↦ Complex.log ((1 - x : ℝ) : ℂ) / (x : ℂ))
      (𝓝[Set.Ioo (0 : ℝ) 1] 0)
      (𝓝 (-1)) := by
  -- This is just the real slope limit transported through `Complex.ofReal`.
  rw [nhdsWithin_Ioo_eq_nhdsGT zero_lt_one]
  have hreal :
      Tendsto (fun x : ℝ ↦ Real.log (1 - x) / x) (𝓝[>] (0 : ℝ)) (𝓝 (-1)) := by
    simpa [nhdsWithin_Ioo_eq_nhdsGT zero_lt_one] using real_tendsto_log_one_sub_div_at_zero
  have hofReal :
      Tendsto
        (Complex.ofReal ∘ fun x : ℝ ↦ Real.log (1 - x) / x)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.ofReal (-1 : ℝ))) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hcomplex :
      Tendsto
        (fun x : ℝ ↦ Complex.log ((1 - x : ℝ) : ℂ) / (x : ℂ))
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.ofReal (-1 : ℝ))) := by
    refine Tendsto.congr' ?_ hofReal
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

/-- Helper for Exercise 16: the shifted owner series extends continuously to `0` from within
`(0,1)`, where its value is `0` because of the prepended zero coefficient. -/
lemma tendsto_ofScalarsSum_prependZero_real_within_at_zero :
    Tendsto
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

/-- Helper for Exercise 16: the first dilogarithm term tends to `0` as `x → 0+` inside
`(0,1)`. -/
lemma tendsto_dilogarithmPowerSeries_real_within_at_zero :
    Tendsto
      (fun x : ℝ ↦ dilogarithmPowerSeries (x : ℂ))
      (𝓝[Set.Ioo (0 : ℝ) 1] 0)
      (𝓝 0) := by
  -- Route correction: transfer the endpoint limit through the canonical shifted owner series.
  refine tendsto_nhdsWithin_congr ?_ tendsto_ofScalarsSum_prependZero_real_within_at_zero
  intro x hx
  rw [dilogarithmPowerSeries_eq_ofScalarsSum_prependZero]

/-- Helper for Exercise 16: the factor `log x * x` tends to `0` for real `x → 0+`, viewed in
`ℂ`. -/
lemma complex_tendsto_log_mul_real_at_zero :
    Tendsto
      (fun x : ℝ ↦ Complex.log (x : ℂ) * (x : ℂ))
      (𝓝[Set.Ioo (0 : ℝ) 1] 0)
      (𝓝 0) := by
  rw [nhdsWithin_Ioo_eq_nhdsGT zero_lt_one]
  have hreal :
      Tendsto (fun x : ℝ ↦ Real.log x * x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    -- This is the standard `x log x → 0` estimate on the positive side.
    simpa only [Real.rpow_one] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  have hofReal :
      Tendsto
        (fun x : ℝ ↦ ((Real.log x * x : ℝ) : ℂ))
        (𝓝[>] (0 : ℝ))
        (𝓝 0) := by
    simpa only [Function.comp_apply] using
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hreal)
  refine tendsto_nhdsWithin_congr ?_ hofReal
  intro x hx
  calc
    (((Real.log x * x : ℝ)) : ℂ) = (Complex.ofReal (Real.log x)) * (x : ℂ) := by simp
    _ = Complex.log (x : ℂ) * (x : ℂ) := by rw [Complex.ofReal_log hx.le]

/-- Helper for Exercise 16: the logarithmic correction term tends to `0` along `x → 0+`. -/
lemma tendsto_log_mul_log_one_sub_within_at_zero :
    Tendsto
      (fun x : ℝ ↦ Complex.log (x : ℂ) * Complex.log ((1 - x : ℝ) : ℂ))
      (𝓝[Set.Ioo (0 : ℝ) 1] 0)
      (𝓝 0) := by
  have hfactorized :
      Tendsto
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

/-- Exercise 16 (5): any constant appearing in the reflection identity of part (4) is the sum
`∑_{n≥1} 1 / n^2`. -/
theorem dilog_reflection_constant_eq_tsum_one_div_sq
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
      Tendsto
        (fun x : ℝ ↦ ofScalarsSum (prependZero exercise16Coeffs) ((1 - x : ℝ) : ℂ))
        (𝓝[Set.Ioo (0 : ℝ) 1] 0)
        (𝓝 (∑' n : ℕ, prependZero exercise16Coeffs n)) := by
    -- Transport the Abel limit for the shifted owner series through `x ↦ 1 - x`.
    simpa only [Function.comp_apply] using
      (exercise16_tendsto_realAbelPowerSeriesSum_at_one
        (prependZero exercise16Coeffs) hprepend).comp
        exercise16_tendsto_one_sub_within_at_zero_to_one
  have hsecond :
      Tendsto
        (fun x : ℝ ↦ dilogarithmPowerSeries ((1 - x : ℝ) : ℂ))
        (𝓝[Set.Ioo (0 : ℝ) 1] 0)
        (𝓝 (∑' n : ℕ, prependZero exercise16Coeffs n)) := by
    -- Rewrite the reflected term back to the source-facing dilogarithm notation only once.
    refine tendsto_nhdsWithin_congr ?_ hsecond_owner
    intro x hx
    rw [dilogarithmPowerSeries_eq_ofScalarsSum_prependZero]
  have htotal :
      Tendsto
        (fun x : ℝ ↦
          dilogarithmPowerSeries (x : ℂ)
            + dilogarithmPowerSeries ((1 - x : ℝ) : ℂ)
            + Complex.log (x : ℂ) * Complex.log ((1 - x : ℝ) : ℂ))
        (𝓝[Set.Ioo (0 : ℝ) 1] 0)
        (𝓝 (∑' n : ℕ, prependZero exercise16Coeffs n)) := by
    -- The first term vanishes, the second tends to the coefficient sum, and the log correction
    -- disappears at the endpoint.
    simpa [add_assoc] using
      (tendsto_dilogarithmPowerSeries_real_within_at_zero.add hsecond).add
        tendsto_log_mul_log_one_sub_within_at_zero
  have hconst :
      Tendsto
        (fun _ : ℝ ↦ a)
        (𝓝[Set.Ioo (0 : ℝ) 1] 0)
        (𝓝 (∑' n : ℕ, prependZero exercise16Coeffs n)) := by
    -- On `(0,1)`, the reflection identity identifies the constant with the limiting expression.
    refine tendsto_nhdsWithin_congr ?_ htotal
    intro x hx
    have hx_reflection := ha (x : ℂ) (hdomain x hx)
    simpa [add_assoc] using (sub_eq_iff_eq_add.mp hx_reflection.symm).symm
  have hne : NeBot (𝓝[Set.Ioo (0 : ℝ) 1] 0) := by
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

/-- Exercise 16 (6): evaluating the reflection identity at `z = 1 / 2` gives
`a - (log 2)^2 = ∑_{n≥1} 1 / (n^2 2^{n-1})`. -/
theorem dilog_reflection_constant_sub_log_two_sq_eq_tsum
    {a : ℂ} (ha : Exercise16ReflectionConstant a) :
    a - log (2 : ℂ) ^ 2 =
      ∑' n : ℕ, (1 : ℂ) / (((n + 1 : ℂ) ^ 2) * (2 : ℂ) ^ n) := by
  have hhalf_mem : ((1 : ℂ) / 2) ∈ exercise16Domain := by
    refine ⟨?_, ?_⟩
    · simpa [exercise16Domain, Metric.mem_ball, dist_eq_norm] using
        (by norm_num : ‖((1 : ℂ) / 2 : ℂ)‖ < 1)
    · simpa [exercise16Domain, Metric.mem_ball, dist_eq_norm] using
        (by norm_num : ‖((1 : ℂ) / 2) - 1‖ < 1)
  have hlog_half : log ((1 : ℂ) / 2) = -log (2 : ℂ) := by
    -- Rewrite the midpoint logarithm through the real logarithm identity `log (1/2) = - log 2`.
    calc
      log ((1 : ℂ) / 2) = (Real.log ((2 : ℝ)⁻¹) : ℂ) := by
        rw [show ((1 : ℂ) / 2) = (((2 : ℝ)⁻¹ : ℝ) : ℂ) by norm_num]
        rw [← Complex.ofReal_log (by positivity : 0 ≤ (2 : ℝ)⁻¹)]
      _ = -(Real.log (2 : ℝ) : ℂ) := by
        rw [Real.log_inv]
        simp
      _ = -log (2 : ℂ) := by
        have hlog_two : (Real.log (2 : ℝ) : ℂ) = log (2 : ℂ) := by
          rw [Complex.ofReal_log (by positivity : 0 ≤ (2 : ℝ))]
          norm_num
        simp [hlog_two]
  have hreflection := ha ((1 : ℂ) / 2) hhalf_mem
  have hreflection' : 2 * dilogarithmPowerSeries ((1 : ℂ) / 2) = a - log (2 : ℂ) ^ 2 := by
    -- At the midpoint both dilogarithm terms coincide, and the logarithm square simplifies.
    rw [show (1 : ℂ) - (1 : ℂ) / 2 = (1 : ℂ) / 2 by norm_num, hlog_half] at hreflection
    simpa [pow_two, ← two_mul] using hreflection
  have htsum :
      2 * dilogarithmPowerSeries ((1 : ℂ) / 2) =
        ∑' n : ℕ, (1 : ℂ) / (((n + 1 : ℂ) ^ 2) * (2 : ℂ) ^ n) := by
    -- Expand the midpoint dilogarithm series and simplify each coefficient.
    rw [dilogarithmPowerSeries_eq_tsum]
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
    a - log (2 : ℂ) ^ 2 = 2 * dilogarithmPowerSeries ((1 : ℂ) / 2) := hreflection'.symm
    _ = ∑' n : ℕ, (1 : ℂ) / (((n + 1 : ℂ) ^ 2) * (2 : ℂ) ^ n) := htsum
