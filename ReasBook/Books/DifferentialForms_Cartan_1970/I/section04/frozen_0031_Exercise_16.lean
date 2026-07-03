import Mathlib
import DifferentialForms_Cartan_1970.I.section02.«frozen_0007_Example_I_2_extra_5»
import DifferentialForms_Cartan_1970.I.section02.«frozen_0013_Proposition_7_1»
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
  have hAtOne : ofScalarsSum a (1 : 𝕜) = ∑' n : ℕ, a n := by
    -- Evaluate the scalar power series at `1`.
    rw [ofScalars_sum_eq]
    simp
  have hcont : ContinuousOn (fun x : ℝ ↦ ofScalarsSum a (x : 𝕜)) (Set.Icc (0 : ℝ) 1) := by
    -- The same summable majorant from part (2) gives continuity of the summed function.
    rw [ofScalarsSum_eq_tsum]
    refine continuousOn_tsum (fun n ↦ ?_) ha.norm ?_
    · simpa [smul_eq_mul] using
        (show ContinuousOn (fun x : ℝ ↦ a n * (x : 𝕜) ^ n) (Set.Icc (0 : ℝ) 1) from
          ((continuous_const : Continuous fun _ : ℝ ↦ a n).mul (RCLike.continuous_ofReal.pow n))
            .continuousOn)
    · intro n x hx
      simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
        exercise16_term_norm_le_coeff_norm_on_unitInterval a n hx
  have hlim :
      Filter.Tendsto (fun x : ℝ ↦ ofScalarsSum a (x : 𝕜)) (𝓝[Set.Ioo (0 : ℝ) 1] 1)
        (𝓝 (ofScalarsSum a (1 : 𝕜))) := by
    -- Restrict the continuous extension on `[0,1]` to the left-hand approach through `(0,1)`.
    simpa [ContinuousWithinAt] using
      (hcont.continuousWithinAt (Set.right_mem_Icc.2 zero_le_one)).mono Set.Ioo_subset_Icc_self
  simpa [hAtOne] using hlim

end RealAbelPowerSeries

-- Proof sketch: differentiate the two dilogarithm-type series termwise on `exercise16Domain`,
-- use Proposition 6.1 to identify the derivatives with logarithms, compare with the derivative
-- of `-log z * log (1 - z)`, and conclude that the difference is constant on the connected
-- domain `exercise16Domain`.
/-! The remaining complex part follows the textbook route exactly: first rewrite the
source-facing dilogarithm as one scalar power series, then differentiate termwise and
apply the zero-derivative constancy theorem on the lens domain. -/

/-- Helper for Exercise 16: the lens domain is stable under the involution `z ↦ 1 - z`. -/
theorem exercise16Domain_one_sub {z : ℂ} (hz : z ∈ exercise16Domain) :
    1 - z ∈ exercise16Domain := by
  rcases hz with ⟨hz0, hz1⟩
  constructor
  · -- The first ball condition comes from the second one after reversing the subtraction order.
    simpa [exercise16Domain, Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hz1
  · -- The second ball condition is just the original bound `‖z‖ < 1`.
    have hz0' : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz0
    simpa [Metric.mem_ball, dist_eq_norm] using (show ‖-z‖ < 1 by simpa using hz0')

/-- Helper for Exercise 16: every point of the lens domain lies in the slit plane, so the
principal logarithm is differentiable there. -/
theorem exercise16Domain_mem_slitPlane {z : ℂ} (hz : z ∈ exercise16Domain) :
    z ∈ Complex.slitPlane :=
  Complex.ball_one_subset_slitPlane hz.2

/-- Helper for Exercise 16: if `z` lies in the lens domain, then so does `1 - z`, hence both
logarithms in the reflection identity stay on the principal branch. -/
theorem exercise16Domain_one_sub_mem_slitPlane {z : ℂ} (hz : z ∈ exercise16Domain) :
    1 - z ∈ Complex.slitPlane := by
  -- The first ball condition gives `‖z‖ < 1`, which is exactly the slit-plane criterion for `1-z`.
  simpa [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one (by simpa using hz.1)

namespace Complex

/-- Helper for Exercise 16: the dilogarithm-type series is the scalar power series with vanishing
constant coefficient and coefficient `1 / n^2` in degree `n ≥ 1`. -/
theorem dilogarithmPowerSeries_eq_shifted_ofScalarsSum (z : ℂ) :
    dilogarithmPowerSeries z =
      ofScalarsSum (fun n : ℕ ↦ if n = 0 then 0 else (1 : ℂ) / ((n : ℂ) ^ 2)) z := by
  -- Rewrite both sides as `tsum`s and compare the coefficients termwise.
  rw [dilogarithmPowerSeries_eq_tsum, ofScalars_sum_eq]
  refine tsum_congr fun n ↦ ?_
  cases n with
  | zero =>
      simp
  | succ n =>
      simp [smul_eq_mul]

/-- Helper for Exercise 16: on the lens domain, differentiating the dilogarithm-type series
termwise yields `-log (1 - z) / z`. -/
theorem dilogarithmPowerSeries_hasDerivAt_on_domain {z : ℂ} (hz : z ∈ exercise16Domain) :
    HasDerivAt dilogarithmPowerSeries (-Complex.log (1 - z) / z) z := by
  let A : ℕ → ℂ := fun n ↦ if n = 0 then 0 else (1 : ℂ) / ((n : ℂ) ^ 2)
  let B : ℕ → ℂ := fun n ↦ (1 : ℂ) / (n + 1 : ℂ)
  have hz0 : ‖z‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz.1
  have hA_radius : (ofScalars ℂ A).radius = 1 := by
    -- The coefficient sequence matches the inverse-square model from the earlier radius theorem.
    simpa [A, one_div] using inverse_square_series_radius_eq_one (𝕜 := ℂ)
  have hz_radius : (‖z‖₊ : ℝ≥0∞) < (ofScalars ℂ A).radius := by
    rw [hA_radius]
    simpa using hz0
  have hcoeff :
      (fun n ↦ (n.succ : ℂ) * A n.succ) = B := by
    funext n
    have hn : (n + 1 : ℂ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    calc
      (n.succ : ℂ) * A n.succ = (n + 1 : ℂ) * ((1 : ℂ) / ((n + 1 : ℂ) ^ 2)) := by
        simp [A]
      _ = (1 : ℂ) / (n + 1 : ℂ) := by
        field_simp [hn]
      _ = B n := by
        simp [B]
  have hderiv :
      HasDerivAt dilogarithmPowerSeries (ofScalarsSum B z) z := by
    -- Route correction: work with the canonical scalar power series API before converting back to
    -- the source-facing notation `dilogarithmPowerSeries`.
    have hderivA :
        HasDerivAt (ofScalarsSum A) (ofScalarsSum B z) z := by
      simpa [hcoeff] using hasDerivAt_ofScalarsSum_of_mem_radius A hz_radius
    have hEq : dilogarithmPowerSeries = fun w ↦ ofScalarsSum A w := by
      funext w
      simpa [A] using dilogarithmPowerSeries_eq_shifted_ofScalarsSum w
    simpa [hEq] using hderivA
  have hz_ne : z ≠ 0 := Complex.slitPlane_ne_zero (exercise16Domain_mem_slitPlane hz)
  have hseries :
      Complex.logarithmicPowerSeries (-z) = -(z * ofScalarsSum B z) := by
    -- Re-expand the logarithmic power series at `-z` and collect the common factor `-z`.
    rw [Complex.logarithmicPowerSeries, ofScalars_sum_eq, ← tsum_mul_left]
    refine tsum_congr fun n ↦ ?_
    have hpow :
        (-z) ^ (n + 1) = (-1 : ℂ) ^ (n + 1) * z ^ (n + 1) := by
      simpa [neg_mul] using (mul_pow (-1 : ℂ) z (n + 1)).symm
    calc
      (-1 : ℂ) ^ n * (-z) ^ (n + 1) / (n + 1) =
          (-1 : ℂ) ^ n * ((-1 : ℂ) ^ (n + 1) * z ^ (n + 1)) / (n + 1) := by
            rw [hpow]
      _ = -(z ^ (n + 1) / (n + 1 : ℂ)) := by
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = -z * (B n • z ^ n) := by
            simp [B, smul_eq_mul, pow_succ', div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hsum :
      z * ofScalarsSum B z = -Complex.log (1 - z) := by
    have hlog :
        Complex.logarithmicPowerSeries (-z) = Complex.log (1 - z) := by
      simpa using logarithmic_power_series_tsum_eq (-z) (by simpa using hz0)
    calc
      z * ofScalarsSum B z = -Complex.logarithmicPowerSeries (-z) := by
        rw [hseries]
        ring
      _ = -Complex.log (1 - z) := by
        rw [hlog]
  have hrewrite : ofScalarsSum B z = -Complex.log (1 - z) / z := by
    -- Divide the identity `z * S'(z) = -log (1-z)` by `z`, which is nonzero on the domain.
    apply (eq_div_iff hz_ne).2
    simpa [mul_comm] using hsum
  simpa [hrewrite] using hderiv

end Complex

/-- Helper for Exercise 16: the reflection combination
`S(z) + S(1-z) + log z * log(1-z)` has zero derivative on the lens domain. -/
theorem exercise16_reflection_function_deriv_zero {z : ℂ} (hz : z ∈ exercise16Domain) :
    HasDerivAt
      (fun w ↦
        Complex.dilogarithmPowerSeries w + Complex.dilogarithmPowerSeries (1 - w) +
          Complex.log w * Complex.log (1 - w))
      0 z := by
  have hS₁ :
      HasDerivAt Complex.dilogarithmPowerSeries (-Complex.log (1 - z) / z) z :=
    Complex.dilogarithmPowerSeries_hasDerivAt_on_domain hz
  have hone_sub : HasDerivAt (fun w : ℂ ↦ 1 - w) (-1) z := by
    -- Differentiate the affine involution `w ↦ 1 - w`.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      ((hasDerivAt_id z).neg.const_add (1 : ℂ))
  have hS₂ :
      HasDerivAt (fun w ↦ Complex.dilogarithmPowerSeries (1 - w))
        (Complex.log z / (1 - z)) z := by
    -- Differentiate the shifted dilogarithm by chaining the previous derivative formula with
    -- the involution `w ↦ 1 - w`.
    simpa using
      (Complex.dilogarithmPowerSeries_hasDerivAt_on_domain (exercise16Domain_one_sub hz)).comp z
        hone_sub
  have hlog₁ :
      HasDerivAt (fun w : ℂ ↦ Complex.log w) (1 / z) z := by
    -- The first logarithm is differentiated on the slit plane.
    simpa using (hasDerivAt_id z).clog (exercise16Domain_mem_slitPlane hz)
  have hlog₂ :
      HasDerivAt (fun w : ℂ ↦ Complex.log (1 - w)) (-1 / (1 - z)) z := by
    -- The second logarithm is the same branch composed with the involution.
    simpa using hone_sub.clog (exercise16Domain_one_sub_mem_slitPlane hz)
  have hprod :
      HasDerivAt (fun w : ℂ ↦ Complex.log w * Complex.log (1 - w))
        (Complex.log (1 - z) / z - Complex.log z / (1 - z)) z := by
    -- Product differentiation reproduces the textbook derivative from Proposition 6.2.
    simpa [sub_eq_add_neg, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hlog₁.mul hlog₂
  have hsum :
      HasDerivAt
        (fun w ↦
          Complex.dilogarithmPowerSeries w + Complex.dilogarithmPowerSeries (1 - w) +
            Complex.log w * Complex.log (1 - w))
        ((-Complex.log (1 - z) / z) + Complex.log z / (1 - z) +
          (Complex.log (1 - z) / z - Complex.log z / (1 - z))) z := by
    simpa [add_assoc, add_left_comm, add_comm] using (hS₁.add hS₂).add hprod
  have hcancel :
      (-Complex.log (1 - z) / z) + Complex.log z / (1 - z) +
          (Complex.log (1 - z) / z - Complex.log z / (1 - z)) = 0 := by
    ring
  simpa [hcancel] using hsum
/-- Exercise 16 (4): there exists a constant `a` such that on the lens-shaped domain
`D = {z : ℂ | ‖z‖ < 1 and ‖z - 1‖ < 1}` one has
`S(z) + S(1 - z) = a - log z log (1 - z)` for
`S = Complex.dilogarithmPowerSeries`. -/
theorem exercise16_exists_reflection_constant :
    ∃ a : ℂ, Exercise16ReflectionConstant a := by
  let G : ℂ → ℂ := fun z ↦
    Complex.dilogarithmPowerSeries z + Complex.dilogarithmPowerSeries (1 - z) +
      Complex.log z * Complex.log (1 - z)
  have hD_open : IsOpen exercise16Domain := by
    simpa [exercise16Domain] using isOpen_ball.inter isOpen_ball
  have hD_preconnected : IsPreconnected exercise16Domain := by
    simpa [exercise16Domain] using
      ((convex_ball (0 : ℂ) 1).inter (convex_ball (1 : ℂ) 1)).isPreconnected
  have hG_diff : DifferentiableOn ℂ G exercise16Domain := by
    intro z hz
    exact (exercise16_reflection_function_deriv_zero hz).differentiableAt.differentiableWithinAt
  obtain ⟨a, ha_const⟩ :=
    hD_open.exists_is_const_of_fderiv_eq_zero hD_preconnected hG_diff fun z hz ↦ by
      -- Convert the scalar derivative statement to the zero Fréchet derivative required by the
      -- constancy theorem on an open preconnected set.
      simpa [G] using (exercise16_reflection_function_deriv_zero hz).hasFDerivAt.fderiv
  refine ⟨a, ?_⟩
  intro z hz
  have hGz : G z = a := ha_const z hz
  -- Rearrange the constant-value identity back into the textbook reflection formula.
  rw [eq_sub_iff_add_eq]
  simpa [G, add_assoc, add_left_comm, add_comm] using hGz

-- Proof sketch: evaluate the reflection identity along the real interval `(0, 1)` and apply
-- part (3) to pass to the limit `x → 1`, using that `S(0) = 0` and the principal logarithm
-- vanishes at `1`.
-- Route correction: the remaining blocker is now purely endpoint analysis, not the reflection
-- identity itself.
-- TODO: specialize the reflection identity to real `x ∈ (0,1)`, show
-- `Complex.dilogarithmPowerSeries (1 - x) → 0` by continuity at `0`, and prove
-- `Complex.log x * Complex.log (1 - x) → 0` as `x → 1-`.
/-- Exercise 16 (5): every reflection constant from part (4) is equal to
`∑_{n ≥ 1} 1 / n^2`, written in Lean as `∑_{n ≥ 0} 1 / (n + 1)^2`. -/
theorem exercise16_reflection_constant_eq_zeta_two
    {a : ℂ} (ha : Exercise16ReflectionConstant a) :
    a = ∑' n : ℕ, (1 : ℂ) / ((n + 1 : ℂ) ^ 2) := sorry

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
  have hlog_half : Complex.log ((1 : ℂ) / 2) = -Complex.log 2 := by
    -- On positive real numbers, the principal branch coincides with the real logarithm.
    calc
      Complex.log ((1 : ℂ) / 2) = ((Real.log ((1 : ℝ) / 2)) : ℂ) := by
        rw [Complex.ofReal_log]
        positivity
      _ = (-Real.log 2 : ℂ) := by
        norm_num
        simpa [one_div] using congrArg (fun t : ℝ ↦ (t : ℂ)) (Real.log_inv (2 : ℝ))
      _ = -Complex.log 2 := by
        rw [← Complex.ofReal_log]
        positivity
  have hmidpoint :
      a - Complex.log 2 ^ 2 = (2 : ℂ) * Complex.dilogarithmPowerSeries ((1 : ℂ) / 2) := by
    -- At `z = 1 / 2`, the two dilogarithm terms coincide and the logarithm square simplifies.
    have hreflect :
        Complex.dilogarithmPowerSeries ((1 : ℂ) / 2) +
            Complex.dilogarithmPowerSeries ((1 : ℂ) / 2) =
          a - Complex.log ((1 : ℂ) / 2) * Complex.log ((1 : ℂ) / 2) := by
      simpa using hhalf
    calc
      a - Complex.log 2 ^ 2 = a - Complex.log ((1 : ℂ) / 2) * Complex.log ((1 : ℂ) / 2) := by
        rw [hlog_half]
        ring
      _ = Complex.dilogarithmPowerSeries ((1 : ℂ) / 2) +
            Complex.dilogarithmPowerSeries ((1 : ℂ) / 2) := hreflect.symm
      _ = (2 : ℂ) * Complex.dilogarithmPowerSeries ((1 : ℂ) / 2) := by
        ring
  have hseries :
      (2 : ℂ) * Complex.dilogarithmPowerSeries ((1 : ℂ) / 2) =
        ∑' n : ℕ, (1 : ℂ) / (((n + 1 : ℂ) ^ 2) * (2 : ℂ) ^ n) := by
    -- Rewrite the midpoint value by its `tsum` expansion and simplify the scalar factor `2`.
    rw [Complex.dilogarithmPowerSeries_eq_tsum, tsum_mul_left]
    refine tsum_congr fun n ↦ ?_
    have htwo : (2 : ℂ) ≠ 0 := by
      norm_num
    have hnsucc : (n + 1 : ℂ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    field_simp [pow_succ, htwo, hnsucc, mul_assoc, mul_left_comm, mul_comm]
    ring
  exact hmidpoint.trans hseries
