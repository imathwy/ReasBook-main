import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap01.Exercise_1_4_4
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap02.Example_2_28

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory

private theorem petersburgHalfPos : 0 < (1 / 2 : ℝ) := by
  norm_num

private theorem petersburgHalfLeOne : (1 / 2 : ℝ) ≤ 1 := by
  norm_num

/-- The first winning round on the canonical fair coin-flip space `Bool^ℕ`, counted as the number
of initial losses before the first win; it is `⊤` on the all-losses path. Here `false` denotes a
loss and `true` a win. -/
noncomputable def petersburgFirstWinWaitingTime : BernoulliSequence → ℕ∞ :=
  rowFirstSuccessWaitingTime (fun _ n ω ↦ ω n) 0

@[simp] theorem petersburgFirstWinWaitingTime_eq_top_iff {ω : BernoulliSequence} :
    petersburgFirstWinWaitingTime ω = ⊤ ↔ ∀ n, ω n = false := by
  simp [petersburgFirstWinWaitingTime, rowFirstSuccessWaitingTime_eq_top_iff]

@[simp] theorem petersburgFirstWinWaitingTime_eq_coe_iff {ω : BernoulliSequence} {n : ℕ} :
    petersburgFirstWinWaitingTime ω = (n : ℕ∞) ↔
      ω n = true ∧ ∀ k < n, ω k = false := by
  simp [petersburgFirstWinWaitingTime, rowFirstSuccessWaitingTime_eq_coe_iff]

/-- The textbook round payoff attached to a coin flip: `false` is the loss `-1`, `true` is the
win `1`. -/
def petersburgRoundPayoff : Bool → ℝ
  | false => -1
  | true => 1

@[simp] theorem petersburgRoundPayoff_false : petersburgRoundPayoff false = -1 := rfl
@[simp] theorem petersburgRoundPayoff_true : petersburgRoundPayoff true = 1 := rfl

/-- The adapted stake `H_n`: before round `n + 1`, the gambler stakes `2^n` exactly when the
first `n` rounds have all been losses, and otherwise stops playing. -/
def petersburgStake (n : ℕ) (ω : BernoulliSequence) : ℝ :=
  if ∀ k < n, ω k = false then (2 : ℝ) ^ n else 0

/-- Companion waiting-time payoff formula: if the first win occurs after `m` initial losses, then
after `n + 1` rounds the cumulative Petersburg gain is `1 - 2^(n + 1)` while no win has yet
occurred (`n < m`) and `1` afterwards. -/
def petersburgProfit (n m : ℕ) : ℝ :=
  if n < m then 1 - (2 : ℝ) ^ (n + 1) else 1

@[simp] theorem petersburgProfit_eq_lossValue_iff {n m : ℕ} :
    petersburgProfit n m = 1 - (2 : ℝ) ^ (n + 1) ↔ n < m := by
  by_cases h : n < m
  · simp [petersburgProfit, h]
  · have hpow_pos : 0 < (2 : ℝ) ^ (n + 1) := by
      positivity
    constructor
    · intro hEq
      simp [petersburgProfit, h] at hEq
      linarith
    · intro hlt
      exact (h hlt).elim

@[simp] theorem petersburgProfit_eq_one_iff {n m : ℕ} :
    petersburgProfit n m = 1 ↔ m ≤ n := by
  by_cases h : n < m
  · simp [petersburgProfit, h, Nat.not_le.mpr h]
  · simp [petersburgProfit, h, Nat.not_lt.mp h]

/-- For each finite first winning round, the waiting-time payoff formula eventually stabilizes at
the gain `1`. -/
theorem petersburgProfit_tendsto_one (m : ℕ) :
    Tendsto (fun n ↦ petersburgProfit n m) atTop (nhds (1 : ℝ)) := by
  have h_eventually : (fun _ : ℕ ↦ (1 : ℝ)) =ᶠ[atTop] fun n ↦ petersburgProfit n m := by
    exact Filter.eventually_atTop.2 ⟨m, fun n hn ↦ by simp [petersburgProfit, Nat.not_lt.mpr hn]⟩
  exact Tendsto.congr' h_eventually tendsto_const_nhds

/-- The cumulative Petersburg gain `S_n` after the first `n` rounds on the fair coin-flip space,
using the textbook payoff convention `false ↦ -1`, `true ↦ 1`. -/
def petersburgPartialSum (n : ℕ) (ω : BernoulliSequence) : ℝ :=
  Finset.sum (Finset.range n) fun k ↦
    petersburgStake k ω * petersburgRoundPayoff (ω k)

/-- The extended-real pointwise limit `S`: it equals `1` on paths with a win and `-∞` on the
all-losses path. -/
noncomputable def petersburgLimit (ω : BernoulliSequence) : EReal :=
  by
    classical
    exact if ∀ n, ω n = false then ⊥ else 1

/-- On a path whose first win occurs after `m` initial losses, the partial sums agree with the
companion waiting-time payoff formula. -/
theorem petersburgPartialSum_succ_eq_profit_of_waitingTime {ω : BernoulliSequence} {n m : ℕ}
    (hω : petersburgFirstWinWaitingTime ω = (m : ℕ∞)) :
    petersburgPartialSum (n + 1) ω = petersburgProfit n m := by
  sorry

/-- The canonical first-win waiting time on the fair Bernoulli product space has the geometric law
with parameter `1 / 2`, pushed forward along `ℕ ↪ ℕ∞`. -/
theorem hasLaw_petersburgFirstWinWaitingTime :
    HasLaw petersburgFirstWinWaitingTime
      (Measure.map (fun n : ℕ ↦ (n : ℕ∞))
        (geometricMeasure
          (⟨(1 / 2 : ℝ), petersburgHalfPos.le, petersburgHalfLeOne⟩ : unitInterval)))
      fairBernoulliMeasure := by
  sorry

/-- The Petersburg partial sums converge pointwise in `EReal` to the extended-real limit `S`,
including the null all-losses branch where `S = -∞`. -/
theorem petersburgPartialSum_tendsto_limit (ω : BernoulliSequence) :
    Tendsto (fun n ↦ (petersburgPartialSum n ω : EReal)) atTop (nhds (petersburgLimit ω)) := by
  sorry

/-- The all-losses path has probability zero, so the extended-real limit is almost surely `1`. -/
theorem petersburgLimit_ae_eq_one :
    petersburgLimit =ᵐ[fairBernoulliMeasure] fun _ ↦ (1 : EReal) := by
  sorry

/-- Every finite-stage Petersburg gain has expectation `0` under the fair Bernoulli product
measure. -/
theorem integral_petersburgPartialSum_eq_zero (n : ℕ) :
    ∫ ω, petersburgPartialSum n ω ∂ fairBernoulliMeasure = 0 := by
  sorry

/-- The Petersburg partial sums converge almost surely to the extended-real limit `S`. -/
theorem petersburgPartialSum_ae_tendsto_limit :
    ∀ᵐ ω ∂ fairBernoulliMeasure,
      Tendsto (fun n ↦ (petersburgPartialSum n ω : EReal)) atTop (nhds (petersburgLimit ω)) :=
  Filter.Eventually.of_forall petersburgPartialSum_tendsto_limit

/-- The Petersburg partial sums admit no integrable minorant under the fair Bernoulli product
measure. -/
theorem petersburgPartialSum_no_integrable_minorant :
    ¬ ∃ g : BernoulliSequence → ℝ,
      Integrable g fairBernoulliMeasure ∧
        ∀ n, g ≤ᵐ[fairBernoulliMeasure] petersburgPartialSum n := by
  sorry

-- Proof sketch: the fair Petersburg doubling strategy lives on the canonical fair coin-flip space
-- `Bool^ℕ`; the adapted stakes `H_n` generate partial sums `S_n` with expectation `0`, the
-- pathwise limit is the extended-real random variable `S` that equals `-∞` on the null
-- all-losses branch and `1` otherwise, and the sequence has no integrable minorant.
/-- Example 4.22: on the canonical fair coin-flip space `Bool^ℕ`, with textbook round payoff
`false ↦ -1` and `true ↦ 1`, the adapted doubling stakes `H_n` define a gain process `S_n` that
converges almost surely to the extended-real limit `S`, every `S_n` has expectation `0`, and the
sequence admits no integrable minorant. -/
theorem example_4_22 :
    (∀ᵐ ω ∂ fairBernoulliMeasure,
      Tendsto (fun n ↦ (petersburgPartialSum n ω : EReal)) atTop (nhds (petersburgLimit ω))) ∧
    (∀ n, ∫ ω, petersburgPartialSum n ω ∂ fairBernoulliMeasure = 0) ∧
    ¬ ∃ g : BernoulliSequence → ℝ,
      Integrable g fairBernoulliMeasure ∧
        ∀ n, g ≤ᵐ[fairBernoulliMeasure] petersburgPartialSum n := by
  exact ⟨petersburgPartialSum_ae_tendsto_limit, integral_petersburgPartialSum_eq_zero,
    petersburgPartialSum_no_integrable_minorant⟩
