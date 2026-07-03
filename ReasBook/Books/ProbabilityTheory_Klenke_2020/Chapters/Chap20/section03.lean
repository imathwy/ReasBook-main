import Mathlib
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_20_3_1 (from Items/Chap20) -/
open MeasureTheory Set
open scoped ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The set of `τ`-invariant probability measures on the measurable space `Ω`. -/
def tauInvariantProbabilityMeasures (τ : Ω → Ω) : Set (Measure Ω) :=
  {μ | MeasurePreserving τ μ μ ∧ IsProbabilityMeasure μ}

-- Proof sketch: invariance under `τ` is preserved by nonnegative linear combinations because
-- pushforward is affine on measures, and the total mass of a convex combination of probability
-- measures is still `1`.
/-- Exercise 20.3.1 (1): the set of `τ`-invariant probability measures is convex. -/
theorem tauInvariantProbabilityMeasures_convex (τ : Ω → Ω) :
    Convex ℝ≥0∞ (tauInvariantProbabilityMeasures τ) := by
  intro μ hμ ν hν a b ha hb hab
  rcases hμ with ⟨hμτ, hμprob⟩
  rcases hν with ⟨hντ, hνprob⟩
  refine ⟨?_, ?_⟩
  · simpa using (hμτ.smul_measure a).add_measure (hντ.smul_measure b)
  · exact ⟨by simp [Measure.add_apply, hab, hμprob.measure_univ, hνprob.measure_univ]⟩

/- Exercise 20.3.1 (2): for probability measures, ergodicity is exactly the canonical mathlib
criterion `Ergodic.iff_mem_extremePoints`, identifying ergodic measures with the extreme points of
the set of invariant probability measures. -/
recall Ergodic.iff_mem_extremePoints

/-! ### Exercise_20_3_2 (from Items/Chap20) -/
open scoped Topology
open Filter

/-- The leading digit in the base-`p` expansion of `n`, i.e. the last entry of `p.digits n`. -/
def baseLeadingDigit (p n : ℕ) : ℕ :=
  (p.digits n).getLastD 0

-- Proof sketch: for `n ≠ 0`, the base-`p` digit list of `n` is nonempty, so `getLastD` is the
-- actual last digit of `p.digits n`; then apply the canonical bound `Nat.digits_lt_base`.
/-- The leading digit of a nonzero natural number in base `p` is strictly less than `p`. -/
theorem baseLeadingDigit_lt_base {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) :
    baseLeadingDigit p n < p := by
  have hdigits : p.digits n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  rw [baseLeadingDigit, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hdigits,
    Option.getD_some]
  exact Nat.digits_lt_base hp (List.getLast_mem hdigits)

-- Proof sketch: write the leading base-`p` digit of `q^i` as the indicator of the interval
-- `[log d / log p, log (d + 1) / log p)` for the fractional parts of `i * log q / log p`, then
-- apply equidistribution on the circle using the squarefreeness hypothesis on `p`.
/-- Exercise 20.3.2: for squarefree `p` and `2 ≤ q < p`, the leading base-`p` digits of `q^n`
satisfy Benford's law with logarithmic frequencies. -/
theorem powers_leading_digit_benford
    {p q d : ℕ} (hpSq : Squarefree p) (hq2 : 2 ≤ q) (hq_lt : q < p)
    (hd1 : 1 ≤ d) (hd_lt : d < p) :
    Tendsto
      (fun n : ℕ ↦
        (((Finset.Icc 1 n).filter fun i ↦ baseLeadingDigit p (q ^ i) = d).card : ℝ) / n)
      atTop
      (𝓝 ((Real.log (d + 1) - Real.log d) / Real.log p)) := sorry

/-! ### Example_20_3 (from Items/Chap20) -/
open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory
open ProbabilityTheory.Kernel

noncomputable section

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- The uniform Bernoulli law on `Bool`, used for the standard nonstationary counterexample with
constant tail coordinates. -/
def example203_counterexample_law : ProbabilityMeasure Bool :=
  ⟨(PMF.uniformOfFintype Bool).toMeasure, inferInstance⟩

-- Proof sketch: unfold `example203_counterexample_law`; it is defined to be the probability
-- measure associated with the uniform pmf on `Bool`.
/-- The counterexample law is the uniform law on `Bool`. -/
theorem example203_counterexample_law_eq_uniform :
    (example203_counterexample_law : Measure Bool) = (PMF.uniformOfFintype Bool).toMeasure := rfl

/-- The explicit counterexample process with `X₀(ω) = !ω` and `X_{n + 1}(ω) = ω`, so the tail is
constant while the initial coordinate is different. -/
def example203_counterexample_process : ℕ → Bool → Bool
  | 0, ω => !ω
  | _ + 1, ω => ω

-- Proof sketch: unfold `example203_counterexample_process`; every positive-time coordinate is the
-- identity map on `Bool`.
/-- Every positive-time coordinate of the counterexample process is the identity map on `Bool`. -/
theorem example203_counterexample_process_succ_apply (n : ℕ) (ω : Bool) :
    example203_counterexample_process (n + 1) ω = ω := rfl

/-- The textbook coefficients `c₁, …, c_k` induce the Chapter 9 owner coefficients by inserting
the zero coefficient `c₀ = 0`. -/
def movingAverageOneBasedWeights {k : ℕ} (c : Fin k → ℝ) : ℕ → ℝ
  | 0 => 0
  | i + 1 => if h : i < k then c ⟨i, h⟩ else 0

-- Proof sketch: split the Chapter 9 moving-average sum into the zero term and the positive-time
-- tail; the inserted zero coefficient kills the `i = 0` term, and the remaining range is exactly
-- the textbook sum over `l = 1, ..., k`.
/-- The Chapter 9 moving-average owner recovers the textbook one-based finite sum after inserting
the zero coefficient `c₀ = 0`. -/
theorem movingAverageProcess_oneBased_apply {Ω' : Type u} (Y : ℤ → Ω' → ℝ) {k : ℕ}
    (c : Fin k → ℝ) (n : ℤ) (ω : Ω') :
    movingAverageProcess Y (movingAverageOneBasedWeights c) k n ω =
      ∑ l : Fin k, c l * Y (n - (((l : ℕ) + 1 : ℕ) : ℤ)) ω := by
  rw [movingAverageProcess_apply]
  rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ movingAverageOneBasedWeights c i * Y (n - i) ω)
    (k + 1)]
  rw [Fin.sum_univ_succ]
  simp [movingAverageOneBasedWeights]

/- Example 20.3 (1): item (i). An i.i.d. process is stationary via the Chapter 9 owner theorem
`isStationaryProcess_of_iIndepFun_identDistrib`. -/
recall isStationaryProcess_of_iIndepFun_identDistrib

-- Proof sketch: the measure `example203_counterexample_law` is symmetric under `ω ↦ !ω`, while
-- every positive-time coordinate of `example203_counterexample_process` is the identity map; hence
-- each marginal has the same Bernoulli law.
/-- Example 20.3 (2): item (i). The explicit process with `X₁ = X₂ = X₃ = ...` still has the same
one-dimensional marginal law at every time. -/
theorem example203_counterexample_identically_distributed (n : ℕ) :
    IdentDistrib
      (example203_counterexample_process n)
      (example203_counterexample_process 0)
      (example203_counterexample_law : Measure Bool)
      (example203_counterexample_law : Measure Bool) := sorry

-- Proof sketch: under this process, the shifted pair `(X₁, X₂)` is almost surely concentrated on
-- the diagonal because all positive-time coordinates agree, while `(X₀, X₁)` is not; therefore the
-- whole process law cannot be shift-invariant.
/-- Example 20.3 (3): item (i). Equal one-dimensional marginals without independence do not imply
stationarity in general. -/
theorem example203_counterexample_not_stationary :
    ¬ IsStationaryProcess
      example203_counterexample_process
      (example203_counterexample_law : Measure Bool) := sorry

-- Proof sketch: `Kernel.trajMeasure` builds the canonical path law of the homogeneous Markov
-- chain started from `π`. Since `π` is invariant under `κ`, every time shift of the coordinate
-- process has the same finite-dimensional distributions as the original one.
/-- Example 20.3 (4): item (ii). A Markov chain started from an invariant distribution is
stationary. -/
theorem coordinate_process_traj_measure_is_stationary_of_invariant
    (κ : Kernel E E) [IsMarkovKernel κ] (π : ProbabilityMeasure E)
    (hπ : Invariant κ (π : Measure E)) :
    IsStationaryProcess
      (fun n x ↦ x n)
      (trajMeasure
        (π : Measure E)
        (fun n ↦ comap κ (fun x ↦ x ⟨n, mem_Iic.2 le_rfl⟩) (by fun_prop))) := sorry

-- Proof sketch: each shifted moving-average coordinate is the same finite linear combination of a
-- shifted stationary family `Y`; after translating the textbook coefficients to the Chapter 9
-- owner coefficients, the result is exactly `movingAverageProcess_isStationary`.
/-- Example 20.3 (5): item (iii). After inserting the zero coefficient `c₀ = 0`, the Chapter 9
moving-average owner shows that the textbook finite linear filter
`X_n = ∑_{l=1}^k c_l Y_{n-l}` is stationary whenever `Y` is stationary. -/
theorem movingAverageProcess_isStationary_of_oneBasedCoefficients
    (μ : Measure Ω) (Y : ℤ → Ω → ℝ) {k : ℕ} (c : Fin k → ℝ)
    (hY_stationary : IsStationaryProcess Y μ) :
    IsStationaryProcess (movingAverageProcess Y (movingAverageOneBasedWeights c) k) μ :=
  movingAverageProcess_isStationary μ Y (movingAverageOneBasedWeights c) k hY_stationary
