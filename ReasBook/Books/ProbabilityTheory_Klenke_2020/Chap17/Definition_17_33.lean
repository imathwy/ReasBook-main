import ProbabilityTheory_Klenke_2020.Chap09.Definition_9_1
import ProbabilityTheory_Klenke_2020.Chap17.Definition_17_28
import ProbabilityTheory_Klenke_2020.Chap17.Theorem_17_8
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v}

/- Layering for Definition 17.33:
- `totalVisitsFrom` is the primitive pathwise visit-count observable from time `N` onward.
- `greenFunctionFrom` is the owner abstraction for the expected visit count from time `N` onward.
- `totalVisits` and `greenFunction` are the `N = 0` source-facing specializations.
- Later positive-time variants should reuse `greenFunctionFrom P X 1` rather than introducing
  parallel Green-function owners. -/

/-- The total number of visits of the trajectory `X` to the state `y` from time `N` onward,
counted by the counting measure on the set of visit times. -/
def totalVisitsFrom (X : ℕ → Ω → E) (y : E) (N : ℕ) (ω : Ω) : ℝ≥0∞ :=
  Measure.count {n : ℕ | N ≤ n ∧ X n ω = y}

/-- The Green function counting visits to `y` from time `N` onward under the start law `P x`. -/
def greenFunctionFrom
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (N : ℕ) (x y : E) : ℝ≥0∞ :=
  ∫⁻ ω, totalVisitsFrom X y N ω ∂(P x : Measure Ω)

/-- The total number of visits of the trajectory `X` to the state `y`, counted by the counting
measure on the set of visit times. -/
def totalVisits (X : ℕ → Ω → E) (y : E) (ω : Ω) : ℝ≥0∞ :=
  totalVisitsFrom X y 0 ω

/-- Definition 17.33: the Green function `G(x, y)` is the expected total number of visits of the
trajectory `X` to the state `y` under the initial law `P x`; the pathwise visit count is
`totalVisits X y`. -/
def greenFunction (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x y : E) : ℝ≥0∞ :=
  greenFunctionFrom P X 0 x y

notation "G[" P ", " X "; " N "]" =>
  greenFunctionFrom P X N

notation "G[" P ", " X "]" =>
  greenFunction P X

-- Proof sketch: unfold `totalVisitsFrom`; it is defined to be the counting measure of the set of
-- visit times to `y` from time `N` onward.
/-- Evaluating `totalVisitsFrom` counts the visit times of the trajectory at the state `y` from
time `N` onward. -/
theorem totalVisitsFrom_eq_count (X : ℕ → Ω → E) (y : E) (N : ℕ) (ω : Ω) :
    totalVisitsFrom X y N ω = Measure.count {n : ℕ | N ≤ n ∧ X n ω = y} := sorry

-- Proof sketch: unfold `greenFunctionFrom`; this is exactly the lower integral of
-- `totalVisitsFrom X y N` under the initial law `P x`.
/-- The Green function from time `N` onward is the expectation of the corresponding visit count. -/
theorem greenFunctionFrom_eq_lintegral_totalVisitsFrom
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (N : ℕ) (x y : E) :
    (G[P, X; N]) x y = ∫⁻ ω, totalVisitsFrom X y N ω ∂(P x : Measure Ω) := sorry

section MeasurableState

variable [MeasurableSpace E] [MeasurableSingletonClass E]
variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}

-- Proof sketch: write `totalVisitsFrom X y N` as the counting measure of the set of visit times
-- from `N` onward, expand that counting measure as the sum of singleton indicators, and
-- interchange the lower integral with the countable sum.
/-- For a stochastic process on a measurable state space with measurable singletons, the Green
function from time `N` onward equals the series of the time-`n` probabilities that the trajectory
is at the state `y` for times `n ≥ N`. -/
theorem greenFunctionFrom_eq_tsum_visitProbabilities
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (hX : IsStochasticProcess X)
    (N : ℕ) (x y : E) :
    (G[P, X; N]) x y =
      ∑' n : ℕ, (P x : Measure Ω) {ω | N ≤ n ∧ X n ω = y} := sorry

-- Proof sketch: specialize `greenFunctionFrom_eq_tsum_visitProbabilities` to `N = 1` and rewrite
-- `1 ≤ n` as `0 < n`.
/-- For a stochastic process, the positive-time Green function `G[P, X; 1] x y` is the series of
the strictly positive-time visit probabilities. -/
theorem greenFunctionFrom_one_eq_tsum_positiveStateProbabilities
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (hX : IsStochasticProcess X) (x y : E) :
    (G[P, X; 1]) x y =
      ∑' n : ℕ, (P x : Measure Ω) {ω | 0 < n ∧ X n ω = y} := by
  simpa [Nat.succ_le_iff] using greenFunctionFrom_eq_tsum_visitProbabilities P X hX 1 x y

-- Proof sketch: combine
-- `greenFunctionFrom_one_eq_tsum_positiveStateProbabilities` with `everHitsProbability_def`; both
-- are built from the same strictly positive-time event `{ω | ∃ n > 0, X n ω = y}`.
/-- For a stochastic process on a measurable state space with measurable singletons, positivity of
the positive-time Green function is equivalent to positivity of the ever-hit probability. -/
theorem greenFunctionFrom_one_pos_iff_everHitsProbability_pos
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (hX : IsStochasticProcess X) (x y : E) :
    0 < (G[P, X; 1]) x y ↔ 0 < (F[P, X]) x y := sorry

end MeasurableState

-- Proof sketch: unfold `totalVisits`; it is defined to be the counting measure of the set of
-- times at which the trajectory is at `y`.
/-- Evaluating `totalVisits` counts the visit times of the trajectory at the state `y`. -/
theorem totalVisits_eq_count (X : ℕ → Ω → E) (y : E) (ω : Ω) :
    totalVisits X y ω = Measure.count {n : ℕ | X n ω = y} := sorry

-- Proof sketch: unfold `greenFunction`; this is exactly the lower integral of `totalVisits X y`
-- under the initial law `P x`.
/-- The Green function is the expectation of the total visit count. -/
theorem greenFunction_eq_lintegral_totalVisits
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (x y : E) :
    (G[P, X]) x y = ∫⁻ ω, totalVisits X y ω ∂(P x : Measure Ω) := sorry

section MeasurableState

variable [MeasurableSpace E] [MeasurableSingletonClass E]
variable {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}

-- Proof sketch: write `totalVisits X y` as the counting measure of the set of visit times, expand
-- that counting measure as the sum of the singleton indicators, and interchange the lower integral
-- with the countable sum.
/-- For a stochastic process on a measurable state space with measurable singletons, the Green
function equals the series of the time-`n` probabilities that the trajectory is at the state `y`.
-/
theorem greenFunction_eq_tsum_stateProbabilities
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (hX : IsStochasticProcess X) (x y : E) :
    (G[P, X]) x y = ∑' n : ℕ, (P x : Measure Ω) {ω | X n ω = y} := sorry

end MeasurableState

end ProbabilityTheory
