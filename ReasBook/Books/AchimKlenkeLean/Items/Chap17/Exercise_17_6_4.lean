import AchimKlenkeLean.Items.Chap17.Remark_17_31
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

open DiscreteMarkovChain

/- Layering for Exercise 17.6.4:
- primitive/source-facing data: the explicit singleton-mass function for the candidate invariant
  measure of Fig. 17.2;
- core/canonical owner: `Kernel.Invariant` for stationarity of that measure;
- source-facing chain-level clause (4): for `r ∈ {0} ∪ (1 / 2, 1]` the source classifies the
  chain as transient, so we keep that clause as the main local chain-level statement;
- derived recurrence API: clauses (2) and (3), together with the `r > 1 / 2` branch of clause
  (4), are already owned upstream by `Remark_17_31`;
- bridge/view for the exceptional boundary `r = 0`: the sharper owner-level state
  classification is recorded locally through `IsPositiveRecurrentState` and `IsTransientState`. -/

/-- The singleton-mass function of the weighted counting measure used in the invariant-measure
calculation for the reflected nearest-neighbor chain of Fig. 17.2. It gives mass `1 - r` to `0`
and mass `(r / (1 - r))^n` to `n + 1`. -/
def figure17_2InvariantMass (r : ℝ≥0∞) : ℕ → ℝ≥0∞
  | 0 => 1 - r
  | n + 1 => (r / (1 - r)) ^ n

/-- The weighted counting measure on `ℕ` with singleton masses given by
`figure17_2InvariantMass r`. -/
def figure17_2InvariantMeasure (r : ℝ≥0∞) : Measure ℕ :=
  Measure.count.withDensity (figure17_2InvariantMass r)

-- Proof sketch: on the discrete state space `ℕ`, `Measure.count.withDensity` evaluates on a
-- singleton `{n}` as the density value at `n`.
/-- The weighted counting measure `figure17_2InvariantMeasure r` has singleton mass
`figure17_2InvariantMass r n` at `{n}`. -/
theorem figure17_2InvariantMeasure_apply_singleton (r : ℝ≥0∞) (n : ℕ) :
    figure17_2InvariantMeasure r {n} = figure17_2InvariantMass r n := sorry

-- Proof sketch: sum the singleton masses of `figure17_2InvariantMeasure r`. For `r < 1`, the tail
-- is a geometric series with ratio `r / (1 - r)`, so finiteness is equivalent to that ratio being
-- strictly smaller than `1`, i.e. to `r < 1 / 2`. For `r ≥ 1`, the denominator `1 - r` vanishes,
-- so the tail masses blow up and the total mass is automatically infinite.
/-- The weighted counting measure `figure17_2InvariantMeasure r` has finite total mass exactly in
the left-drift regime `r < 1 / 2`. -/
theorem figure17_2InvariantMeasure_univ_lt_top_iff (r : ℝ≥0∞) :
    figure17_2InvariantMeasure r Set.univ < ∞ ↔ r < 1 / 2 := sorry

-- Proof sketch: evaluate the stationarity equation on singletons. The boundary balance
-- `μ {0} = μ {1} * (1 - r)` and the interior balance
-- `μ {n + 1} * (1 - r) = μ {n} * r` are exactly the recursion satisfied by
-- `figure17_2InvariantMass r`. The boundary value `r = 1` is excluded because the chain then
-- drifts deterministically to `+∞`, while this mass profile does not satisfy the singleton
-- balance equation at `1`.
/-- Exercise 17.6.4 (1): for `r ∈ [0, 1)` the weighted counting measure with singleton masses
`μ {0} = 1 - r` and `μ {n + 1} = (r / (1 - r))^n` is invariant for the Fig. 17.2 transition
kernel. -/
theorem figure17_2InvariantMeasure_isInvariant
    (r : Set.Icc (0 : ℝ≥0∞) 1) (hr1 : (r : ℝ≥0∞) < 1) :
    Kernel.Invariant (discreteMatrixKernel (figure17_2TransitionMatrix r))
      (figure17_2InvariantMeasure r) := sorry

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {r : Set.Icc (0 : ℝ≥0∞) 1} {P : ℕ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℕ}
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦ discreteMatrixKernel (figure17_2TransitionMatrix r) ^ n) P X]

/- Exercise 17.6.4 (2): the left-drift positive-recurrence clause is already the exact
source-facing theorem owned by `Remark_17_31`. -/
recall figure17_2_allStatesPositiveRecurrent_of_lt_half

/- Exercise 17.6.4 (3): the critical null-recurrence clause is already the exact source-facing
theorem owned by `Remark_17_31`. -/
recall figure17_2_allStatesNullRecurrent_of_eq_half

/-- Exercise 17.6.4 (4): in the source wording, for `r ∈ {0} ∪ (1 / 2, 1]` the chain is
transient. In the chapter owner API we record this source-facing clause as non-recurrence of the
chain, while the sharper owner-level classification of the exceptional boundary case `r = 0` is
split out into companion theorems below. -/
theorem figure17_2_not_recurrent_of_eq_zero_or_half_lt
    (hr : (r : ℝ≥0∞) = 0 ∨ 1 / 2 < (r : ℝ≥0∞)) :
    ¬ IsRecurrentMarkovChain P X := sorry

/- Companion boundary analysis for Exercise 17.6.4 (4): unlike the right-drift owner statement
`∀ x, IsTransientState P X x`, the exceptional case `r = 0` falls into the deterministic
two-cycle `0 ↔ 1`, so only the states `n + 2` remain transient. -/

/-- In the degenerate boundary case `r = 0`, the state `0` belongs to the deterministic two-cycle
`0 ↔ 1`, so it is positive recurrent. -/
theorem figure17_2_zero_positiveRecurrent_of_eq_zero
    (hr : (r : ℝ≥0∞) = 0) :
    IsPositiveRecurrentState P X 0 := sorry

/-- In the degenerate boundary case `r = 0`, the state `1` belongs to the deterministic two-cycle
`0 ↔ 1`, so it is positive recurrent. -/
theorem figure17_2_one_positiveRecurrent_of_eq_zero
    (hr : (r : ℝ≥0∞) = 0) :
    IsPositiveRecurrentState P X 1 := sorry

/-- In the degenerate boundary case `r = 0`, every state `n + 2` drifts deterministically toward
the two-cycle `0 ↔ 1`, so it is transient. -/
theorem figure17_2_states_ge_two_transient_of_eq_zero
    (hr : (r : ℝ≥0∞) = 0) (n : ℕ) :
    IsTransientState P X (n + 2) := sorry

/- Companion to Exercise 17.6.4 (4): the genuine right-drift branch `r > 1 / 2` is already the
exact owner theorem from `Remark_17_31`. -/
recall figure17_2_allStatesTransient_of_half_lt

end

end ProbabilityTheory
