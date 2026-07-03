import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_17_6_1 (from Items/Chap17) -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory.DiscreteMarkovChain

open Figure17_1State

/-- The weights of the invariant distributions of Fig. 17.1, parameterized by the mass assigned to
the absorbing state `s2`. -/
def figure17_1InvariantWeights (t : Set.Icc (0 : ℝ≥0∞) 1) : Figure17_1State → ℝ≥0∞
  | s2 => t.1
  | s6 => (1 - t.1) * ((4 : ℝ≥0∞) / 17)
  | s7 => (1 - t.1) * ((5 : ℝ≥0∞) / 17)
  | s8 => (1 - t.1) * ((8 : ℝ≥0∞) / 17)
  | _ => 0

-- Proof sketch: expand the finite sum over the eight states of `Figure17_1State`; only the masses
-- at `s2`, `s6`, `s7`, and `s8` are nonzero, and their total is
-- `t + (1 - t) * (4 / 17 + 5 / 17 + 8 / 17) = 1`.
/-- The weights defining the invariant family of Fig. 17.1 form a probability vector. -/
theorem figure17_1InvariantWeights_sum (t : Set.Icc (0 : ℝ≥0∞) 1) :
    Finset.univ.sum (figure17_1InvariantWeights t) = 1 := sorry

/-- The invariant distribution of Fig. 17.1 with mass `t` at the absorbing state `s2` and
remaining mass distributed over the positive recurrent class `{s6, s7, s8}` in the proportions
`4 : 5 : 8`. -/
def figure17_1InvariantDistribution (t : Set.Icc (0 : ℝ≥0∞) 1) :
    ProbabilityMeasure Figure17_1State :=
  ⟨(PMF.ofFintype (figure17_1InvariantWeights t) (figure17_1InvariantWeights_sum t)).toMeasure,
    inferInstance⟩

-- Proof sketch: the only closed communicating classes of Fig. 17.1 are the absorbing singleton
-- `{s2}` and the irreducible class `{s6, s7, s8}`. Every invariant distribution is therefore a
-- convex combination of the Dirac mass at `s2` and the unique stationary distribution on
-- `{s6, s7, s8}`, whose weights are `4 / 17`, `5 / 17`, and `8 / 17`.
/-- Exercise 17.6.1 (1): the invariant distributions of Fig. 17.1 are exactly the convex
combinations of the absorbing law at `s2` and the stationary law on `{s6, s7, s8}` with weights
`4 / 17`, `5 / 17`, and `8 / 17`. -/
theorem figure17_1_invariantDistributions_eq_range :
    invariantDistributions (discreteMatrixKernel figure17_1TransitionMatrix) =
      Set.range figure17_1InvariantDistribution := sorry

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Figure17_1State → ProbabilityMeasure Ω} {X : ℕ → Ω → Figure17_1State}
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦ (discreteMatrixKernel figure17_1TransitionMatrix) ^ n) P X]

/- Exercise 17.6.1 (2): this is the Fig. 17.1 positive-recurrence statement already owned by
Remark 17.31, so the exercise file reuses that canonical theorem directly. -/
recall figure17_1_states678_positiveRecurrent

/- Exercise 17.6.1 (3)-(5): the three Fig. 17.1 first-return-time values are already owned by
Remark 17.31, so the exercise file reuses that canonical theorem directly. -/
recall figure17_1_expectedReturnTimes

end

end ProbabilityTheory.DiscreteMarkovChain

/-! ### Exercise_17_6_2 (from Items/Chap17) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

section

variable {E : Type u} [MeasurableSpace E]

/- Layering for Exercise 17.6.2:
- `Kernel.Invariant` is the `core/canonical` owner notion for a measure fixed by one kernel.
- `IsInvariantDistributionForSemigroup` is the `source-facing` semigroup predicate obtained by
  quantifying that owner notion over all times `t`.
- `isInvariantDistributionForSemigroup_iff_qMatrixBalance` is the bridge from this semigroup-level
  invariance predicate to the generator-matrix balance equation. -/

/-- A probability measure is invariant for a Markov semigroup if it is invariant for every
time-`t` transition kernel. -/
def IsInvariantDistributionForSemigroup
    (κ : NNReal → Kernel E E) (π : ProbabilityMeasure E) : Prop :=
  ∀ t : NNReal, Kernel.Invariant (κ t) (π : Measure E)

-- Proof sketch: unfold `IsInvariantDistributionForSemigroup`; it is defined exactly by requiring
-- invariance for each time slice `κ t`.
/-- Semigroup invariance means invariance under each transition kernel `κ t`. -/
theorem isInvariantDistributionForSemigroup_iff
    (κ : NNReal → Kernel E E) (π : ProbabilityMeasure E) :
    IsInvariantDistributionForSemigroup κ π ↔
      ∀ t : NNReal, Kernel.Invariant (κ t) (π : Measure E) :=
  Iff.rfl

end

section

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

-- Proof sketch: write invariance as `π.bind (κ t) = π`, evaluate both sides on the singleton
-- `{y}`, and differentiate at `t = 0` using the assumed right-derivative formula for the
-- singleton transition probabilities. For the converse, use the balance equation as the vanishing
-- derivative of the singleton masses under the forward equation, then deduce that the law started
-- from `π` is constant in time.
/-- Exercise 17.6.2: for a continuous-time Markov chain with Q-matrix `q`, a probability measure
`π` is invariant exactly when for every state `y` the weighted generator column sum
`∑' x, π {x} * q x y` exists and vanishes. -/
theorem isInvariantDistributionForSemigroup_iff_qMatrixBalance
    (κ : NNReal → Kernel E E) [IsMarkovSemigroup κ]
    (q : E → E → ℝ)
    (hκq : HasGeneratorMatrix κ q)
    (π : ProbabilityMeasure E) :
    IsInvariantDistributionForSemigroup κ π ↔
      ∀ y : E, Summable (fun x : E ↦ (π {x} : ℝ) * q x y) ∧
        (∑' x : E, (π {x} : ℝ) * q x y) = 0 := sorry

end

end ProbabilityTheory

/-! ### Exercise_17_6_3 (from Items/Chap17) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {G : Type u} [AddCommGroup G]

section

variable {Ω : Type v} [MeasurableSpace Ω]
variable [Countable G] [MeasurableSpace G] [DiscreteMeasurableSpace G]

/- Layering for Exercise 17.6.3:
- core/canonical owner: a step law `ν : ProbabilityMeasure G` together with
  `[IsMarkovProcessRealization (fun n ↦ dirac_convolution_kernel (ν : Measure G) ^ n) P X]`;
- bridge/view: a translation-invariant transition matrix `p`, whose row at `0` is the common
  increment law;
- source-facing conclusion: an irreducible random walk on a countable Abelian group is positive
  recurrent exactly when the group is finite. -/

-- Proof sketch: Theorem 17.51 identifies positive recurrence of an irreducible chain with the
-- existence of an invariant distribution. For the canonical convolution kernel of a group step law
-- `ν`, any invariant distribution must be constant on all translates, so it can have total mass
-- `1` only when `G` is finite; conversely, if `G` is finite, the normalized counting measure is
-- invariant under the walk, and Theorem 17.51 yields positive recurrence.
/-- Exercise 17.6.3 at the owner layer: an irreducible random walk on a countable Abelian group
with step law `ν` is positive recurrent if and only if the group is finite. The canonical public
interface is the convolution-kernel realization of the walk. -/
theorem irreducible_abelianGroupRandomWalk_isPositiveRecurrent_iff_finite
    (ν : ProbabilityMeasure G)
    (P : G → ProbabilityMeasure Ω) (X : ℕ → Ω → G)
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ dirac_convolution_kernel (ν : Measure G) ^ n) P X]
    [Kernel.IsIrreducible
      (Measure.count : Measure G) (dirac_convolution_kernel (ν : Measure G))] :
    IsPositiveRecurrentMarkovChain P X ↔ Finite G := sorry

-- Proof sketch: the hypothesis `∀ x y, p x y = p 0 (y - x)` identifies the row `p 0` as the
-- intrinsic increment law of the walk. The realization instance forces `discreteMatrixKernel p`
-- to be a Markov kernel, so the row-sum condition is derivable internally; thus this is exactly
-- the owner theorem above read in the source matrix presentation.
/-- Bridge form of Exercise 17.6.3: if the transition matrix depends only on the increment
`y - x`, then the irreducible walk is positive recurrent exactly when the group is finite. The
translation-invariant matrix presentation is kept only as a source-facing view of the owner
step-law theorem. -/
theorem irreducible_translationInvariant_groupRandomWalk_isPositiveRecurrent_iff_finite
    (p : G → G → ℝ≥0∞)
    (htranslation : ∀ x y : G, p x y = p 0 (y - x))
    (P : G → ProbabilityMeasure Ω) (X : ℕ → Ω → G)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    [Kernel.IsIrreducible (Measure.count : Measure G) (discreteMatrixKernel p)] :
    IsPositiveRecurrentMarkovChain P X ↔ Finite G := sorry

end

end ProbabilityTheory

/-! ### Exercise_17_6_4 (from Items/Chap17) -/
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

/-! ### Exercise_17_6_5 (from Items/Chap17) -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

private def resetWalkTransientExampleSequenceReal : ℕ → ℝ :=
  fun n ↦ 1 - 1 / (n + 2 : ℝ) ^ (2 : ℕ)

-- Proof sketch: `1 / (n + 2)^2` lies in `[0, 1]` for every `n`, so subtracting it from `1`
-- again gives a value in `[0, 1]`.
private theorem resetWalkTransientExampleSequenceReal_isProbabilitySequence :
    IsResetWalkProbabilitySequence resetWalkTransientExampleSequenceReal := sorry

/-- A transient example sequence for the reset walk, with square-summable defects `1 - p_n`. -/
def resetWalkTransientExampleSequence : ResetWalkParameters :=
  ⟨resetWalkTransientExampleSequenceReal,
    resetWalkTransientExampleSequenceReal_isProbabilitySequence⟩

private def resetWalkNullRecurrentExampleSequenceReal : ℕ → ℝ :=
  fun n ↦ 1 - 1 / (n + 2 : ℝ)

-- Proof sketch: since `n + 2 ≥ 2`, the harmonic term `1 / (n + 2)` lies in `[0, 1 / 2]`,
-- hence `1 - 1 / (n + 2)` lies in `[1 / 2, 1]`.
private theorem resetWalkNullRecurrentExampleSequenceReal_isProbabilitySequence :
    IsResetWalkProbabilitySequence resetWalkNullRecurrentExampleSequenceReal := sorry

/-- A null recurrent example sequence for the reset walk, with harmonic defects `1 - p_n`. -/
def resetWalkNullRecurrentExampleSequence : ResetWalkParameters :=
  ⟨resetWalkNullRecurrentExampleSequenceReal,
    resetWalkNullRecurrentExampleSequenceReal_isProbabilitySequence⟩

private def resetWalkPositiveRecurrentExampleSequenceReal : ℕ → ℝ :=
  fun _ ↦ 1 / 2

-- Proof sketch: the constant value `1 / 2` lies in `[0, 1]`.
private theorem resetWalkPositiveRecurrentExampleSequenceReal_isProbabilitySequence :
    IsResetWalkProbabilitySequence resetWalkPositiveRecurrentExampleSequenceReal := sorry

/-- A positive recurrent geometric example sequence for the reset walk. -/
def resetWalkPositiveRecurrentExampleSequence : ResetWalkParameters :=
  ⟨resetWalkPositiveRecurrentExampleSequenceReal,
    resetWalkPositiveRecurrentExampleSequenceReal_isProbabilitySequence⟩

private def resetWalkDyadicSpikeSequenceReal : ℕ → ℝ :=
  fun n ↦
    if 2 ^ Nat.log2 n = n then
      1 / 3
    else
      1 - 1 / (n + 2 : ℝ) ^ (2 : ℕ)

-- Proof sketch: both branches lie in `[0, 1]`: the spike branch is the constant `1 / 3`, and
-- the background branch is the transient example sequence.
private theorem resetWalkDyadicSpikeSequenceReal_isProbabilitySequence :
    IsResetWalkProbabilitySequence resetWalkDyadicSpikeSequenceReal := sorry

/-- A dyadic-spike sequence for the reset walk: at powers of two the upward-jump probability is
`1 / 3`, while away from powers of two the defects are square-summable. -/
def resetWalkDyadicSpikeSequence : ResetWalkParameters :=
  ⟨resetWalkDyadicSpikeSequenceReal, resetWalkDyadicSpikeSequenceReal_isProbabilitySequence⟩

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : ℕ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℕ}

section ResetWalkRealization

variable {p : ResetWalkParameters}
variable [IsMarkovProcessRealization (fun n ↦ resetWalkKernel p ^ n) P X]

/- Exercise 17.6.5 (1): this recurrence criterion is already the source-facing reset-walk theorem
from Example 17.52. -/
recall resetWalk_isRecurrentMarkovChain_iff_not_summable_one_sub

-- Proof sketch: use the tail-sum formula `𝔼[τ] = ∑_{n ≥ 0} ℙ(τ > n)` for the first return time to
-- `0`; for the reset walk, the survival probability `ℙ_0(τ_0^1 > n)` is exactly the prefix
-- product `∏_{k < n} p_k`.
/-- Exercise 17.6.5 (2): the expected first return time to `0` in the reset walk is the series
`M = ∑_{n=0}^\infty ∏_{k=0}^{n-1} p_k`, represented here by `resetWalkMassSeries p`. -/
theorem expectedFirstReturnTime_resetWalk_zero_eq_massSeries :
    expectedFirstReturnTime P X 0 = resetWalkMassSeries p := sorry

/- Exercise 17.6.5 (3): this positive-recurrence criterion is already the source-facing
reset-walk theorem from Example 17.52. -/
recall resetWalk_isPositiveRecurrentMarkovChain_iff_massSeries_lt_top

end ResetWalkRealization

section TransientExample

variable [IsMarkovProcessRealization
  (fun n ↦ resetWalkKernel resetWalkTransientExampleSequence ^ n) P X]

-- Proof sketch: for `resetWalkTransientExampleSequence`, the defect series
-- `∑ 1 / (n + 2)^2` is summable, so part (1) gives nonrecurrence; irreducibility of the reset
-- walk then identifies the regime as one where every state is transient, hence Definition 17.30
-- applies vacuously.
/-- Exercise 17.6.5 (4): part (iii)(a). The sequence
`p_n = 1 - 1 / (n + 2)^2` gives a transient reset walk. -/
theorem resetWalkTransientExample_isTransientMarkovChain :
    IsTransientMarkovChain (resetWalkTransitionMatrix resetWalkTransientExampleSequence) P X :=
  sorry

end TransientExample

section NullRecurrentExample

variable [IsMarkovProcessRealization
  (fun n ↦ resetWalkKernel resetWalkNullRecurrentExampleSequence ^ n) P X]

-- Proof sketch: for `p_n = 1 - 1 / (n + 2)`, the defect series is harmonic and hence divergent,
-- while the prefix products are comparable to `1 / (n + 1)`, so the return-time series is
-- infinite. Parts (1) and (3) therefore give recurrence but not positive recurrence.
/-- Exercise 17.6.5 (5): part (iii)(b). The sequence
`p_n = 1 - 1 / (n + 2)` gives a null recurrent reset walk. -/
theorem resetWalkNullRecurrentExample_isNullRecurrentMarkovChain :
    IsNullRecurrentMarkovChain P X := sorry

end NullRecurrentExample

section PositiveRecurrentExample

variable [IsMarkovProcessRealization
  (fun n ↦ resetWalkKernel resetWalkPositiveRecurrentExampleSequence ^ n) P X]

-- Proof sketch: for the constant choice `p_n = 1 / 2`, the prefix products form a geometric
-- sequence, so `M` is finite; part (3) then yields positive recurrence.
/-- Exercise 17.6.5 (6): part (iii)(c). The constant sequence `p_n = 1 / 2` gives a positive
recurrent reset walk. -/
theorem resetWalkPositiveRecurrentExample_isPositiveRecurrentMarkovChain :
    IsPositiveRecurrentMarkovChain P X := sorry

end PositiveRecurrentExample

section DyadicSpikeExample

variable [IsMarkovProcessRealization
  (fun n ↦ resetWalkKernel resetWalkDyadicSpikeSequence ^ n) P X]

-- Proof sketch: each dyadic spike contributes a factor `1 / 3` to the prefix product, so along
-- the interval `[2^m, 2^(m + 1))` the product is bounded by a multiple of `3^{-m}`; this makes
-- the mass series `M` summable, and part (3) yields positive recurrence.
/-- Exercise 17.6.5 (7): part (iii)(d). The dyadic-spike sequence gives a positive recurrent reset
walk. -/
theorem resetWalkDyadicSpikeExample_isPositiveRecurrentMarkovChain :
    IsPositiveRecurrentMarkovChain P X := sorry

end DyadicSpikeExample

-- Proof sketch: up to time `n`, the dyadic spikes contribute about `(2 / 3) log₂ n` to the defect
-- sum, while the square-summable background contributes only a bounded amount. Hence the
-- exponential comparison terms are comparable to `n^{-2 / (3 * log 2)}`, whose exponent is
-- strictly smaller than `1`, so the series is not summable.
/-- Exercise 17.6.5 (8): part (iii)(d). For the dyadic-spike sequence, the exponential comparison
series `∑ exp ( - ∑_{k < n} (1 - p_k))` is still divergent. -/
theorem resetWalkDyadicSpikeExample_expSeries_not_summable :
    ¬ Summable
      (fun n ↦
        Real.exp
          (-Finset.sum (Finset.range n) (fun k ↦ 1 - resetWalkDyadicSpikeSequence k))) := sorry

end ProbabilityTheory

/-! ### Example_17_6 (from Items/Chap17) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

/-- Example 17.6 (1): if `ν` is a convolution semigroup on `ℝ^d`, then the canonical coordinate
process on the path space `(ℝ^d)^[0,∞)` admits path laws `x ↦ P_x` making it a
time-homogeneous Markov process whose time-`t` transition kernel is
`x ↦ δ_x ∗ ν_t`. -/
theorem exists_timeHomogeneousMarkovProcess_of_isConvolutionSemigroup {d : ℕ}
    (ν : NNReal → ProbabilityMeasure (Fin d → ℝ)) (hν : IsConvolutionSemigroupWithZero ν) :
    ∃ P : (Fin d → ℝ) → ProbabilityMeasure (NNReal → Fin d → ℝ),
      ∃ κ : Kernel (Fin d → ℝ) (NNReal → Fin d → ℝ),
        IsTimeHomogeneousMarkovProcess Function.eval P κ ∧
          ∀ t : NNReal,
            transitionKernel κ t =
              dirac_convolution_kernel (ν t : Measure (Fin d → ℝ)) := sorry

-- Proof sketch: apply Example 17.6 (1) and then pass from the source-facing path-kernel
-- formulation of Definition 17.3 to the owner abstraction `IsMarkovProcessRealization` via
-- `IsTimeHomogeneousMarkovProcess.toIsMarkovProcessRealization`.
/-- The canonical coordinate process on the path space realizes the translated convolution kernels
`x ↦ δ_x ∗ ν_t` as a continuous-time Markov process. -/
theorem exists_markovProcessRealization_of_isConvolutionSemigroup {d : ℕ}
    (ν : NNReal → ProbabilityMeasure (Fin d → ℝ)) (hν : IsConvolutionSemigroupWithZero ν) :
    ∃ P : (Fin d → ℝ) → ProbabilityMeasure (NNReal → Fin d → ℝ),
      IsMarkovProcessRealization
        (fun t ↦ dirac_convolution_kernel (ν t : Measure (Fin d → ℝ)))
        P Function.eval := by
  sorry

-- Proof sketch: Example 17.6 yields a canonical-process realization of the translated kernels, and
-- Theorem 17.8 identifies the owner abstraction `IsMarkovProcessRealization` with the ambient
-- semigroup structure on those transition kernels.
/-- Example 17.6 (2): the translated increment kernels `x ↦ δ_x ∗ ν_t` form a
time-homogeneous Markov semigroup. -/
instance translatedIncrementKernel_isMarkovSemigroup {d : ℕ}
    (ν : NNReal → ProbabilityMeasure (Fin d → ℝ)) (hν : IsConvolutionSemigroupWithZero ν) :
    IsMarkovSemigroup
      (fun t ↦ dirac_convolution_kernel (ν t : Measure (Fin d → ℝ))) := by
  rcases exists_timeHomogeneousMarkovProcess_of_isConvolutionSemigroup ν hν with
    ⟨P, κ, hMarkov, hκ⟩
  letI :
      IsTimeHomogeneousMarkovProcess Function.eval P κ :=
    hMarkov
  have hSemigroup : IsMarkovSemigroup (transitionKernel κ) :=
    IsTimeHomogeneousMarkovProcess.transitionKernel_isMarkovSemigroup Function.eval
  have hκ' :
      transitionKernel κ =
        fun t ↦ dirac_convolution_kernel (ν t : Measure (Fin d → ℝ)) :=
    funext hκ
  simpa [hκ'] using hSemigroup

/-! ### Exercise_17_6_6 (from Items/Chap17) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

/- Layering for Exercise 17.6.6:
- `IsIrreducibleMarkovChain P X` and `IsRecurrentMarkovChain P X` are the source-facing Chapter 17
  hypotheses.
- `Kernel.Invariant` is the core/canonical owner predicate for invariant measures of a fixed
  kernel.
- `discreteMatrixKernel p` remains only the concrete bridge/view turning a stochastic matrix into
  the kernel whose invariant measures are being compared. -/

section

variable {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [IsMarkovProcessRealization (fun n ↦ discreteMatrixKernel p ^ n) P X]

-- Proof sketch: for a fixed nonzero invariant measure `π`, use the exercise's induction on the
-- first return to a reference state `x` to identify every singleton mass `π {y}` with
-- `π {x} * μ_x {y}`, where `μ_x` is the return-cycle occupation measure from Theorem 17.47.
-- Applying this description to two invariant measures and comparing the same reference state
-- yields a strictly positive scalar relating them.
/-- Exercise 17.6.6: if the realized discrete-time chain with transition matrix `p` is
irreducible in the Chapter 17 sense and recurrent, then any two nonzero invariant measures for
`discreteMatrixKernel p` are proportional. Equivalently, the invariant measure is unique up to
multiplication by a positive constant. -/
theorem invariantMeasures_unique_up_to_scale_of_irreducible_recurrent
    (hirr : IsIrreducibleMarkovChain P X) (hrec : IsRecurrentMarkovChain P X) {μ ν : Measure E}
    (hμ : Kernel.Invariant (discreteMatrixKernel p) μ)
    (hν : Kernel.Invariant (discreteMatrixKernel p) ν)
    (hμ_ne : μ ≠ 0) (hν_ne : ν ≠ 0) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ν = c • μ := sorry

-- Proof sketch: apply Theorem 17.37 to pass from the kernel irreducibility of
-- `discreteMatrixKernel p` to the source-facing predicate `IsIrreducibleMarkovChain P X`, then
-- invoke Exercise 17.6.6.
/-- Kernel-style specialization of Exercise 17.6.6 for realizations of a stochastic matrix. -/
theorem invariantMeasures_unique_up_to_scale_of_irreducible_recurrent_of_discreteMatrixKernel_isIrreducible
    [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p)]
    (hrec : IsRecurrentMarkovChain P X) {μ ν : Measure E}
    (hμ : Kernel.Invariant (discreteMatrixKernel p) μ)
    (hν : Kernel.Invariant (discreteMatrixKernel p) ν)
    (hμ_ne : μ ≠ 0) (hν_ne : ν ≠ 0) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ν = c • μ := by
  exact invariantMeasures_unique_up_to_scale_of_irreducible_recurrent
    (isIrreducibleMarkovChain_of_discreteMatrixKernel_isIrreducible p P X) hrec hμ hν hμ_ne hν_ne

end

end ProbabilityTheory
