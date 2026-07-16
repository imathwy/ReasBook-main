import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap19.Theorem_19_15
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

attribute [local instance] Classical.propDecidable

namespace ProbabilityTheory

/-- The occupancy states of the `K`-urn model with `N` indistinguishable balls, represented as
weak compositions of `N` indexed by the urns. -/
abbrev GibbsUrnState (K N : ℕ) :=
  {η : Fin K → ℕ // η ∈ Finset.piAntidiag Finset.univ N}

/-- The Boltzmann weight `exp (-β W_j)` of the target urn `j`. -/
def gibbsUrnTargetWeight {K : ℕ} (β : ℝ) (W : Fin K → ℝ) (j : Fin K) : ℝ :=
  Real.exp (-β * W j)

/-- The normalizing constant `Z = ∑_j exp (-β W_j)` for the Gibbs relocation law. -/
def gibbsUrnPartitionFunction {K : ℕ} (β : ℝ) (W : Fin K → ℝ) : ℝ :=
  ∑ j : Fin K, gibbsUrnTargetWeight β W j

/-- The Gibbs relocation law on the urn labels. -/
def gibbsUrnTargetDistribution {K : ℕ} (β : ℝ) (W : Fin K → ℝ) : Fin K → ℝ≥0∞ :=
  fun j ↦ ENNReal.ofReal (gibbsUrnTargetWeight β W j / gibbsUrnPartitionFunction β W)

/-- The predicate that `η'` is obtained from `η` by choosing a ball from urn `i` and moving it to
urn `j`. -/
def IsGibbsUrnSingleBallMove {K N : ℕ} (η η' : GibbsUrnState K N) (i j : Fin K) : Prop :=
  0 < η.1 i ∧
    if i = j then
      η' = η
    else
      η'.1 i + 1 = η.1 i ∧ η'.1 j = η.1 j + 1 ∧ ∀ k : Fin K, k ≠ i → k ≠ j → η'.1 k = η.1 k

/-- The one-step transition matrix of the occupancy chain: first choose a ball uniformly, then
resample its destination urn according to the Gibbs law. -/
def gibbsUrnTransitionMatrix (K N : ℕ) (β : ℝ) (W : Fin K → ℝ) :
    GibbsUrnState K N → GibbsUrnState K N → ℝ≥0∞ :=
  fun η η' ↦
    ∑ i : Fin K,
      (((η.1 i : ℕ) : ℝ≥0∞) / (N : ℝ≥0∞)) *
        ∑ j : Fin K,
          if IsGibbsUrnSingleBallMove η η' i j then gibbsUrnTargetDistribution β W j else 0

/-- The multinomial Gibbs weight of an occupancy state. -/
def gibbsUrnOccupancyWeight (K N : ℕ) (β : ℝ) (W : Fin K → ℝ) (η : GibbsUrnState K N) :
    ℝ≥0∞ :=
  (Nat.multinomial Finset.univ η.1 : ℝ≥0∞) *
    ∏ j : Fin K, gibbsUrnTargetDistribution β W j ^ η.1 j

-- Proof sketch: the numerator is the finite Boltzmann sum `∑_j exp (-β W_j)`, and `hK` ensures
-- this sum is strictly positive because at least one index contributes a positive exponential term;
-- dividing each Boltzmann factor by this common normalizing constant makes the total mass `1`.
/-- The Gibbs relocation probabilities sum to one over the `K` urns. -/
theorem gibbsUrnTargetDistribution_sum {K : ℕ} (β : ℝ) (W : Fin K → ℝ) (hK : 0 < K) :
    ∑ j : Fin K, gibbsUrnTargetDistribution β W j = 1 := sorry

-- Proof sketch: apply the multinomial theorem to the probability vector
-- `gibbsUrnTargetDistribution β W`; after using `gibbsUrnTargetDistribution_sum`, the total mass
-- becomes `(∑_j q_j)^N = 1^N = 1`.
/-- The multinomial Gibbs weights form a probability vector on the occupancy states. -/
theorem gibbsUrnOccupancyWeight_sum {K N : ℕ} (β : ℝ) (W : Fin K → ℝ) (hK : 0 < K) :
    ∑ η : GibbsUrnState K N, gibbsUrnOccupancyWeight K N β W η = 1 := sorry

/-- The multinomial Gibbs distribution on occupancy states. -/
def gibbsUrnInvariantDistribution (K N : ℕ) (β : ℝ) (W : Fin K → ℝ) (hK : 0 < K) :
    ProbabilityMeasure (GibbsUrnState K N) :=
  ⟨(PMF.ofFintype (gibbsUrnOccupancyWeight K N β W) (gibbsUrnOccupancyWeight_sum β W hK)).toMeasure,
    inferInstance⟩

-- Proof sketch: if `N = 0`, then every row index lies in the empty state space unless `K > 0`,
-- so the row-sum condition is vacuous. For `N > 0`, fix an occupancy `η` and sum the transition
-- probabilities over all possible one-ball moves: the choice probabilities `η i / N` sum to `1`
-- because `η` contains exactly `N` balls, and the relocation probabilities sum to `1` by
-- `gibbsUrnTargetDistribution_sum`.
/-- The Gibbs urn transition matrix is stochastic, so it defines a discrete-time Markov chain on
the occupancy states. -/
theorem gibbsUrnTransitionMatrix_isStochastic {K N : ℕ} (β : ℝ) (W : Fin K → ℝ)
    (hN : 0 < N) :
    IsStochasticMatrix (gibbsUrnTransitionMatrix K N β W) := sorry

-- Proof sketch: compare the detailed-balance weights of two occupancies connected by a single-ball
-- move. The multinomial coefficient changes by the usual ratio `η i / (η' j)`, which cancels the
-- factor coming from choosing a ball in urn `i`, while the Gibbs factor contributes exactly the
-- destination probability `exp (-β W_j) / Z`.
/-- Exercise 19.2.2: for the occupancy chain of `N` indistinguishable balls in `K` urns with
relocation probabilities proportional to `exp (-β W_j)`, the multinomial Gibbs distribution is a
reversing measure. In particular, it is the invariant distribution of this Markov chain. -/
theorem gibbsUrnKernel_isReversible {K N : ℕ} (β : ℝ) (W : Fin K → ℝ)
    (hK : 0 < K) (hN : 0 < N) :
    Kernel.IsReversible (discreteMatrixKernel (gibbsUrnTransitionMatrix K N β W))
      (gibbsUrnInvariantDistribution K N β W hK : Measure (GibbsUrnState K N)) := sorry

-- Proof sketch: by `gibbsUrnTransitionMatrix_isStochastic`, the discrete kernel
-- `discreteMatrixKernel (gibbsUrnTransitionMatrix K N β W)` is Markov; then
-- `Kernel.IsReversible.invariant` applied to
-- `gibbsUrnKernel_isReversible` yields invariance of the Gibbs law.
/-- The multinomial Gibbs law is invariant for the Gibbs urn kernel. -/
theorem gibbsUrnInvariantDistribution_isInvariant {K N : ℕ} (β : ℝ) (W : Fin K → ℝ)
    (hK : 0 < K) (hN : 0 < N) :
    Kernel.Invariant (discreteMatrixKernel (gibbsUrnTransitionMatrix K N β W))
      (gibbsUrnInvariantDistribution K N β W hK : Measure (GibbsUrnState K N)) := sorry

end ProbabilityTheory
