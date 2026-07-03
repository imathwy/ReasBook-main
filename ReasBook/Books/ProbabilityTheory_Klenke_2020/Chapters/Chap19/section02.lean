import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_19_2_1 (from Items/Chap19) -/
open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

namespace Kernel

/-- A continuous linear endomorphism of `L²(π)` realizes kernel averaging along `κ` if every
square-integrable representative `φ` is sent to the `L²(π)` class of `x ↦ ∫ y, φ y ∂κ x`.
Because the condition is required for every representative of an `L²` class, it encodes the
descent of kernel averaging to a genuine operator on `L²(π)` rather than depending on a chosen
coercion `L²(π) → E → ℝ`. -/
def IsL2TransitionOperator (κ : Kernel E E) (π : Measure E)
    (T : (E →₂[π] ℝ) →L[ℝ] (E →₂[π] ℝ)) : Prop :=
  ∀ ⦃φ : E → ℝ⦄ (hφ : MemLp φ 2 π), T (hφ.toLp φ) =ᵐ[π] fun x ↦ ∫ y, φ y ∂κ x

end Kernel

-- Proof sketch: for the forward implication, use detailed balance to rewrite
-- `⟪T f, g⟫ = ∫ x ∫ y, f y * g x ∂(discreteMatrixKernel p x) ∂π` symmetrically in `f` and `g`,
-- giving a symmetric operator and hence a self-adjoint one. For the reverse implication, test the
-- symmetry identity on indicator functions of measurable sets to recover the detailed-balance
-- equality in the definition of `Kernel.IsReversible`.
/-- Exercise 19.2.1: a discrete transition matrix `p` is reversible with respect to `π` if and
only if the `L²(π)` Markov operator `f ↦ p f` is self-adjoint. Here the operator is represented by
any continuous linear map on `L²(π)` that realizes one-step averaging against
`discreteMatrixKernel p` on every square-integrable representative. -/
theorem discreteMatrix_isReversible_iff_markovOperator_isSelfAdjoint
    {p : E → E → ℝ≥0∞} {π : Measure E}
    {T : (E →₂[π] ℝ) →L[ℝ] (E →₂[π] ℝ)}
    (hT : (discreteMatrixKernel p).IsL2TransitionOperator π T) :
    IsReversible (discreteMatrixKernel p) π ↔ IsSelfAdjoint T := sorry

end ProbabilityTheory

/-! ### Exercise_19_2_2 (from Items/Chap19) -/
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

/-! ### Theorem_19_2 (from Items/Chap19) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E]

-- Proof sketch: for each `x ∉ A`, combine the integrability of `f` and `g` under `κ x`, use
-- linearity of the integral, and substitute the harmonicity identities for `f` and `g`.
/-- Theorem 19.2: if `f` and `g` are harmonic outside `A` for a kernel `κ`, then every linear
combination `α • f + β • g` is harmonic outside `A` as well. -/
theorem IsHarmonicOutside.smul_add
    {κ : Kernel E E} {A : Set E} {f g : E → ℝ}
    (hf : IsHarmonicOutside κ A f) (hg : IsHarmonicOutside κ A g) (α β : ℝ) :
    IsHarmonicOutside κ A (α • f + β • g) := sorry

end ProbabilityTheory
