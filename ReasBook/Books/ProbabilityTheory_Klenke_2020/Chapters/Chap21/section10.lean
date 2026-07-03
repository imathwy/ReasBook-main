import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_21_10_1 (from Items/Chap21) -/
open MeasureTheory
open OrderDual

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/- Exercise 21.10.1 is `source-facing`: the textbook variables `Y_n` are the unweighted quadratic
partition sums at the horizon `T = 1` from the proof of Theorem 21.64. Their
`core/canonical` owner is Chapter 21's pathwise construction
`weightedPartitionQuadraticVariationApproximationUpTo`; the only `bridge/view` content here is to
regard those pathwise sums as random variables and then as a reverse-time process on `ℕᵒᵈ`.

Primitive data:
* a real process `X : NNReal → Ω → ℝ`;
* an admissible partition sequence `P`.

Derived API:
* the random variables obtained by evaluating the pathwise partition sums on each sample point;
* the reverse-time process `n ↦ Y_n`, used in the backwards-martingale statement.
-/

/-- The unweighted quadratic partition sum along the `n`-th row of `P`, viewed as a real random
variable on `Ω`. -/
noncomputable def partitionQuadraticVariationApproximationUpToRandomVariable
    (X : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (T : NNReal) (n : ℕ) : Ω → ℝ :=
  fun ω ↦
    weightedPartitionQuadraticVariationApproximationUpTo
      (fun _ ↦ (1 : ℝ)) (fun t ↦ X t ω) P T n

section

variable (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
omit [MeasurableSpace Ω]

/-- Unfolding the random-variable bridge returns the underlying pathwise quadratic partition sum. -/
theorem partitionQuadraticVariationApproximationUpToRandomVariable_def
    (X : NNReal → Ω → ℝ) (T : NNReal) (n : ℕ) :
    partitionQuadraticVariationApproximationUpToRandomVariable X P T n =
      fun ω ↦
        weightedPartitionQuadraticVariationApproximationUpTo
          (fun _ ↦ (1 : ℝ)) (fun t ↦ X t ω) P T n :=
  rfl

end

/-- The reverse-time process associated with the quadratic partition sums up to the horizon `T`. -/
noncomputable abbrev partitionQuadraticVariationApproximationUpToBackwardProcess
    (X : NNReal → Ω → ℝ) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (T : NNReal) : ℕᵒᵈ → Ω → ℝ :=
  fun n ↦ partitionQuadraticVariationApproximationUpToRandomVariable X P T (ofDual n)

-- Proof sketch: each `Y_n` is a finite sum of products of the strongly measurable coordinates
-- `X (P n k)` and `X (partitionNextPointUpTo P n k T)`.
/-- Each quadratic partition-sum random variable is strongly measurable whenever the underlying
process is strongly measurable at every time. -/
theorem partitionQuadraticVariationApproximationUpToRandomVariable_stronglyMeasurable
    {X : NNReal → Ω → ℝ} (hX_meas : ∀ t, StronglyMeasurable (X t))
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] (T : NNReal) (n : ℕ) :
    StronglyMeasurable
      (partitionQuadraticVariationApproximationUpToRandomVariable X P T n) := by
  sorry

/-- The reverse-time quadratic partition-sum process is strongly measurable at every index. -/
theorem partitionQuadraticVariationApproximationUpToBackwardProcess_stronglyMeasurable
    {X : NNReal → Ω → ℝ} (hX_meas : ∀ t, StronglyMeasurable (X t))
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕᵒᵈ) :
    StronglyMeasurable
      (partitionQuadraticVariationApproximationUpToBackwardProcess X P T n) := by
  simpa [partitionQuadraticVariationApproximationUpToBackwardProcess] using
    partitionQuadraticVariationApproximationUpToRandomVariable_stronglyMeasurable
      hX_meas P T (ofDual n)

namespace IsBrownianMotion

-- Proof sketch: for the admissible partition sequence `P`, the random variables from the proof of
-- Theorem 21.64 are exactly the reverse-time process obtained by specializing
-- `weightedPartitionQuadraticVariationApproximationUpTo` to the constant weight `1` and the
-- horizon `T = 1`; the Brownian bridge/independent-increments argument identifies them as a
-- backwards martingale.
/-- Exercise 21.10.1: for Brownian motion `W` and an admissible partition sequence `P`, the
random variables `Y_n = \sum_{t \in \mathcal P_1^n} (W_{t'} - W_t)^2` from the proof of
Theorem 21.64 form a backwards martingale. -/
theorem partitionQuadraticVariationApproximationUpTo_one_backwardsMartingale
    {W : NNReal → Ω → ℝ} (hW : IsBrownianMotion μ W)
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] :
    Martingale
      (partitionQuadraticVariationApproximationUpToBackwardProcess W P 1)
      (Filtration.natural
        (partitionQuadraticVariationApproximationUpToBackwardProcess W P 1)
        (partitionQuadraticVariationApproximationUpToBackwardProcess_stronglyMeasurable
          hW.stronglyMeasurable P 1))
      μ := by
  sorry

end IsBrownianMotion

end ProbabilityTheory

/-! ### Exercise_21_10_2 (from Items/Chap21) -/
open Filter MeasureTheory ProbabilityTheory

noncomputable section

local notation "PathSpace" => C(NNReal, ℝ)
local notation "PathwiseProcess" => NNReal → ℝ

-- Proof sketch: first prove the claim for step functions that are constant on partition
-- intervals, where the weighted sums become finite linear combinations of the defining
-- convergence in `HasSquareVariationAlongPartition`. Then approximate a continuous `f` on
-- `[0, T]` uniformly by such step functions, use the vanishing mesh of `P`, and pass to the
-- Lebesgue--Stieltjes integral against the chosen representing measure `μV.measure`.
/-- Exercise 21.10.2: if `V` is a chosen square-variation path of `X` along the admissible
partition sequence `P`, then for every continuous `f : [0, ∞) → ℝ` the weighted quadratic
partition sums of `X` along `P` converge on `[0, T]` to the Lebesgue--Stieltjes integral of `f`
against a chosen Stieltjes-measure representation of `V`. -/
theorem tendsto_weightedPartitionQuadraticVariationApproximationUpTo
    (f : NNReal → ℝ) (hf : Continuous f) (X : PathSpace) {V : PathwiseProcess}
    (μV : Measure NNReal)
    (hμV :
      ∀ T : NNReal,
        V T = ∫ _ in Set.Icc 0 T, (1 : ℝ) ∂μV)
    (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (hX : HasSquareVariationAlongPartition X P V) :
    ∀ T : NNReal,
      Tendsto
        (fun n : ℕ ↦ weightedPartitionQuadraticVariationApproximationUpTo f X P T n)
        atTop
        (nhds (∫ s in Set.Icc 0 T, f s ∂μV)) := sorry

/-! ### Exercise_21_10_3 (from Items/Chap21) -/
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

/- Exercise 21.10.3 is `source-facing` existential content.

Domain-style sampling for the owner abstraction:
* `IsContinuousLocalMartingale` from Definition 21.66 is the chapter owner for the process `M`.
* `continuousSquareVariationProcess` from Theorem 21.70 is the canonical bracket owner, so the
  bracket is derived data rather than an extra primitive field.
* `IsStoppingTime` and `stoppedValue` are the existing owner-level interfaces for the stopping-time
  part of the statement.

Primitive data versus derived API:
* primitive data: the filtered probability space, the process `M`, and the stopping time `τ`;
* derived data: the bracket process `⟨M⟩ = continuousSquareVariationProcess hM`.

Accordingly, the exercise is stated directly with the canonical bracket owner instead of a local
package carrying a separate square-variation witness. -/

-- Proof sketch: take a Brownian motion `B` and stop it at an almost surely finite stopping time
-- with infinite mean, such as a return time to `0`; then `⟨B⟩_τ = τ` has infinite expectation,
-- while `B_τ = 0` almost surely keeps the stopped second moment finite.
/-- Exercise 21.10.3: there exists a continuous local martingale `M` with `M_0 = 0` and an almost
surely finite stopping time `τ` such that the stopped square variation has infinite expectation,
but the stopped second moment `E[M_τ^2]` is not infinite. -/
theorem exists_infinite_bracket_expectation_without_infinite_stopped_square_expectation :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω'),
      letI := mΩ'
      ∃ (μ : Measure Ω') (_ : IsProbabilityMeasure μ) (ℱ : Filtration NNReal mΩ')
        (M : NNReal → Ω' → ℝ) (τ : Ω' → ENNReal)
        (hM : IsContinuousLocalMartingale ℱ μ M),
        (∀ ω : Ω', M 0 ω = 0) ∧
          IsStoppingTime ℱ τ ∧
          (∀ᵐ ω ∂μ, τ ω ≠ ∞) ∧
          (∫⁻ ω,
              ENNReal.ofReal
                (stoppedValue (continuousSquareVariationProcess hM) τ ω) ∂μ) = ∞ ∧
          (∫⁻ ω, ENNReal.ofReal ((stoppedValue M τ ω) ^ (2 : ℕ)) ∂μ) ≠ ∞ := sorry

end ProbabilityTheory

/-! ### Remark_21_10 (from Items/Chap21) -/
open MeasureTheory ProbabilityTheory

universe u v w

variable {T : Type u} {Ω : Type v} {Ω' : Type w}
variable [MeasurableSpace Ω] [MeasurableSpace Ω']

-- Proof sketch: for a finite index set `I`, the owner finite-dimensional laws
-- `P.map (fun ω ↦ I.restrict (X · ω))` and `Q.map (fun ω ↦ I.restrict (Y · ω))` are Gaussian by
-- `IsGaussianProcess.hasGaussianLaw`; centeredness identifies their means with `0`, and the
-- covariance-function hypothesis identifies their covariance bilinear forms, so equality follows
-- from the finite-dimensional uniqueness of Gaussian laws by mean and covariance.
/-- Remark 21.10: the covariance function determines each finite-dimensional law of a centered
Gaussian process. Concretely, two centered Gaussian processes with the same covariance function
have the same finite-dimensional laws. -/
theorem finiteDimensionalDistributions_eq_of_centered_gaussian_covariance
    {P : Measure Ω} {Q : Measure Ω'}
    {X : T → Ω → ℝ} {Y : T → Ω' → ℝ}
    (hX : IsGaussianProcess X P) (hY : IsGaussianProcess Y Q)
    (hX_centered : ∀ t, P[X t] = 0)
    (hY_centered : ∀ t, Q[Y t] = 0)
    (hcov : ∀ s t, cov[X s, X t; P] = cov[Y s, Y t; Q])
    (I : Finset T) :
    P.map (fun ω ↦ I.restrict (X · ω)) = Q.map (fun ω ↦ I.restrict (Y · ω)) := sorry
