import AchimKlenkeLean.Items.Chap09.Example_9_8
import AchimKlenkeLean.Items.Chap08.Example_8_27
import AchimKlenkeLean.Items.Chap17.Definition_17_16
import AchimKlenkeLean.Items.Chap17.Theorem_17_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: unfold the recursive definition of `stochasticMatrixTrajectory`; at each step the
-- random map adds the current increment `Z n`, so induction on `n` identifies the trajectory with
-- the initial state plus the partial-sum process `randomWalkProcess Z`.
/-- The random mapping trajectory driven by `R_n(y) = y + Z_n` is the initial state plus the
partial sums of the increment sequence. -/
theorem stochasticMatrixTrajectory_add_eq_randomWalkProcess
    {Ω' : Type v} (Z : ℕ → Ω' → ℤ) (x : ℤ) :
    ∀ n : ℕ,
      stochasticMatrixTrajectory (fun k ω y ↦ y + Z k ω) x n =
        fun ω ↦ x + randomWalkProcess Z n ω := sorry

-- Proof sketch: realize the chain with transition matrix `p` through its owner abstraction
-- `IsMarkovProcessRealization`, sample i.i.d. increments with common law given by the row at the
-- origin, and drive the random maps `R_n(y) = y + Z_n`. The resulting trajectory has the same
-- transition semigroup as `X`, so the finite-dimensional distributions agree.
/-- Example 17.18: if a discrete-time Markov chain on `ℤ` has translation-invariant transition
matrix `p`, then for every starting state `x` it has the same finite-dimensional distributions as
the chain driven by i.i.d. increments with common law the row `p(0, ·)`, realized through the
random maps `R_n(y) = y + Z_n`. -/
theorem exists_randomMappingRepresentation_of_translationInvariantTransitionMatrix
    (p : ℤ → ℤ → ℝ≥0∞) (hp_stochastic : IsStochasticMatrix p)
    (hp : IsTranslationInvariantStepMatrix p)
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ) (x : ℤ)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] :
    ∃ (Ω' : Type v), ∃ _ : MeasurableSpace Ω', ∃ Q : ProbabilityMeasure Ω', ∃ Z : ℕ → Ω' → ℤ,
      iIndepFun Z (Q : Measure Ω') ∧
        (∀ n : ℕ,
          HasLaw (Z n) (discreteMatrixKernel p 0) (Q : Measure Ω')) ∧
        ∀ {n : ℕ} (times : Fin (n + 1) → ℕ), times 0 = 0 → StrictMono times →
          (P x : Measure Ω).map (fun ω i ↦ X (times i) ω) =
            (Q : Measure Ω').map
              (fun ω i ↦ stochasticMatrixTrajectory (fun k ω' y ↦ y + Z k ω') x (times i) ω) :=
            sorry

-- Proof sketch: apply
-- `exists_randomMappingRepresentation_of_translationInvariantTransitionMatrix` and rewrite the
-- random-mapping trajectory using
-- `stochasticMatrixTrajectory_add_eq_randomWalkProcess`.
/-- Equivalently, a chain with translation-invariant transition matrix has the same finite-
dimensional distributions as the partial-sum random walk `x + ∑_{i < n} Z_i` with i.i.d.
increments of law `p(0, ·)`. In Lean's `0`-based indexing, `randomWalkProcess Z n` is the
textbook sum `Z₁ + ⋯ + Zₙ`. -/
theorem isIntegerRandomWalk_of_translationInvariantTransitionMatrix
    (p : ℤ → ℤ → ℝ≥0∞) (hp_stochastic : IsStochasticMatrix p)
    (hp : IsTranslationInvariantStepMatrix p)
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ) (x : ℤ)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] :
    ∃ (Ω' : Type v), ∃ _ : MeasurableSpace Ω', ∃ Q : ProbabilityMeasure Ω', ∃ Z : ℕ → Ω' → ℤ,
      iIndepFun Z (Q : Measure Ω') ∧
        (∀ n : ℕ,
          HasLaw (Z n) (discreteMatrixKernel p 0) (Q : Measure Ω')) ∧
        ∀ {n : ℕ} (times : Fin (n + 1) → ℕ), times 0 = 0 → StrictMono times →
          (P x : Measure Ω).map (fun ω i ↦ X (times i) ω) =
            (Q : Measure Ω').map
              (fun ω i ↦ x + randomWalkProcess Z (times i) ω) := sorry
