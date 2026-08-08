import Mathlib
import ProbabilityTheory_Klenke_2020.Chap09.Example_9_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

-- Proof sketch: use the Gaussian translation semigroup `κ_t(x, ·) = δ_x ∗ 𝒩(0,t)` and the
-- initial law `δ₀` to obtain a unique path-space measure from the Markov-semigroup construction of
-- Corollary 14.44 / Kolmogorov extension, then identify the finite-dimensional laws by Theorem
-- 14.28 to get independent stationary Gaussian increments and the start at `0`.
/-- Example 14.45: on the canonical path space `ℝ^[0,∞)`, there is a unique probability measure
under which the coordinate process starts at `0` and has independent, stationary, normally
distributed increments. -/
theorem existsUnique_pathMeasure_independent_stationary_gaussian_increments :
    ∃! μ : Measure (NNReal → ℝ),
      IsProbabilityMeasure μ ∧
        HasLaw (Function.eval 0) (Measure.dirac 0) μ ∧
        HasStationaryIndependentIncrements Function.eval μ ∧
        ∀ ⦃s t : NNReal⦄, s ≤ t →
          HasLaw (fun ω : NNReal → ℝ ↦ ω t - ω s) (gaussianReal 0 (t - s)) μ := sorry

/-- The canonical path-space law with independent stationary centered Gaussian increments starting
at `0`. -/
noncomputable def gaussianIncrementPathMeasure : Measure (NNReal → ℝ) :=
  Classical.choose existsUnique_pathMeasure_independent_stationary_gaussian_increments

-- Proof sketch: apply `Classical.choose_spec` to the unique-existence theorem defining
-- `gaussianIncrementPathMeasure`.
/-- The chosen Gaussian increment path measure satisfies the defining start-at-zero and
independent-stationary-Gaussian-increment properties. -/
theorem gaussianIncrementPathMeasure_spec :
    IsProbabilityMeasure gaussianIncrementPathMeasure ∧
      HasLaw (Function.eval 0) (Measure.dirac 0) gaussianIncrementPathMeasure ∧
      HasStationaryIndependentIncrements Function.eval gaussianIncrementPathMeasure ∧
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        HasLaw
          (fun ω : NNReal → ℝ ↦ ω t - ω s)
          (gaussianReal 0 (t - s))
          gaussianIncrementPathMeasure := by
  rcases Classical.choose_spec
      existsUnique_pathMeasure_independent_stationary_gaussian_increments with
    ⟨hμ, _⟩
  exact hμ

/-- The chosen Gaussian increment path measure is a probability measure. -/
instance : IsProbabilityMeasure gaussianIncrementPathMeasure := by
  rcases gaussianIncrementPathMeasure_spec with ⟨hprob, _, _, _⟩
  exact hprob

/-- The chosen Gaussian increment path measure starts from `0`. -/
theorem gaussianIncrementPathMeasure_start_hasLaw :
    HasLaw (Function.eval 0) (Measure.dirac 0) gaussianIncrementPathMeasure := by
  rcases gaussianIncrementPathMeasure_spec with ⟨_, hstart, _, _⟩
  exact hstart

/-- The chosen Gaussian increment path measure has stationary independent increments for the
canonical coordinate process. -/
theorem gaussianIncrementPathMeasure_hasStationaryIndependentIncrements :
    HasStationaryIndependentIncrements Function.eval gaussianIncrementPathMeasure := by
  rcases gaussianIncrementPathMeasure_spec with ⟨_, _, hinc, _⟩
  exact hinc

/-- Under the chosen Gaussian increment path measure, every increment over `[s,t]` has the
centered Gaussian law with variance `t - s`. -/
theorem gaussianIncrementPathMeasure_increment_hasLaw {s t : NNReal} (hst : s ≤ t) :
    HasLaw
      (fun ω : NNReal → ℝ ↦ ω t - ω s)
      (gaussianReal 0 (t - s))
      gaussianIncrementPathMeasure := by
  rcases gaussianIncrementPathMeasure_spec with ⟨_, _, _, hgauss⟩
  exact hgauss hst
