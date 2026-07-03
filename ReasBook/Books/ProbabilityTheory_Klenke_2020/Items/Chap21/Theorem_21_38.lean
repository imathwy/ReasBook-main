import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

namespace ProbabilityTheory

local notation "Ω" => C(NNReal, ℝ)

local instance continuousPathSpaceMeasurableSpace : MeasurableSpace Ω :=
  borel Ω

local instance continuousPathSpaceBorelSpace : BorelSpace Ω :=
  ⟨rfl⟩

-- Proof sketch: each coordinate map `ω ↦ ω (times i)` is continuous on `C([0, ∞), ℝ)`, and a
-- finite product of measurable coordinate maps is measurable.
/-- The projection sending a continuous path to its values at a finite tuple of times is
measurable. -/
theorem measurable_continuousPathProjection {n : ℕ} (times : Fin (n + 1) → NNReal) :
    Measurable (fun ω : Ω ↦ fun i ↦ ω (times i)) := sorry

/-- The finite-dimensional marginal of a probability measure on `C([0, ∞), ℝ)` along the time
tuple `times`. -/
noncomputable def continuousPathFiniteDimensionalDistribution (μ : ProbabilityMeasure Ω)
    {n : ℕ} (times : Fin (n + 1) → NNReal) : ProbabilityMeasure (Fin (n + 1) → ℝ) :=
  ProbabilityMeasure.map μ (measurable_continuousPathProjection times).aemeasurable

-- Proof sketch: unfold `continuousPathFiniteDimensionalDistribution`; it is defined as the
-- pushforward of `μ` by the path-evaluation map `ω ↦ (ω (times i))ᵢ`.
/-- Coercing the finite-dimensional marginal to a measure recovers the corresponding pushforward
measure. -/
theorem continuousPathFiniteDimensionalDistribution_toMeasure (μ : ProbabilityMeasure Ω)
    {n : ℕ} (times : Fin (n + 1) → NNReal) :
    (continuousPathFiniteDimensionalDistribution μ times : Measure (Fin (n + 1) → ℝ)) =
      (μ : Measure Ω).map (fun ω ↦ fun i ↦ ω (times i)) := sorry

-- Proof sketch: weak convergence on `C([0, ∞), ℝ)` implies weak convergence of every finite-time
-- projection by continuity of the projection map, and Prokhorov yields tightness. Conversely,
-- tightness gives relative compactness, and Lemma 21.36 identifies every subsequential weak limit
-- with `P` from the common finite-dimensional marginals.
/-- Theorem 21.38: for probability measures on `C([0, ∞), ℝ)`, weak convergence is equivalent to
finite-dimensional-distribution convergence together with tightness of the sequence. -/
theorem tendsto_iff_finiteDimensionalDistribution_tendsto_and_isTight
    (P : ProbabilityMeasure Ω) (Pn : ℕ → ProbabilityMeasure Ω) :
    ((∀ n : ℕ, ∀ times : Fin (n + 1) → NNReal,
        Tendsto (fun k ↦ continuousPathFiniteDimensionalDistribution (Pn k) times) atTop
          (𝓝 (continuousPathFiniteDimensionalDistribution P times))) ∧
      IsTightMeasureSet (Set.range fun n ↦ (Pn n : Measure Ω))) ↔
        Tendsto Pn atTop (𝓝 P) := sorry

end ProbabilityTheory
