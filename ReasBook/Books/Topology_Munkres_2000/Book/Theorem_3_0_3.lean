module

public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.UniformSpace.HeineCantor

public section

/-- A continuous real-valued function on `Set.Icc a b` is uniformly continuous. -/
theorem uniformContinuousOnIcc {a b : ℝ} (f : Set.Icc a b → ℝ) (hf : Continuous f) :
    UniformContinuous f :=
  CompactSpace.uniformContinuous_of_continuous hf

/-- Theorem 3.0.3. A continuous real-valued function on `Set.Icc a b` satisfies
the uniform ε-δ continuity condition. -/
theorem uniformContinuityOnIcc {a b : ℝ} (f : Set.Icc a b → ℝ) (hf : Continuous f) :
    ∀ ε > 0, ∃ δ > 0, ∀ x₁ x₂, dist x₁ x₂ < δ → dist (f x₁) (f x₂) < ε := by
  simpa only using Metric.uniformContinuous_iff.mp (uniformContinuousOnIcc f hf)
