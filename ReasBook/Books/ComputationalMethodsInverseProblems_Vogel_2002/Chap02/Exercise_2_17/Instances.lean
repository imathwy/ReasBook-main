module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

public section

universe u

/-- Finite-dimensionality transports along the canonical linear equivalence
`toWeakSpace ℝ H : H ≃ₗ[ℝ] WeakSpace ℝ H`. -/
instance weakSpaceFiniteDimensional
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] :
    FiniteDimensional ℝ (WeakSpace ℝ H) :=
  (toWeakSpace ℝ H).finiteDimensional
