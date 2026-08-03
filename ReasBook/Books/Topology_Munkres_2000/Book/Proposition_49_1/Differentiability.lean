module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Topology.UnitInterval

public section

open Set

namespace ClosedUnitInterval

/-- A real-valued function on the closed unit interval is nowhere differentiable
if none of its extensions to `ℝ` is differentiable within the interval at any
point. -/
def IsNowhereDifferentiable (f : unitInterval → ℝ) : Prop :=
  ∀ g : ℝ → ℝ, (∀ y : unitInterval, g y = f y) →
    ∀ x : unitInterval, ¬ DifferentiableWithinAt ℝ g (Icc (0 : ℝ) 1) x

end ClosedUnitInterval
