module

import Mathlib.Topology.ContinuousMap.Defs

universe u v

/- Notation 52.2: The source writes `h : (X, x₀) → (Y, y₀)` to record that a
continuous map `h : C(X, Y)` carries `x₀` to `y₀`. In Lean this condition is
the equality `h x₀ = y₀`. -/
#check fun {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (h : C(X, Y)) (x₀ : X) (y₀ : Y) ↦ h x₀ = y₀
