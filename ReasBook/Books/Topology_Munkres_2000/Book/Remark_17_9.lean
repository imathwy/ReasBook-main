module

import Mathlib.Topology.Neighborhoods

universe u

/- Remark 17.9: A sequence `x₁, x₂, ...` in a topological space converges to
`x` exactly when every open neighborhood `U` of `x` contains every term from
some index onward. This is `tendsto_atTop_nhds` specialized to `ℕ`. -/
#check fun {X : Type u} [TopologicalSpace X] (sequence : ℕ → X) (x : X) ↦
  (tendsto_atTop_nhds :
    Filter.Tendsto sequence Filter.atTop (nhds x) ↔
      ∀ U, x ∈ U → IsOpen U → ∃ N : ℕ, ∀ n, N ≤ n → sequence n ∈ U)
