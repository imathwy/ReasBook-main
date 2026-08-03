module

import Mathlib.Data.PNat.Defs
import Mathlib.Topology.Neighborhoods

universe u

/- Exercise 3.99.3 (1): When the directed index type is `ℕ+`, a net in `X`
is a positive-integer-indexed sequence, namely a function `ℕ+ → X`. -/
#check fun (X : Type u) ↦ (ℕ+ → X)

/- Exercise 3.99.3 (2): For a sequence indexed by `ℕ+`, convergence to `x`
means that every open neighborhood of `x` contains every term from some index
onward. -/
#check fun {X : Type u} [TopologicalSpace X] (sequence : ℕ+ → X) (x : X) ↦
  (tendsto_atTop_nhds :
    Filter.Tendsto sequence Filter.atTop (nhds x) ↔
      ∀ U, x ∈ U → IsOpen U → ∃ N : ℕ+, ∀ n, N ≤ n → sequence n ∈ U)
