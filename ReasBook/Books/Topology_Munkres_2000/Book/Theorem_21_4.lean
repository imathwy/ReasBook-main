module

import Mathlib.Topology.Sequences

public section

open Filter Set
open scoped Topology

universe u

/- Theorem 21.4. In a metrizable space, every point of `closure A` is the limit of a
sequence of points of `A`. -/
#check (mem_closure_iff_seq_limit.mp :
  ∀ {X : Type u} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    {A : Set X} {x : X},
    x ∈ closure A →
      ∃ sequence : ℕ → X, (∀ n, sequence n ∈ A) ∧ Tendsto sequence atTop (𝓝 x))
