module

import Mathlib.Topology.Sequences

open Filter Set
open scoped Topology

universe u

/- Lemma 21.2 (1). The limit of a sequence in `A` belongs to `closure A`. -/
#check seqClosure_subset_closure

/- Lemma 21.2 (2). In a metrizable space, every point of `closure A` is the
limit of a sequence in `A`. -/
#check (mem_closure_iff_seq_limit.mp :
  ∀ {X : Type u} [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X]
    {A : Set X} {x : X},
    x ∈ closure A →
      ∃ sequence : ℕ → X, (∀ n, sequence n ∈ A) ∧ Tendsto sequence atTop (𝓝 x))
