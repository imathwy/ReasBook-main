module

import Mathlib.Topology.Sequences

open Set

universe u v

section Closure

variable {X : Type u} [TopologicalSpace X] (A : Set X)

/- Theorem 30.1 (1). Every sequential limit of points of `A` belongs to `closure A`. -/
#check (seqClosure_subset_closure : seqClosure A ⊆ closure A)

variable [FirstCountableTopology X]

/- Theorem 30.1 (2). In a first-countable space, every point of `closure A` is a
sequential limit of points of `A`. -/
#check (FrechetUrysohnSpace.closure_subset_seqClosure A : closure A ⊆ seqClosure A)

end Closure

section Continuity

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)

/- Theorem 30.1 (3). A continuous map preserves limits of sequences. -/
#check (Continuous.seqContinuous : Continuous f → SeqContinuous f)

variable [FirstCountableTopology X]

/- Theorem 30.1 (4). On a first-countable domain, a map preserving limits of sequences
is continuous. -/
#check (SeqContinuous.continuous : SeqContinuous f → Continuous f)

end Continuity
