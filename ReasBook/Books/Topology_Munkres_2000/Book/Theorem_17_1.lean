module

import Mathlib.Topology.Basic

public section

universe u v

section

variable (X : Type u) [TopologicalSpace X]

/- Theorem 17.1 (1): The empty set and the universal set `X` are closed. -/
#check (isClosed_empty : IsClosed (∅ : Set X))
#check (isClosed_univ : IsClosed (Set.univ : Set X))

variable (s : Set (Set X))

/- Theorem 17.1 (2): Arbitrary intersections of closed subsets of `X` are closed. -/
#check (isClosed_sInter : (∀ t ∈ s, IsClosed t) → IsClosed (⋂₀ s))

variable (ι : Type v) [Finite ι] (f : ι → Set X)

/- Theorem 17.1 (3): Finite unions of closed subsets of `X` are closed. -/
#check (isClosed_iUnion_of_finite : (∀ i, IsClosed (f i)) → IsClosed (⋃ i, f i))

end
