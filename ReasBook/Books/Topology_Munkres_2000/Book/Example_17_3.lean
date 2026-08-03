module

public import Mathlib.Topology.Constructions

public section

universe u

variable (X : Type u)

/- Example 17.3: In the finite complement topology on `X`, the closed sets are
`Set.univ` and the finite subsets of `X`. -/
#check (CofiniteTopology.isClosed_iff :
  ∀ {s : Set (CofiniteTopology X)}, IsClosed s ↔ s = Set.univ ∨ s.Finite)
