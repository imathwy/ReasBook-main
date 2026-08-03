module

public import Mathlib.Topology.Constructions

public section

universe u

variable (X : Type u)

/- Example 12.3: The subsets `U` with `U = ∅` or finite complement form the
finite complement topology on `X`. -/
#check (TopologicalSpace.cofinite : TopologicalSpace X)
#check (CofiniteTopology.isOpen_iff' :
  ∀ {U : Set (CofiniteTopology X)}, IsOpen U ↔ U = ∅ ∨ Uᶜ.Finite)
