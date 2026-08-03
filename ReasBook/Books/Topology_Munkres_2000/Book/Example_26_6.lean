module

public import Topology_Munkres_2000.Book.Exercise_17_16.Separation
public import Mathlib.Topology.NoetherianSpace

public section

/- Example 26.6 (1). In the finite complement topology on `ℝ`, the closed sets
are `Set.univ` and the finite subsets. -/
#check (CofiniteTopology.isClosed_iff :
  ∀ {s : Set (CofiniteTopology ℝ)}, IsClosed s ↔ s = Set.univ ∨ s.Finite)

/- Example 26.6 (2). Every subset of `ℝ` with the finite complement topology is
compact. -/
#check (TopologicalSpace.NoetherianSpace.isCompact :
  ∀ s : Set (CofiniteTopology ℝ), IsCompact s)

/- Example 26.6: The finite complement topology on `ℝ` is not Hausdorff. -/
#check RealTopology.cofiniteNotT2Space
