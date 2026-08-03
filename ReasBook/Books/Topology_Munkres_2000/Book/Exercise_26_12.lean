module

public import Topology_Munkres_2000.Book.Definition_26_7.PerfectMap
public import Topology_Munkres_2000.Book.Exercise_26_12.ProperMap

public section

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

namespace IsPerfectMap

/-- Exercise 26.12: If the codomain of a perfect map is compact, then its domain is compact. -/
theorem compactSpace {p : X → Y} (hp : IsPerfectMap p) [CompactSpace Y] : CompactSpace X :=
  hp.toIsProperMap.compactSpace

end IsPerfectMap
