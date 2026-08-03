module

public import Mathlib.Topology.Maps.Proper.Basic

public section

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

namespace IsProperMap

/-- A proper map with compact codomain has compact domain. -/
theorem compactSpace {p : X → Y} (hp : IsProperMap p) [CompactSpace Y] : CompactSpace X := by
  rw [← isCompact_univ_iff]
  simpa using hp.isCompact_preimage isCompact_univ

end IsProperMap
