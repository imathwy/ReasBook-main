module

public import Topology_Munkres_2000.Book.Example_28_2.Instances

public section

namespace OpenOmegaOne

/-- Helper for Exercise 38.5: every point of the open first-uncountable ordinal has a
compact neighborhood. -/
instance instWeaklyLocallyCompactSpace : WeaklyLocallyCompactSpace OpenOmegaOne where
  exists_compact_mem_nhds a := by
    -- A compact initial interval ending past `a` is a neighborhood of `a`.
    obtain ⟨b, hab⟩ := exists_gt a
    exact ⟨Set.Iic b, isCompact_Iic b, Iic_mem_nhds hab⟩

/-- The open first-uncountable ordinal is locally compact. -/
instance instLocallyCompactSpace : LocallyCompactSpace OpenOmegaOne := by
  exact inferInstance

end OpenOmegaOne

end
