module

public import Topology_Munkres_2000.Book.Definition_29_1.LocalCompactness
public import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RatLemmas

public section

/- Example 29.1 (1): The real line is locally compact in the compact-neighborhood sense. -/
#check (inferInstance : WeaklyLocallyCompactSpace ℝ)

namespace Rat

/-- Example 29.1 (2): The rational numbers with their usual topology are not locally compact
in the compact-neighborhood sense. -/
theorem notWeaklyLocallyCompact : ¬ WeaklyLocallyCompactSpace ℚ := by
  intro h
  obtain ⟨K, hK, hK_mem⟩ := h.exists_compact_mem_nhds 0
  have hzero : (0 : ℚ) ∈ interior K := mem_interior_iff_mem_nhds.2 hK_mem
  rw [interior_compact_eq_empty hK] at hzero
  exact hzero

end Rat
