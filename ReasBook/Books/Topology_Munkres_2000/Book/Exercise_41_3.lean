module

public import Mathlib.Topology.Compactness.Paracompact
import Topology_Munkres_2000.Book.Exercise_38_5.Instances
import Topology_Munkres_2000.Book.Exercise_41_2

public section

universe u

/-- Exercise 41.3: Not every locally compact Hausdorff space is paracompact;
`OpenOmegaOne` is a counterexample. -/
theorem not_all_locallyCompact_t2_paracompact :
    ¬ ∀ (X : Type (u + 1)) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X],
      ParacompactSpace X := by
  intro h
  exact OpenOmegaOne.notParacompact (h OpenOmegaOne)
