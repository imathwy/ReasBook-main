module

public import Topology_Munkres_2000.Book.Definition_61_1.Separation
public import Topology_Munkres_2000.Book.Definition_61_2.Arc
public import Topology_Munkres_2000.Book.Definition_55_2.Instances
import Topology_Munkres_2000.Book.Exercise_62_2
import Topology_Munkres_2000.Book.Exercise_51_3.Contractible

public section

open Set

/-- Theorem 63.2 (A nonseparation theorem). An arc in the standard two-sphere
does not separate the sphere. -/
theorem arc_not_separates (D : Set (StandardSphere 2)) [Topology.IsArc D] :
    ¬ D.Separates := by
  -- Use unit-interval coordinates to transport compactness and contractibility to the arc.
  obtain ⟨e⟩ := Topology.IsArc.homeomorphic_unitInterval (X := D)
  letI : CompactSpace D := e.symm.compactSpace
  letI : ContractibleSpace D := e.contractibleSpace
  -- The compact-contractible nonseparation theorem now applies directly.
  exact compactContractible_not_separates_twoSphere D
