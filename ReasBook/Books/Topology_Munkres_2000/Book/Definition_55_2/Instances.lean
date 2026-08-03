module

public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Mathlib.Analysis.Normed.Module.Connected

public section

namespace StandardSphere

/-- The standard two-sphere is connected. -/
instance instConnectedSpaceTwo : ConnectedSpace (StandardSphere 2) := by
  -- Compute that the ambient Euclidean space has dimension greater than one.
  have ambientRank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    apply Module.one_lt_rank_of_one_lt_finrank
    rw [finrank_euclideanSpace_fin]
    norm_num
  -- Apply sphere connectedness and transfer it to the sphere subtype.
  exact Subtype.connectedSpace (isConnected_sphere ambientRank 0 zero_le_one)

end StandardSphere
