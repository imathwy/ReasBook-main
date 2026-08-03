module

public import Topology_Munkres_2000.Book.Remark_60_1.AntipodalCover

public section

namespace RealProjectivePlane

/-- Helper for Remark 60.1: a compact closed embedding of the projective plane in
Euclidean three-space would select one point continuously from every antipodal pair. -/
lemma closedEmbedding_exists_quotientMapSection
    (f : RealProjectivePlane → EuclideanSpace ℝ (Fin 3))
    (hf : Topology.IsEmbedding f)
    (hcompact : IsCompact (Set.range f))
    (hclosed : IsClosed (Set.range f)) :
    ∃ s : RealProjectivePlane → UnitSphereThree,
      Continuous s ∧ Function.RightInverse s quotientMap := by
  -- TODO: Use local codimension-one separation of the embedded closed surface to choose
  -- one sheet of the antipodal cover on each chart, then glue the choices by lift uniqueness.
  sorry

end RealProjectivePlane
