module

public import Topology_Munkres_2000.Book.Definition_81_6.ProperlyDiscontinuous
public import Mathlib.Topology.Compactness.LocallyCompact

public section

universe u v

namespace ProperlyDiscontinuousSMul

variable {G : Type u} {X : Type v} [Group G] [TopologicalSpace X] [MulAction G X]

/-- A free properly discontinuous action in the compact-set sense is properly discontinuous
in the neighborhood-disjointness sense. -/
instance toProperlyDiscontinuousMulAction [ContinuousConstSMul G X] [T2Space X]
    [LocallyCompactSpace X] [IsCancelSMul G X] [ProperlyDiscontinuousSMul G X] :
    ProperlyDiscontinuousMulAction G X := by
  refine { exists_nhds_disjoint_image := ?_ }
  intro x
  -- Compact-set proper discontinuity supplies the neighborhood; freeness rules out stabilizers.
  obtain ⟨U, hU, hdisjoint⟩ :=
    ProperlyDiscontinuousSMul.exists_nhds_disjoint_image G x
  refine ⟨U, hU, ?_⟩
  intro g hg
  apply hdisjoint g
  intro hfixed
  exact hg (IsCancelSMul.eq_one_of_smul hfixed)

end ProperlyDiscontinuousSMul

namespace MulAction

variable {G : Type u} {X : Type v} [Group G] [TopologicalSpace X] [MulAction G X]

/-- The orbit space of a locally compact space under a continuous group action is locally
compact. -/
instance instLocallyCompactSpaceOrbitRelQuotient [ContinuousConstSMul G X]
    [LocallyCompactSpace X] : LocallyCompactSpace (Quotient (orbitRel G X)) :=
  MulAction.isOpenQuotientMap_quotientMk.locallyCompactSpace

end MulAction
