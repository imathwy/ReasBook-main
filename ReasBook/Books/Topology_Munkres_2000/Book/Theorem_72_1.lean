module

public import Topology_Munkres_2000.Book.Theorem_72_1.Attachment
public import Topology_Munkres_2000.Book.Lemma_55_1.Inclusions
public import Mathlib.Topology.Connected.PathConnected

public section

universe u

/-- Theorem 72.1 (1): If a disk map sends its interior bijectively onto the complement
of a closed path-connected subspace, then inclusion induces a surjection on fundamental groups. -/
theorem adjoinTwoCell_inclusion_surjective {X : Type u} [TopologicalSpace X]
    [T2Space X] (A : Set X) (hA_closed : IsClosed A)
    (hA_pathConnected : IsPathConnected A) (h : C(B², X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary 1) A)
    (h_interior : Set.BijOn h ClosedUnitDisk.interior Aᶜ)
    (p : StandardSphere.boundary 1) :
    Function.Surjective
      (FundamentalGroup.mapOfSubtype A (ClosedUnitDisk.boundaryMap A h h_boundary p)) := sorry

/-- Theorem 72.1 (2): Under the same bijective-interior attachment hypothesis, the
kernel of the inclusion-induced homomorphism is the least normal subgroup containing
the image of the attaching-loop homomorphism. -/
theorem adjoinTwoCell_inclusion_ker {X : Type u} [TopologicalSpace X]
    [T2Space X] (A : Set X) (hA_closed : IsClosed A)
    (hA_pathConnected : IsPathConnected A) (h : C(B², X))
    (h_boundary : Set.MapsTo h (StandardSphere.boundary 1) A)
    (h_interior : Set.BijOn h ClosedUnitDisk.interior Aᶜ)
    (p : StandardSphere.boundary 1) :
    (FundamentalGroup.mapOfSubtype A (ClosedUnitDisk.boundaryMap A h h_boundary p)).ker =
      Subgroup.normalClosure
        (Set.range (FundamentalGroup.map (ClosedUnitDisk.boundaryMap A h h_boundary) p)) := sorry

end
