module

public import Topology_Munkres_2000.Book.Theorem_31_1

public section

universe u v

/- Exercise 31.8 uses the canonical action data `MulAction G X` and `ContinuousSMul G X`, and
the canonical orbit space `MulAction.orbitRel.Quotient G X`. -/

/-- Exercise 31.8 (1): Hausdorffness descends to the orbit quotient of a continuous action by a
compact topological group. -/
theorem t2SpaceOrbitQuotientOfCompact (G : Type u) (X : Type v)
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [CompactSpace G]
    [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X] [T2Space X] :
    T2Space (MulAction.orbitRel.Quotient G X) := inferInstance

/-- Exercise 31.8 (2): Regularity descends to the orbit quotient of a continuous action by a
compact topological group, using the book's `T3Space` convention. -/
theorem t3SpaceOrbitQuotientOfCompact (G : Type u) (X : Type v)
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [CompactSpace G]
    [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X] [T3Space X] :
    T3Space (MulAction.orbitRel.Quotient G X) := inferInstance

/-- Exercise 31.8 (3): Normality descends to the orbit quotient of a continuous action by a
compact topological group, using the book's `T4Space` convention. -/
theorem t4SpaceOrbitQuotientOfCompact (G : Type u) (X : Type v)
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [CompactSpace G]
    [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X] [T4Space X] :
    T4Space (MulAction.orbitRel.Quotient G X) := inferInstance

/-- Exercise 31.8 (4): Local compactness descends to the orbit quotient of a continuous action by
a compact topological group, in the book's `WeaklyLocallyCompactSpace` sense. -/
theorem weaklyLocallyCompactSpaceOrbitQuotientOfCompact (G : Type u) (X : Type v)
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [CompactSpace G]
    [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
    [WeaklyLocallyCompactSpace X] :
    WeaklyLocallyCompactSpace (MulAction.orbitRel.Quotient G X) := inferInstance

/-- Exercise 31.8 (5): Second countability descends to the orbit quotient of a continuous action by
a compact topological group. -/
theorem secondCountableTopologyOrbitQuotientOfCompact (G : Type u) (X : Type v)
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [CompactSpace G]
    [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
    [SecondCountableTopology X] :
    SecondCountableTopology (MulAction.orbitRel.Quotient G X) := inferInstance
