module

public import Topology_Munkres_2000.Book.Definition_26_7.PerfectMap
public import Mathlib.Topology.Algebra.Group.Pointwise

public section

universe u v

namespace MulAction.OrbitQuotient

/-- The orbit projection for a continuous action by a compact topological group is a perfect
map. -/
public theorem isPerfectMap_quotientMk {G : Type u} {X : Type v}
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [CompactSpace G]
    [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X] :
    IsPerfectMap (Quotient.mk (MulAction.orbitRel G X)) := by
  -- Use the closed quotient map and reduce compactness of its fibers to compactness of orbits.
  rw [isPerfectMap_iff]
  refine ⟨continuous_quotient_mk', MulAction.isClosedMap_quotient,
    Quotient.mk_surjective, ?_⟩
  intro (y : MulAction.orbitRel.Quotient G X)
  have h_fiber :
      (Quotient.mk (MulAction.orbitRel G X)) ⁻¹' {y} = y.orbit := by
    ext x
    rw [Set.mem_preimage, Set.mem_singleton_iff,
      MulAction.orbitRel.Quotient.mem_orbit, @Quotient.mk''_eq_mk]
  rw [h_fiber]
  induction y using Quotient.inductionOn'
  rw [MulAction.orbitRel.Quotient.orbit_mk, MulAction.orbit, ← Set.image_univ]
  exact isCompact_univ.image (continuous_id.smul continuous_const)

end MulAction.OrbitQuotient
