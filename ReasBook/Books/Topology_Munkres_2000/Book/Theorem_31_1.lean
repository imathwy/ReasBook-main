module

public import Topology_Munkres_2000.Book.Definition_31_4
public import Topology_Munkres_2000.Book.Definition_26_7.PerfectMap
import Topology_Munkres_2000.Book.Exercise_31_6.ClosedMap
import Topology_Munkres_2000.Book.Exercise_31_7
public import Mathlib.Topology.Algebra.Group.Pointwise

public section

universe u v

namespace MulAction.OrbitQuotient

/-- Helper for Theorem 31.1: every orbit of a continuous action by a compact monoid is
compact. -/
private lemma isCompact_orbit_of_compact {G : Type u} {X : Type v}
    [TopologicalSpace G] [Monoid G] [CompactSpace G]
    [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X] (x : X) :
    IsCompact (MulAction.orbit G x) := by
  -- Realize the orbit as the image of the compact group under the orbit map.
  rw [MulAction.orbit, ← Set.image_univ]
  exact isCompact_univ.image (continuous_id.smul continuous_const)

/-- Helper for Theorem 31.1: a fiber of the orbit projection is the orbit represented by its
quotient point. -/
private lemma preimage_singleton_quotientMk_eq_orbit {G : Type u} {X : Type v}
    [Group G] [MulAction G X] (y : MulAction.orbitRel.Quotient G X) :
    (Quotient.mk (MulAction.orbitRel G X)) ⁻¹' {y} = y.orbit := by
  -- Membership on both sides says exactly that the point has quotient class `y`.
  ext x
  rw [Set.mem_preimage, Set.mem_singleton_iff,
    MulAction.orbitRel.Quotient.mem_orbit, @Quotient.mk''_eq_mk]

/-- Helper for Theorem 31.1: every fiber of the orbit projection for a compact continuous
action is compact. -/
private lemma isCompact_preimage_singleton_quotientMk {G : Type u} {X : Type v}
    [TopologicalSpace G] [Group G] [CompactSpace G]
    [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
    (y : MulAction.orbitRel.Quotient G X) :
    IsCompact ((Quotient.mk (MulAction.orbitRel G X)) ⁻¹' {y}) := by
  -- Replace the fiber by its orbit and reduce a quotient point to a representative.
  rw [preimage_singleton_quotientMk_eq_orbit]
  induction y using Quotient.inductionOn'
  rw [MulAction.orbitRel.Quotient.orbit_mk]
  exact isCompact_orbit_of_compact _

/-- Helper for Theorem 31.1: the orbit projection for a continuous action by a compact
topological group is a perfect map. -/
theorem isPerfectMap_quotientMk {G : Type u} {X : Type v}
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [CompactSpace G]
    [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X] :
    IsPerfectMap (Quotient.mk (MulAction.orbitRel G X)) := by
  -- Assemble continuity, closedness, surjectivity, and the compact-fiber interface above.
  rw [isPerfectMap_iff]
  exact ⟨continuous_quotient_mk', MulAction.isClosedMap_quotient,
    Quotient.mk_surjective, isCompact_preimage_singleton_quotientMk⟩

/-- Theorem 31.1 (1). The orbit quotient of a Hausdorff space by a continuous action of a
compact topological group is Hausdorff. -/
instance instT2SpaceOfCompact {G : Type u} {X : Type v}
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [CompactSpace G]
    [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X] [T2Space X] :
    T2Space (MulAction.orbitRel.Quotient G X) :=
  isPerfectMap_quotientMk.t2Space

/-- Theorem 31.1 (2). The orbit quotient of a regular space by a continuous
action of a compact topological group is regular, using the book's `T3Space` convention. -/
instance instT3SpaceOfCompact {G : Type u} {X : Type v}
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [CompactSpace G]
    [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X] [T3Space X] :
    T3Space (MulAction.orbitRel.Quotient G X) :=
  isPerfectMap_quotientMk.t3Space

/-- Theorem 31.1 (3). The orbit quotient of a normal space by a continuous action of a
compact topological group is normal, using the book's `T4Space` convention. -/
instance instT4SpaceOfCompact {G : Type u} {X : Type v}
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [CompactSpace G]
    [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X] [T4Space X] :
    T4Space (MulAction.orbitRel.Quotient G X) :=
  isPerfectMap_quotientMk.isClosedMap.t4Space
    isPerfectMap_quotientMk.toIsProperMap.continuous isPerfectMap_quotientMk.surjective

/-- Theorem 31.1 (4). The orbit quotient of a locally compact space by a
continuous action of a compact topological group is locally compact in the book's
`WeaklyLocallyCompactSpace` sense. -/
instance instWeaklyLocallyCompactSpaceOfCompact {G : Type u} {X : Type v}
    [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [CompactSpace G]
    [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
    [WeaklyLocallyCompactSpace X] :
    WeaklyLocallyCompactSpace (MulAction.orbitRel.Quotient G X) :=
  isPerfectMap_quotientMk.weaklyLocallyCompactSpace

/-- Theorem 31.1 (5). The orbit quotient of a second-countable space by a group action
continuous in the space variable is second-countable. In particular, this applies to the
continuous action of a compact topological group in the theorem. -/
instance instSecondCountableTopology {G : Type u} {X : Type v} [Group G]
    [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
    [SecondCountableTopology X] :
    SecondCountableTopology (MulAction.orbitRel.Quotient G X) :=
  ContinuousConstSMul.secondCountableTopology

end MulAction.OrbitQuotient
