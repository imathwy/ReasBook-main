module

public import Mathlib.Topology.Algebra.Group.Quotient
public import Topology_Munkres_2000.Book.Definition_26_7.PerfectMap
public import Topology_Munkres_2000.Book.Exercise_26_12.ProperMap

public section

universe u

open scoped Pointwise

/- Exercise 26.13 (1): If `A` is closed and `B` is compact in a topological
group `G`, then the pointwise product `A * B` is closed. -/
#check fun {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {A B : Set G} (hA : IsClosed A) (hB : IsCompact B) ↦
  IsClosed.mul_right_of_isCompact hA hB

/- Exercise 26.13 (2): If `H` is a compact subgroup of a topological group
`G`, then the quotient map `QuotientGroup.mk : G → G ⧸ H` is closed. -/
#check fun {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {H : Subgroup G} (hH : IsCompact (H : Set G)) ↦
  QuotientGroup.isClosedMap_coe hH

namespace QuotientGroup

/-- Helper for Exercise 26.13: the fiber over the class of `g` is its left coset of `H`. -/
lemma preimage_singleton_mk_eq_leftCoset
    {G : Type u} [Group G] (H : Subgroup G) (g : G) :
    (QuotientGroup.mk : G → G ⧸ H) ⁻¹' {(g : G ⧸ H)} = g • (H : Set G) := by
  -- Express the singleton preimage in the set-builder form used by the coset API.
  simpa only [Set.preimage, Set.mem_singleton_iff] using eq_class_eq_leftCoset H g

/-- Helper for Exercise 26.13: every fiber of the quotient projection is compact when `H` is. -/
lemma isCompact_preimage_singleton_mk
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {H : Subgroup G} (hH : IsCompact (H : Set G)) (y : G ⧸ H) :
    IsCompact ((QuotientGroup.mk : G → G ⧸ H) ⁻¹' {y}) := by
  -- Choose a representative, rewrite its fiber as a coset, and translate compactness.
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  rw [preimage_singleton_mk_eq_leftCoset]
  exact hH.smul g

/-- Exercise 26.13: The quotient projection by a compact subgroup is a perfect map. -/
theorem isPerfectMap_coe {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {H : Subgroup G} (hH : IsCompact (H : Set G)) :
    IsPerfectMap (QuotientGroup.mk : G → G ⧸ H) := by
  -- Assemble continuity, closedness, surjectivity, and compactness of every fiber.
  rw [isPerfectMap_iff]
  exact ⟨continuous_mk, isClosedMap_coe hH, mk_surjective,
    isCompact_preimage_singleton_mk hH⟩

/-- A topological group with a compact subgroup and compact quotient by that subgroup is compact. -/
theorem compactSpace_of_compact_quotient
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (H : Subgroup G) (hH : IsCompact (H : Set G)) [CompactSpace (G ⧸ H)] :
    CompactSpace G :=
  (isPerfectMap_coe hH).toIsProperMap.compactSpace

end QuotientGroup
