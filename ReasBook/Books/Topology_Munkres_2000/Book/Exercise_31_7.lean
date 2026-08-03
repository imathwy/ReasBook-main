module

public import Topology_Munkres_2000.Book.Definition_26_7.PerfectMap
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Separation.Regular

public section

universe u v

open Filter Topology TopologicalSpace

namespace IsPerfectMap

/-- Exercise 31.7 (1): The codomain of a closed continuous surjection with compact fibers
from a Hausdorff space is Hausdorff. -/
theorem t2Space {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] {p : X → Y}
    (hp : IsPerfectMap p) : T2Space Y := by
  -- Pull distinct points back to their disjoint compact fibers.
  rw [t2Space_iff_disjoint_nhds]
  intro y z hyz
  rw [← Filter.disjoint_comap_iff hp.surjective]
  have hfibers : Disjoint (p ⁻¹' {y}) (p ⁻¹' {z}) := by
    rw [Set.disjoint_left]
    intro x hxy hxz
    exact hyz (Set.mem_singleton_iff.mp hxy |>.symm.trans (Set.mem_singleton_iff.mp hxz))
  have hseparated := SeparatedNhds.of_isCompact_isCompact_isClosed
    (hp.isCompact_fiber y) (hp.isCompact_fiber z) (hp.isCompact_fiber z).isClosed hfibers
  -- Closedness compares the pulled-back point filters with the fiber filters.
  exact hseparated.disjoint_nhdsSet.mono hp.isClosedMap.comap_nhds_le
    hp.isClosedMap.comap_nhds_le

/-- Companion to Exercise 31.7 (2): The codomain of a closed continuous surjection with
compact fibers from a regular space is regular. Here `T3Space` expresses the book's convention
for a regular space. -/
theorem t3Space {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [T3Space X] {p : X → Y}
    (hp : IsPerfectMap p) : T3Space Y := by
  letI : T2Space Y := hp.t2Space
  have hregular : RegularSpace Y := by
    refine ⟨?_⟩
    intro s y hs hy
    -- Reflect the desired separation to the closed preimage and the compact fiber.
    rw [← Filter.disjoint_comap_iff hp.surjective]
    have hpreimage : IsClosed (p ⁻¹' s) := hs.preimage hp.toIsProperMap.continuous
    have hpoint : ∀ x ∈ p ⁻¹' {y}, Disjoint (𝓝ˢ (p ⁻¹' s)) (𝓝 x) := by
      intro x hx
      -- Regularity separates each point of the fiber from the closed preimage.
      refine RegularSpace.regular hpreimage ?_
      intro hxs
      exact hy (Set.mem_singleton_iff.mp hx ▸ hxs)
    have hseparated : Disjoint (𝓝ˢ (p ⁻¹' s)) (𝓝ˢ (p ⁻¹' {y})) :=
      (hp.isCompact_fiber y).disjoint_nhdsSet_right.2 hpoint
    -- The two closed-map inequalities descend this separation to `Y`.
    exact hseparated.mono hp.isClosedMap.comap_nhdsSet_le hp.isClosedMap.comap_nhds_le
  letI : RegularSpace Y := hregular
  exact inferInstance

/-- Companion to Exercise 31.7 (3): The codomain of a closed continuous surjection with
compact fibers from a locally compact space is locally compact. Here
`WeaklyLocallyCompactSpace` expresses the book's §29 convention. -/
theorem weaklyLocallyCompactSpace {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [WeaklyLocallyCompactSpace X] {p : X → Y}
    (hp : IsPerfectMap p) : WeaklyLocallyCompactSpace Y := by
  refine ⟨fun y ↦ ?_⟩
  -- Enlarge the compact fiber to the interior of a compact source set.
  obtain ⟨K, hK, hfiber⟩ := exists_compact_superset (hp.isCompact_fiber y)
  refine ⟨p '' K, hK.image hp.toIsProperMap.continuous, ?_⟩
  have hopen : IsOpen (Set.kernImage p (interior K)) :=
    isClosedMap_iff_kernImage.mp hp.isClosedMap isOpen_interior
  have hy : y ∈ Set.kernImage p (interior K) := by
    intro x hxy
    exact hfiber (Set.mem_singleton_iff.mpr hxy)
  have hsubset : Set.kernImage p (interior K) ⊆ p '' K := by
    intro z hz
    obtain ⟨x, rfl⟩ := hp.surjective z
    exact ⟨x, interior_subset (hz rfl), rfl⟩
  -- This open kernel image is the required neighborhood inside the compact image.
  exact Filter.mem_of_superset (hopen.mem_nhds hy) hsubset

/-- Helper for Exercise 31.7: a compact fiber inside an open preimage has a finite cover by
members of a prescribed basis whose union remains in that preimage. -/
private lemma existsFiniteBasisCoverFiber {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {p : X → Y} (hp : IsPerfectMap p)
    {B : Set (Set X)} (hB : IsTopologicalBasis B) {U : Set Y} (hU : IsOpen U) {y : Y}
    (hy : y ∈ U) :
    ∃ J : Set (Set X), J.Finite ∧ J ⊆ B ∧ p ⁻¹' {y} ⊆ ⋃₀ J ∧ ⋃₀ J ⊆ p ⁻¹' U := by
  let C : Set (Set X) := {V | V ∈ B ∧ V ⊆ p ⁻¹' U}
  have hpreimage : IsOpen (p ⁻¹' U) := hU.preimage hp.toIsProperMap.continuous
  -- Every point of the fiber lies in a basis member selected inside the open preimage.
  have hcover : p ⁻¹' {y} ⊆ ⋃ V ∈ C, V := by
    intro x hx
    have hpx : p x = y := Set.mem_singleton_iff.mp hx
    have hpxU : p x ∈ U := by
      rw [hpx]
      exact hy
    have hxU : x ∈ p ⁻¹' U := hpxU
    obtain ⟨V, hVB, hxV, hVsub⟩ := hB.exists_subset_of_mem_open hxU hpreimage
    exact Set.mem_iUnion.2 ⟨V, Set.mem_iUnion.2 ⟨⟨hVB, hVsub⟩, hxV⟩⟩
  obtain ⟨J, hJC, hJfinite, hJcover⟩ :=
    (hp.isCompact_fiber y).elim_finite_subcover_image (c := fun V : Set X ↦ V)
      (fun V hV ↦ hB.isOpen hV.1) hcover
  refine ⟨J, hJfinite, fun V hV ↦ (hJC hV).1, ?_, ?_⟩
  · rwa [Set.sUnion_eq_biUnion]
  · rw [Set.sUnion_eq_biUnion]
    exact Set.iUnion₂_subset fun V hV ↦ (hJC hV).2

/-- Helper for Exercise 31.7: kernel images of finite unions of source basis members form a
topological basis on the codomain of a perfect map. -/
private lemma kernImageFiniteUnionsBasis {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {p : X → Y} (hp : IsPerfectMap p)
    {B : Set (Set X)} (hB : IsTopologicalBasis B) :
    IsTopologicalBasis
      ((fun J : Set (Set X) ↦ Set.kernImage p (⋃₀ J)) '' {J | J.Finite ∧ J ⊆ B}) := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro V ⟨J, hJ, rfl⟩
    apply isClosedMap_iff_kernImage.mp hp.isClosedMap
    exact isOpen_sUnion fun W hW ↦ hB.isOpen (hJ.2 hW)
  · intro y U hy hU
    obtain ⟨J, hJfinite, hJB, hfiber, hJpreimage⟩ :=
      existsFiniteBasisCoverFiber hp hB hU hy
    refine ⟨Set.kernImage p (⋃₀ J), ⟨J, ⟨hJfinite, hJB⟩, rfl⟩, ?_, ?_⟩
    · intro x hxy
      exact hfiber (Set.mem_singleton_iff.mpr hxy)
    · intro z hz
      obtain ⟨x, rfl⟩ := hp.surjective z
      exact hJpreimage (hz rfl)

/-- Companion to Exercise 31.7 (4): The codomain of a closed continuous surjection with
compact fibers from a second-countable space is second-countable. -/
theorem secondCountableTopology {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [SecondCountableTopology X] {p : X → Y}
    (hp : IsPerfectMap p) : SecondCountableTopology Y := by
  -- Count finite subfamilies of the canonical countable source basis, then map them downstairs.
  refine (kernImageFiniteUnionsBasis hp (isBasis_countableBasis X)).secondCountableTopology ?_
  exact (Set.countable_setOf_finite_subset (countable_countableBasis X)).image _

end IsPerfectMap
