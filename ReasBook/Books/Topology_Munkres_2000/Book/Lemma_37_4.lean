module

public import Mathlib.Topology.Compactness.Compact
public import Topology_Munkres_2000.Book.Proposition_15_1

public section

open Set

universe u v

namespace CompactSpace

/-- Helper for Lemma 37.4: a finite family of open rectangles covering a vertical
slice also covers an open tube around that slice. -/
private lemma existsOpenTube_subset_finsetUnion {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (𝒜 : Set (Set (X × Y))) (hrect : 𝒜 ⊆ openRectangles X Y)
    (x : X) (s : Finset 𝒜)
    (hs : {x} ×ˢ (Set.univ : Set Y) ⊆ ⋃ A ∈ s, (A : Set (X × Y))) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      U ×ˢ (Set.univ : Set Y) ⊆ ⋃ A ∈ s, (A : Set (X × Y)) := by
  classical
  choose first second hfirst hsecond hprod using fun A : 𝒜 ↦
    (mem_openRectangles (A : Set (X × Y))).mp (hrect A.property)
  let active := s.filter fun A ↦ x ∈ first A
  let U := ⋂ A ∈ active, first A
  -- The active first-coordinate factors have an open finite intersection containing `x`.
  have hUopen : IsOpen U := by
    exact isOpen_biInter_finset fun A _ ↦ hfirst A
  have hxU : x ∈ U := by
    refine Set.mem_iInter₂.mpr ?_
    intro A hA
    exact (Finset.mem_filter.mp hA).2
  refine ⟨U, hUopen, hxU, ?_⟩
  -- A rectangle covering `(x, y)` is active, so its first factor contains every point of `U`.
  intro z hz
  have hxyCover : (x, z.2) ∈ ⋃ A ∈ s, (A : Set (X × Y)) := by
    exact hs ⟨Set.mem_singleton x, Set.mem_univ z.2⟩
  obtain ⟨A, hAs, hxyA⟩ := Set.mem_iUnion₂.mp hxyCover
  have hxyProd : (x, z.2) ∈ first A ×ˢ second A := by
    rw [← hprod A]
    exact hxyA
  have hAactive : A ∈ active := by
    exact Finset.mem_filter.mpr ⟨hAs, hxyProd.1⟩
  have hzProd : z ∈ first A ×ˢ second A := ⟨Set.mem_iInter₂.mp hz.1 A hAactive, hxyProd.2⟩
  apply Set.mem_iUnion₂.mpr
  refine ⟨A, hAs, ?_⟩
  rwa [hprod A]

/-- Helper for Lemma 37.4: the base points whose vertical slices are covered by
a fixed finite family of open rectangles form an open set. -/
private lemma isOpen_setOf_slice_subset_finsetUnion {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (𝒜 : Set (Set (X × Y))) (hrect : 𝒜 ⊆ openRectangles X Y) (s : Finset 𝒜) :
    IsOpen {x : X |
      {x} ×ˢ (Set.univ : Set Y) ⊆ ⋃ A ∈ s, (A : Set (X × Y))} := by
  -- The tube lemma supplies an open neighborhood contained in the same slice-covering set.
  refine isOpen_iff_forall_mem_open.mpr ?_
  intro x hx
  obtain ⟨U, hUopen, hxU, hUcover⟩ :=
    existsOpenTube_subset_finsetUnion 𝒜 hrect x s hx
  refine ⟨U, ?_, hUopen, hxU⟩
  intro x' hx' z hz
  rcases z with ⟨z1, z2⟩
  simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true] at hz
  subst z1
  exact hUcover ⟨hx', Set.mem_univ z2⟩

/-- Helper for Lemma 37.4: finitely many tube covers combine into one finite
cover of the whole product. -/
private lemma finiteTubeCovers_coverProduct {X : Type u} {Y : Type v}
    {ι : Type*} {𝒜 : Set (Set (X × Y))} [DecidableEq 𝒜]
    (t : Finset ι) (U : ι → Set X) (s : ι → Finset 𝒜)
    (hbase : (Set.univ : Set X) ⊆ ⋃ i ∈ t, U i)
    (htube : ∀ i, U i ×ˢ (Set.univ : Set Y) ⊆
      ⋃ A ∈ s i, (A : Set (X × Y))) :
    (Set.univ : Set (X × Y)) ⊆ ⋃ A ∈ t.biUnion s, (A : Set (X × Y)) := by
  -- Choose a selected tube above the first coordinate, then promote its rectangle to the union.
  intro z _
  obtain ⟨i, hit, hzi⟩ := Set.mem_iUnion₂.mp (hbase (Set.mem_univ z.1))
  obtain ⟨A, hAs, hzA⟩ := Set.mem_iUnion₂.mp (htube i ⟨hzi, Set.mem_univ z.2⟩)
  apply Set.mem_iUnion₂.mpr
  exact ⟨A, Finset.mem_biUnion.mpr ⟨i, hit, hAs⟩, hzA⟩

/-- Lemma 37.4. A family of open rectangles with no finite subcover of `X × Y`
has a vertical slice `{x} ×ˢ Set.univ` with no finite subcover from the family. -/
theorem existsSliceNotFinitelyCovered {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X]
    (𝒜 : Set (Set (X × Y)))
    (hrect : 𝒜 ⊆ openRectangles X Y)
    (hncover : ∀ s : Finset 𝒜,
      ¬ (Set.univ : Set (X × Y)) ⊆ ⋃ A ∈ s, (A : Set (X × Y))) :
    ∃ x : X, ∀ s : Finset 𝒜,
      ¬ ({x} ×ˢ (Set.univ : Set Y)) ⊆ ⋃ A ∈ s, (A : Set (X × Y)) := by
  classical
  -- If every slice has a finite cover, choose one such family at each base point.
  by_contra h
  push Not at h
  choose s hs using h
  let U : X → Set X := fun x ↦
    {x' | {x'} ×ˢ (Set.univ : Set Y) ⊆ ⋃ A ∈ s x, (A : Set (X × Y))}
  have hUopen : ∀ x, IsOpen (U x) := by
    intro x
    exact isOpen_setOf_slice_subset_finsetUnion 𝒜 hrect (s x)
  have hUcover : (Set.univ : Set X) ⊆ ⋃ x, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hs x⟩
  -- Compactness selects finitely many of these slice-covering neighborhoods.
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUopen hUcover
  have htube : ∀ x, U x ×ˢ (Set.univ : Set Y) ⊆
      ⋃ A ∈ s x, (A : Set (X × Y)) := by
    intro x z hz
    exact hz.1 ⟨Set.mem_singleton z.1, hz.2⟩
  -- Merging their finite rectangle families contradicts the no-finite-subcover hypothesis.
  exact hncover (t.biUnion s) (finiteTubeCovers_coverProduct t U s ht htube)

end CompactSpace
