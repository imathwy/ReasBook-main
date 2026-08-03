module

public import Mathlib.Topology.Compactness.Lindelof

universe u v

public section

namespace LindelofSpace

/-- Helper for Exercise 30.14: an open cover of `X × Y` has a finite subfamily
covering a full product neighborhood of each vertical fiber. -/
private lemma exists_open_finset_subcover_prod {X : Type u} {Y : Type v} {ι : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y] (U : ι → Set (X × Y))
    (hUo : ∀ i, IsOpen (U i)) (hU : Set.univ ⊆ ⋃ i, U i) (x : X) :
    ∃ t : Finset ι, ∃ V : Set X,
      IsOpen V ∧ x ∈ V ∧ V ×ˢ Set.univ ⊆ ⋃ i ∈ t, U i := by
  classical
  -- Compactness first reduces the cover on the vertical fiber to finitely many members.
  obtain ⟨t, ht⟩ := (isCompact_singleton.prod isCompact_univ).elim_finite_subcover U hUo
    (fun z _ ↦ hU (Set.mem_univ z))
  have hto : IsOpen (⋃ i ∈ t, U i) :=
    isOpen_biUnion fun i _ ↦ hUo i
  -- The tube lemma enlarges the compact fiber to a product neighborhood.
  obtain ⟨V, W, hVo, _, hxV, hYW, hVW⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hto ht
  refine ⟨t, V, hVo, hxV (Set.mem_singleton x), ?_⟩
  intro z hz
  exact hVW ⟨hz.1, hYW hz.2⟩

/-- Helper for Exercise 30.14: a countable bounded union of finite sets is countable. -/
private lemma countableFinsetBiUnion {X : Type*} {ι : Type*} {c : Set X}
    (hc : c.Countable) (t : X → Finset ι) :
    (⋃ x ∈ c, (t x : Set ι)).Countable := by
  -- Each fiber of the bounded union is finite, hence countable.
  exact hc.biUnion fun x _ ↦ Finset.countable_toSet (t x)

/-- Helper for Exercise 30.14: the product of a Lindelöf space and a compact space
is a Lindelöf set. -/
private lemma isLindelof_prod_of_compact {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [LindelofSpace X] [CompactSpace Y] :
    IsLindelof (Set.univ : Set (X × Y)) := by
  classical
  -- Start with an arbitrary open cover and choose a finite tube cover above each point of `X`.
  apply isLindelof_of_countable_subcover
  intro ι U hUo hU
  choose t V hVo hxV hVU using fun x ↦ exists_open_finset_subcover_prod U hUo hU x
  -- Lindelöfness of `X` selects countably many of the tube neighborhoods.
  obtain ⟨c, hc, hcV⟩ := isLindelof_univ.elim_countable_subcover V hVo
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  refine ⟨⋃ x ∈ c, (t x : Set ι), countableFinsetBiUnion hc t, ?_⟩
  -- Flatten the finite covers attached to the selected tube neighborhoods.
  intro z _
  obtain ⟨x, hxc, hzx⟩ := Set.mem_iUnion₂.mp (hcV (Set.mem_univ z.1))
  obtain ⟨i, hit, hzi⟩ := Set.mem_iUnion₂.mp (hVU x ⟨hzx, Set.mem_univ z.2⟩)
  exact Set.mem_iUnion₂.mpr ⟨i, Set.mem_iUnion₂.mpr ⟨x, hxc, hit⟩, hzi⟩

/-- Exercise 30.14: The product of a Lindelöf space with a compact space is Lindelöf. -/
instance prodOfCompactSpace {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [LindelofSpace X] [CompactSpace Y] :
    LindelofSpace (X × Y) :=
  { isLindelof_univ := isLindelof_prod_of_compact }

end LindelofSpace
