module

public import Topology_Munkres_2000.Book.Exercise_4_99_2.LocallyMetrizable
public import Mathlib.Topology.Metrizable.Urysohn

public section

universe u

open scoped Topology

namespace LocallyMetrizableSpace

/-- Helper for Exercise 34.7: every point has an open neighborhood with metrizable closure. -/
private lemma exists_isOpen_metrizableClosure_mem
    {X : Type u} [TopologicalSpace X] [RegularSpace X] [LocallyMetrizableSpace X] (x : X) :
    ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ TopologicalSpace.MetrizableSpace (closure U) := by
  -- Shrink a metrizable neighborhood so that its closure remains inside it.
  rcases LocallyMetrizableSpace.exists_metrizable_nhds x with ⟨s, hs, hsMetric⟩
  rcases (hasBasis_opens_closure x).mem_iff.mp hs with ⟨U, ⟨hxU, hUopen⟩, hclosure⟩
  letI : TopologicalSpace.MetrizableSpace s := hsMetric
  refine ⟨U, hxU, hUopen, ?_⟩
  exact (Topology.IsEmbedding.inclusion hclosure).metrizableSpace

/-- Helper for Exercise 34.7: a subset with metrizable closure in a compact space is second
countable. -/
private lemma secondCountableTopology_of_metrizableClosure
    {X : Type u} [TopologicalSpace X] [CompactSpace X] (U : Set X)
    (hclosureMetric : TopologicalSpace.MetrizableSpace (closure U)) :
    SecondCountableTopology U := by
  -- The closed closure is compact, hence second countable because it is metrizable.
  letI : TopologicalSpace.MetrizableSpace (closure U) := hclosureMetric
  letI : CompactSpace (closure U) :=
    isClosed_closure.isClosedEmbedding_subtypeVal.compactSpace
  letI : SecondCountableTopology (closure U) := inferInstance
  -- Pull second countability back along the inclusion into the closure.
  exact (Topology.IsEmbedding.inclusion subset_closure).secondCountableTopology

/-- Exercise 34.7: A compact Hausdorff space is metrizable if every point has a
metrizable neighborhood in the subspace topology. -/
instance metrizableSpace_of_compact
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [LocallyMetrizableSpace X] : TopologicalSpace.MetrizableSpace X := by
  -- Choose an open neighborhood cover whose closures are metrizable.
  choose U hxU hUopen hUclosureMetric using
    fun x : X ↦ exists_isOpen_metrizableClosure_mem x
  have hUsecondCountable : ∀ x, SecondCountableTopology (U x) := by
    intro x
    exact secondCountableTopology_of_metrizableClosure (U x) (hUclosureMetric x)
  -- Compactness reduces the cover to finitely many second-countable open subspaces.
  obtain ⟨t, _, hcover⟩ := isCompact_univ.elim_nhds_subcover U fun x _ ↦
    (hUopen x).mem_nhds (hxU x)
  letI : ∀ i : t, SecondCountableTopology (U i.1) := fun i ↦ hUsecondCountable i.1
  letI : SecondCountableTopology X := by
    apply TopologicalSpace.secondCountableTopology_of_countable_cover
      (fun i : t ↦ hUopen i.1)
    apply Set.Subset.antisymm
    · exact Set.subset_univ _
    · simpa only [Set.iUnion_subtype] using hcover
  -- Urysohn's metrization theorem now applies to the compact Hausdorff space.
  infer_instance

end LocallyMetrizableSpace
