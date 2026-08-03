module

public import Topology_Munkres_2000.Book.Exercise_4_99_2.LocallyMetrizable
public import Mathlib.Topology.Metrizable.Urysohn

public section

universe u

open scoped Topology

namespace LocallyMetrizableSpace

/-- Helper for Exercise 34.8: every point has an open neighborhood with metrizable closure. -/
lemma exists_isOpen_metrizableClosure_mem
    {X : Type u} [TopologicalSpace X] [RegularSpace X] [LocallyMetrizableSpace X] (x : X) :
    ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ TopologicalSpace.MetrizableSpace (closure U) := by
  -- Shrink a metrizable neighborhood so its closure remains inside that neighborhood.
  rcases LocallyMetrizableSpace.exists_metrizable_nhds x with ⟨s, hs, hsMetric⟩
  rcases (hasBasis_opens_closure x).mem_iff.mp hs with ⟨U, ⟨hxU, hUopen⟩, hclosure⟩
  letI : TopologicalSpace.MetrizableSpace s := hsMetric
  refine ⟨U, hxU, hUopen, ?_⟩
  exact (Topology.IsEmbedding.inclusion hclosure).metrizableSpace

/-- Helper for Exercise 34.8: a subset with metrizable closure in a Lindelöf space is second
countable. -/
lemma secondCountableTopology_of_metrizableClosure
    {X : Type u} [TopologicalSpace X] [LindelofSpace X] (U : Set X)
    (hclosureMetric : TopologicalSpace.MetrizableSpace (closure U)) :
    SecondCountableTopology U := by
  -- The closed closure is Lindelöf, hence second countable because it is metrizable.
  letI : TopologicalSpace.MetrizableSpace (closure U) := hclosureMetric
  letI : LindelofSpace (closure U) :=
    isClosed_closure.isClosedEmbedding_subtypeVal.LindelofSpace
  letI : SecondCountableTopology (closure U) := inferInstance
  -- Pull second countability back along the inclusion into the closure.
  exact (Topology.IsEmbedding.inclusion subset_closure).secondCountableTopology

/-- Exercise 34.8: A regular Lindelöf space that is locally metrizable is metrizable.
Here `T3Space` expresses the book's convention for a regular space. -/
instance metrizableSpace_of_t3_lindelof
    {X : Type u} [TopologicalSpace X] [T3Space X] [LindelofSpace X]
    [LocallyMetrizableSpace X] : TopologicalSpace.MetrizableSpace X := by
  -- Choose pointwise open neighborhoods whose closures are metrizable.
  choose U hxU hUopen hUclosureMetric using
    fun x : X ↦ exists_isOpen_metrizableClosure_mem x
  have hUsecondCountable : ∀ x, SecondCountableTopology (U x) := by
    intro x
    exact secondCountableTopology_of_metrizableClosure (U x) (hUclosureMetric x)
  -- Lindelöfness reduces this neighborhood cover to a countable subcover.
  obtain ⟨t, htCountable, hcover⟩ :=
    LindelofSpace.elim_nhds_subcover U fun x ↦ (hUopen x).mem_nhds (hxU x)
  letI : Countable t := htCountable.to_subtype
  letI : ∀ i : t, SecondCountableTopology (U i.1) := fun i ↦ hUsecondCountable i.1
  letI : SecondCountableTopology X := by
    apply TopologicalSpace.secondCountableTopology_of_countable_cover
      (fun i : t ↦ hUopen i.1)
    simpa only [Set.iUnion_subtype] using hcover
  -- Urysohn's metrization theorem finishes from T₃ and second countability.
  infer_instance

end LocallyMetrizableSpace
