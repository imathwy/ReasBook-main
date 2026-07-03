import Mathlib.Topology.Compactness.SigmaCompact

open Set

noncomputable section

-- Domain sampling: this item lies in the topology/compactness domain for open subspaces.
-- The owner-level declarations inspected before refinement were
-- `IsOpen.locallyCompactSpace`, `sigmaCompactSpace_of_locallyCompact_secondCountable`,
-- `CompactExhaustion.choice`, `CompactExhaustion.isCompact`, `CompactExhaustion.subset`, and
-- `CompactExhaustion.iUnion_eq`. The source-facing statement below is a `bridge/view` theorem
-- derived from the core owner `CompactExhaustion D`; no parallel chosen-witness owner is kept.

/-- Lemma V.1-extra-7: an open subset `D` of a locally compact second countable space admits an
exhaustive sequence of compact subsets of the ambient space, meaning a monotone sequence of
compact sets whose union is `D`. The textbook case `D ⊆ ℂ` is the specialization `X = ℂ`. -/
theorem exists_exhaustive_compact_sequence_of_isOpen
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
    (D : Set X) (hD : IsOpen D) :
    ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ Monotone K ∧ ⋃ n, K n = D := by
  letI : LocallyCompactSpace D := hD.locallyCompactSpace
  letI : SigmaCompactSpace D := sigmaCompactSpace_of_locallyCompact_secondCountable
  let K : CompactExhaustion D := CompactExhaustion.choice D
  refine ⟨fun n ↦ ((↑) : D → X) '' K n, ?_, ?_, ?_⟩
  · intro n
    simpa only using (K.isCompact n).image continuous_subtype_val
  · intro m n hmn z hz
    rcases hz with ⟨w, hw, rfl⟩
    exact ⟨w, K.subset hmn hw, rfl⟩
  · ext z
    simp only [mem_iUnion, mem_image]
    constructor
    · rintro ⟨n, w, hw, rfl⟩
      exact w.2
    · intro hz
      rcases K.exists_mem ⟨z, hz⟩ with ⟨n, hzn⟩
      exact ⟨n, ⟨⟨z, hz⟩, hzn, rfl⟩⟩
