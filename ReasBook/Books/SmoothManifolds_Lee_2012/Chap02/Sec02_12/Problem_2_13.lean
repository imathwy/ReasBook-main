import Mathlib.Topology.PartitionOfUnity

-- Declarations for this item will be appended below by the statement pipeline.

universe u

-- Proof sketch: for an open cover `U`, choose a subordinate partition of unity `f`. The open sets
-- `{x | 0 < f i x}` form a locally finite refinement of `U`: local finiteness comes from
-- `PartitionOfUnity.locallyFinite`, each positivity set lies in `U i` because positivity implies
-- membership in `support (f i) ⊆ tsupport (f i) ⊆ U i`, and the positivity sets cover `M` since at
-- each point the partition sums to `1`, so some summand is positive there.
/-- Problem 2-13: if every indexed open cover of `M` admits a partition of unity subordinate to that
cover, then `M` is paracompact. -/
theorem paracompactSpace_of_hasSubordinatePartitionOfUnity
    {M : Type u} [TopologicalSpace M]
    (hM : ∀ {ι : Type u} (U : ι → Set M), (∀ i, IsOpen (U i)) → (⋃ i, U i = Set.univ) →
      ∃ f : PartitionOfUnity ι M Set.univ, f.IsSubordinate U) :
    ParacompactSpace M := by
  refine ⟨fun ι U hU_open hU_cover ↦ ?_⟩
  obtain ⟨f, hf⟩ := hM U hU_open hU_cover
  let V : ι → Set M := fun i ↦ (f i : M → ℝ) ⁻¹' Set.Ioi 0
  refine ⟨ι, V, ?_, ?_, ?_, ?_⟩
  · intro i
    exact isOpen_Ioi.preimage (f i).continuous
  · ext x
    constructor
    · intro _
      simp
    · intro _
      rcases f.exists_pos (by simp : x ∈ Set.univ) with ⟨i, hi⟩
      exact Set.mem_iUnion.2 ⟨i, by simpa [V] using hi⟩
  · refine f.locallyFinite.subset fun i x hx ↦ ?_
    change 0 < (f i : M → ℝ) x at hx
    simpa [Function.mem_support] using (ne_of_gt hx)
  · intro i
    refine ⟨i, fun x hx ↦ hf i <| subset_tsupport (f i : M → ℝ) ?_⟩
    change 0 < (f i : M → ℝ) x at hx
    simpa [Function.mem_support] using (ne_of_gt hx)
