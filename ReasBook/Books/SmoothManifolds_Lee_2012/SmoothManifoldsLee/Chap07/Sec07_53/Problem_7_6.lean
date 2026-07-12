import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- The source statement is purely topological-group theoretic, so the canonical owner abstraction
-- is `IsTopologicalGroup`, with the proof reusing mathlib's canonical symmetric neighborhood
-- theorem around the identity.

/-- Problem 7-6: if `U` is a neighborhood of the identity in a topological group `G` (hence in
particular in a Lie group), then there exists a neighborhood `V` of the identity such that
`V ⊆ U` and `g * h⁻¹ ∈ U` whenever `g, h ∈ V`. -/
theorem exists_nhds_one_subset_mul_inv_mem
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Set G) (hU : U ∈ nhds (1 : G)) :
    ∃ V : Set G,
      V ∈ nhds (1 : G) ∧
      V ⊆ U ∧
      ∀ ⦃g h : G⦄, g ∈ V → h ∈ V → g * h⁻¹ ∈ U := by
  obtain ⟨V, hV_nhds, -, hV_symm, hV_mul⟩ := exists_closed_nhds_one_inv_eq_mul_subset hU
  refine ⟨V, hV_nhds, ?_, ?_⟩
  · intro g hg
    have hV_one : (1 : G) ∈ V := mem_of_mem_nhds hV_nhds
    have hV_one_inv : (1 : G)⁻¹ ∈ V := by
      rw [← hV_symm]
      simpa [Set.mem_inv] using hV_one
    simpa using hV_mul (Set.mul_mem_mul hg hV_one_inv)
  · intro g h hg hh
    have hh_inv : h⁻¹ ∈ V := by
      rw [← hV_symm]
      simpa [Set.mem_inv] using hh
    exact hV_mul <| Set.mul_mem_mul hg hh_inv
