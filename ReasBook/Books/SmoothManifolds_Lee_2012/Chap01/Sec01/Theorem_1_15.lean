import SmoothManifolds_Lee_2012.Chap01.Sec01.Definition_1_extra_4
import SmoothManifolds_Lee_2012.Chap01.Sec01.Lemma_1_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Set TopologicalSpace
open scoped Topology

/-- A topological manifold is paracompact. -/
-- Proof sketch: a topological manifold is locally compact because it is charted over a
-- finite-dimensional Euclidean space, and it is second-countable by definition; therefore it is
-- sigma-compact, hence paracompact by the standard locally-compact sigma-compact Hausdorff
-- criterion.
theorem paracompactSpace_of_topologicalManifold (n : ℕ) (M : Type u) [TopologicalSpace M]
    [TopologicalManifold n M] : ParacompactSpace M := by
  letI : LocallyCompactSpace M :=
    TopologicalManifold.locallyCompactSpace_of_topologicalManifold n M
  letI : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  infer_instance

namespace TopologicalSpace.IsOpenCover

/-- Companion bridge: given an open cover of a locally compact sigma-compact Hausdorff space and
any basis for its topology, there exists a countable locally finite refinement by basis elements.
-/
-- Proof sketch: use local compactness and sigma-compactness to obtain a compact exhaustion, cover
-- each compact layer by finitely many basis elements subordinate to the given open cover, and
-- then take the union of these finite subcovers; the layer construction forces local finiteness.
theorem exists_countable_locallyFinite_refinement_of_isTopologicalBasis {M : Type u}
    [TopologicalSpace M] [LocallyCompactSpace M] [SigmaCompactSpace M] [T2Space M]
    {ι : Type v} {U : ι → Opens M}
    (hU : IsOpenCover U) {B : Set (Set M)} (hB : IsTopologicalBasis B) :
    ∃ (κ : Type u), Countable κ ∧ ∃ V : κ → Opens M,
      IsOpenCover V ∧ LocallyFinite (fun j ↦ (V j : Set M)) ∧
        (∀ j, (V j : Set M) ∈ B) ∧
          (∀ j, ∃ i, (V j : Set M) ⊆ U i) := by
  -- Choose, at each point, one member of the original cover that contains that point.
  choose i hi using fun x : M ↦ hU.exists_mem_nhds x
  have hBU :
      ∀ x : M,
        (𝓝 x).HasBasis
          (fun s : Set M ↦ s ∈ B ∧ x ∈ s ∧ s ⊆ U (i x))
          id := by
    intro x
    let hxB : (𝓝 x).HasBasis (fun s : Set M ↦ s ∈ B ∧ x ∈ s) id := hB.nhds_hasBasis
    simpa [and_assoc] using hxB.restrict_subset (hi x)
  -- Feed the subordinate neighborhood bases into the standard locally finite refinement theorem.
  rcases refinement_of_locallyCompact_sigmaCompact_of_nhds_basis hBU with
    ⟨κ, c, W, hW_basis, hW_cover, hW_locallyFinite⟩
  have hκ : Countable κ := by
    simpa [Set.countable_univ_iff] using
      hW_locallyFinite.countable_univ fun j ↦ ⟨c j, (hW_basis j).2.1⟩
  refine ⟨κ, hκ, ?_⟩
  refine ⟨fun j ↦ ⟨W j, hB.isOpen (hW_basis j).1⟩, ?_, hW_locallyFinite, ?_, ?_⟩
  · exact IsOpenCover.of_sets (fun j ↦ hB.isOpen (hW_basis j).1) hW_cover
  · exact fun j ↦ (hW_basis j).1
  · exact fun j ↦ ⟨i (c j), (hW_basis j).2.2⟩

end TopologicalSpace.IsOpenCover

/-- Theorem 1.15: given an open cover of a topological manifold, there exists a countable locally
finite refinement by precompact coordinate balls subordinate to the cover. -/
theorem exists_countable_locally_finite_precompact_coordinate_ball_refinement (n : ℕ)
    {M : Type u} [TopologicalSpace M] [TopologicalManifold n M] {ι : Type v}
    {U : ι → Opens M} (hU : IsOpenCover U) :
    ∃ (κ : Type u), Countable κ ∧ ∃ V : κ → Opens M,
      IsOpenCover V ∧ LocallyFinite (fun j ↦ (V j : Set M)) ∧
        (∀ j, IsPrecompactCoordinateBall n (V j : Set M)) ∧
          (∀ j, ∃ i, (V j : Set M) ⊆ U i) := by
  -- Start from the countable basis of precompact coordinate balls supplied earlier.
  have hBasis :
      ∃ B : Set (Set M),
        B.Countable ∧ IsTopologicalBasis B ∧ ∀ s ∈ B, IsPrecompactCoordinateBall n s :=
    exists_countable_precompact_coordinate_ball_basis
  rcases hBasis with ⟨B, -, hB_basis, hB_precompact⟩
  -- Apply the abstract refinement theorem to this specific basis.
  have hRefinement :
      ∃ (κ : Type u), Countable κ ∧ ∃ V : κ → Opens M,
        IsOpenCover V ∧ LocallyFinite (fun j ↦ (V j : Set M)) ∧
          (∀ j, (V j : Set M) ∈ B) ∧
            (∀ j, ∃ i, (V j : Set M) ⊆ U i) :=
    by
      letI : LocallyCompactSpace M :=
        TopologicalManifold.locallyCompactSpace_of_topologicalManifold n M
      letI : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
      exact hU.exists_countable_locallyFinite_refinement_of_isTopologicalBasis hB_basis
  rcases hRefinement with
    ⟨κ, hκ, V, hV_cover, hV_locallyFinite, hV_mem, hV_subordinate⟩
  refine ⟨κ, hκ, V, hV_cover, hV_locallyFinite, ?_, hV_subordinate⟩
  intro j
  exact hB_precompact _ (hV_mem j)
