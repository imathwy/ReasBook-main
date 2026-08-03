module

public import Mathlib.Topology.Compactness.Compact
public import Topology_Munkres_2000.Book.Definition_26_4.Tube

public section

universe u v

/-- Lemma 26.8 (the tube lemma). An open set containing the slice over `x₀`
contains a tube about that slice. -/
theorem tubeLemma {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace Y] {x₀ : X} {N : Set (X × Y)}
    (hN_open : IsOpen N)
    (h_slice : ({x₀} : Set X) ×ˢ (Set.univ : Set Y) ⊆ N) :
    ∃ T : Set (X × Y), Set.IsTubeAbout x₀ T ∧ T ⊆ N := by
  -- Enlarge the compact slice to an open product still contained in `N`.
  obtain ⟨W, V, hW_open, _, hx₀W, h_univ_V, hWV⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hN_open h_slice
  -- Replace the second open factor by all of `Y`, which it already contains.
  refine ⟨W ×ˢ Set.univ, Set.IsTubeAbout.prod_univ hW_open ?_, ?_⟩
  · exact Set.singleton_subset_iff.mp hx₀W
  · intro p hp
    exact hWV ⟨hp.1, h_univ_V hp.2⟩

/-- The tube supplied by `tubeLemma` can be realized as the product of an open
neighborhood of `x₀` with all of `Y`. -/
theorem exists_open_prod_univ_subset {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace Y] {x₀ : X} {N : Set (X × Y)}
    (hN_open : IsOpen N)
    (h_slice : ({x₀} : Set X) ×ˢ (Set.univ : Set Y) ⊆ N) :
    ∃ W : Set X, IsOpen W ∧ x₀ ∈ W ∧ W ×ˢ (Set.univ : Set Y) ⊆ N := by
  obtain ⟨T, hT_tube, hT⟩ := tubeLemma hN_open h_slice
  obtain ⟨W, hW_open, hx₀, rfl⟩ := Set.isTubeAbout_iff.mp hT_tube
  exact ⟨W, hW_open, hx₀, hT⟩
