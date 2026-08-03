module

public import Topology_Munkres_2000.Book.Example_24_3

public section

/-- Example 24.4: If `n > 1`, punctured Euclidean space
`ℝⁿ ∖ {0}` is path connected. -/
theorem isPathConnected_puncturedEuclideanSpace (n : ℕ) (hn : 1 < n) :
    IsPathConnected ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := by
  apply isPathConnected_compl_singleton_of_one_lt_rank
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  exact_mod_cast hn
