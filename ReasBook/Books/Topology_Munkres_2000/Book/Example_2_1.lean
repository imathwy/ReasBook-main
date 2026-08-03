module

public import Topology_Munkres_2000.Book.Example_2_1.SquareMaps

public section

/-- Example 2.1 check-only entry: the four square functions have the domains and
codomains specified in the example. -/
theorem squareFunctionsHaveSpecifiedTypes :
    Nonempty
      ((ℝ → ℝ) × (NNReal → ℝ) × (ℝ → NNReal) × (NNReal → NNReal)) := by
  -- Package the four already defined square functions with their specified types.
  exact ⟨realSquare, nnrealSquareToReal, realSquareToNNReal, NNReal.sqrt.symm⟩
