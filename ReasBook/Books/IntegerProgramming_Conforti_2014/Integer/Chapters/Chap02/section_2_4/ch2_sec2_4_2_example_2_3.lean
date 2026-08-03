import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search note: `lean_leansearch` was unavailable in this session, so this file uses
-- direct local inspection of Mathlib's matrix API.

/-- The maximal-clique versus node incidence matrix `A_c` displayed in Example 2.3. -/
def example_2_3_clique_matrix : Matrix (Fin 3) (Fin 5) ℚ :=
  !![(1 : ℚ), 1, 0, 0, 1;
    0, 1, 1, 1, 0;
    0, 1, 0, 1, 1]

/-- The fractional point `(0, 1/2, 1/2, 1/2, 0)` used in Example 2.3. -/
def example_2_3_fractional_point : Fin 5 → ℚ :=
  ![(0 : ℚ), 1 / 2, 1 / 2, 1 / 2, 0]

/-- The fractional point from Example 2.3 lies in the unit cube. -/
theorem example_2_3_fractional_point_mem_unit_cube :
    ∀ i, 0 ≤ example_2_3_fractional_point i ∧ example_2_3_fractional_point i ≤ 1 := sorry

/-- Example 2.3. For the maximal-clique incidence matrix `A_c` of Fig. 2.1, the point
`(0, 1/2, 1/2, 1/2, 0)` yields row values `(1/2, 3/2, 1)`, so the clique inequality
`x₂ + x₃ + x₄ ≤ 1` is violated. -/
theorem example_2_3_clique_matrix_mulVec_fractional_point :
    example_2_3_clique_matrix.mulVec example_2_3_fractional_point =
      ![(1 : ℚ) / 2, 3 / 2, 1] := sorry
