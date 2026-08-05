import Books.FirstOrderMethodsInOptimization_Beck_2017.Chap02.Proposition_2_13

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix

noncomputable section

section

/- Example 2.10 is bridge-only: the intrinsic statement is the chapter owner theorem
`support_function_unit_simplex_eq_coordinate_max`, which already identifies the support function
of the unit simplex with the coordinate supremum `⨆ i, (y i : EReal)`. -/
recall support_function_unit_simplex_eq_coordinate_max

variable {n : ℕ} [Nonempty (Fin n)] (y : Fin n → ℝ)

/- For a nonempty finite index type, the coordinate supremum from the owner theorem is the finite
maximum over `Finset.univ`. -/
theorem support_function_unit_simplex_eq_coordinate_sup' :
    support_function (stdSimplex ℝ (Fin n)) (dotProductEquiv ℝ (Fin n) y) =
      Finset.univ.sup' Finset.univ_nonempty (fun i ↦ (y i : EReal)) := by
  simpa [Finset.sup'_univ_eq_ciSup] using support_function_unit_simplex_eq_coordinate_max y

end
