import Integer.Chapters.Chap05.section_5_1_4.ch5_sec5_1_4_definition_5_1_4_extra_1
import Integer.Chapters.Chap06.section_6_1.ch6_sec6_1_definition_6_1_extra_1
import Integer.Chapters.Chap06.section_6_2.ch6_sec6_2_example_6_10

open scoped BigOperators Matrix

/-
Domain-style sampling for this refine pass:
* primary domain: one-row Gomory mixed-integer cuts for a tableau row of a corner polyhedron
* core/canonical owner: `gomory_mixed_integer_inequality`
* source-facing owner: `exercise_6_1_row_gomory_mixed_integer_cut`
* bridge/view layer here: the tableau row is extended off the nonbasic support by
  `Finset.piecewise`
-/

noncomputable section

section Exercise61

variable {n p : ℕ}

/-- The tableau-row Gomory mixed-integer cut of Exercise 6.1, formed from row `i` by extending
the nonbasic coefficients by zero outside `corner_nonbasic_indices hp B`. -/
def exercise_6_1_row_gomory_mixed_integer_cut
    (hp : p ≤ n)
    (B : Finset (Fin p))
    (barA : Matrix (Fin p) (Fin n) ℚ)
    (barb : Fin p → ℚ)
    (i : Fin p)
    (hfrac : 0 < Int.fract (barb i : ℝ)) : Set (Fin n → ℝ) :=
  gomory_mixed_integer_cut p
    ((corner_nonbasic_indices hp B).piecewise (fun j ↦ (barA i j : ℝ)) 0)
    (barb i : ℝ)
    hfrac

/-- The row-cut owner of Exercise 6.1 is exactly the Chapter 5 canonical owner
`gomory_mixed_integer_inequality` specialized to the first `p` integer coordinates and the
zero-extended tableau row. -/
theorem exercise_6_1_row_gomory_mixed_integer_cut_eq_gomory_mixed_integer_inequality
    (hp : p ≤ n)
    (B : Finset (Fin p))
    (barA : Matrix (Fin p) (Fin n) ℚ)
    (barb : Fin p → ℚ)
    (i : Fin p)
    (hfrac : 0 < Int.fract (barb i : ℝ)) :
    exercise_6_1_row_gomory_mixed_integer_cut hp B barA barb i hfrac =
      gomory_mixed_integer_inequality
        (Finset.univ.filter fun j : Fin n ↦ j.1 < p)
        ((corner_nonbasic_indices hp B).piecewise (fun j ↦ (barA i j : ℝ)) 0)
        (barb i : ℝ)
        hfrac := by
  let row : Fin n → ℝ :=
    (corner_nonbasic_indices hp B).piecewise (fun j ↦ (barA i j : ℝ)) 0
  let I : Finset (Fin n) := Finset.univ.filter fun j : Fin n ↦ j.1 < p
  have hrow :
      0 < gomory_row_fraction (barb i : ℝ) := hfrac
  ext x
  change
      (1 ≤ ∑ j : Fin n,
          gomory_mixed_integer_cut_coefficient p row (barb i : ℝ) hrow j * x j) ↔
        1 ≤ ∑ j : Fin n,
          gomory_mixed_integer_inequality_coefficient I row (barb i : ℝ) hfrac j * x j
  have hcoeff :
      ∀ j : Fin n,
        gomory_mixed_integer_cut_coefficient p row (barb i : ℝ) hrow j =
          gomory_mixed_integer_inequality_coefficient I row (barb i : ℝ) hfrac j := by
    intro j
    by_cases hj : j.1 < p
    · simp [gomory_mixed_integer_cut_coefficient, gomory_mixed_integer_inequality_coefficient,
        row, I, hj]
    · by_cases hpos : 0 < row j
      · simp [gomory_mixed_integer_cut_coefficient, gomory_mixed_integer_inequality_coefficient,
          row, I, hj, le_of_lt hpos]
      · by_cases hneg : row j < 0
        · simp [gomory_mixed_integer_cut_coefficient,
            gomory_mixed_integer_inequality_coefficient, row, I, hj, not_le.mpr hneg]
        · have hzero : row j = 0 := by linarith
          simp [gomory_mixed_integer_cut_coefficient,
            gomory_mixed_integer_inequality_coefficient, row, I, hj, hzero]
  have hsum :
      ∑ j : Fin n, gomory_mixed_integer_cut_coefficient p row (barb i : ℝ) hrow j * x j =
        ∑ j : Fin n,
          gomory_mixed_integer_inequality_coefficient I row (barb i : ℝ) hfrac j * x j := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hcoeff j]
  simp [hsum]

/-- Exercise 6.1. If `i ∈ B` indexes a tableau row of (6.2) with fractional right-hand side,
then the tableau-row Gomory mixed-integer cut generated from that row is valid for the corner
polyhedron `corner_polyhedron hp B barA barb`. -/
theorem exercise_6_1_row_gomory_mixed_integer_cut_valid_for_corner
    (hp : p ≤ n)
    (B : Finset (Fin p))
    (barA : Matrix (Fin p) (Fin n) ℚ)
    (barb : Fin p → ℚ)
    {i : Fin p}
    (hi : i ∈ B)
    (hfrac : 0 < Int.fract (barb i : ℝ)) :
    corner_polyhedron hp B barA barb ⊆
      exercise_6_1_row_gomory_mixed_integer_cut hp B barA barb i hfrac := sorry

/-- Exercise 6.1. If `i ∈ B` indexes a tableau row of (6.2) with fractional right-hand side,
then the canonical Chapter 5 owner `gomory_mixed_integer_inequality` generated from that row is
valid for the corner polyhedron `corner_polyhedron hp B barA barb`. The row coefficients are
extended by zero outside the nonbasic index set using `Finset.piecewise`, and the integer block
is the first `p` coordinates of `Fin n`. -/
theorem exercise_6_1_gomory_mixed_integer_inequality_valid_for_corner
    (hp : p ≤ n)
    (B : Finset (Fin p))
    (barA : Matrix (Fin p) (Fin n) ℚ)
    (barb : Fin p → ℚ)
    {i : Fin p}
    (hi : i ∈ B)
    (hfrac : 0 < Int.fract (barb i : ℝ)) :
    corner_polyhedron hp B barA barb ⊆
      gomory_mixed_integer_inequality
        (Finset.univ.filter fun j : Fin n ↦ j.1 < p)
        ((corner_nonbasic_indices hp B).piecewise (fun j ↦ (barA i j : ℝ)) 0)
        (barb i : ℝ)
        hfrac := by
  simpa [exercise_6_1_row_gomory_mixed_integer_cut_eq_gomory_mixed_integer_inequality hp B barA
    barb i hfrac] using
    exercise_6_1_row_gomory_mixed_integer_cut_valid_for_corner hp B barA barb hi hfrac

end Exercise61
