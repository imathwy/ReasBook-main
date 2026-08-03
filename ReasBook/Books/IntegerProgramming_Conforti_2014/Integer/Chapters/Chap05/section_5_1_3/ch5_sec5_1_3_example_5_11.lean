import Integer.Chapters.Chap05.section_5_1_5.ch5_sec5_1_5_theorem_5_12

open scoped Matrix

-- This example reuses the Chapter 3/5 owners `polyhedron_le_set`,
-- `mixed_integer_feasible_set`, and `mixed_split_closure`.

section Example511

/- Source-facing layer: the concrete simplex and mixed-integer set from Example 5.11 are kept in
`Fin 3 → ℝ` coordinates. Core/canonical layer: the simplex is presented through its matrix owner,
and the mixed-integer set is presented through the Chapter 5 owner
`mixed_integer_feasible_set`. -/

/-- A matrix presentation of the simplex from Example 5.11 in the coordinate order
`(x₁, x₂, y)`. -/
def example_5_11_matrix : Matrix (Fin 4) (Fin 3) ℝ :=
  ![![-1, 0, 1],
    ![0, -1, 1],
    ![1, 1, 2],
    ![0, 0, -1]]

/-- The right-hand side vector for `example_5_11_matrix`. -/
def example_5_11_rhs : Fin 4 → ℝ :=
  ![0, 0, 2, 0]

/-- The integer-variable index set `I = {x₁, x₂}` from Example 5.11. -/
def example_5_11_integer_indices : Finset (Fin 3) :=
  {0, 1}

/-- The simplex `P = {(x₁, x₂, y) ∈ ℝ³_+ | y ≤ x₁, y ≤ x₂, x₁ + x₂ + 2 y ≤ 2}` from
Example 5.11, written in `Fin 3 → ℝ` coordinates. -/
def example_5_11_polyhedron : Set (Fin 3 → ℝ) :=
  polyhedron_le_set example_5_11_matrix example_5_11_rhs

/-- Membership in `example_5_11_polyhedron` is exactly the explicit nonnegativity and simplex
inequality system from Example 5.11. -/
theorem mem_example_5_11_polyhedron_iff
    {v : Fin 3 → ℝ} :
    v ∈ example_5_11_polyhedron ↔
      0 ≤ v 0 ∧
        0 ≤ v 1 ∧
          0 ≤ v 2 ∧
            v 2 ≤ v 0 ∧
              v 2 ≤ v 1 ∧
                v 0 + v 1 + 2 * v 2 ≤ 2 := by
  rw [example_5_11_polyhedron, mem_polyhedron_le_set_iff]
  constructor
  · intro hv
    have h0 := hv 0
    have h1 := hv 1
    have h2 := hv 2
    have h3 := hv 3
    norm_num [example_5_11_matrix, example_5_11_rhs, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      at h0 h1 h2 h3
    have hyx0 : v 2 ≤ v 0 := by
      simpa using h0
    have hyx1 : v 2 ≤ v 1 := by
      simpa using h1
    have hineq : v 0 + v 1 + 2 * v 2 ≤ 2 := by
      simpa using h2
    have hy : 0 ≤ v 2 := by
      have h3' : -v 2 ≤ 0 := by
        simpa using h3
      linarith
    have hx0 : 0 ≤ v 0 := by
      linarith
    have hx1 : 0 ≤ v 1 := by
      linarith
    exact ⟨hx0, hx1, hy, hyx0, hyx1, hineq⟩
  · rintro ⟨hx0, hx1, hy, hyx0, hyx1, hineq⟩ i
    fin_cases i
    · simpa [example_5_11_matrix, example_5_11_rhs, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        using hyx0
    · simpa [example_5_11_matrix, example_5_11_rhs, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        using hyx1
    · simpa [example_5_11_matrix, example_5_11_rhs, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        using hineq
    · have h3 : -v 2 ≤ 0 := by
        linarith
      simpa [example_5_11_matrix, example_5_11_rhs, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        using h3

/-- The mixed-integer set
`S = {(x₁, x₂, y) ∈ ℤ²_+ × ℝ_+ | y ≤ x₁, y ≤ x₂, x₁ + x₂ + 2 y ≤ 2}` from Example 5.11. -/
def example_5_11_mixed_integer_set : Set (Fin 3 → ℝ) :=
  mixed_integer_feasible_set
    example_5_11_matrix
    example_5_11_rhs
    example_5_11_integer_indices

/-- Membership in `example_5_11_mixed_integer_set` means feasibility in
`example_5_11_polyhedron` together with integrality of the first two coordinates. -/
theorem mem_example_5_11_mixed_integer_set_iff
    {v : Fin 3 → ℝ} :
    v ∈ example_5_11_mixed_integer_set ↔
      v ∈ example_5_11_polyhedron ∧
        (∃ z : ℤ, v 0 = (z : ℝ)) ∧
          ∃ z : ℤ, v 1 = (z : ℝ) := by
  rw [example_5_11_mixed_integer_set, mem_mixed_integer_feasible_set_iff]
  constructor
  · rintro ⟨hv, hint⟩
    refine ⟨?_, ?_, ?_⟩
    · change v ∈ polyhedron_le_set example_5_11_matrix example_5_11_rhs
      exact (mem_polyhedron_le_set_iff).2 hv
    · exact hint 0 (by simp [example_5_11_integer_indices])
    · exact hint 1 (by simp [example_5_11_integer_indices])
  · rintro ⟨hv, hz0, hz1⟩
    refine ⟨?_, ?_⟩
    · have hv' : v ∈ polyhedron_le_set example_5_11_matrix example_5_11_rhs := by
        simpa [example_5_11_polyhedron] using hv
      exact (mem_polyhedron_le_set_iff).1 hv'
    · intro j hj
      fin_cases j
      · simpa [example_5_11_integer_indices] using hz0
      · simpa [example_5_11_integer_indices] using hz1
      · simp [example_5_11_integer_indices] at hj

/-- The `k`-fold mixed split closure `P^k` of the Example 5.11 simplex relative to the integer
coordinates `I = {x₁, x₂}`. -/
def example_5_11_iterated_split_closure (k : ℕ) : Set (Fin 3 → ℝ) :=
  (mixed_split_closure example_5_11_integer_indices)^[k] example_5_11_polyhedron

/-- The zeroth mixed split closure `P⁰` of Example 5.11 is the original simplex `P`. -/
theorem example_5_11_iterated_split_closure_zero :
    example_5_11_iterated_split_closure 0 = example_5_11_polyhedron :=
  rfl

/-- The recursive step `P^(k + 1) = (P^k)^split` for the Example 5.11 mixed split-closure
sequence relative to `I = {x₁, x₂}`. -/
theorem example_5_11_iterated_split_closure_succ
    (k : ℕ) :
    example_5_11_iterated_split_closure (k + 1) =
      mixed_split_closure example_5_11_integer_indices
        (example_5_11_iterated_split_closure k) := by
  simp [example_5_11_iterated_split_closure, Function.iterate_succ_apply']

/-- The witness point `((1 / 2), (1 / 2), (1 / 2) / 3^k)` remains in the `k`-fold mixed split
closure of the Example 5.11 simplex relative to `I = {x₁, x₂}`. -/
theorem example_5_11_witness_mem_iterated_split_closure
    (k : ℕ) :
    ![(1 / 2 : ℝ), (1 / 2 : ℝ), (1 / 2 : ℝ) / (3 : ℝ) ^ k] ∈
      example_5_11_iterated_split_closure k := sorry

/-- The mixed-integer hull of the Example 5.11 set lies in the plane `y = 0`. -/
theorem example_5_11_mixed_integer_hull_subset_y_eq_zero :
    convexHull ℝ example_5_11_mixed_integer_set ⊆
      {v : Fin 3 → ℝ | v 2 = 0} := sorry

/-- Example 5.11. For the simplex
`P = {(x₁, x₂, y) ∈ ℝ³_+ | y ≤ x₁, y ≤ x₂, x₁ + x₂ + 2 y ≤ 2}` and the mixed-integer set
`S = {(x₁, x₂, y) ∈ ℤ²_+ × ℝ_+ | y ≤ x₁, y ≤ x₂, x₁ + x₂ + 2 y ≤ 2}`, every positive iterated
mixed split closure `P^k` relative to `I = {x₁, x₂}` is still strictly larger than `conv(S)`. -/
theorem example_5_11_iterated_split_closure_ne_convexHull_mixed_integer_set
    (k : ℕ)
    (hk : 0 < k) :
    example_5_11_iterated_split_closure k ≠ convexHull ℝ example_5_11_mixed_integer_set :=
  sorry

end Example511
