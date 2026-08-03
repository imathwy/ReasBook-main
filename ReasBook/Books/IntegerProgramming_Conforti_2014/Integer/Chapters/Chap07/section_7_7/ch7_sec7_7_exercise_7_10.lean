import Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_2_theorem_7_7
import Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_proposition_7_2
import Integer.Chapters.Chap07.section_7_1.ch7_sec7_1_proposition_7_1_part2
import Integer.Chapters.Chap07.section_7_7.ch7_sec7_7_exercise_7_8

open scoped BigOperators Matrix
open SequenceIndependentLifting

section Exercise710

/-- The weight vector `(8,5,3,12)` from Exercise 7.10, indexed so that `i : Fin 4` represents the
textbook variable `x_(i+1)`. -/
def exercise_7_10_weights : Fin 4 → ℕ :=
  ![8, 5, 3, 12]

/-- The real-valued weight vector of Exercise 7.10, used by the Chapter 3 and 7.2 real-vector
owners, is the canonical coercion bridge from `exercise_7_10_weights`. -/
abbrev exercise_7_10_weights_real : Fin 4 → ℝ :=
  fun i ↦ (exercise_7_10_weights i : ℝ)

/-- The knapsack capacity in Exercise 7.10. -/
def exercise_7_10_capacity : ℕ :=
  14

/-- The natural `0,1` knapsack set attached to the data of Exercise 7.10. -/
def exercise_7_10_knapsack_set : Set (Fin 4 → ℝ) :=
  zero_one_knapsack_set exercise_7_10_weights_real exercise_7_10_capacity

/-- The minimal cover `C = {1,2,3}` from Exercise 7.10, represented on `Fin 4` by the zero-based
indices `{0,1,2}`. -/
def exercise_7_10_cover : Finset (Fin 4) :=
  {0, 1, 2}

/-- Membership in the concrete cover from Exercise 7.10 means being one of the first three
coordinates. -/
theorem mem_exercise_7_10_cover_iff
    (j : Fin 4) :
    j ∈ exercise_7_10_cover ↔ j.1 < 3 := by
  fin_cases j <;> decide

/-- The cover `C = {1,2,3}` is a minimal knapsack cover for the instance of Exercise 7.10. -/
theorem exercise_7_10_cover_is_minimal :
    IsMinimalKnapsackCover
      exercise_7_10_weights
      exercise_7_10_capacity
      exercise_7_10_cover := sorry

/-- The base cover-inequality coefficients `(1,1,1)` on `(x₁,x₂,x₃)` are the Chapter 7 owner
`SequenceIndependentLifting.base_coefficients` specialized to `Finset.univ`. -/
theorem exercise_7_10_cover_base_coeff_eq :
    base_coefficients (Finset.univ : Finset (Fin 3)) (fun _ ↦ (1 : ℝ)) = fun _ ↦ 1 := by
  ext i
  simp [base_coefficients]

/-- The residual weight vector `(8,5,3)` for the lifting problem obtained from Exercise 7.10
after fixing `x₄ = 1`. -/
def exercise_7_10_x4_lifting_weights : Fin 3 → ℕ :=
  fun i ↦ exercise_7_10_weights ⟨i.1, Nat.lt_trans i.2 (by decide)⟩

/-- The real-valued residual weight vector `(8,5,3)` used by the canonical `0,1` knapsack-set
owner is the coercion bridge from `exercise_7_10_x4_lifting_weights`. -/
abbrev exercise_7_10_x4_lifting_weights_real : Fin 3 → ℝ :=
  fun i ↦ (exercise_7_10_x4_lifting_weights i : ℝ)

/-- The residual lifting weights are exactly `(8,5,3)`. -/
theorem exercise_7_10_x4_lifting_weights_eq :
    exercise_7_10_x4_lifting_weights = ![8, 5, 3] :=
  by
    ext i
    fin_cases i <;> rfl

/-- The residual capacity for the lifting problem after fixing `x₄ = 1`. -/
def exercise_7_10_x4_lifting_capacity : ℕ :=
  exercise_7_10_capacity - exercise_7_10_weights 3

/-- Casting a binary natural assignment for `(x₁,x₂,x₃)` to `ℝ` identifies the residual
feasibility condition after fixing `x₄ = 1` with membership in the canonical `0,1` knapsack set
with weights `(8,5,3)` and capacity `2`. -/
theorem exercise_7_10_x4_lifting_feasible_iff_mem_zero_one_knapsack_set
    (x : Fin 3 → ℕ) :
    ((∀ i, x i = 0 ∨ x i = 1) ∧
        ∑ i, exercise_7_10_x4_lifting_weights i * x i ≤ exercise_7_10_x4_lifting_capacity) ↔
      (fun i ↦ (x i : ℝ)) ∈
        zero_one_knapsack_set
          exercise_7_10_x4_lifting_weights_real
          exercise_7_10_x4_lifting_capacity := sorry

/-- Exercise 7.10 (1): Proposition 7.2 applied to the `x₄ = 1` slice of the Exercise 7.10
knapsack set gives the last-coordinate lifting coefficient `α₄ = 2`; equivalently, the slice
objective `x₁ + x₂ + x₃` has greatest value `0` there. -/
theorem exercise_7_10_alpha_4_spec :
    last_coordinate_lifting_coefficient
        exercise_7_10_knapsack_set
        (base_coefficients (Finset.univ : Finset (Fin 3)) fun _ ↦ (1 : ℝ))
        (cover_inequality_rhs exercise_7_10_cover) =
      2 ∧
      IsGreatest
        (last_coordinate_slice_values
          exercise_7_10_knapsack_set
          (base_coefficients (Finset.univ : Finset (Fin 3)) fun _ ↦ (1 : ℝ))
          1)
        0 := sorry

/-- The lifted coefficient vector of Exercise 7.10 is the canonical lifted-cover coefficient owner
for the cover `{1,2,3}` and the complement coefficient `2` on `x₄`. -/
theorem exercise_7_10_lifted_cover_coeff_eq :
    lifted_cover_inequality_coeff
        exercise_7_10_cover
        ![(0 : ℝ), 0, 0, 2] =
      ![(1 : ℝ), 1, 1, 2] := by
  ext i
  fin_cases i <;> rfl

/-- The zero solution on `(x₁,x₂,x₃)` is feasible for the
residual-capacity lifting problem after setting `x₄ = 1`. -/
theorem exercise_7_10_x4_lifting_zero_feasible :
    (0 : Fin 3 → ℝ) ∈
      zero_one_knapsack_set
        exercise_7_10_x4_lifting_weights_real
        exercise_7_10_x4_lifting_capacity := by
  rw [mem_zero_one_knapsack_set_iff]
  constructor
  · intro i
    left
    simp
  · simp

/-- The zero solution on `(x₁,x₂,x₃)` has objective value `0`. -/
theorem exercise_7_10_x4_lifting_zero_objective :
    ∑ i, (0 : Fin 3 → ℕ) i = 0 := by
  simp

/-- Every feasible solution of the residual-capacity lifting problem after setting `x₄ = 1` has
objective value at most `0`. -/
theorem exercise_7_10_x4_lifting_objective_nonpositive
    (y : Fin 3 → ℕ)
    (hy : (fun i ↦ (y i : ℝ)) ∈
      zero_one_knapsack_set
        exercise_7_10_x4_lifting_weights_real
        exercise_7_10_x4_lifting_capacity) :
    ∑ i, y i ≤ 0 := sorry

/-- Exercise 7.10 (2): the lifted cover inequality `x₁ + x₂ + x₃ + 2x₄ ≤ 2`
is not a Chvatal inequality for the natural `0,1` knapsack formulation
of Exercise 7.10. -/
theorem exercise_7_10_lifted_cover_inequality_is_not_chvatal :
    ¬ IsKnapsackChvatalPresentation
        exercise_7_10_weights
        exercise_7_10_capacity
        ![(1 : ℝ), 1, 1, 2]
        (exercise_7_10_cover.card - 1) := sorry

end Exercise710
