import Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_1_remark_7_5

open scoped BigOperators Matrix

section Example76

/-- The weight vector `(5,4,3,2,1)` from Example 7.6. -/
def example_7_6_weights : Fin 5 → ℕ :=
  ![5, 4, 3, 2, 1]

/-- The `0,1` knapsack set
`K = {x ∈ {0,1}^5 : 5x₁ + 4x₂ + 3x₃ + 2x₄ + x₅ ≤ 5}` from Example 7.6. -/
def example_7_6_knapsack_set : Set (Fin 5 → ℝ) :=
  zero_one_knapsack_set (fun i ↦ (example_7_6_weights i : ℝ)) 5

/-- Membership in `example_7_6_knapsack_set` means being binary and satisfying the displayed
knapsack inequality. -/
theorem mem_example_7_6_knapsack_set_iff
    (x : Fin 5 → ℝ) :
    x ∈ example_7_6_knapsack_set ↔
      (∀ i, x i = 0 ∨ x i = 1) ∧
        ((5 : ℝ) * x 0 + 4 * x 1 + 3 * x 2 + 2 * x 3 + x 4 ≤ 5) := sorry

/-- The knapsack polytope `conv(K)` attached to Example 7.6. -/
def example_7_6_knapsack_polytope : Set (Fin 5 → ℝ) :=
  zero_one_knapsack_polytope (fun i ↦ (example_7_6_weights i : ℝ)) 5

/-- `example_7_6_knapsack_polytope` is the convex hull of the Example 7.6 feasible set. -/
theorem example_7_6_knapsack_polytope_eq_convexHull :
    example_7_6_knapsack_polytope = convexHull ℝ example_7_6_knapsack_set := sorry

/-- The cover `C = {3,4,5}` from Example 7.6, written with zero-based indices as `{2,3,4}`. -/
def example_7_6_cover : Finset (Fin 5) :=
  {2, 3, 4}

/-- The values `μ₀ = 0`, `μ₁ = 3`, `μ₂ = 5`, and `μ₃ = 6` used in Example 7.6. -/
def example_7_6_mu : ℕ → ℕ
  | 0 => 0
  | 1 => 3
  | 2 => 5
  | 3 => 6
  | _ => 6

/-- The lifting profile used in Example 7.6 has coefficients `2` on item `1` and `1` on item `2`
outside the cover, and its values on the cover are ignored by `remark_7_5_lifting_coeff`. -/
def example_7_6_lifting_function : Fin 5 → ℕ :=
  ![2, 1, 0, 0, 0]

/-- The lifted cover inequality from Example 7.6 has coefficient vector `(2,1,1,1,1)`. -/
def example_7_6_lifted_vector : Fin 5 → ℝ :=
  remark_7_5_lifting_coeff example_7_6_cover example_7_6_lifting_function

/-- `example_7_6_lifted_vector` evaluates to the displayed coefficient vector `(2,1,1,1,1)`. -/
theorem example_7_6_lifted_vector_apply
    (j : Fin 5) :
    example_7_6_lifted_vector j =
      ![(2 : ℝ), 1, 1, 1, 1] j := sorry

/-- Every item weight in Example 7.6 is at most the capacity `5`. -/
theorem example_7_6_weights_le_capacity
    (j : Fin 5) :
    example_7_6_weights j ≤ 5 := sorry

/-- The first non-cover weight lies in the interval `μ₂ ≤ a₁ ≤ μ₃ - 1` used to read off
`α₁ = 2`. -/
theorem example_7_6_first_weight_interval :
    example_7_6_mu 2 ≤ example_7_6_weights 0 ∧
      example_7_6_weights 0 ≤ example_7_6_mu 3 - 1 := sorry

/-- The second non-cover weight lies in the interval `μ₁ ≤ a₂ ≤ μ₂ - 1` used to read off
`α₂ = 1`. -/
theorem example_7_6_second_weight_interval :
    example_7_6_mu 1 ≤ example_7_6_weights 1 ∧
      example_7_6_weights 1 ≤ example_7_6_mu 2 - 1 := sorry

/-- The non-cover items of Example 7.6 satisfy the interval hypothesis from Remark 7.5. -/
theorem example_7_6_interval_indices :
    remark_7_5_interval_indices
      example_7_6_weights
      example_7_6_cover
      example_7_6_mu
      example_7_6_lifting_function := sorry

/-- The strengthened upper bound `a_j ≤ μ_{h(j)+1} - 1` from Remark 7.5 holds for every non-cover
item in Example 7.6. -/
theorem example_7_6_strong_upper_bound :
    remark_7_5_strong_upper_bound
      example_7_6_weights
      example_7_6_cover
      example_7_6_mu
      example_7_6_lifting_function
      1 := sorry

/-- Example 7.6 (1). The set `C = {3,4,5}` is a minimal cover for the knapsack set
`K = {x ∈ {0,1}^5 : 5x₁ + 4x₂ + 3x₃ + 2x₄ + x₅ ≤ 5}`. -/
theorem example_7_6_cover_is_minimal :
    IsMinimalKnapsackCover example_7_6_weights 5 example_7_6_cover := sorry

/-- Example 7.6 (2). The first lifted coefficient satisfies `α₁ = 2`. -/
theorem example_7_6_alpha_1_eq_two :
    example_7_6_lifting_function 0 = 2 := sorry

/-- Example 7.6 (3). The second lifted coefficient satisfies `α₂ = 1`. -/
theorem example_7_6_alpha_2_eq_one :
    example_7_6_lifting_function 1 = 1 := sorry

/-- Example 7.6 (4). By Remark 7.5, the lifted inequality
`2x₁ + x₂ + x₃ + x₄ + x₅ ≤ 2` defines a facet of `conv(K)`. -/
theorem example_7_6_lifted_inequality_is_facet_defining :
    example_7_6_lifted_vector ∈
      facet_defining_liftings_of_minimal_cover_inequality
        example_7_6_weights
        5
        example_7_6_cover := sorry

/-- Example 7.6 (5). By Remark 7.5, `2x₁ + x₂ + x₃ + x₄ + x₅ ≤ 2` is the unique
facet-defining lifting of the minimal cover inequality attached to `C = {3,4,5}`. -/
theorem example_7_6_unique_facet_defining_lifting
    {α : Fin 5 → ℝ}
    (hα : α ∈
      facet_defining_liftings_of_minimal_cover_inequality
        example_7_6_weights
        5
        example_7_6_cover) :
    α = example_7_6_lifted_vector := sorry

end Example76
