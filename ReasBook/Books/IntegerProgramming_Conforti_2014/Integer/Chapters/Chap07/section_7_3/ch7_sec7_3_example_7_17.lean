import Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_theorem_7_16

open scoped BigOperators
open OrderedFlowCover

-- Declarations for this item will be appended below by the statement pipeline.

section Example717

/-- The capacity vector `(17, 9, 8, 6, 5, 4)` from Example 7.17. -/
def example_7_17_capacity : Fin 6 → ℝ
  | 0 => 17
  | 1 => 9
  | 2 => 8
  | 3 => 6
  | 4 => 5
  | 5 => 4

/-- The right-hand side `20` from Example 7.17. -/
def example_7_17_rhs : ℝ :=
  20

/-- The flow-cover set `C = {3,4,5,6}` from Example 7.17, written with zero-based `Fin 6`
indices as `{2,3,4,5}`. -/
def example_7_17_cover : Finset (Fin 6) :=
  {2, 3, 4, 5}

/-- The source cover in Example 7.17 has four elements. -/
theorem example_7_17_cover_card :
    example_7_17_cover.card = 4 := by
  decide

/-- The cover excess `λ = 23 - 20 = 3` for Example 7.17. -/
def example_7_17_excess : ℝ :=
  3

/-- The flow-cover excess attached to `example_7_17_cover` is the source value `3`. -/
theorem example_7_17_excess_eq_flow_cover_excess :
    example_7_17_excess =
      flow_cover_excess example_7_17_capacity example_7_17_rhs example_7_17_cover := by
  sorry

/-- The capacities in Example 7.17 are nonnegative. -/
theorem example_7_17_capacity_nonneg (i : Fin 6) :
    0 ≤ example_7_17_capacity i := by
  fin_cases i <;> norm_num [example_7_17_capacity]

/-- The source cover `C = {3,4,5,6}` is a flow cover for Example 7.17. -/
instance example_7_17_isFlowCover :
    IsFlowCover example_7_17_capacity example_7_17_rhs example_7_17_cover := by
  sorry

/-- The right-hand side `9` of the lifted flow cover inequality in Example 7.17. -/
def example_7_17_inequality_rhs : ℝ :=
  9

/-- The single-node flow set
`T = {(x,y) ∈ {0,1}^6 × ℝ^6_+ | y₁ + ⋯ + y₆ ≤ 20, y₁ ≤ 17 x₁, y₂ ≤ 9 x₂, y₃ ≤ 8 x₃,
y₄ ≤ 6 x₄, y₅ ≤ 5 x₅, y₆ ≤ 4 x₆}` from Example 7.17, encoded in `((Fin 6 → ℝ) × (Fin 6 → ℝ))`.
-/
def example_7_17_flow_set : Set ((Fin 6 → ℝ) × (Fin 6 → ℝ)) :=
  single_node_flow_set example_7_17_capacity example_7_17_rhs

/-- Membership in `example_7_17_flow_set` is exactly the explicit binary, nonnegativity,
capacity, and upper-bound system from Example 7.17. -/
theorem mem_example_7_17_flow_set_iff
    {p : (Fin 6 → ℝ) × (Fin 6 → ℝ)} :
    p ∈ example_7_17_flow_set ↔
      (∀ i, p.1 i = 0 ∨ p.1 i = 1) ∧
        (∀ i, 0 ≤ p.2 i) ∧
          p.2 0 + p.2 1 + p.2 2 + p.2 3 + p.2 4 + p.2 5 ≤ 20 ∧
            p.2 0 ≤ 17 * p.1 0 ∧
              p.2 1 ≤ 9 * p.1 1 ∧
                p.2 2 ≤ 8 * p.1 2 ∧
                  p.2 3 ≤ 6 * p.1 3 ∧
                    p.2 4 ≤ 5 * p.1 4 ∧
                      p.2 5 ≤ 4 * p.1 5 := by
  constructor
  · intro hp
    rcases (mem_single_node_flow_set_iff example_7_17_capacity example_7_17_rhs p).1 hp with
      ⟨hx, hy, hsum, hcap⟩
    refine ⟨hx, hy, ?_, hcap 0, hcap 1, hcap 2, hcap 3, hcap 4, hcap 5⟩
    simpa [example_7_17_rhs, Fin.sum_univ_six] using hsum
  · intro hp
    rcases hp with ⟨hx, hy, hsum, h0, h1, h2, h3, h4, h5⟩
    refine (mem_single_node_flow_set_iff example_7_17_capacity example_7_17_rhs p).2 ?_
    refine ⟨hx, hy, ?_, ?_⟩
    · simpa [example_7_17_rhs, Fin.sum_univ_six] using hsum
    · intro i
      fin_cases i
      · simpa [example_7_17_capacity] using h0
      · simpa [example_7_17_capacity] using h1
      · simpa [example_7_17_capacity] using h2
      · simpa [example_7_17_capacity] using h3
      · simpa [example_7_17_capacity] using h4
      · simpa [example_7_17_capacity] using h5

/-- The admissible lifting pairs `(α₁, β₁)` for the coordinates `(y₁, x₁)` in Example 7.17. -/
def example_7_17_first_lifting_pairs : Set (ℝ × ℝ) :=
  {p |
    p = (0, 0) ∨
      p = ((1 / 2 : ℝ), (-(5 / 2 : ℝ))) ∨
        p = ((3 / 5 : ℝ), (-(18 / 5 : ℝ))) ∨
          p = (1, -10)}

/-- Membership in `example_7_17_first_lifting_pairs` means belonging to the four listed
possibilities for `(α₁, β₁)`. -/
theorem mem_example_7_17_first_lifting_pairs_iff
    {p : ℝ × ℝ} :
    p ∈ example_7_17_first_lifting_pairs ↔
      p = (0, 0) ∨
        p = ((1 / 2 : ℝ), (-(5 / 2 : ℝ))) ∨
          p = ((3 / 5 : ℝ), (-(18 / 5 : ℝ))) ∨
            p = (1, -10) := Iff.rfl

/-- The admissible lifting pairs `(α₂, β₂)` for the coordinates `(y₂, x₂)` in Example 7.17. -/
def example_7_17_second_lifting_pairs : Set (ℝ × ℝ) :=
  {p | p = (0, 0) ∨ p = ((3 / 4 : ℝ), (-(15 / 4 : ℝ)))}

/-- Membership in `example_7_17_second_lifting_pairs` means belonging to the two listed
possibilities for `(α₂, β₂)`. -/
theorem mem_example_7_17_second_lifting_pairs_iff
    {p : ℝ × ℝ} :
    p ∈ example_7_17_second_lifting_pairs ↔
      p = (0, 0) ∨ p = ((3 / 4 : ℝ), (-(15 / 4 : ℝ))) := Iff.rfl

/-- The ordered cover data from Theorem 7.16 specialized to Example 7.17 lists the cover indices
`2, 3, 4, 5`, corresponding to the source indices `3, 4, 5, 6`. -/
def example_7_17_cover_order : Fin example_7_17_cover.card ↪ Fin 6 :=
  { toFun := fun i ↦ ⟨i.1 + 2, by
      have hi : i.1 < 4 := by
        simpa [example_7_17_cover_card] using i.2
      omega⟩
    inj' := by
      intro i j hij
      apply Fin.ext
      exact Nat.add_right_cancel (Fin.ext_iff.mp hij) }

/-- The ordered cover data for Example 7.17 enumerates `example_7_17_cover`. -/
theorem example_7_17_cover_order_enumerates :
    enumerates example_7_17_cover example_7_17_cover_order := by
  sorry

/-- Along the ordered cover of Example 7.17, the cover capacities are weakly decreasing. -/
theorem example_7_17_cover_order_antitone :
    Antitone fun h : Fin example_7_17_cover.card ↦
      example_7_17_capacity (example_7_17_cover_order h) := by
  sorry

/-- The cut index `r` from Theorem 7.16 is `4` in Example 7.17. -/
def example_7_17_cutIndex : ℕ :=
  4

/-- The Example 7.17 cut index satisfies the source cut-index conditions from Theorem 7.16. -/
theorem example_7_17_cutIndex_isCutIndex :
    isCutIndex
      example_7_17_capacity
      example_7_17_cover
      example_7_17_cover_order
      example_7_17_excess
      example_7_17_cutIndex := by
  sorry

/-- The listed admissible pairs for `(α₁, β₁)` are exactly the Theorem 7.16 admissible pairs for
the first noncover coordinate. -/
theorem example_7_17_first_lifting_pair_iff_admissiblePair
    (α₁ β₁ : ℝ) :
    (α₁, β₁) ∈ example_7_17_first_lifting_pairs ↔
      admissiblePair
        example_7_17_capacity
        example_7_17_rhs
        example_7_17_cover
        example_7_17_cover_order
        example_7_17_cutIndex
        0
        α₁
        β₁ := by
  sorry

/-- The listed admissible pairs for `(α₂, β₂)` are exactly the Theorem 7.16 admissible pairs for
the second noncover coordinate. -/
theorem example_7_17_second_lifting_pair_iff_admissiblePair
    (α₂ β₂ : ℝ) :
    (α₂, β₂) ∈ example_7_17_second_lifting_pairs ↔
      admissiblePair
        example_7_17_capacity
        example_7_17_rhs
        example_7_17_cover
        example_7_17_cover_order
        example_7_17_cutIndex
        1
        α₂
        β₂ := by
  sorry

/-- The `α`-coefficients on `N \ C = {1,2}` from Example 7.17, written with zero-based
`Fin 6` indices as `{0,1}`. -/
def example_7_17_alpha_coeffs (α₁ α₂ : ℝ) : Fin 6 → ℝ
  | 0 => α₁
  | 1 => α₂
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0

/-- The `β`-coefficients on `N \ C = {1,2}` from Example 7.17, written with zero-based
`Fin 6` indices as `{0,1}`. -/
def example_7_17_beta_coeffs (β₁ β₂ : ℝ) : Fin 6 → ℝ
  | 0 => β₁
  | 1 => β₂
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0

/-- The left-hand side of the lifted flow cover inequality from Example 7.17 evaluated at a point
`(x, y)` and coefficient pair choices `(α₁, β₁)` and `(α₂, β₂)`. -/
def example_7_17_lifted_flow_cover_value
    (α₁ β₁ α₂ β₂ : ℝ)
    (p : (Fin 6 → ℝ) × (Fin 6 → ℝ)) : ℝ :=
  α₁ * p.2 0 + β₁ * p.1 0 + α₂ * p.2 1 + β₂ * p.1 1 +
    p.2 2 + p.2 3 + p.2 4 + p.2 5 - 5 * p.1 2 - 3 * p.1 3 - 2 * p.1 4 - p.1 5

/-- `example_7_17_lifted_flow_cover_value α₁ β₁ α₂ β₂ p` expands to the explicit left-hand side
of the lifted flow cover inequality from Example 7.17. -/
theorem example_7_17_lifted_flow_cover_value_eq
    (α₁ β₁ α₂ β₂ : ℝ)
    (p : (Fin 6 → ℝ) × (Fin 6 → ℝ)) :
    example_7_17_lifted_flow_cover_value α₁ β₁ α₂ β₂ p =
      α₁ * p.2 0 + β₁ * p.1 0 + α₂ * p.2 1 + β₂ * p.1 1 +
        p.2 2 + p.2 3 + p.2 4 + p.2 5 - 5 * p.1 2 - 3 * p.1 3 - 2 * p.1 4 - p.1 5 :=
  rfl

/-- The canonical lifted flow-cover owner from Theorem 7.16 differs from the source-facing
left-hand side in Example 7.17 by the constant shift `20 - 9 = 11`. -/
theorem flow_cover_lifted_value_eq_example_7_17_lifted_flow_cover_value_add
    (α₁ β₁ α₂ β₂ : ℝ)
    (p : (Fin 6 → ℝ) × (Fin 6 → ℝ)) :
    flow_cover_lifted_value
        example_7_17_capacity
        example_7_17_rhs
        example_7_17_cover
        (example_7_17_alpha_coeffs α₁ α₂)
        (example_7_17_beta_coeffs β₁ β₂)
        p =
      example_7_17_lifted_flow_cover_value α₁ β₁ α₂ β₂ p +
        (example_7_17_rhs - example_7_17_inequality_rhs) := by
  sorry

/-- The equality face cut out on `conv(T)` by the lifted flow cover inequality from Example 7.17.
-/
def example_7_17_lifted_flow_cover_face
    (α₁ β₁ α₂ β₂ : ℝ) : Set ((Fin 6 → ℝ) × (Fin 6 → ℝ)) :=
  {p |
    p ∈ convexHull ℝ example_7_17_flow_set ∧
      example_7_17_lifted_flow_cover_value α₁ β₁ α₂ β₂ p = example_7_17_inequality_rhs}

/-- Membership in `example_7_17_lifted_flow_cover_face α₁ β₁ α₂ β₂` means lying in `conv(T)` and
meeting the lifted flow cover inequality at equality. -/
theorem mem_example_7_17_lifted_flow_cover_face_iff
    {α₁ β₁ α₂ β₂ : ℝ}
    {p : (Fin 6 → ℝ) × (Fin 6 → ℝ)} :
    p ∈ example_7_17_lifted_flow_cover_face α₁ β₁ α₂ β₂ ↔
      p ∈ convexHull ℝ example_7_17_flow_set ∧
        example_7_17_lifted_flow_cover_value α₁ β₁ α₂ β₂ p = 9 := Iff.rfl

/-- The source-facing equality face from Example 7.17 coincides with the canonical face from
Theorem 7.16 after shifting the constant term to the right-hand side. -/
theorem example_7_17_lifted_flow_cover_face_iff_flow_cover_lifted_face
    (α₁ β₁ α₂ β₂ : ℝ)
    {p : (Fin 6 → ℝ) × (Fin 6 → ℝ)} :
    p ∈ example_7_17_lifted_flow_cover_face α₁ β₁ α₂ β₂ ↔
      p ∈ flow_cover_lifted_face
        example_7_17_capacity
        example_7_17_rhs
        example_7_17_cover
        (example_7_17_alpha_coeffs α₁ α₂)
        (example_7_17_beta_coeffs β₁ β₂)
        example_7_17_rhs := by
  sorry

/-- The lifted flow cover inequality from Example 7.17 is facet-defining for `conv(T)` when it is
valid on `conv(T)` and the equality face it cuts out is a facet of `conv(T)`. -/
def example_7_17_lifted_flow_cover_facet_defining
    (α₁ β₁ α₂ β₂ : ℝ) : Prop :=
  (∀ ⦃p : (Fin 6 → ℝ) × (Fin 6 → ℝ)⦄,
      p ∈ convexHull ℝ example_7_17_flow_set →
        example_7_17_lifted_flow_cover_value α₁ β₁ α₂ β₂ p ≤ example_7_17_inequality_rhs) ∧
    IsFacetOf
      (convexHull ℝ example_7_17_flow_set)
      (example_7_17_lifted_flow_cover_face α₁ β₁ α₂ β₂)

/-- `example_7_17_lifted_flow_cover_facet_defining α₁ β₁ α₂ β₂` unfolds to validity of the
lifted flow cover inequality on `conv(T)` together with facetness of its equality face. -/
theorem example_7_17_lifted_flow_cover_facet_defining_iff
    {α₁ β₁ α₂ β₂ : ℝ} :
    example_7_17_lifted_flow_cover_facet_defining α₁ β₁ α₂ β₂ ↔
      (∀ ⦃p : (Fin 6 → ℝ) × (Fin 6 → ℝ)⦄,
          p ∈ convexHull ℝ example_7_17_flow_set →
            example_7_17_lifted_flow_cover_value α₁ β₁ α₂ β₂ p ≤ 9) ∧
        IsFacetOf
          (convexHull ℝ example_7_17_flow_set)
          (example_7_17_lifted_flow_cover_face α₁ β₁ α₂ β₂) := Iff.rfl

/-- The source-facing facet-defining predicate in Example 7.17 is equivalent to the canonical
Theorem 7.16 facet-defining owner after moving the constant `11` to the right-hand side. -/
theorem
    example_7_17_lifted_flow_cover_facet_defining_iff_flow_cover_lifted_inequality_facet_defining
    (α₁ β₁ α₂ β₂ : ℝ) :
    example_7_17_lifted_flow_cover_facet_defining α₁ β₁ α₂ β₂ ↔
      flow_cover_lifted_inequality_facet_defining
        example_7_17_capacity
        example_7_17_rhs
        example_7_17_cover
        (example_7_17_alpha_coeffs α₁ α₂)
        (example_7_17_beta_coeffs β₁ β₂)
        example_7_17_rhs := by
  sorry

/-- Example 7.17 restated through Theorem 7.16: the source lifting-pair lists are equivalent to
the canonical admissible-pair condition on the two coordinates outside the cover. -/
theorem example_7_17_all_outside_pairs_admissible_iff
    (α₁ β₁ α₂ β₂ : ℝ) :
    ((α₁, β₁) ∈ example_7_17_first_lifting_pairs ∧
        (α₂, β₂) ∈ example_7_17_second_lifting_pairs) ↔
      ∀ i, i ∉ example_7_17_cover →
        admissiblePair
          example_7_17_capacity
          example_7_17_rhs
          example_7_17_cover
          example_7_17_cover_order
          example_7_17_cutIndex
          i
          (example_7_17_alpha_coeffs α₁ α₂ i)
          (example_7_17_beta_coeffs β₁ β₂ i) := by
  sorry

/-- Example 7.17. For the single-node flow set
`T = {(x,y) ∈ {0,1}^6 × ℝ^6_+ | y₁ + ⋯ + y₆ ≤ 20, y₁ ≤ 17 x₁, y₂ ≤ 9 x₂, y₃ ≤ 8 x₃,
y₄ ≤ 6 x₄, y₅ ≤ 5 x₅, y₆ ≤ 4 x₆}` and the flow cover `C = {3,4,5,6}`, the lifted flow cover
inequality
`α₁ y₁ + β₁ x₁ + α₂ y₂ + β₂ x₂ + y₃ + y₄ + y₅ + y₆ - 5 x₃ - 3 x₄ - 2 x₅ - x₆ ≤ 9`
is facet-defining for `conv(T)` if and only if `(α₁, β₁)` and `(α₂, β₂)` belong to the listed
sets of admissible lifting pairs. -/
theorem example_7_17_lifted_flow_cover_inequality_facet_defining_iff
    (α₁ β₁ α₂ β₂ : ℝ) :
    example_7_17_lifted_flow_cover_facet_defining α₁ β₁ α₂ β₂ ↔
      (α₁, β₁) ∈ example_7_17_first_lifting_pairs ∧
        (α₂, β₂) ∈ example_7_17_second_lifting_pairs := sorry

end Example717
