import Integer.Chapters.Chap06.section_6_3_2.ch6_sec6_3_2_theorem_6_30
import Integer.Chapters.Chap06.section_6_3_4.ch6_sec6_3_4_remark_6_36

open scoped Matrix Pointwise

noncomputable section

section Example639

local notation "R2" => Fin 2 → ℝ
local notation "Z2" => Fin 2 → ℤ

/-- The triangle `B = conv((0,0), (2,0), (0,2))` from Example 6.39. -/
def example_6_39_triangle : Set R2 :=
  convexHull ℝ
    (Set.range fun i : Fin 3 ↦
      match i.1 with
      | 0 => ![(0 : ℝ), 0]
      | 1 => ![2, 0]
      | _ => ![0, 2])

/-- `example_6_39_triangle` is exactly the triangle
`{x | 0 ≤ x₁, 0 ≤ x₂, x₁ + x₂ ≤ 2}`. -/
theorem example_6_39_triangle_eq :
    example_6_39_triangle =
      {x : R2 | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ (2 : ℝ)} := sorry

/-- The three boundary lattice points `(1,0)`, `(0,1)`, and `(1,1)` used in Example 6.39. -/
def example_6_39_boundary_point : Fin 3 → R2 :=
  fun i ↦
    match i.1 with
    | 0 => ![(1 : ℝ), 0]
    | 1 => ![0, (1 : ℝ)]
    | _ => ![(1 : ℝ), 1]

/-- Expanding `example_6_39_boundary_point` recovers the three displayed boundary lattice
points. -/
theorem example_6_39_boundary_point_apply
    (i : Fin 3) :
    example_6_39_boundary_point i =
      match i.1 with
      | 0 => ![(1 : ℝ), 0]
      | 1 => ![0, (1 : ℝ)]
      | _ => ![(1 : ℝ), 1] :=
  rfl

/-- The translate `B - f`, written as `{r | r + f ∈ B}`. -/
def example_6_39_shifted_triangle (f : R2) : Set R2 :=
  {r : R2 | r + f ∈ example_6_39_triangle}

/-- The source-facing translate `B - f` agrees with the canonical pointwise translate `(-f) +ᵥ B`.
-/
theorem example_6_39_shifted_triangle_eq_neg_vadd
    (f : R2) :
    example_6_39_shifted_triangle f = (-f) +ᵥ example_6_39_triangle := by
  rw [neg_vadd_set_eq_setOf_add_mem]
  ext r
  simp [example_6_39_shifted_triangle, add_comm]

/-- `example_6_39_shifted_triangle f` is the translate of the triangle by `-f`, written by its
three facet inequalities. -/
theorem example_6_39_shifted_triangle_eq
    (f : R2) :
    example_6_39_shifted_triangle f =
      {r : R2 |
        -(f 0) ≤ r 0 ∧
          -(f 1) ≤ r 1 ∧
            r 0 + r 1 ≤ (2 : ℝ) - (f 0 + f 1)} := sorry

/-- The function `ψ` of Example 6.39, defined as the gauge of `B - f`. -/
def example_6_39_psi (f : R2) : R2 → ℝ :=
  gauge (example_6_39_shifted_triangle f)

/-- Unfolding `example_6_39_psi f` recovers the gauge of the translated triangle `B - f`. -/
theorem example_6_39_psi_def
    (f : R2) :
    example_6_39_psi f = gauge (example_6_39_shifted_triangle f) :=
  rfl

/-- The region `R(z_i)` from Example 6.39 attached to the `i`-th boundary lattice point. -/
def example_6_39_lifting_region_at
    (f : R2) (i : Fin 3) : Set R2 :=
  {r : R2 |
    example_6_39_psi f r +
        example_6_39_psi f (example_6_39_boundary_point i - f - r) =
      1}

/-- Membership in `example_6_39_lifting_region_at f i` is exactly the displayed spindle equality
for the boundary point `z_i`. -/
theorem example_6_39_mem_lifting_region_at_iff
    {f r : R2} {i : Fin 3} :
    r ∈ example_6_39_lifting_region_at f i ↔
      example_6_39_psi f r +
          example_6_39_psi f (example_6_39_boundary_point i - f - r) =
        1 :=
  Iff.rfl

/-- The union `R = R(z₁) ∪ R(z₂) ∪ R(z₃)` from Example 6.39. -/
def example_6_39_lifting_region
    (f : R2) : Set R2 :=
  {r : R2 | ∃ i : Fin 3, r ∈ example_6_39_lifting_region_at f i}

/-- Membership in `example_6_39_lifting_region f` means membership in one of the three spindle
regions attached to the boundary lattice points. -/
theorem example_6_39_mem_lifting_region_iff
    {f r : R2} :
    r ∈ example_6_39_lifting_region f ↔
      ∃ i : Fin 3, r ∈ example_6_39_lifting_region_at f i :=
  Iff.rfl

/-- The fixed triangle of Example 6.39 is maximal lattice-free. -/
theorem example_6_39_triangle_is_maximal_lattice_free :
    is_maximal_lattice_free example_6_39_triangle := sorry

/-- Example 6.39 (1). If `f` lies in the interior of the maximal lattice-free triangle `B`, then
the gauge `ψ` of `B - f` is a minimal valid function for `R_f`. -/
theorem example_6_39_psi_is_minimal_valid_function
    {f : R2}
    (hf : f ∈ interior example_6_39_triangle) :
    IsMinimalValidFunctionForContinuousInfiniteRelaxation f (example_6_39_psi f) := sorry

/-- Under the interior-point hypothesis of Example 6.39, `example_6_39_psi f` is available
through the chapter's canonical minimal-valid-function instance. -/
instance instExample639PsiMinimalValidFunction
    {f : R2} [Fact (f ∈ interior example_6_39_triangle)] :
    IsMinimalValidFunctionForContinuousInfiniteRelaxation f (example_6_39_psi f) :=
  example_6_39_psi_is_minimal_valid_function ‹Fact (f ∈ interior example_6_39_triangle)›.out

/-- Example 6.39 (2). For each of the three boundary lattice points `z_i`, the gauge of `B - f`
evaluated at `z_i - f` is equal to `1`. -/
theorem example_6_39_boundary_points_gauge_eq_one
    {f : R2}
    (hf : f ∈ interior example_6_39_triangle)
    (i : Fin 3) :
    example_6_39_psi f (example_6_39_boundary_point i - f) = 1 := sorry

/-- Example 6.39 (3). The integer translates of the lifting region
`R = R(z₁) ∪ R(z₂) ∪ R(z₃)` cover the whole plane. -/
theorem example_6_39_lifting_region_covers_plane
    {f : R2}
    (hf : f ∈ interior example_6_39_triangle)
    (r : R2) :
    ∃ w : Z2, (fun i : Fin 2 ↦ r i + (w i : ℝ)) ∈ example_6_39_lifting_region f :=
  sorry

/-- Example 6.39 (4). Because the lifting region covers `ℝ²` modulo integer translations, the
trivial lifting of `ψ` is a minimal lifting of `ψ`. -/
theorem example_6_39_trivial_lifting_is_minimal_lifting
    {f : R2}
    (hf : f ∈ interior example_6_39_triangle) :
    IsMinimalLiftingOf f (trivial_lifting (example_6_39_psi f)) (example_6_39_psi f) := sorry

/-- Under the interior-point hypothesis of Example 6.39, the trivial lifting is available
through the canonical minimal-lifting instance. -/
instance instExample639TrivialLiftingMinimalLifting
    {f : R2} [Fact (f ∈ interior example_6_39_triangle)] :
    IsMinimalLiftingOf f (trivial_lifting (example_6_39_psi f)) (example_6_39_psi f) :=
  example_6_39_trivial_lifting_is_minimal_lifting
    ‹Fact (f ∈ interior example_6_39_triangle)›.out

/-- Example 6.39 (5). Under the same hypotheses, every minimal lifting of `ψ` coincides with the
trivial lifting; equivalently, the trivial lifting is the unique minimal lifting of `ψ`. -/
theorem example_6_39_eq_trivial_lifting_of_minimal_lifting
    {f : R2}
    (hf : f ∈ interior example_6_39_triangle)
    {π : R2 → ℝ}
    (hπ : IsMinimalLiftingOf f π (example_6_39_psi f)) :
    π = trivial_lifting (example_6_39_psi f) := sorry

/-- Example 6.39 (6). For every `r ∈ ℝ²`, there is an integer vector `w̄` such that `r + w̄`
lies in the lifting region and realizes the trivial lifting value
`inf_{w ∈ ℤ²} ψ(r + w) = ψ(r + w̄)`. -/
theorem example_6_39_exists_translate_attaining_trivial_lifting
    {f : R2}
    (hf : f ∈ interior example_6_39_triangle)
    (r : R2) :
    ∃ wbar : Z2,
      (fun i : Fin 2 ↦ r i + (wbar i : ℝ)) ∈ example_6_39_lifting_region f ∧
        trivial_lifting (example_6_39_psi f) r =
          example_6_39_psi f (fun i : Fin 2 ↦ r i + (wbar i : ℝ)) := sorry

end Example639
