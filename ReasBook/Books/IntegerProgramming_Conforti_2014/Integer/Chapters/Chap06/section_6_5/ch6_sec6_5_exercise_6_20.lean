import Integer.Chapters.Chap06.section_6_2.ch6_sec6_2_example_6_9
import Integer.Chapters.Chap06.section_6_3_4.ch6_sec6_3_4_remark_6_36

-- This exercise reuses the Section 6.2 lattice-free owner `is_maximal_lattice_free` together
-- with the Chapter 6 mixed-integer lifting owners from Remark 6.36.

section Exercise620

local notation "R2" => Fin 2 → ℝ
local notation "Z2" => Fin 2 → ℤ

/-- The triangle `K` of Exercise 6.20 with vertices `(-1 / 2, 0)`, `(3 / 2, 0)`, and
`(1 / 2, 2)`. -/
def exercise_6_20_triangle : Set R2 :=
  convexHull ℝ
    (Set.range fun i : Fin 3 ↦
      match i.1 with
      | 0 => ![(-((1 / 2 : ℝ))), (0 : ℝ)]
      | 1 => ![(3 / 2 : ℝ), (0 : ℝ)]
      | _ => ![(1 / 2 : ℝ), (2 : ℝ)])

/-- The point `f = (1 / 2, 1 / 2)` from Exercise 6.20, written in `ℝ²`. -/
noncomputable def exercise_6_20_f : R2 :=
  ![(1 / 2 : ℝ), (1 / 2 : ℝ)]

/-- The translated set `K - f` from Exercise 6.20, written as `{r | r + f ∈ K}`. -/
def exercise_6_20_shifted_triangle : Set R2 :=
  {r : R2 | r + exercise_6_20_f ∈ exercise_6_20_triangle}

/-- `exercise_6_20_shifted_triangle` is exactly the translate `K - f`, written by its three
facet inequalities. -/
theorem exercise_6_20_shifted_triangle_eq :
    exercise_6_20_shifted_triangle =
      {r : R2 |
        (-2 : ℝ) * r 1 ≤ 1 ∧
          (-((4 / 3 : ℝ))) * r 0 + (2 / 3 : ℝ) * r 1 ≤ 1 ∧
            (4 / 3 : ℝ) * r 0 + (2 / 3 : ℝ) * r 1 ≤ 1} := sorry

/-- The function `ψ_K` from Exercise 6.20, defined as the gauge of `K - f`. -/
noncomputable def exercise_6_20_psi : R2 → ℝ :=
  gauge exercise_6_20_shifted_triangle

/-- Exercise 6.20 (2). For the translated triangle `K - f`, the function `ψ_K` is the gauge
`max {-2 r₂, -(4 / 3) r₁ + (2 / 3) r₂, (4 / 3) r₁ + (2 / 3) r₂}`. -/
theorem exercise_6_20_psi_apply
    (r : R2) :
    exercise_6_20_psi r =
      max
        (max ((-2 : ℝ) * r 1) ((-((4 / 3 : ℝ))) * r 0 + (2 / 3 : ℝ) * r 1))
        ((4 / 3 : ℝ) * r 0 + (2 / 3 : ℝ) * r 1) := sorry

/-- The four boundary lattice points of `K`, listed as `(0, 0)`, `(1, 0)`, `(0, 1)`, and
`(1, 1)`. -/
def exercise_6_20_boundary_point : Fin 4 → R2 :=
  fun i ↦
    match i.1 with
    | 0 => ![(0 : ℝ), 0]
    | 1 => ![1, 0]
    | 2 => ![0, 1]
    | _ => ![1, 1]

/-- Expanding `exercise_6_20_boundary_point` recovers the four displayed boundary lattice
points. -/
theorem exercise_6_20_boundary_point_apply
    (i : Fin 4) :
    exercise_6_20_boundary_point i =
      match i.1 with
      | 0 => ![(0 : ℝ), 0]
      | 1 => ![1, 0]
      | 2 => ![0, 1]
      | _ => ![1, 1] :=
  rfl

/-- The spindle in the lifting region attached to the `i`-th boundary lattice point of
`exercise_6_20_boundary_point`, written in the canonical Chapter 6 spindle form. -/
def exercise_6_20_lifting_region_at
    (i : Fin 4) : Set R2 :=
  {r : R2 |
    exercise_6_20_psi r +
        exercise_6_20_psi (exercise_6_20_boundary_point i - exercise_6_20_f - r) =
      1}

/-- Membership in `exercise_6_20_lifting_region_at i` is exactly the standard spindle equality
for the boundary lattice point `exercise_6_20_boundary_point i`. -/
theorem exercise_6_20_mem_lifting_region_at_iff
    {i : Fin 4} {r : R2} :
    r ∈ exercise_6_20_lifting_region_at i ↔
      exercise_6_20_psi r +
          exercise_6_20_psi (exercise_6_20_boundary_point i - exercise_6_20_f - r) =
        1 :=
  Iff.rfl

/-- Unfolding `exercise_6_20_lifting_region_at i` recovers the displayed spindle inequalities for
the `i`-th boundary lattice point. -/
theorem exercise_6_20_lifting_region_at_apply
    (i : Fin 4) :
    exercise_6_20_lifting_region_at i =
      match i.1 with
      | 0 =>
          {r : R2 |
            0 ≤ r 0 - (2 : ℝ) * r 1 ∧
              r 0 - (2 : ℝ) * r 1 ≤ (1 / 2 : ℝ) ∧
                (-(1 / 2 : ℝ)) ≤ r 0 + (2 : ℝ) * r 1 ∧
                  r 0 + (2 : ℝ) * r 1 ≤ 0}
      | 1 =>
          {r : R2 |
            0 ≤ r 0 - (2 : ℝ) * r 1 ∧
              r 0 - (2 : ℝ) * r 1 ≤ (3 / 2 : ℝ) ∧
                (-(1 / 2 : ℝ)) ≤ r 0 + (2 : ℝ) * r 1 ∧
                  r 0 + (2 : ℝ) * r 1 ≤ 0}
      | 2 =>
          {r : R2 |
            (-(3 / 2 : ℝ)) ≤ r 0 - (2 : ℝ) * r 1 ∧
              r 0 - (2 : ℝ) * r 1 ≤ 0 ∧
                (-(1 / 2 : ℝ)) ≤ r 0 ∧
                  r 0 ≤ 0}
      | _ =>
          {r : R2 |
            0 ≤ r 0 ∧
              r 0 ≤ (1 / 2 : ℝ) ∧
                0 ≤ r 0 + (2 : ℝ) * r 1 ∧
                  r 0 + (2 : ℝ) * r 1 ≤ (3 / 2 : ℝ)} := sorry

/-- The region on which every minimal lifting of `ψ_K` agrees with `ψ_K`. -/
def exercise_6_20_lifting_region : Set R2 :=
  {r : R2 | ∃ i : Fin 4, r ∈ exercise_6_20_lifting_region_at i}

/-- Membership in `exercise_6_20_lifting_region` means membership in one of the four spindles
attached to the boundary lattice points of `K`. -/
theorem exercise_6_20_mem_lifting_region_iff
    {r : R2} :
    r ∈ exercise_6_20_lifting_region ↔
      ∃ i : Fin 4, r ∈ exercise_6_20_lifting_region_at i :=
  Iff.rfl

/-- Exercise 6.20 (1). The triangle with vertices `(-1 / 2, 0)`, `(3 / 2, 0)`, and `(1 / 2, 2)`
is a maximal lattice-free convex set. -/
theorem exercise_6_20_triangle_is_maximal_lattice_free :
    is_maximal_lattice_free exercise_6_20_triangle := sorry

/-- Exercise 6.20 (3). If `π_K` is any minimal lifting of `ψ_K`, then the region
`{r ∈ ℝ² | π_K(r) = ψ_K(r)}` is the union of the four spindles attached to the boundary lattice
points `(0, 0)`, `(1, 0)`, `(0, 1)`, and `(1, 1)` of `K`. -/
theorem exercise_6_20_eq_set_of_minimal_lifting_eq_psi
    (π : R2 → ℝ)
    (hπ : IsMinimalLiftingOf exercise_6_20_f π exercise_6_20_psi) :
    {r : R2 | π r = exercise_6_20_psi r} = exercise_6_20_lifting_region := sorry

/-- Integer translates of the lifting region of Exercise 6.20 cover the whole plane. -/
theorem exercise_6_20_lifting_region_covers_plane
    (r : R2) :
    ∃ w : Z2, (fun i : Fin 2 ↦ r i + (w i : ℝ)) ∈ exercise_6_20_lifting_region := sorry

/-- Because the lifting region covers `ℝ²` modulo integer translations, the trivial lifting of
`ψ_K` is a minimal lifting of `ψ_K`. -/
instance exercise_6_20_trivial_lifting_is_minimal_lifting :
    IsMinimalLiftingOf exercise_6_20_f (trivial_lifting exercise_6_20_psi) exercise_6_20_psi :=
  sorry

/-- Every minimal lifting of `ψ_K` coincides with the trivial lifting of `ψ_K`; equivalently, the
trivial lifting is the unique minimal lifting. -/
theorem exercise_6_20_eq_trivial_lifting_of_minimal_lifting
    {π : R2 → ℝ}
    (hπ : IsMinimalLiftingOf exercise_6_20_f π exercise_6_20_psi) :
    π = trivial_lifting exercise_6_20_psi := sorry

/-- Exercise 6.20 (4). The function `ψ_K` has a unique minimal lifting. -/
theorem exercise_6_20_existsUnique_minimal_lifting :
    ∃! π : R2 → ℝ, IsMinimalLiftingOf exercise_6_20_f π exercise_6_20_psi := sorry

end Exercise620
