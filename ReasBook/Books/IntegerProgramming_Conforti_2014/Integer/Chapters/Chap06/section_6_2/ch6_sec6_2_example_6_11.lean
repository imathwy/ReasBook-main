import Integer.Chapters.Chap05.section_5_1_3.ch5_sec5_1_3_example_5_11
import Integer.Chapters.Chap05.section_5_1_3.ch5_sec5_1_3_definition_5_1_3_extra_1
import Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_theorem_6_18

open scoped Matrix

-- This example reuses the Chapter 5 Example 5.11 owners
-- `example_5_11_polyhedron` and `example_5_11_mixed_integer_set`, together with the Chapter 5
-- split-rank owner `is_split_rank_of_inequality` and the Chapter 6 owner `is_lattice_free`.

section Example611

local notation "R2" => Fin 2 → ℝ
local notation "R3" => Fin 3 → ℝ

/-- The triangle `K = conv{(0, 0), (2, 0), (0, 2)}` from Example 6.11. -/
def example_6_11_triangle : Set R2 :=
  convexHull ℝ
    (Set.range fun i : Fin 3 ↦
      match i.1 with
      | 0 => ![(0 : ℝ), 0]
      | 1 => ![2, 0]
      | _ => ![0, 2])

/-- `example_6_11_triangle` is exactly the convex hull of the three vertices
`(0, 0)`, `(2, 0)`, and `(0, 2)`. -/
theorem example_6_11_triangle_eq :
    example_6_11_triangle =
      convexHull ℝ
        (Set.range fun i : Fin 3 ↦
          match i.1 with
          | 0 => ![(0 : ℝ), 0]
          | 1 => ![2, 0]
          | _ => ![0, 2]) :=
  rfl

/-- The computed intersection cut in the slack variables `s₁`, `s₂`, `s₃` from Example 6.11. -/
def example_6_11_intersection_cut : Set R3 :=
  {s : R3 | 1 ≤ (1 / 2 : ℝ) * s 0 + (1 / 2 : ℝ) * s 1 + (1 / 2 : ℝ) * s 2}

/-- Membership in `example_6_11_intersection_cut` is exactly the inequality
`(1/2) s₁ + (1/2) s₂ + (1/2) s₃ ≥ 1`. -/
theorem mem_example_6_11_intersection_cut_iff
    {s : R3} :
    s ∈ example_6_11_intersection_cut ↔
      1 ≤ (1 / 2 : ℝ) * s 0 + (1 / 2 : ℝ) * s 1 + (1 / 2 : ℝ) * s 2 :=
  Iff.rfl

/-- The tableau expression for the continuous basic variable `y` in Example 6.11. -/
noncomputable def example_6_11_tableau_y (s : R3) : ℝ :=
  (1 / 2 : ℝ) - (1 / 4 : ℝ) * s 0 - (1 / 4 : ℝ) * s 1 - (1 / 4 : ℝ) * s 2

/-- `example_6_11_tableau_y` is the affine form
`1/2 - (1/4) s₁ - (1/4) s₂ - (1/4) s₃`. -/
theorem example_6_11_tableau_y_eq
    (s : R3) :
    example_6_11_tableau_y s =
      (1 / 2 : ℝ) - (1 / 4 : ℝ) * s 0 - (1 / 4 : ℝ) * s 1 - (1 / 4 : ℝ) * s 2 :=
  rfl

/-- Example 6.11 (1). The triangle `K = conv{(0, 0), (2, 0), (0, 2)}` used to define the
intersection cut is lattice-free. -/
theorem example_6_11_triangle_is_lattice_free :
    is_lattice_free example_6_11_triangle := sorry

/-- Example 6.11 (2). The intersection cut
`(1/2) s₁ + (1/2) s₂ + (1/2) s₃ ≥ 1` is equivalent, via
`y = 1/2 - (1/4) s₁ - (1/4) s₂ - (1/4) s₃`, to the inequality `y ≤ 0`. -/
theorem example_6_11_intersection_cut_iff_tableau_y_nonpositive
    (s : R3) :
    s ∈ example_6_11_intersection_cut ↔ example_6_11_tableau_y s ≤ 0 := by
  rw [mem_example_6_11_intersection_cut_iff, example_6_11_tableau_y_eq]
  constructor <;> intro h <;> linarith

/-- Example 6.11 (3). For the mixed-integer set of Example 5.11, the inequality `y ≤ 0`
obtained from the intersection cut does not have a finite split rank. -/
theorem example_6_11_y_inequality_has_no_finite_split_rank
    (k : ℕ) :
    ¬ is_split_rank_of_inequality
        split_closure
        example_5_11_polyhedron
        example_5_11_mixed_integer_set
        ![(0 : ℝ), 0, 1]
        0
        k := sorry

end Example611
