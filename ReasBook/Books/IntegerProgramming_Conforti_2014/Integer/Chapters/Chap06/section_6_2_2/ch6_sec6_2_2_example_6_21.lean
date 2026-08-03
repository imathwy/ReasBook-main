import Mathlib.Analysis.Convex.Gauge
import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
import Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_theorem_6_18

open scoped Matrix Pointwise

-- This example reuses the Chapter 6 lattice-free owner `is_lattice_free` from Theorem 6.18 and
-- keeps mathlib's canonical gauge owner `gauge` as the public surface.

section Example621

local notation "R2" => Fin 2 → ℝ

/-- The triangle `B` from Example 6.21, with vertices `(0, 0)`, `(2, 0)`, and `(0, 2)`. -/
def example_6_21_triangle : Set R2 :=
  convexHull ℝ
    (Set.range fun i : Fin 3 ↦
      match i.1 with
      | 0 => ![(0 : ℝ), 0]
      | 1 => ![2, 0]
      | _ => ![0, 2])

/-- Helper for Example 6.21: the triangle `B` is the standard right triangle
`{x | 0 ≤ x₁, 0 ≤ x₂, x₁ + x₂ ≤ 2}`. -/
lemma example_6_21_triangle_eq_standard :
    example_6_21_triangle =
      {x : R2 | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ (2 : ℝ)} := by
  sorry

/-- `example_6_21_triangle` is exactly the set
`{x | -2 * (x 0 - 1/2) ≤ 1, -2 * (x 1 - 1/2) ≤ 1, (x 0 - 1/2) + (x 1 - 1/2) ≤ 1}`. -/
theorem example_6_21_triangle_eq :
    example_6_21_triangle =
      {x : R2 |
        (-2 : ℝ) * (x 0 - (1 / 2 : ℝ)) ≤ 1 ∧
        (-2 : ℝ) * (x 1 - (1 / 2 : ℝ)) ≤ 1 ∧
        (x 0 - (1 / 2 : ℝ)) + (x 1 - (1 / 2 : ℝ)) ≤ 1} := by
  -- Rewrite the triangle into its standard nonnegative-coordinate description first.
  rw [example_6_21_triangle_eq_standard]
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hx0, hx1, hxsum⟩
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  · intro hx
    rcases hx with ⟨hx0, hx1, hxsum⟩
    refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- The point `bbar = (1/2, 1/2)` from Example 6.21. -/
noncomputable def example_6_21_bbar : R2 :=
  ![(1 / 2 : ℝ), (1 / 2 : ℝ)]

/-- `example_6_21_bbar` is the point `(1/2, 1/2)` in `ℝ²`. -/
theorem example_6_21_bbar_eq :
    example_6_21_bbar = ![(1 / 2 : ℝ), (1 / 2 : ℝ)] :=
  rfl

/-- The translated set `K = B - bbar` used to define the gauge in Example 6.21. -/
def example_6_21_shifted_triangle : Set R2 :=
  {rho : R2 | rho + example_6_21_bbar ∈ example_6_21_triangle}

/-- `example_6_21_shifted_triangle` is exactly the translated inequality set
`{rho | -2 rho₁ ≤ 1, -2 rho₂ ≤ 1, rho₁ + rho₂ ≤ 1}`. -/
theorem example_6_21_shifted_triangle_eq :
    example_6_21_shifted_triangle =
      {rho : R2 |
        (-2 : ℝ) * rho 0 ≤ 1 ∧
        (-2 : ℝ) * rho 1 ≤ 1 ∧
        rho 0 + rho 1 ≤ 1} := by
  sorry

/-- Helper for Example 6.21: a point lies in the interior of `B` exactly when the three standard
triangle inequalities are strict. -/
lemma example_6_21_mem_interior_triangle_iff
    (x : R2) :
    x ∈ interior example_6_21_triangle ↔
      0 < x 0 ∧ 0 < x 1 ∧ x 0 + x 1 < (2 : ℝ) := by
  sorry

/-- Example 6.21 (1). The triangle `B` from the example is lattice-free. -/
theorem example_6_21_triangle_is_lattice_free :
    is_lattice_free example_6_21_triangle := by
  sorry

/-- Example 6.21 (2). The point `bbar = (1/2, 1/2)` lies in the interior of `B`. -/
theorem example_6_21_bbar_mem_interior_triangle :
    example_6_21_bbar ∈ interior example_6_21_triangle := by
  -- All three strict triangle inequalities hold at the midpoint `(1/2, 1/2)`.
  rw [example_6_21_bbar_eq]
  have hstrict :
      0 < (![(1 / 2 : ℝ), (1 / 2 : ℝ)] : R2) 0 ∧
        0 < (![(1 / 2 : ℝ), (1 / 2 : ℝ)] : R2) 1 ∧
        (![(1 / 2 : ℝ), (1 / 2 : ℝ)] : R2) 0 + (![(1 / 2 : ℝ), (1 / 2 : ℝ)] : R2) 1 <
          (2 : ℝ) := by
    norm_num
  exact (example_6_21_mem_interior_triangle_iff ![(1 / 2 : ℝ), (1 / 2 : ℝ)]).2 hstrict

/-- Helper for Example 6.21: the gauge candidate is the maximum of the three facet functionals. -/
def example_6_21_psi (rho : R2) : ℝ :=
  max (max ((-2 : ℝ) * rho 0) ((-2 : ℝ) * rho 1)) (rho 0 + rho 1)

/-- Helper for Example 6.21: the gauge candidate is always nonnegative. -/
lemma example_6_21_psi_nonnegative
    (rho : R2) :
    0 ≤ example_6_21_psi rho := by
  -- If all three branches were negative, the first two would force positive coordinates, which
  -- contradicts negativity of their sum.
  by_contra hneg
  have hmax : example_6_21_psi rho < 0 := lt_of_not_ge hneg
  have h0 : (-2 : ℝ) * rho 0 < 0 := by
    exact lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hmax
  have h1 : (-2 : ℝ) * rho 1 < 0 := by
    exact lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hmax
  have hsum : rho 0 + rho 1 < 0 := by
    exact lt_of_le_of_lt (le_max_right _ _) hmax
  linarith

/-- Helper for Example 6.21: multiplying a maximum by a nonnegative scalar may be pulled out. -/
lemma example_6_21_mul_max_of_nonneg
    {a b c : ℝ}
    (hc : 0 ≤ c) :
    max (c * a) (c * b) = c * max a b := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab, max_eq_right]
    exact mul_le_mul_of_nonneg_left hab hc
  · rw [max_eq_left hba, max_eq_left]
    exact mul_le_mul_of_nonneg_left hba hc

/-- Helper for Example 6.21: the facet-max function `ψ` is subadditive. -/
lemma example_6_21_psi_add_le
    (rho sigma : R2) :
    example_6_21_psi (rho + sigma) ≤ example_6_21_psi rho + example_6_21_psi sigma := by
  sorry

/-- Helper for Example 6.21: the facet-max function `ψ` is positively homogeneous for
nonnegative scalars. -/
lemma example_6_21_psi_smul_nonneg
    (rho : R2)
    {c : ℝ}
    (hc : 0 ≤ c) :
    example_6_21_psi (c • rho) = c * example_6_21_psi rho := by
  sorry

/-- Helper for Example 6.21: the translated triangle `K = B - bbar` is the unit sublevel set of
the facet-max function `ψ`. -/
lemma example_6_21_shifted_triangle_eq_unit_sublevel_set :
    example_6_21_shifted_triangle = {rho : R2 | example_6_21_psi rho ≤ 1} := by
  sorry

/-- Helper for Example 6.21: positive dilates of `K = B - bbar` scale the right-hand sides of its
three facet inequalities. -/
lemma example_6_21_mem_smul_shifted_triangle_iff
    {a : ℝ}
    (ha : 0 < a)
    (rho : R2) :
    rho ∈ a • example_6_21_shifted_triangle ↔
      (-2 : ℝ) * rho 0 ≤ a ∧
      (-2 : ℝ) * rho 1 ≤ a ∧
      rho 0 + rho 1 ≤ a := by
  sorry

/-- Helper for Example 6.21: the origin lies in the interior of `K = B - bbar`. -/
lemma example_6_21_zero_mem_interior_shifted_triangle :
    (0 : R2) ∈ interior example_6_21_shifted_triangle := by
  refine mem_interior_iff_mem_nhds.2 ?_
  apply Metric.mem_nhds_iff.2
  refine ⟨(1 / 4 : ℝ), by norm_num, ?_⟩
  intro rho hrho
  rw [Metric.mem_ball, dist_pi_lt_iff] at hrho
  · rw [example_6_21_shifted_triangle_eq]
    refine ⟨?_, ?_, ?_⟩
    · have h0 : |rho 0| < (1 / 4 : ℝ) := by simpa using hrho 0
      linarith [abs_lt.1 h0 |>.1]
    · have h1 : |rho 1| < (1 / 4 : ℝ) := by simpa using hrho 1
      linarith [abs_lt.1 h1 |>.1]
    · have h0 : |rho 0| < (1 / 4 : ℝ) := by simpa using hrho 0
      have h1 : |rho 1| < (1 / 4 : ℝ) := by simpa using hrho 1
      linarith [abs_lt.1 h0 |>.2, abs_lt.1 h1 |>.2]
  · norm_num

/-- Example 6.21 (3). The gauge of `K = B - bbar` is
`psi rho = max {-2 rho_1, -2 rho_2, rho_1 + rho_2}`. -/
theorem example_6_21_gauge_formula
    (rho : R2) :
    gauge example_6_21_shifted_triangle rho =
      max (max ((-2 : ℝ) * rho 0) ((-2 : ℝ) * rho 1)) (rho 0 + rho 1) := by
  sorry

/-- Helper for Example 6.21: the translated triangle has strict interior description matching its
three facet inequalities. -/
lemma example_6_21_mem_interior_shifted_triangle_iff
    (rho : R2) :
    rho ∈ interior example_6_21_shifted_triangle ↔
      (-2 : ℝ) * rho 0 < 1 ∧
      (-2 : ℝ) * rho 1 < 1 ∧
      rho 0 + rho 1 < 1 := by
  sorry

/-- Helper for Example 6.21: embedded integer points do not lie in the interior of the triangle
`B`. -/
lemma example_6_21_integer_point_not_mem_interior
    (z : Fin 2 → ℤ) :
    (Int.cast ∘ z : R2) ∉ interior example_6_21_triangle := by
  sorry

/-- Example 6.21 (4). For the tableau
`x1 = 1/2 + (1/4) x3 - (3/4) x4 - (1/4) x5 + x6`,
`x2 = 1/2 + (3/4) x3 - (1/4) x4 + (3/4) x5 - (3/4) x6`
with `x1, x2` integral and `x3, x4, x5, x6 >= 0`, the intersection cut defined by `B` is
`x3 + (3/2) x4 + (1/2) x5 + (3/2) x6 >= 1`. -/
theorem example_6_21_intersection_cut_valid
    {x1 x2 x3 x4 x5 x6 : ℝ}
    (hx1 :
      x1 = (1 / 2 : ℝ) + (1 / 4 : ℝ) * x3 - (3 / 4 : ℝ) * x4 - (1 / 4 : ℝ) * x5 + x6)
    (hx2 :
      x2 = (1 / 2 : ℝ) + (3 / 4 : ℝ) * x3 - (1 / 4 : ℝ) * x4 + (3 / 4 : ℝ) * x5 -
        (3 / 4 : ℝ) * x6)
    (hx1_int : ∃ z1 : ℤ, x1 = z1)
    (hx2_int : ∃ z2 : ℤ, x2 = z2)
    (hx3_nonneg : 0 ≤ x3)
    (hx4_nonneg : 0 ≤ x4)
    (hx5_nonneg : 0 ≤ x5)
    (hx6_nonneg : 0 ≤ x6) :
    x3 + (3 / 2 : ℝ) * x4 + (1 / 2 : ℝ) * x5 + (3 / 2 : ℝ) * x6 ≥ 1 := by
  sorry

end Example621
