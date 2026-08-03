import Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_example_6_21
import Integer.Chapters.Chap06.section_6_3_2.max_linear_representation

section Example632

open scoped Matrix

-- This item keeps Example 6.32 source-facing, but derives its three regions from the Chapter 6.3.2
-- dot-product surface and the canonical Example 6.21 gauge owner.

local notation "R2" => Fin 2 → ℝ
local notation "ψ" => gauge example_6_21_shifted_triangle

/-- The three normals whose linear pieces realize the gauge from Example 6.21. -/
def example_6_32_branch_normal : Fin 3 → R2
  | ⟨0, _⟩ => ![-2, 0]
  | ⟨1, _⟩ => ![0, -2]
  | _ => ![1, 1]

local notation "ℓ" => fun i : Fin 3 ↦ fun r : R2 ↦ example_6_32_branch_normal i ⬝ᵥ r

/-- The first branch normal from Example 6.32 evaluates to the linear piece `-2 r₁`. -/
@[simp] theorem example_6_32_branch_normal_zero_value (r : R2) :
    example_6_32_branch_normal 0 ⬝ᵥ r = (-2 : ℝ) * r 0 := by
  simp [dotProduct, example_6_32_branch_normal]

/-- The second branch normal from Example 6.32 evaluates to the linear piece `-2 r₂`. -/
@[simp] theorem example_6_32_branch_normal_one_value (r : R2) :
    example_6_32_branch_normal 1 ⬝ᵥ r = (-2 : ℝ) * r 1 := by
  simp [dotProduct, example_6_32_branch_normal]

/-- The third branch normal from Example 6.32 evaluates to the linear piece `r₁ + r₂`. -/
@[simp] theorem example_6_32_branch_normal_two_value (r : R2) :
    example_6_32_branch_normal 2 ⬝ᵥ r = r 0 + r 1 := by
  simp [dotProduct, example_6_32_branch_normal]

/-- Example 6.32 presents the gauge from Example 6.21 as the maximum of the three linear pieces
coming from `example_6_32_branch_normal`. -/
theorem example_6_32_gauge_eq_max_branch_normal (r : R2) :
    ψ r =
      max
        (max (example_6_32_branch_normal 0 ⬝ᵥ r)
          (example_6_32_branch_normal 1 ⬝ᵥ r))
        (example_6_32_branch_normal 2 ⬝ᵥ r) := by
  rw [example_6_21_gauge_formula]
  simp [dotProduct, example_6_32_branch_normal]

/-- The same three normals realize `ψ` in the canonical `sup'` form used by
`IsMaxLinearRepresentation`. -/
theorem example_6_32_gauge_eq_sup_branch_normal (r : R2) :
    ψ r =
      Finset.univ.sup' (by simp : (Finset.univ : Finset (Fin 3)).Nonempty) (fun i ↦ ℓ i r) := by
  rw [example_6_32_gauge_eq_max_branch_normal]
  refine le_antisymm ?_ ?_
  · refine max_le ?_ ?_
    · refine max_le ?_ ?_
      · exact Finset.le_sup' (fun i ↦ ℓ i r) (by simp)
      · exact Finset.le_sup' (fun i ↦ ℓ i r) (by simp)
    · exact Finset.le_sup' (fun i ↦ ℓ i r) (by simp)
  · refine Finset.sup'_le (by simp) (fun i ↦ ℓ i r) ?_
    intro i hi
    fin_cases i <;> simp

/-- The three normals from Example 6.32 form a max-linear representation of the gauge from
Example 6.21. -/
theorem example_6_32_branch_normal_isMaxLinearRepresentation :
    IsMaxLinearRepresentation ψ example_6_32_branch_normal := by
  intro r
  exact example_6_32_gauge_eq_sup_branch_normal r

/-- Example 6.32 therefore gives a concrete three-normal max-linear representation of the gauge
from Example 6.21, matching the owner used in Corollary 6.31. -/
theorem example_6_32_gauge_has_three_branch_bound :
    HasMaxLinearRepresentationOfSizeLE 3 ψ :=
  HasMaxLinearRepresentationOfSizeLE.of_isMaxLinearRepresentation le_rfl
    example_6_32_branch_normal_isMaxLinearRepresentation

/-- The first cone `P1` from Example 6.32, where the branch `-2 r₁` dominates the other two
linear pieces. -/
def example_6_32_p1 : Set R2 :=
  {r |
    ℓ 1 r ≤ ℓ 0 r ∧
      ℓ 2 r ≤ ℓ 0 r}

/-- Membership in `example_6_32_p1` is exactly the pair of dominance inequalities defining the
first piece of `ψ`. -/
theorem mem_example_6_32_p1_iff (r : R2) :
    r ∈ example_6_32_p1 ↔
      (-2 : ℝ) * r 0 ≥ (-2 : ℝ) * r 1 ∧ (-2 : ℝ) * r 0 ≥ r 0 + r 1 := sorry

/-- The second cone `P2` from Example 6.32, where the branch `-2 r₂` dominates the other two
linear pieces. -/
def example_6_32_p2 : Set R2 :=
  {r |
    ℓ 0 r ≤ ℓ 1 r ∧
      ℓ 2 r ≤ ℓ 1 r}

/-- Membership in `example_6_32_p2` is exactly the pair of dominance inequalities defining the
second piece of `ψ`. -/
theorem mem_example_6_32_p2_iff (r : R2) :
    r ∈ example_6_32_p2 ↔
      (-2 : ℝ) * r 1 ≥ (-2 : ℝ) * r 0 ∧ (-2 : ℝ) * r 1 ≥ r 0 + r 1 := sorry

/-- The third cone `P3` from Example 6.32, where the branch `r₁ + r₂` dominates the other two
linear pieces. -/
def example_6_32_p3 : Set R2 :=
  {r |
    ℓ 0 r ≤ ℓ 2 r ∧
      ℓ 1 r ≤ ℓ 2 r}

/-- Membership in `example_6_32_p3` is exactly the pair of dominance inequalities defining the
third piece of `ψ`. -/
theorem mem_example_6_32_p3_iff (r : R2) :
    r ∈ example_6_32_p3 ↔
      r 0 + r 1 ≥ (-2 : ℝ) * r 0 ∧ r 0 + r 1 ≥ (-2 : ℝ) * r 1 := sorry

/-- Every `r ∈ ℝ²` lies in at least one of the three cones from Example 6.32. -/
theorem example_6_32_mem_p1_or_p2_or_p3 (r : R2) :
    r ∈ example_6_32_p1 ∨ r ∈ example_6_32_p2 ∨ r ∈ example_6_32_p3 := sorry

/-- Example 6.32 (1). For `f = (1 / 2, 1 / 2)` and the maximal `ℤ²`-free set `B` of Example 6.21,
the corresponding function `ψ(r) = gauge (B - f) r` satisfies `ψ(r) = -2 r₁` on the cone `P1`. -/
theorem example_6_32_psi_eq_on_p1
    (r : R2)
    (hr : r ∈ example_6_32_p1) :
    ψ r = (-2 : ℝ) * r 0 := sorry

/-- Example 6.32 (2). For `f = (1 / 2, 1 / 2)` and the maximal `ℤ²`-free set `B` of Example 6.21,
the corresponding function `ψ(r) = gauge (B - f) r` satisfies `ψ(r) = -2 r₂` on the cone `P2`. -/
theorem example_6_32_psi_eq_on_p2
    (r : R2)
    (hr : r ∈ example_6_32_p2) :
    ψ r = (-2 : ℝ) * r 1 := sorry

/-- Example 6.32 (3). For `f = (1 / 2, 1 / 2)` and the maximal `ℤ²`-free set `B` of Example 6.21,
the corresponding function `ψ(r) = gauge (B - f) r` satisfies `ψ(r) = r₁ + r₂` on the cone `P3`.
-/
theorem example_6_32_psi_eq_on_p3
    (r : R2)
    (hr : r ∈ example_6_32_p3) :
    ψ r = r 0 + r 1 := sorry

end Example632
