import Integer.Chapters.Chap05.section_5_6.ch5_sec5_6_exercise_5_19
import Integer.Chapters.Chap05.section_5_6.ch5_sec5_6_exercise_5_25

open scoped BigOperators

-- Primary domain: Chapter 5 lift-and-project closures on finite-coordinate polyhedra in `ℝ^n`.
-- Sampled owner abstractions:
-- * Section 5.4: `coordinate_lift_project_hull`
-- * Theorem 5.22: sequential convexification along prefix coordinates
-- * Exercise 5.25: `kth_lift_project_closure`
-- This file is source-facing: it reuses the Exercise 5.19 polyhedron owner for the common
-- pairwise-inequality polyhedron, introduces the Exercise 5.26 subset-sum relaxation, and
-- uses the Exercise 5.25 closure iteration owner directly.

section Exercise526

variable {n : ℕ}

/-- The nonnegative polyhedron cut out by the subset-sum inequalities
`∑_{j ∈ J} x_j ≤ 1` for all `(k + 2)`-element subsets `J`. -/
def exercise_5_26_subset_sum_relaxation
    (n k : ℕ) : Set (Fin n → ℝ) :=
  {x |
    (∀ i : Fin n, 0 ≤ x i) ∧
      ∀ J : Finset (Fin n), J.card = k + 2 → J.sum x ≤ 1}

/-- Membership in `exercise_5_26_subset_sum_relaxation n k` is exactly nonnegativity together
with the subset-sum inequalities `∑_{j ∈ J} x_j ≤ 1` for all `(k + 2)`-element sets `J`. -/
theorem mem_exercise_5_26_subset_sum_relaxation_iff
    {k : ℕ}
    {x : Fin n → ℝ} :
    x ∈ exercise_5_26_subset_sum_relaxation n k ↔
      (∀ i : Fin n, 0 ≤ x i) ∧
        ∀ J : Finset (Fin n), J.card = k + 2 → J.sum x ≤ 1 :=
  Iff.rfl

/-- Exercise 5.26. For `k + 2 ≤ n`, the `k`th lift-and-project closure of
`P = {x ∈ ℝ_+^n | x_i + x_j ≤ 1 for all 1 ≤ i < j ≤ n}` is exactly the set
`{x ∈ ℝ_+^n | ∑_{j ∈ J} x_j ≤ 1 for all J with |J| = k + 2}`. -/
theorem exercise_5_26_kth_lift_project_closure_eq_subset_sum_relaxation
    (n k : ℕ)
    (hk : k + 2 ≤ n) :
    kth_lift_project_closure (Nat.le_refl n) (exercise_5_19_polyhedron n) k =
      exercise_5_26_subset_sum_relaxation n k := sorry

/-- Membership in the `k`th lift-and-project closure from Exercise 5.26 is exactly
nonnegativity together with the subset-sum inequalities `∑_{j ∈ J} x_j ≤ 1` for all
`(k + 2)`-element sets `J`. -/
theorem mem_exercise_5_26_kth_lift_project_closure_iff
    {k : ℕ}
    (hk : k + 2 ≤ n)
    {x : Fin n → ℝ} :
    x ∈ kth_lift_project_closure (Nat.le_refl n) (exercise_5_19_polyhedron n) k ↔
      (∀ i : Fin n, 0 ≤ x i) ∧
        ∀ J : Finset (Fin n), J.card = k + 2 → J.sum x ≤ 1 := by
  rw [exercise_5_26_kth_lift_project_closure_eq_subset_sum_relaxation n k hk]
  exact mem_exercise_5_26_subset_sum_relaxation_iff

end Exercise526
