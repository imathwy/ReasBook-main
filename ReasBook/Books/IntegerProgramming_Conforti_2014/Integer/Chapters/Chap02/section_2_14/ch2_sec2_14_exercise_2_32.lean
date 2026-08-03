import Mathlib

open scoped BigOperators

-- Semantic search tooling was unavailable in this environment; the API choice here uses standard
-- `Fin`-indexed vectors, support counting by `Finset.filter`, and `convexHull` from mathlib.

/-- Counts the number of nonzero coordinates of a `Fin`-indexed real vector. -/
noncomputable def nonzero_coordinate_count {k : ℕ} (y : Fin k → ℝ) : ℕ :=
  (Finset.univ.filter fun j : Fin k ↦ y j ≠ 0).card

/-- The intended feasible set: each variable lies between `0` and its upper bound, and at most
`ℓ` variables are nonzero. -/
def bounded_nonzero_cardinality_feasible {k : ℕ} (u : Fin k → ℝ) (ℓ : ℕ) (y : Fin k → ℝ) :
    Prop :=
  (∀ j, 0 ≤ y j ∧ y j ≤ u j) ∧ nonzero_coordinate_count y ≤ ℓ

/-- The standard binary-activation mixed-integer formulation for imposing that at most `ℓ`
bounded continuous variables are nonzero. -/
def bounded_nonzero_cardinality_milp {k : ℕ} (u : Fin k → ℝ) (ℓ : ℕ) (x y : Fin k → ℝ) :
    Prop :=
  (∀ j, x j = 0 ∨ x j = 1) ∧
    (∀ j, 0 ≤ y j ∧ y j ≤ u j * x j) ∧
    (∑ j, x j) ≤ (ℓ : ℝ)

/-- The linear programming relaxation of the binary-activation formulation. -/
def bounded_nonzero_cardinality_relaxation {k : ℕ} (u : Fin k → ℝ) (ℓ : ℕ)
    (x y : Fin k → ℝ) : Prop :=
  (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧
    (∀ j, 0 ≤ y j ∧ y j ≤ u j * x j) ∧
    (∑ j, x j) ≤ (ℓ : ℝ)

/-- Exercise 2.32: the binary-activation constraints give an exact mixed-integer formulation for
the bounded vectors with at most `ℓ` nonzero coordinates. -/
theorem exercise_2_32 {k : ℕ} (u : Fin k → ℝ) (hu : ∀ j, 0 ≤ u j) (ℓ : ℕ) (y : Fin k → ℝ) :
    bounded_nonzero_cardinality_feasible u ℓ y ↔
      ∃ x : Fin k → ℝ, bounded_nonzero_cardinality_milp u ℓ x y := sorry

/-- The LP relaxation of the activation formulation projects to the convex hull of the intended
feasible set. -/
theorem bounded_nonzero_cardinality_relaxation_is_perfect {k : ℕ} (u : Fin k → ℝ)
    (hu : ∀ j, 0 ≤ u j) (ℓ : ℕ) :
    convexHull ℝ {y : Fin k → ℝ | bounded_nonzero_cardinality_feasible u ℓ y} =
      {y : Fin k → ℝ | ∃ x : Fin k → ℝ, bounded_nonzero_cardinality_relaxation u ℓ x y} := sorry
