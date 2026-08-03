import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

-- Semantic recall note: `lean_leansearch` is unavailable in this runner, so this file uses
-- source-faithful local notions for explicit piecewise-linear descriptions and MILP formulations.

/-- A finite interval cover on which a real-valued function is affine. -/
structure PiecewiseLinearOnInterval (l u : ℝ) (f : ℝ → ℝ) where
  pieces : ℕ
  lower : Fin pieces → ℝ
  upper : Fin pieces → ℝ
  slope : Fin pieces → ℝ
  intercept : Fin pieces → ℝ
  lower_le_upper : ∀ j, lower j ≤ upper j
  cover : Set.Icc l u ⊆ ⋃ j, Set.Icc (lower j) (upper j)
  eq_affine : ∀ j x, x ∈ Set.Icc (lower j) (upper j) → f x = slope j * x + intercept j

/-- The separable objective function `x ↦ ∑ i, fᵢ(xᵢ)`. -/
def separableObjective {n : ℕ} (f : Fin n → ℝ → ℝ) : (Fin n → ℝ) → ℝ :=
  fun x ↦ ∑ i, f i (x i)

/-- A mixed-integer linear extended formulation for maximizing a function over a feasible set. -/
structure MixedIntegerLinearFormulation (n : ℕ) (P : Set (Fin n → ℝ))
    (objective : (Fin n → ℝ) → ℝ) where
  vars : ℕ
  constraints : ℕ
  xEmbedding : Fin n ↪ Fin vars
  integerVars : Finset (Fin vars)
  A : Matrix (Fin constraints) (Fin vars) ℝ
  b : Fin constraints → ℝ
  c : Fin vars → ℝ
  of_original :
    ∀ ⦃x : Fin n → ℝ⦄, x ∈ P →
      ∃ y : Fin vars → ℝ,
        (∀ j ∈ integerVars, ∃ z : ℤ, y j = (z : ℝ)) ∧
        (∀ i, y (xEmbedding i) = x i) ∧
        (∀ r, (A.mulVec y) r ≤ b r) ∧
        objective x = ∑ j, c j * y j
  to_original :
    ∀ ⦃y : Fin vars → ℝ⦄,
      (∀ j ∈ integerVars, ∃ z : ℤ, y j = (z : ℝ)) →
      (∀ r, (A.mulVec y) r ≤ b r) →
      (fun i ↦ y (xEmbedding i)) ∈ P ∧
        objective (fun i ↦ y (xEmbedding i)) = ∑ j, c j * y j

/-- Exercise 2.23: if `P ⊆ [l, u]` is a polytope and each coordinate objective `f i` is piecewise
linear on `[l i, u i]`, then maximizing `∑ i, f i (x i)` over `x ∈ P` admits a mixed-integer
linear programming formulation. -/
theorem separable_piecewise_linear_maximization_has_milp_formulation
    {n : ℕ} (P : Set (Fin n → ℝ)) (l u : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hP : P ⊆ Set.Icc l u)
    (hf : ∀ i, PiecewiseLinearOnInterval (l i) (u i) (f i)) :
    Nonempty (MixedIntegerLinearFormulation n P (separableObjective f)) := sorry
