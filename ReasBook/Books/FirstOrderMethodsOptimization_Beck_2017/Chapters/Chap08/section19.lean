import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_8_19 (from Chap08) -/
/- Definition 8.19 is `source-facing`: it reintroduces the Lagrangian dual objective
`q(λ) = min_{x ∈ X} L(x; λ)` for the inequality-constrained primal problem from this chapter. The
`core/canonical` owners for this data are already Chapter 3's declarations `lagrangian` and
`lagrangian_dual_objective`, so this item should reuse that existing owner directly rather than
manufacturing a second dual-objective wrapper for the same mathematics. -/

/- Definition 8.19: the Lagrangian dual objective function `q(λ)` of
`min f(x)` subject to `g(x) ≤ 0` and `x ∈ X` is the existing owner
`lagrangian_dual_objective`, which formalizes the textbook formula by sending `λ` to the infimum
over `X` of the Lagrangian `L(x; λ) = f(x) + λᵀ g(x)`. -/
recall lagrangian_dual_objective

/- The displayed formula `q(λ) = min_{x ∈ X} L(x; λ)` is formalized by the canonical infimum
statement `lagrangian_dual_objective_eq_sInf`. -/
recall lagrangian_dual_objective_eq_sInf

/-! ### Example_8_19 (from Chap08) -/
open Matrix
open WithLp (toLp)
open scoped BigOperators Matrix

noncomputable section

section

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The matrix `A = ((1, 2), (3, 4))` from Example 8.19. -/
def example_8_19_matrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 : ℝ), 2; 3, 4]

/-- Example 8.19 (1): the objective on `ℝ²` is
`f(x₁, x₂) = |x₁ + 2 x₂| + |3 x₁ + 4 x₂|`. -/
def example_8_19_objective (x : E) : ℝ :=
  |x 0 + 2 * x 1| + |3 * x 0 + 4 * x 1|

-- Proof sketch: compute `example_8_19_matrix.toEuclideanLin x`, identify its two coordinates with
-- `x₁ + 2x₂` and `3x₁ + 4x₂`, and rewrite the `ℓ¹` norm on `ℝ²` as the sum of the absolute values
-- of those coordinates.
/-- The Example 8.19 objective is the `ℓ¹` norm of `A x`. -/
theorem example_8_19_objective_eq_l1_matrix_norm (x : E) :
    example_8_19_objective x =
      ‖toLp 1 (fun i : Fin 2 ↦ (example_8_19_matrix.toEuclideanLin x) i)‖ := sorry

-- Proof sketch: evaluate the objective at the origin and simplify the two absolute values.
/-- Example 8.19 (2): the objective value at the origin is `0`. -/
theorem example_8_19_objective_zero :
    example_8_19_objective (0 : E) = 0 := sorry

-- Proof sketch: `example_8_19_objective` is a norm of the linear image `A x`, hence is
-- nonnegative everywhere. Evaluating at the origin gives `0`, so `0` is a global minimizer on
-- `ℝ²`.
/-- Example 8.19 (3): the origin is an optimal solution of the unconstrained problem. -/
theorem example_8_19_isMinOn_origin :
    IsMinOn example_8_19_objective Set.univ (0 : E) := sorry

-- Proof sketch: view the real-valued objective as the everywhere-finite extended-real-valued
-- function `x ↦ (example_8_19_objective x : EReal)`. Use convexity of the `ℓ¹` norm composed with
-- the linear map `example_8_19_matrix.toEuclideanLin`, the fact that the feasible set is
-- `Set.univ`, and `example_8_19_isMinOn_origin` together with `example_8_19_objective_zero` to
-- identify the optimal set and optimal value.
/-- Example 8.19 (4): the example objective satisfies Assumption 8.7 on `ℝ²`, with feasible set
`Set.univ`, optimal set `{0}`, and optimal value `0`. -/
theorem example_8_19_isConstrainedConvexProblem :
    IsConstrainedConvexProblem
      (fun x : E ↦ (example_8_19_objective x : EReal))
      Set.univ ({(0 : E)} : Set E) 0 := sorry

-- Proof sketch: the decimal constant `7.2111` is strictly positive.
/-- The displayed Lipschitz constant `7.2111` is positive. -/
theorem example_8_19_lipschitz_constant_pos :
    0 < (7.2111 : ℝ) := sorry

-- Proof sketch: use the affine-`ℓ¹` subdifferential description from Proposition 3.19 together
-- with the four possible sign choices of the two residual coordinates to reduce every strong-dual
-- subgradient to one of four explicit vectors. Then bound each of their Euclidean norms by
-- `7.2111`.
/-- Every strong-dual subgradient of the Example 8.19 objective on `ℝ²` has norm at most
`7.2111`. -/
theorem example_8_19_subgradient_norm_le
    {x : E} {g : StrongDual ℝ E} (hx : x ∈ Set.univ)
    (hg : g ∈ strongDualSubdifferential
      (fun y : E ↦ (example_8_19_objective y : EReal)) x) :
    ‖g‖ ≤ (7.2111 : ℝ) := sorry

/-- Example 8.19 (5): the example admits the explicit subgradient norm bound package with
Lipschitz constant `L_f = 7.2111`. -/
def example_8_19_subgradient_norm_bound :
    SubgradientNormBoundOn
      (fun x : E ↦ (example_8_19_objective x : EReal))
      Set.univ where
  L_f := 7.2111
  L_f_pos := example_8_19_lipschitz_constant_pos
  norm_le := example_8_19_subgradient_norm_le

-- Proof sketch: unfold `example_8_19_subgradient_norm_bound` and read off its stored constant.
/-- The bound package for Example 8.19 stores the constant `L_f = 7.2111`. -/
theorem example_8_19_subgradient_norm_bound_L_f :
    example_8_19_subgradient_norm_bound.L_f = 7.2111 := sorry

/-- Example 8.19 (6): the chosen subgradient direction is the transpose-sign vector
`Aᵀ sgn(Ax)`, using the book convention `sgn 0 = 1`. -/
def example_8_19_subgradient_direction (x : E) : E :=
  example_8_19_matrix.transpose.toEuclideanLin
    (toLp 2 (sgn (fun i ↦ (example_8_19_matrix.toEuclideanLin x) i)))

-- Proof sketch: apply Proposition 3.19 (2) to the affine `ℓ¹` objective with matrix
-- `example_8_19_matrix` and zero offset, then rewrite the objective through
-- `example_8_19_objective_eq_l1_matrix_norm`.
/-- Example 8.19 (7): the chosen vector `v(x)` belongs to the Euclidean subdifferential
`∂ f(x)`. -/
theorem example_8_19_subgradient_direction_mem (x : E) :
    example_8_19_subgradient_direction x ∈
      euclideanSubdifferentialAt example_8_19_objective x := sorry

-- Proof sketch: the two sign coordinates in `sgn (A x)` each take only the values `±1`, so the
-- vector `Aᵀ sgn(Ax)` can only be one of the four explicit combinations obtained from those sign
-- pairs.
/-- Example 8.19 (8): the chosen subgradient direction takes only the four values
`(-4, -6)`, `(2, 2)`, `(-2, -2)`, and `(4, 6)`. -/
theorem example_8_19_subgradient_direction_mem_four_values (x : E) :
    example_8_19_subgradient_direction x ∈
      ({(!₂[(-4 : ℝ), -6] : E), !₂[(2 : ℝ), 2], !₂[(-2 : ℝ), -2], !₂[(4 : ℝ), 6]} :
        Set E) := sorry

-- Proof sketch: combine `example_8_19_subgradient_direction_mem_four_values` with the fact that
-- each of the four explicit vectors is nonzero.
/-- The chosen subgradient direction in Example 8.19 is never the zero vector. -/
theorem example_8_19_subgradient_direction_ne_zero (x : E) :
    example_8_19_subgradient_direction x ≠ 0 := sorry

-- Proof sketch: `example_8_19_subgradient_direction_ne_zero` lets us expand `polyak_stepsize`
-- through its nonzero branch, and `(example_8_19_objective x : EReal).toReal =
-- example_8_19_objective x` because the objective is real-valued.
/-- Polyak's stepsize rule for the chosen Example 8.19 subgradient reduces to the displayed
quotient formula. -/
theorem example_8_19_polyak_stepsize_eq_quotient (x : E) :
    polyak_stepsize
        (fun y : E ↦ (example_8_19_objective y : EReal))
        0 x (example_8_19_subgradient_direction x) =
      example_8_19_objective x /
        ‖example_8_19_subgradient_direction x‖ ^ (2 : ℕ) := sorry

/-- Example 8.19 (9): the subgradient-method update is the Polyak quotient step taken in the
chosen direction `v(x)`. -/
def example_8_19_polyak_update (x : E) : E :=
  x -
    (example_8_19_objective x /
      ‖example_8_19_subgradient_direction x‖ ^ (2 : ℕ)) •
      example_8_19_subgradient_direction x

-- Proof sketch: unfold `example_8_19_polyak_update` and replace the scalar quotient by
-- `polyak_stepsize` using `example_8_19_polyak_stepsize_eq_quotient`.
/-- The Example 8.19 update map is exactly one Polyak step written with the chapter owner
`polyak_stepsize`. -/
theorem example_8_19_polyak_update_eq_polyak_step (x : E) :
    example_8_19_polyak_update x =
      x -
        polyak_stepsize
            (fun y : E ↦ (example_8_19_objective y : EReal))
            0 x (example_8_19_subgradient_direction x) •
          example_8_19_subgradient_direction x := sorry

end
