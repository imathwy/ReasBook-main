import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Theorem_3_24

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open WithLp (toLp)

section

variable {m n p : ℕ}
variable
  {f : (Fin n → ℝ) → ℝ}
  {g : (Fin n → ℝ) → Fin m → ℝ}
  {A : Matrix (Fin p) (Fin n) ℝ} {b : Fin p → ℝ}
  {xTilde : Fin n → ℝ}
  {fOpt rho1 rho2 delta : ℝ}

local notation "IneqSpace" => EuclideanSpace ℝ (Fin m)
local notation "EqSpace" => EuclideanSpace ℝ (Fin p)
local notation "ineqViolationVec" => (toLp 2 ((g xTilde)⁺) : IneqSpace)
local notation "eqResidualVec" => (toLp 2 (A *ᵥ xTilde + b) : EqSpace)
local notation "penalizedGap" =>
  f xTilde - fOpt + rho1 * ‖ineqViolationVec‖ + rho2 * ‖eqResidualVec‖

-- Proof sketch: the two penalty terms are norms multiplied by real coefficients, so they are
-- nonnegative. Dropping them from the left-hand side of the penalty estimate leaves the desired
-- upper bound for the objective gap.
/-- Theorem 3.26 (1): any point satisfying the penalized upper bound immediately satisfies
`f(x̃) - f_opt ≤ δ`. -/
theorem objective_gap_le_of_penalized_bound
    (hRho1Nonneg : 0 ≤ rho1) (hRho2Nonneg : 0 ≤ rho2)
    (hPenalty : penalizedGap ≤ delta) :
    f xTilde - fOpt ≤ delta := by
  have hPenalty1 : 0 ≤ rho1 * ‖ineqViolationVec‖ :=
    mul_nonneg hRho1Nonneg (norm_nonneg _)
  have hPenalty2 : 0 ≤ rho2 * ‖eqResidualVec‖ :=
    mul_nonneg hRho2Nonneg (norm_nonneg _)
  linarith

variable
  {X : Set (Fin n → ℝ)}
  {yStar : Fin m → ℝ} {zStar : Fin p → ℝ}

local notation "ineqMultiplierVec" => (toLp 2 yStar : IneqSpace)
local notation "eqMultiplierVec" => (toLp 2 zStar : EqSpace)

/- Theorem 3.26 is `source-facing` in the affine-constrained perturbation/penalty API. Its
`core/canonical` owner abstraction is `IsDualOptimalSolution`; the chapter perturbation owner
`value_function` and the bridge theorem
`isDualOptimalSolution_iff_neg_pair_mem_subdifferential_valueFunction_zero` from
`Theorem_3_24` explain why this owner is canonical. This file keeps only the source-facing penalty
estimates and does not add a parallel local owner API on top of those declarations. -/
recall IsDualOptimalSolution
recall isDualOptimalSolution_iff_neg_pair_mem_subdifferential_valueFunction_zero

-- Proof sketch: the dual-optimal solution with value `fOpt` gives the same affine lower bound
-- used in Theorem 3.24, now evaluated at the Euclidean bridge points
-- `u = toLp 2 ((g xTilde)⁺)` and `t = toLp 2 (A *ᵥ xTilde + b)`. Combining
-- that lower bound with the penalized estimate yields
-- `(rho1 - ‖toLp 2 yStar‖) * ‖toLp 2 ((g xTilde)⁺)‖ +
--   (rho2 - ‖toLp 2 zStar‖) * ‖toLp 2 (A *ᵥ xTilde + b)‖ ≤ delta`.
-- The extra assumption `‖toLp 2 zStar‖ ≤ rho2` makes the equality-residual term nonnegative, so
-- it may be discarded; the assumptions `0 < rho1` and `2 * ‖toLp 2 yStar‖ ≤ rho1` then give the
-- stated `2 / rho1` bound.
/-- Theorem 3.26 (2): given a dual optimal multiplier pair with optimal value `fOpt`, the positive
part of the inequality-constraint violation at `x̃`, measured in the Euclidean norm on
`WithLp 2 (Fin m → ℝ)`, is bounded by `(2 / ρ₁) δ` when the penalty parameter `ρ₁` dominates the
Euclidean norm of the inequality multiplier and `ρ₂` is at least the Euclidean norm of the
equality multiplier. -/
theorem positive_constraint_violation_le_two_div_rho1_of_penalized_bound
    (hDual : IsDualOptimalSolution X f g A b fOpt yStar zStar)
    (hxTilde : xTilde ∈ X)
    (hPenalty : penalizedGap ≤ delta)
    (hRho1Pos : 0 < rho1)
    (hRho1 : 2 * ‖ineqMultiplierVec‖ ≤ rho1)
    (hRho2 : ‖eqMultiplierVec‖ ≤ rho2) :
    ‖ineqViolationVec‖ ≤ (2 / rho1) * delta := sorry

-- Proof sketch: use the same dual-optimal affine lower bound with value `fOpt`,
-- `u = toLp 2 ((g xTilde)⁺)` and
-- `t = toLp 2 (A *ᵥ xTilde + b)`. The penalized estimate gives
-- `(rho1 - ‖toLp 2 yStar‖) * ‖toLp 2 ((g xTilde)⁺)‖ +
--   (rho2 - ‖toLp 2 zStar‖) * ‖toLp 2 (A *ᵥ xTilde + b)‖ ≤ delta`.
-- The extra assumption `‖toLp 2 yStar‖ ≤ rho1` makes the inequality-violation term nonnegative,
-- so it may be discarded; the assumptions `0 < rho2` and `2 * ‖toLp 2 zStar‖ ≤ rho2` then give
-- the claimed residual bound.
/-- Theorem 3.26 (3): given a dual optimal multiplier pair with optimal value `fOpt`, the equality
constraint residual at `x̃`, measured in the Euclidean norm on `WithLp 2 (Fin p → ℝ)`, is bounded
by `(2 / ρ₂) δ` when the penalty parameter `ρ₂` dominates the Euclidean norm of the equality
multiplier and `ρ₁` is at least the Euclidean norm of the inequality multiplier. -/
theorem equality_constraint_residual_le_two_div_rho2_of_penalized_bound
    (hDual : IsDualOptimalSolution X f g A b fOpt yStar zStar)
    (hxTilde : xTilde ∈ X)
    (hPenalty : penalizedGap ≤ delta)
    (hRho2Pos : 0 < rho2)
    (hRho2 : 2 * ‖eqMultiplierVec‖ ≤ rho2)
    (hRho1 : ‖ineqMultiplierVec‖ ≤ rho1) :
    ‖eqResidualVec‖ ≤ (2 / rho2) * delta := sorry

end
