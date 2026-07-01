import Nesterov.Chap04.Theorem_4_1_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section
open scoped CubicRegularizedDiagonalInvariants

/- Proposition 4.1.15 lies in the diagonal cubic-regularized quadratic / scalar-duality domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticObjective` in `Theorem_4_1_11`, the chapter owner of the primal cubic
  model;
* `cubicRegularizedQuadraticDualFunction` and `cubicRegularizedQuadraticDualDomain` in
  `Theorem_4_1_11`, the chapter owners of the scalar dual value and its effective domain;
* `cubicRegularizedDiagonalMinimum` in `Definition_4_1_15`, imported through
  `Theorem_4_1_11`, the chapter owner for the boundary value `-H_min`;
* `IsMinOn` and `IsMaxOn` in mathlib, the canonical owner predicates for primal and dual
  optimality.

Best owner abstraction:
* source-facing: the explicit two-dimensional counterexample itself, with the concrete data
  `g = (-1, 0)ᵀ`, `H = diag(0, -1)`, `M = 1`, the two minimizers `(1, ±√3)ᵀ`, and the boundary
  maximizer `λ* = -H_min[Hdiag] = 1`;
* core/canonical: `cubicRegularizedQuadraticObjective`, `cubicRegularizedQuadraticDualFunction`,
  `cubicRegularizedQuadraticDualDomain`, together with `IsMinOn` and `IsMaxOn`;
* bridge/view: the concrete specialization to `n = 2`.

Primitive data:
* the explicit example vectors/matrix `CubicRegularizedQuadraticCounterexample.g`,
  `CubicRegularizedQuadraticCounterexample.Hdiag`,
  `CubicRegularizedQuadraticCounterexample.H`,
  `CubicRegularizedQuadraticCounterexample.minimizerPos`, and
  `CubicRegularizedQuadraticCounterexample.minimizerNeg`.

Derived API:
* the optimality statements for the two explicit minimizers via `IsMinOn`;
* the identity `-H_min[Hdiag] = 1`;
* dual optimality of the same explicit boundary multiplier on
  `cubicRegularizedQuadraticDualDomain g H 1 ∩ Set.Ici (0 : ℝ)` via `IsMaxOn`.

Source/core/bridge triage:
* source-facing: the explicit counterexample data and witness optimality statements below;
* core/canonical: the chapter owner objective/dual/domain family and the order-owner predicates;
* bridge/view: the concrete `n = 2` specialization of those owners.

This file therefore removes the existential wrapper around “multiple minimizers”, keeps the
explicit textbook witnesses as public data, and reuses the canonical expression
`-H_min[Hdiag]` directly instead of introducing a second public owner for the boundary
multiplier. -/

namespace CubicRegularizedQuadraticCounterexample

local notation "E" => EuclideanSpace ℝ (Fin 2)

/-- The example gradient `g = (-1, 0)ᵀ`. -/
def g : E :=
  WithLp.toLp 2 ![-(1 : ℝ), (0 : ℝ)]

/-- The diagonal entries of the example Hessian `H = diag(0, -1)`. -/
def Hdiag : Fin 2 → ℝ :=
  ![(0 : ℝ), (-1 : ℝ)]

/-- The example Hessian `H = diag(0, -1)`. -/
def H : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal Hdiag

/-- The positive-sign primal minimizer `(1, √3)ᵀ`. -/
def minimizerPos : E :=
  WithLp.toLp 2 ![(1 : ℝ), Real.sqrt 3]

/-- The negative-sign primal minimizer `(1, -√3)ᵀ`. -/
def minimizerNeg : E :=
  WithLp.toLp 2 ![(1 : ℝ), -(Real.sqrt 3)]

local notation "v" => cubicRegularizedQuadraticObjective g H 1
local notation "ψ" => cubicRegularizedQuadraticDualFunction g H 1
local notation "Dplus" => cubicRegularizedQuadraticDualDomain g H 1 ∩ Set.Ici (0 : ℝ)

-- Proof sketch: the two vectors differ in their second coordinate, since `√3 ≠ -√3`.
/-- Proposition 4.1.15 (1): the two explicit minimizers in the counterexample are distinct. -/
theorem minimizerPos_ne_minimizerNeg :
    minimizerPos ≠ minimizerNeg := sorry

-- Proof sketch: compute the stationary equations for the explicit cubic model with
-- `g = (-1, 0)ᵀ`, `H = diag(0, -1)`, and `M = 1`, then verify that `(1, √3)ᵀ` globally minimizes
-- the primal objective.
/-- Proposition 4.1.15 (2): the point `(1, √3)ᵀ` is a global minimizer of the explicit
cubic-regularized quadratic counterexample. -/
theorem minimizerPos_isMinOn :
    IsMinOn v Set.univ minimizerPos := sorry

-- Proof sketch: the same stationary-point computation gives the symmetric second minimizer
-- `(1, -√3)ᵀ`.
/-- Proposition 4.1.15 (3): the point `(1, -√3)ᵀ` is also a global minimizer of the explicit
cubic-regularized quadratic counterexample. -/
theorem minimizerNeg_isMinOn :
    IsMinOn v Set.univ minimizerNeg := sorry

-- Proof sketch: for `Hdiag = (0, -1)`, the minimum diagonal entry is `H_min = -1`.
/-- Proposition 4.1.15 (4): for the explicit Hessian `diag(0, -1)`, the boundary multiplier
`-H_min` equals `1`. -/
theorem boundaryMultiplier_eq_one :
    -H_min[Hdiag] = 1 := sorry

-- Proof sketch: evaluate the scalar dual function on `dom ψ ∩ ℝ₊` for the explicit data and
-- verify that the maximum is attained at the boundary multiplier `-H_min[Hdiag] = 1`.
/-- Proposition 4.1.15 (5): the scalar dual optimum for the explicit counterexample is attained
at the boundary multiplier `λ* = -H_min`. -/
theorem boundaryMultiplier_isMaxOn :
    IsMaxOn ψ Dplus (-H_min[Hdiag]) := sorry

end CubicRegularizedQuadraticCounterexample
