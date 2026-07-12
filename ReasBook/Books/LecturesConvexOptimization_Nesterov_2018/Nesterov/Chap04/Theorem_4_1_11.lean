import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Chap04.Definition_4_1_15

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section
open scoped CubicRegularizedDiagonalInvariants

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Theorem 4.1.11 lies in the diagonal cubic-regularized quadratic / scalar-duality domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticObjective` in `Definition_4_1_14`, the chapter owner for the primal
  cubic model;
* `cubicRegularizedQuadraticDualFunction` and `cubicRegularizedQuadraticDualDomain` in
  `Definition_4_1_14`, the chapter owners for the scalar dual value and its effective domain;
* `cubicRegularizedQuadraticScalarDualDomain_eq` in `Definition_4_1_14`, the bridge from
  `dom ψ` to the bounded-below shifted quadratic form;
* `cubicRegularizedQuadraticTauMinimizer` and `cubicRegularizedQuadraticTauMinimizer_def` in
  `Definition_4_1_14`, the owner and defining formula for the slack minimizer `τ(λ)`.

Best owner abstraction:
* source-facing: the diagonal `G² = 0` strong-duality and primal-minimizer theorems from the
  source;
* core/canonical: the primal objective, scalar dual function/domain, and the owner-level slack
  minimizer `cubicRegularizedQuadraticTauMinimizer`;
* bridge/view: the specialization `H = Matrix.diagonal Hdiag`.

Primitive data:
* `g`, `Hdiag`, `M`, and the induced diagonal matrix `H = Matrix.diagonal Hdiag`;
* the diagonal invariant `cubicRegularizedMinimalDiagonalGradientSquare g Hdiag`.

Derived API:
* `cubicRegularizedQuadraticObjective g H M`;
* `cubicRegularizedQuadraticDualFunction g H M`;
* `cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici (0 : ℝ)`;
* `cubicRegularizedQuadraticTauMinimizer M lam` together with
  `cubicRegularizedQuadraticTauMinimizer_def`.

This file therefore keeps the source-facing diagonal theorem family and records the `τ(λ*)`
clause by a labeled recall of the existing owner theorem
`cubicRegularizedQuadraticTauMinimizer_def`, rather than by a duplicate specialized wrapper. -/

/- The cubic objective, scalar dual owner, dual-domain owner, and slack minimizer are already the
upstream declarations from `Definition_4_1_14`. -/
recall cubicRegularizedQuadraticObjective
recall cubicRegularizedQuadraticObjective_apply
recall cubicRegularizedQuadraticScalarLagrangian
recall cubicRegularizedQuadraticDualFunction
recall cubicRegularizedQuadraticDualFunction_eq_sInf
recall cubicRegularizedQuadraticDualDomain
recall mem_cubicRegularizedQuadraticDualDomain_iff
recall cubicRegularizedQuadraticTauMinimizer
recall cubicRegularizedQuadraticTauMinimizer_isMinOn

variable [NeZero n]

section

variable (g : E) (Hdiag : Fin n → ℝ) (M : ℝ)

local notation "H" => Matrix.diagonal Hdiag
local notation "v" => cubicRegularizedQuadraticObjective g H M
local notation "ψ" => cubicRegularizedQuadraticDualFunction g H M
local notation "Dplus" => cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici (0 : ℝ)

variable {lamStar : ℝ}
variable (hM : 0 < M)
variable (hGzero : G²[g;Hdiag] = 0)
variable (hmax : IsMaxOn ψ Dplus lamStar)
variable (hlam : -H_min[Hdiag] < lamStar)

-- Proof sketch: combine the assumption `G² = 0` with the diagonal analysis of the shifted
-- quadratic subproblem to identify the minimizing `h`-variable for every `λ > -H_min`. Then use
-- the assumed maximality of `λ*` on `dom ψ ∩ ℝ₊` to identify the primal infimum with the dual
-- value `ψ(λ*)`; the auxiliary supremum step is the generic order-theoretic fact obtained from
-- `hmax.isLUB` and `IsLUB.csSup_eq`.
/-- Theorem 4.1.11 (1): for the diagonal cubic-regularized quadratic model with `H = diag(Hdiag)`,
if `G² = 0` and the dual problem admits a maximizer `λ* > -H_min`, then strong duality holds at
that maximizer:
the minimum of the primal objective `v(h)` equals the dual value `ψ(λ*)`. -/
theorem cubicRegularizedQuadraticDiagonal_strongDuality_of_zeroMinimalGradientSquare
    (hM : 0 < M)
    (hGzero : G²[g;Hdiag] = 0)
    (hmax : IsMaxOn ψ Dplus lamStar)
    (hlam : -H_min[Hdiag] < lamStar)
    :
    sInf (Set.range fun h : E ↦
      (v h : EReal)) =
      ψ lamStar := sorry

-- Proof sketch: solve the quadratic `h`-subproblem at the dual maximizer `λ*` using the
-- `G² = 0` diagonal case, and then use the primal-dual optimality relations at the maximizing
-- multiplier `λ*` to show that the resulting resolvent point minimizes the original cubic
-- objective.
/-- Theorem 4.1.11 (2): under the same hypotheses, the primal problem admits the explicit global
minimizer `h* = -(H + λ* I)⁻¹ g`. -/
theorem cubicRegularizedQuadraticDiagonal_primalMinimizer_of_zeroMinimalGradientSquare
    (hM : 0 < M)
    (hGzero : G²[g;Hdiag] = 0)
    (hmax : IsMaxOn ψ Dplus lamStar)
    (hlam : -H_min[Hdiag] < lamStar)
    :
    IsMinOn v Set.univ
      (-((H + lamStar • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹).mulVec g) := sorry

/- Theorem 4.1.11 (3): the associated slack minimizer satisfies
`τ(λ*) = 4 λ* |λ*| / M²`; this is exactly the owner theorem
`cubicRegularizedQuadraticTauMinimizer_def`. -/
recall cubicRegularizedQuadraticTauMinimizer_def

end
