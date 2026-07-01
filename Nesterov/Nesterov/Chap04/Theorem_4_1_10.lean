import Nesterov.Chap04.Definition_4_1_15
import Nesterov.Chap04.Definition_4_1_14
import Nesterov.Chap04.Proposition_4_1_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section
open scoped CubicRegularizedDiagonalInvariants

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Domain/API note for this item: the theorem lies in the diagonal cubic-regularized quadratic /
scalar-duality domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticObjective` in `Definition_4_1_14`, the chapter owner of the primal
  cubic model;
* `cubicRegularizedQuadraticDualFunction` and `cubicRegularizedQuadraticDualDomain` in
  `Definition_4_1_14`, the chapter owners of the scalar dual value and its effective domain;
* `cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos` in
  `Proposition_4_1_9`, the existing source-facing domain identity in the nondegenerate diagonal
  case;
* `cubicRegularizedDiagonalMinimum` and
  `cubicRegularizedMinimalDiagonalGradientSquare` in `Definition_4_1_15`, the diagonal owners of
  `H_min` and `G²`;
* `cubicRegularizedQuadraticTauMinimizer` and
  `cubicRegularizedQuadraticTauMinimizer_def` in `Definition_4_1_14`, the chapter owner and
  defining formula for the slack minimizer `τ(λ)`.

Best owner abstraction:
* source-facing: the diagonal `G² > 0` strong-duality and minimizer statements from the source;
* core/canonical: the generic cubic-regularized quadratic objective, dual function, dual domain,
  and tau minimizer together with the diagonal bounded-below-domain owner;
* bridge/view: the specialization `H = Matrix.diagonal Hdiag`.

Primitive data:
* the gradient `g`, diagonal data `Hdiag`, cubic parameter `M`, and the diagonal matrix
  `H = Matrix.diagonal Hdiag`;
* the canonical diagonal invariants `H_min` and `G²`.

Derived API:
* `cubicRegularizedQuadraticObjective g H M`;
* `cubicRegularizedQuadraticDualFunction g H M`;
* `cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici (0 : ℝ)`;
* `IsMaxOn (cubicRegularizedQuadraticDualFunction g H M)
    (cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici (0 : ℝ)) lam`;
* `cubicRegularizedQuadraticTauMinimizer M lam`.

This file therefore keeps the source-facing diagonal theorem family, but removes duplicate local
owners for the primal objective, shifted quadratic form, and dual function. The source domain
clause is reused directly from `Proposition_4_1_9`, while the explicit `τ(λ*)` formula is
reused from the existing owner theorem `cubicRegularizedQuadraticTauMinimizer_def`. -/

section

variable (g : E) (Hdiag : Fin n → ℝ) (M : ℝ)

local notation "H" => Matrix.diagonal Hdiag
local notation "Dplus" => cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici (0 : ℝ)

/- The nondegenerate diagonal domain identity is already the source-facing proposition
`cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos`. -/
recall cubicRegularizedQuadraticDualDomain_eq_Ioi_of_activeGradientSquare_pos

-- Proof sketch: combine the positivity assumption `G² > 0` with the diagonal analysis of the
-- shifted quadratic subproblem to identify the maximizing dual parameter range. Then apply strong
-- duality for the epigraph reformulation to identify the primal infimum with the dual value at a
-- nonnegative dual maximizer.
/-- Theorem 4.1.10: for the diagonal cubic-regularized quadratic model with `H = diag(Hdiag)`,
if `G² = ∑_{i : Hdiag i = H_min} (g i)^2` is positive, then every nonnegative dual maximizer on
`cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici 0` yields strong duality:
the minimum of the primal objective equals the dual value `ψ(λ*)`.
The companion entries in this file record the strong-duality consequences, the explicit primal
minimizer, and the owner-level formula
`cubicRegularizedQuadraticTauMinimizer_def` for the associated slack minimizer `τ(λ*)`. -/
theorem
    cubicRegularizedQuadraticDiagonal_strongDuality_of_dualMaximizer_of_minimalGradientSquare_pos
    (hM : 0 < M) (hGpos : 0 < G²[g;Hdiag]) {lamStar : ℝ}
    (hmax : IsMaxOn (cubicRegularizedQuadraticDualFunction g H M) Dplus lamStar) :
    sInf (Set.range fun h : E ↦
      (cubicRegularizedQuadraticObjective g H M h : EReal)) =
        cubicRegularizedQuadraticDualFunction g H M lamStar := sorry

-- Proof sketch: solve the shifted quadratic subproblem at the maximizing multiplier `λ*`, using
-- the positivity assumption `G² > 0` and the optimality relations from the strong-duality
-- statement to show that the resolvent point minimizes the primal cubic objective.
/-- Under the hypotheses of
`cubicRegularizedQuadraticDiagonal_strongDuality_of_dualMaximizer_of_minimalGradientSquare_pos`,
the primal problem admits the explicit global minimizer
`h* = -(H + λ* I)⁻¹ g`. -/
theorem
    cubicRegularizedQuadraticDiagonal_primalMinimizer_of_dualMaximizer_of_minimalGradientSquare_pos
    (hM : 0 < M) (hGpos : 0 < G²[g;Hdiag]) {lamStar : ℝ}
    (hmax : IsMaxOn (cubicRegularizedQuadraticDualFunction g H M) Dplus lamStar) :
    IsMinOn (cubicRegularizedQuadraticObjective g H M) Set.univ
      (-((H + lamStar • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹).mulVec g) := sorry

/- The source formula `τ(λ*) = 4 λ* |λ*| / M²` is already the exact owner theorem
`cubicRegularizedQuadraticTauMinimizer_def`. -/
recall cubicRegularizedQuadraticTauMinimizer_def

end
