import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_1_6
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Theorem_4_1_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 4.1.13 lies in the cubic-regularized quadratic / scalar-duality domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticObjective` in `Theorem_4_1_11`, the chapter owner of the primal cubic
  model;
* `cubicRegularizedQuadraticDualFunction` and `cubicRegularizedQuadraticDualDomain` in
  `Theorem_4_1_11`, the chapter owners of the scalar dual value and its effective domain;
* `cubicRegularizedQuadraticScalarDualFunction_eq_sInf_quadratic` in `Proposition_4_1_8`, the
  bridge that eliminates the slack variable and reduces the dual value to the shifted quadratic
  subproblem;
* `Matrix.leastEigenvalue` and the notation `λ_min(H)` in `Definition_4_1_6`, the chapter owner
  for the least-eigenvalue quantity of a real matrix;
* `quadraticObjective` in `Chap01/Definition_1_9_1`, the owner of the shifted quadratic
  `h ↦ ⟪g, h⟫ + (1 / 2) ⟪(H + λ I) h, h⟫`.

Best owner abstraction:
* source-facing: the first-order optimality identity and primal-minimizer statement attached to a
  dual maximizer `λ*`;
* core/canonical: `cubicRegularizedQuadraticObjective`, `cubicRegularizedQuadraticDualFunction`,
  `cubicRegularizedQuadraticDualDomain`, the shifted quadratic `quadraticObjective 0 g
  (H + λ • I)`, and the spectral interior condition `-λ_min(H) < λ`;
* bridge/view: the explicit resolvent point `-((H + λ I)⁻¹).mulVec g`.

Primitive data:
* `g`, `H`, `M`, the symmetry hypothesis `H.IsSymm`, and the shifted matrix `H + λ I`;
* dual optimality on `cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici (0 : ℝ)`.

Derived API:
* the explicit resolvent point above;
* the norm identity `‖h*‖ = (2 / M) λ*`;
* the global primal minimizer statement for that same `h*`.

Source/core/bridge triage:
* source-facing: the two textbook consequences for a dual maximizer `λ*`;
* core/canonical: the existing objective/dual owner family from `Theorem_4_1_11`;
* bridge/view: the resolvent formula expressing the source point as `-A⁻¹ g`.

This file therefore stays at the theorem layer and does not introduce a second local owner for the
dual problem or the shifted quadratic subproblem. -/

section

variable (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ)

local notation "Dplus" => cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici (0 : ℝ)
local notation "A" lam => H + lam • (1 : Matrix (Fin n) (Fin n) ℝ)
local notation "resolvent" lam => -Matrix.mulVec ((A lam)⁻¹) g

variable {lamStar : ℝ}
variable (hM : 0 < M) (hH : H.IsSymm)
variable (hmax : IsMaxOn (cubicRegularizedQuadraticDualFunction g H M) Dplus lamStar)
variable (hlam : -λ_min(H) < lamStar)

-- Proof sketch: since `λ*` maximizes `ψ` on `Dplus`, the Hessian is symmetric, and
-- `λ* > -λ_min(H)`, the shifted quadratic owner lies in the positive-definite spectral region.
-- Differentiate the explicit formula for the dual value at interior points, use the resolvent
-- identity for the minimizing `h`-subproblem, and solve `ψ'(λ*) = 0` for the norm of the
-- resolvent point `-((A λ*)⁻¹).mulVec g`.
/-- Proposition 4.1.13: if `λ*` maximizes the dual function `ψ` over `dom ψ ∩ ℝ₊` and the
shifted symmetric Hessian lies in the interior region `λ* > -λ_min(H)`, then the
scalar first-order optimality condition holds:
`‖-(H + λ* I)⁻¹ g‖ = (2 / M) λ*`. -/
theorem cubicRegularizedQuadratic_resolvent_norm_eq_of_dualMaximizer
    (hM : 0 < M) (hH : H.IsSymm)
    (hmax : IsMaxOn (cubicRegularizedQuadraticDualFunction g H M) Dplus lamStar)
    (hlam : -λ_min(H) < lamStar)
    : ‖resolvent lamStar‖ = (2 / M : ℝ) * lamStar := sorry

-- Proof sketch: minimize the quadratic `h`-subproblem in the Lagrangian at the maximizing
-- multiplier `λ*`; the symmetry and spectral-interior hypotheses place `H + λ* I` in the
-- positive-definite quadratic region, so the unique minimizer is `-(H + λ* I)⁻¹ g`. Then
-- combine strong duality at `λ*` with the first-order condition from
-- `cubicRegularizedQuadratic_resolvent_norm_eq_of_dualMaximizer` to conclude that this resolvent
-- point globally minimizes the primal cubic-regularized quadratic objective.
/-- Under the hypotheses of Proposition 4.1.13, the corresponding resolvent point
`-(H + λ* I)⁻¹ g` is a global minimizer of the primal cubic-regularized quadratic objective. -/
theorem cubicRegularizedQuadratic_resolvent_isMinimizer_of_dualMaximizer
    (hM : 0 < M) (hH : H.IsSymm)
    (hmax : IsMaxOn (cubicRegularizedQuadraticDualFunction g H M) Dplus lamStar)
    (hlam : -λ_min(H) < lamStar)
    :
    IsMinOn (cubicRegularizedQuadraticObjective g H M) Set.univ
      (resolvent lamStar) := sorry

end
