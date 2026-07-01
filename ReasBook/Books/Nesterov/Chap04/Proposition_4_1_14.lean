import Mathlib
import Nesterov.Chap04.Proposition_4_1_13

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 4.1.14 lies in the cubic-regularized quadratic / scalar-duality domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticObjective`, `cubicRegularizedQuadraticDualFunction`, and
  `cubicRegularizedQuadraticDualDomain` in `Theorem_4_1_11`, the chapter owners of the primal
  cubic model and scalar dual problem;
* `cubicRegularizedQuadratic_resolvent_norm_eq_of_dualMaximizer` in `Proposition_4_1_13`, the
  owner theorem for the step-length identity attached to a symmetric Hessian and dual maximizer;
* `cubicRegularizedQuadratic_resolvent_isMinimizer_of_dualMaximizer` in `Proposition_4_1_13`,
  the owner theorem identifying the same resolvent point as a primal minimizer;
* `Matrix.leastEigenvalue` and the notation `λ_min(H)` in `Definition_4_1_6`, the chapter owner
  for the least-eigenvalue quantity of a real symmetric matrix;
* `posPart_def`, the canonical bridge rewriting `x⁺` as `max x 0`.

Best owner abstraction:
* source-facing: a chosen point `hStar` with the textbook resolvent representation
  `hStar = -(H + λ* I)⁻¹ g`, together with the derived step length `r := ‖hStar‖`;
* core/canonical: the objective/dual/domain family together with the symmetry and interior
  spectral hypotheses on `H`;
* bridge/view: the dual-maximizer-to-resolvent theorems from `Proposition_4_1_13`.

Primitive data:
* `g`, `H`, `M`, `hH : H.IsSymm`, a dual maximizer `lamStar`, and the interior condition
  `-λ_min(H) < lamStar`;
* a chosen point `hStar` identified with the canonical resolvent point.

Derived API:
* the norm identity `‖hStar‖ = (2 / M) λ*`;
* the fixed-point reformulation for `r := ‖hStar‖`;
* the spectral lower bound for that same `r`.

Source/core/bridge triage:
* source-facing: the three textbook conclusions about `r := ‖hStar‖`;
* core/canonical: the dual-maximizer owner theorems from `Proposition_4_1_13`;
* bridge/view: the equality `hStar = -(H + λ* I)⁻¹ g`.

This file therefore keeps Proposition 4.1.14 at the chosen-minimizer / step-length layer, while
reusing `Proposition_4_1_13` as the proof engine instead of restating a second dual-owner theorem.
-/

section

variable (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ)

local notation "ψ" => cubicRegularizedQuadraticDualFunction g H M
local notation "Dplus" => cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici (0 : ℝ)
local notation "A" lam => H + lam • (1 : Matrix (Fin n) (Fin n) ℝ)
local notation "resolvent" lam => -Matrix.mulVec ((A lam)⁻¹) g

variable {lamStar : ℝ}

-- Proof sketch: rewrite the chosen point `hStar` by the resolvent representation and then apply
-- `cubicRegularizedQuadratic_resolvent_norm_eq_of_dualMaximizer`.
/-- Proposition 4.1.14 (1): if the chosen point `hStar` is represented by
`hStar = -(H + λ* I)⁻¹ g` and `r := ‖hStar‖`, then `r = (2 / M) λ*`. -/
theorem cubicRegularizedQuadratic_stepLength_eq
    (hM : 0 < M) (hH : H.IsSymm)
    (hmax : IsMaxOn ψ Dplus lamStar)
    (hlam : -λ_min(H) < lamStar)
    (hStar : E) (hhStar : hStar = resolvent lamStar) :
    let r := ‖hStar‖
    r = (2 / M : ℝ) * lamStar := sorry

-- Proof sketch: Proposition 4.1.14 (1) identifies `r` with `(2 / M) λ*`, so
-- `(M * r) / 2 = λ*`. Substituting that identity into the resolvent formula yields the claimed
-- fixed-point relation.
/-- Proposition 4.1.14 (2): if `hStar = -(H + λ* I)⁻¹ g` and `r := ‖hStar‖`, then
`r = ‖-(H + (M r / 2) I)⁻¹ g‖`. -/
theorem cubicRegularizedQuadratic_stepLength_fixedPoint
    (hM : 0 < M) (hH : H.IsSymm)
    (hmax : IsMaxOn ψ Dplus lamStar)
    (hlam : -λ_min(H) < lamStar)
    (hStar : E) (hhStar : hStar = resolvent lamStar) :
    let r := ‖hStar‖
    r = ‖resolvent ((M * r) / 2)‖ := sorry

-- Proof sketch: the maximizer hypothesis gives `0 ≤ λ*`, while `hlam` yields
-- `-λ_min(H) ≤ λ*`. Hence `(-λ_min(H))⁺ ≤ λ*`. Multiply by the nonnegative factor `2 / M` and
-- use Proposition 4.1.14 (1).
/-- Proposition 4.1.14 (3): if `hStar = -(H + λ* I)⁻¹ g` and `r := ‖hStar‖`, then
`(2 / M) (-λ_min(H))_+ ≤ r`. -/
theorem cubicRegularizedQuadratic_stepLength_lower_bound
    (hM : 0 < M) (hH : H.IsSymm)
    (hmax : IsMaxOn ψ Dplus lamStar)
    (hlam : -λ_min(H) < lamStar)
    (hStar : E) (hhStar : hStar = resolvent lamStar) :
    let r := ‖hStar‖
    (2 / M : ℝ) * (-λ_min(H))⁺ ≤ r := sorry

end
