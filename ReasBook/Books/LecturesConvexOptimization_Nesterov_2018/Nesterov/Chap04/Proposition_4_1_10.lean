import Mathlib.Tactic.Recall
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Definition_4_1_15
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap04.Proposition_4_1_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section
open scoped CubicRegularizedDiagonalInvariants

variable {n : ℕ} [NeZero n]

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 4.1.10 belongs to the diagonal quadratic-minimization interface.

Sampled owner declarations:
* `quadraticObjective` for the shifted quadratic `q_λ`;
* `UnconstrainedQuadraticMinimizationProblem.minimizer` and
  `UnconstrainedQuadraticMinimizationProblem.minimizer_unique` for the canonical quadratic
  minimizer / uniqueness owner;
* `cubicRegularizedDiagonalMinimum`, `cubicRegularizedMinimalDiagonalIndices`, and
  `cubicRegularizedMinimalDiagonalGradientSquare` for `H_min`, `I*`, and `G²`;
* `cubicRegularizedDiagonalResolvent_isMinOn` in `Proposition_4_1_9`, the upstream owner-level
  minimizer theorem for the diagonal resolvent point.

Source/core/bridge triage:
* source-facing: the coordinate description of the minimizer of `q_λ` in the degenerate case
  `G² = 0`;
* core/canonical: the shifted diagonal quadratic together with its resolvent point
  `-(diag(Hdiag + λ))⁻¹ g`;
* bridge/view: the coordinate formula for that resolvent and the equivalence between being a
  minimizer and satisfying the textbook coordinate formula.

Primitive data:
* the diagonal data `Hdiag`, gradient `g`, and shift `λ`;
* the strict interior inequality `λ > -H_min`.

Derived API:
* the coordinate formula for the diagonal resolvent point;
* the upstream owner-level minimizer theorem for that resolvent;
* the source-facing `iff` statement in the degenerate case `G² = 0`.

This file therefore keeps Proposition 4.1.10 as a source-facing bridge theorem, but exposes the
canonical diagonal resolvent minimizer through the upstream owner theorem in
`Proposition_4_1_9` instead of owning a second copy here. -/

section

variable (g : E) (Hdiag : Fin n → ℝ) (lam : ℝ)

local notation "A" => Matrix.diagonal fun i ↦ Hdiag i + lam

/-- Evaluating the diagonal resolvent point `-(diag(Hdiag + λ))⁻¹ g` gives the coordinate formula
`-g i / (H_i + λ)`. -/
theorem cubicRegularizedDiagonalResolvent_apply
    (hlam : -H_min[Hdiag] < lam) (i : Fin n) :
    (-((A)⁻¹).mulVec g) i = -g i / (Hdiag i + lam) := sorry

/- The owner-level minimizer statement for the diagonal resolvent point is already the upstream
theorem `cubicRegularizedDiagonalResolvent_isMinOn`. -/
recall cubicRegularizedDiagonalResolvent_isMinOn

-- Proof sketch: `λ > -H_min` makes the shifted diagonal Hessian strictly positive, so the
-- shifted quadratic has the canonical resolvent minimizer above. The hypothesis `G² = 0`
-- forces `g i = 0` on `I*`, and the resolvent coordinate formula then reduces exactly to the
-- textbook description `h i = 0` on `I*` and `h i = -g i / (H_i + λ)` off `I*`. Uniqueness of
-- the quadratic minimizer supplies the converse direction.
/-- Proposition 4.1.10: if `G² = 0` and `λ > -H_min`, then a vector `h` minimizes the shifted
diagonal quadratic `q_λ` on `ℝⁿ` exactly when its coordinates satisfy
`h i = 0` on `I*` and `h i = -g i / (H_i + λ)` off `I*`. -/
theorem cubicRegularizedDiagonal_isMinOn_iff
    (hG : G²[g;Hdiag] = 0)
    (hlam : -H_min[Hdiag] < lam)
    (h : E) :
    IsMinOn (quadraticObjective 0 g A) Set.univ h ↔
      ∀ i : Fin n,
        h i =
          if i ∈ I*[Hdiag] then
            0
          else
            -g i / (Hdiag i + lam) := sorry

end
