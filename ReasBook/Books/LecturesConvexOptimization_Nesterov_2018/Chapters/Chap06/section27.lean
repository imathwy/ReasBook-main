import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_27 (from Chap06) -/
noncomputable section

open scoped BigOperators

universe v

/- Definition 6.27 lies in Chapter 6's finite-family log-sum-exp / entropy-smoothing domain.

Primary domain:
- the textbook log-sum-exp potential `η(u)` on a finite score family.

Sampled owner-style declarations:
- `η` in `Chap06/Proposition_6_23`, the existing chapter owner for the textbook log-sum-exp
  potential;
- `eta_apply` in `Chap06/Proposition_6_23`, the upstream coordinate formula for that owner;
- `eta_eq_coordinateMaximum_add_eta_centered` in `Chap06/Proposition_6_23`, the chapter's stable
  max-shift identity for the same log-sum-exp potential;
- `smoothMaxInnerApproximation` in `Chap07/Definition_7_42`, the later affine-score smoothing
  owner built from the same log-sum-exp pattern;
- `logSumExpMaxEigenvalueSmoothing` in `Chap06/Definition_6_47`, the later Chapter 6 smoothing
  owner using the same positive-parameter surface.

Best owner abstraction:
- source-facing/core-canonical: `η`;
- bridge/view: the evaluation theorem `eta_apply`.

Primitive data:
- a finite index type `ι`;
- the positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`;
- the score vector `u : EuclideanSpace ℝ ι`.

Derived API:
- the coordinate formula `eta_apply`.

Since Proposition 6.23 already owns `η` at the positive-parameter layer, this file recalls that
owner directly instead of keeping a second specialization wrapper.
-/

section

variable {ι : Type v} [Fintype ι]

/- Definition 6.27: the textbook finite-family log-sum-exp potential is the canonical Chapter 6
owner `η` for a positive smoothing parameter and a finite score family. -/
recall η

/- Evaluating the recalled owner gives the textbook positive-parameter log-sum-exp formula. -/
recall eta_apply

end

/-! ### Proposition_6_27 (from Chap06) -/
universe u v

section

variable {X : Type u} {U : Type v}

-- Proof sketch: substitute the defining formulas for `μ₁` and `μ₂` into the assumed duality-gap
-- bound, use `D₁ > 0` and `D₂ > 0` to simplify
-- `Real.sqrt (D₂ / D₁) * D₁ = Real.sqrt (D₁ * D₂)` and
-- `Real.sqrt (D₁ / D₂) * D₂ = Real.sqrt (D₁ * D₂)`, and then factor the common term
-- `opNorm12 * Real.sqrt (D₁ * D₂)`.
/-- Proposition 6.27 [Chapter6_1.json:79]: if
`μ₁ = λ₁ ‖A‖_{1,2} √(D₂ / D₁)` and `μ₂ = λ₂ ‖A‖_{1,2} √(D₁ / D₂)`,
then the assumed duality-gap bound
`f(x̄) - φ(ū) ≤ μ₁ D₁ + μ₂ D₂`
implies the symmetric estimate
`f(x̄) - φ(ū) ≤ (λ₁ + λ₂) ‖A‖_{1,2} √(D₁ D₂)`. The positivity assumptions
`λ₁, λ₂ > 0` and `μ₁, μ₂ > 0` from the source are omitted because they are redundant
for the inequality statement itself. -/
theorem duality_gap_le_symmetric_bound_of_parametrized_smoothing_parameters
    {f : X → ℝ} {φ : U → ℝ} {xBar : X} {uBar : U}
    {D₁ D₂ lambda₁ lambda₂ μ₁ μ₂ opNorm12 : ℝ}
    (hD₁ : 0 < D₁) (hD₂ : 0 < D₂)
    (hμ₁ : μ₁ = lambda₁ * opNorm12 * Real.sqrt (D₂ / D₁))
    (hμ₂ : μ₂ = lambda₂ * opNorm12 * Real.sqrt (D₁ / D₂))
    (hgap : f xBar - φ uBar ≤ μ₁ * D₁ + μ₂ * D₂) :
    f xBar - φ uBar ≤ (lambda₁ + lambda₂) * opNorm12 * Real.sqrt (D₁ * D₂) := sorry

end
