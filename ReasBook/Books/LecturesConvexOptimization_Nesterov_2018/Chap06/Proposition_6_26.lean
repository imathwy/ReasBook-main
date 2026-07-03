import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {X : Type u} {U : Type v}

/- Proposition 6.26 lies in the Chapter 6 scalar duality-gap / smoothing-parameter algebra domain.

Mandatory domain-style sampling before refinement:
- `raw_duality_gap_le_excessive_gap_budget` in `Chap06/Lemma_6_2_1`, the chapter owner turning an
  excessive-gap certificate into the source-level budget estimate
  `f xBar - φ uBar ≤ μ₁ D₁ + μ₂ D₂`;
- `scaled_smoothing_parameter_product_eq` in `Chap06/Proposition_6_28`, the nearby scalar owner
  for the same parametrization of `μ₁` and `μ₂`;
- mathlib `Real.sqrt_div` and `Real.sqrt_mul`, the canonical square-root simplification API behind
  the identities `√(D₂ / D₁) * D₁ = √(D₁ D₂)` and `√(D₁ / D₂) * D₂ = √(D₁ D₂)`.

Best owner abstraction:
- source-facing: the raw duality-gap estimate obtained after substituting the symmetric
  parametrization of the smoothing parameters;
- core/canonical: a single real inequality for `f xBar - φ uBar`;
- bridge/view: the budget expression `μ₁ D₁ + μ₂ D₂` rewritten via the defining formulas for `μ₁`
  and `μ₂`.

Primitive data:
- the primal and dual objective values `f xBar` and `φ uBar`;
- the positive constants `D₁` and `D₂`;
- the induced norm value `‖A‖_{1,2}`, recorded directly as the scalar `opNorm12`;
- the smoothing parameters `μ₁` and `μ₂`.

Derived API:
- the symmetric bound `(λ₁ + λ₂) ‖A‖_{1,2} √(D₁ D₂)` obtained by substituting the parametrization
  into the budget estimate.

Source/core/bridge triage:
- source-facing: Proposition 6.26's symmetric duality-gap estimate under parametrization;
- core/canonical: the scalar theorem below;
- bridge/view: the substitution of the parametrized smoothing parameters into the raw budget.

The source mentions a linear operator `A`, but only its induced norm `‖A‖_{1,2}` enters the
statement. Following the statement-stage binder minimization rule, the Lean theorem keeps only this
norm value as explicit data. -/

-- Proof sketch: substitute the defining formulas for `μ₁` and `μ₂` into the assumed bound
-- `f xBar - φ uBar ≤ μ₁ D₁ + μ₂ D₂`, simplify
-- `Real.sqrt (D₂ / D₁) * D₁ = Real.sqrt (D₁ * D₂)` and
-- `Real.sqrt (D₁ / D₂) * D₂ = Real.sqrt (D₁ * D₂)` using `hD₁` and `hD₂`, and then factor out
-- the common term `opNorm12 * Real.sqrt (D₁ * D₂)`.
/-- Proposition 6.26 [Chapter6_2.json:74]: if the raw duality gap is bounded by `μ₁ D₁ + μ₂ D₂`
and the smoothing parameters satisfy
`μ₁ = λ₁ ‖A‖_{1,2} √(D₂ / D₁)` and `μ₂ = λ₂ ‖A‖_{1,2} √(D₁ / D₂)`,
then the gap is bounded by `(λ₁ + λ₂) ‖A‖_{1,2} √(D₁ D₂)`. -/
theorem raw_duality_gap_le_symmetric_bound_of_parametrized_smoothing_parameters
    {f : X → ℝ} {φ : U → ℝ} {xBar : X} {uBar : U}
    {D₁ D₂ lambda₁ lambda₂ μ₁ μ₂ opNorm12 : ℝ}
    (hD₁ : 0 < D₁) (hD₂ : 0 < D₂)
    (hμ₁ : μ₁ = lambda₁ * opNorm12 * Real.sqrt (D₂ / D₁))
    (hμ₂ : μ₂ = lambda₂ * opNorm12 * Real.sqrt (D₁ / D₂))
    (hgap : f xBar - φ uBar ≤ μ₁ * D₁ + μ₂ * D₂) :
    f xBar - φ uBar ≤ (lambda₁ + lambda₂) * opNorm12 * Real.sqrt (D₁ * D₂) := sorry

end
