import Mathlib
import Nesterov.Chap05.Definition_5_4_6_7
import Nesterov.Chap05.Theorem_5_4_6_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm

noncomputable section

universe u v w

/- Theorem 5.4.6.8 lies in the subsection's composed Hessian / local-norm domain.

Sampled owner declarations:
* `hessian` in `Chap01/Definition_1_4_16`, the canonical owner for `∇² Φ`;
* `hessianLocalNorm` / `‖h‖[Φ; p]` in `Definition_5_1_1`, the canonical owner for the square root
  of the Hessian quadratic form;
* `(hessian Φ p).IsPositive` from mathlib's `ContinuousLinearMap.IsPositive` API, together with
  the chapter's `IsSelfConcordantOnWith.hessian_isPositive`, the canonical pointwise
  Hessian-positivity owner and the upstream bridge from self-concordance to that owner;
* `compositionPotentialSigmaOne` and `compositionPotentialSigmaTwo` in `Theorem_5_4_6_5`, the
  source-facing `σ₁` and `σ₂` terms in the subsection;
* `compositionSecondLiftedDirectionDerivative` in `Definition_5_4_6_7`, the bridge realizing the
  lifted derivative direction `l' = (D²ξ(x)[d, d], 0)`;
* the specialized owner-level estimate `‖-l'‖[Φ; (ξ(x), z)] ≤ σ₂`, which is the only `(5.3.13)`
  input used in this cross-term bound.

Source/core/bridge triage:
* source-facing: the cross-term estimate `⟪∇² Φ(ξ(x), z) l, l'⟫ ≤ σ₁^(1/2) σ₂`;
* core/canonical: `(hessian Φ (ξ x, z)).IsPositive`, `hessian Φ (ξ x, z)`, and
  `‖·‖[Φ; (ξ x, z)]`;
* bridge/view: the canonical lifted pair `(fderiv ℝ ξ x d, 0)` and
  `compositionSecondLiftedDirectionDerivative ξ x d`.

Primitive data:
* the map `ξ`, point `x`, direction `d`, and auxiliary point `z`;
* pointwise positivity of the Hessian at `(ξ x, z)`;
* the specialized local-norm estimate for `-l'`.

Derived API:
* the lifted direction `l = (Dξ(x)[d], 0)`;
* the source-facing scalar terms `σ₁` and `σ₂`;
* the local self-concordance bridge hypothesis only when a larger subsection needs to derive the
  pointwise positivity owner above from a domain-level assumption.

The public statement should therefore use the pointwise Hessian-positivity owner together with the
owner-level Hessian and Hessian local norm, rather than carrying redundant self-concordance and
interior-membership assumptions whose only role was to derive this local positivity. -/

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
  [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)]

-- Proof sketch: the pointwise positivity hypothesis on `hessian Φ (ξ x, z)` makes the Hessian
-- local norm a genuine seminorm at `(ξ x, z)`, so Cauchy--Schwarz applies to the Hessian-induced
-- pairing. Bound the mixed Hessian term by
-- `‖(fderiv ℝ ξ x d, 0)‖[Φ; (ξ x, z)] *
-- ‖-compositionSecondLiftedDirectionDerivative ξ x d‖[Φ; (ξ x, z)]`, rewrite the first factor as
-- `σ₁^(1/2)`, and use the specialized `(5.3.13)` estimate for
-- `-compositionSecondLiftedDirectionDerivative ξ x d` to identify the second factor with `σ₂`.
/-- Theorem 5.4.6.8: if the Hessian of `Φ` at `(ξ(x), z)` is positive and the negative lifted
derivative direction `-l'` satisfies the specialized owner-level estimate
`‖-l'‖[Φ; (ξ(x), z)] ≤ σ₂`, then the cross Hessian term
`⟪∇² Φ(ξ(x), z) (Dξ(x)[d], 0), Dl(x)[d]⟫` is bounded above by `σ₁^(1/2) σ₂`, where
`Dl(x)[d] = compositionSecondLiftedDirectionDerivative ξ x d`,
`σ₁ = ⟪∇² Φ(ξ(x), z) (Dξ(x)[d], 0), (Dξ(x)[d], 0)⟫`, and
`σ₂ = ⟪∇ᵧ Φ(ξ(x), z), D²ξ(x)[d, d]⟫`. -/
theorem compositionPotential_crossTerm_le_sqrt_sigmaOne_mul_sigmaTwo
    {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x d : E₁} {z : E₃}
    (hH : (hessian Φ (ξ x, z)).IsPositive)
    (hneg_liftedDirectionDerivative_le_sigmaTwo :
      ‖-compositionSecondLiftedDirectionDerivative ξ x d‖[Φ; (ξ x, z)] ≤
        compositionPotentialSigmaTwo Φ ξ x z d) :
    inner ℝ (hessian Φ (ξ x, z) (fderiv ℝ ξ x d, (0 : E₃)))
        (compositionSecondLiftedDirectionDerivative ξ x d) ≤
      Real.sqrt (compositionPotentialSigmaOne Φ ξ x z d) *
        compositionPotentialSigmaTwo Φ ξ x z d := sorry

end
