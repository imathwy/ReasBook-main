import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_1_1
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Lemma_5_1_3
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Corollary_5_1_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 5.1.14 lies in the Chapter 5 self-concordance / recession-direction domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the quantitative Chapter 5 owner for
  self-concordance on a domain;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` from `Definition_5_1_1`, the canonical owner
  for the Hessian local norm;
* `associatedUnivariateFunctionDomain` from `Definition_5_0_12`, the source-facing owner for the
  natural positivity domain of the reciprocal local-norm slice `τ ↦ ‖h‖[f; x + τ • h]⁻¹`;
* `abs_derivWithin_associatedUnivariateFunction_le` from `Lemma_5_1_3`, the source-facing
  derivative bound for that reciprocal local-norm slice on its natural domain;
* `associatedUnivariateFunction_hasDerivWithinAt` from `Lemma_5_1_3`, the auxiliary derivative
  formula behind that bound;
* `associatedUnivariateFunctionDomain_contains_interval` from `Corollary_5_1_4`, the Chapter 5
  interval-control bridge that keeps the ray argument on the canonical slice-domain owner.

Best owner abstraction:
* source-facing: the recession-direction estimate itself, with the textbook backward-frontier and
  nonascent hypotheses left explicit;
* core/canonical: `IsSelfConcordantOnWith dom Mf f` together with `‖h‖[f; x]`;
* bridge/view: the boundary hypothesis on the backward ray and the nonascent pairing
  `inner ℝ (∇ f x) h ≤ 0`.

Primitive data:
* the self-concordant owner `IsSelfConcordantOnWith dom Mf f`;
* the recession direction `h`;
* the chosen base point `x ∈ dom`;
* the backward-frontier hypothesis for the backward ray from `x` along `-h`;
* the nonascent hypothesis for `h` at `x`.

Derived API:
* the local-norm bound `‖h‖[f; x] ≤ M_f ⟪-∇f(x), h⟫`.

The theorem remains source-facing, but its public surface is refined to the Chapter 5 owner API
instead of a long top-level name carrying the owner in its identifier. Its proof route should use
the canonical slice owners `associatedUnivariateFunction` and
`associatedUnivariateFunctionDomain` rather than rebuilding a separate ray package inside this
file. The chapter's lower Taylor remainder bound is already carried by
`Theorem_5_1_8.taylor_lower_bound_of_hessian_loewner_lower`; this file is the distinct
recession-direction item `(5.1.14)`.
-/

namespace IsSelfConcordantOnWith

section

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}

-- Proof sketch: work on the canonical slice owner `associatedUnivariateFunction dom f x h`.
-- Corollary 5.1.4 keeps a whole interval around `0` inside
-- `associatedUnivariateFunctionDomain dom f x h`, and Lemma 5.1.3 gives the derivative bound for
-- the reciprocal local norm on that domain. The recession and backward-frontier hypotheses show
-- that the maximal backward parameter is finite, so integrating the derivative estimate from that
-- endpoint to `0` yields the lower bound on `‖h‖[f; x]⁻¹`, equivalently the displayed upper bound
-- on `‖h‖[f; x]`.
/-- Theorem 5.1.14: if `f` is self-concordant with positive parameter `M_f` on `dom`, the
direction `h` is a recession direction for `dom`, the backward ray `x - τ h` from a chosen point
`x ∈ dom` meets `frontier dom` at finite distance, and `h` is a nonascent direction for `f` at
`x`, then the local Hessian norm of `h` at `x` is bounded by `M_f` times the pairing of `h` with
the negative gradient. -/
theorem hessianLocalNorm_le_neg_gradient_inner_of_recession_direction
    (hself : IsSelfConcordantOnWith dom Mf f) (hMf : 0 < Mf) {h : E}
    (hrecession : ∀ ⦃x : E⦄, x ∈ dom → ∀ t : ℝ, 0 ≤ t → x + t • h ∈ dom)
    {x : E} (hx : x ∈ dom)
    (hfrontier : ∃ τ : ℝ, 0 < τ ∧ x - τ • h ∈ frontier dom)
    (hnonascent : inner ℝ (∇ f x) h ≤ 0) :
    ‖h‖[f; x] ≤ (Mf : ℝ) * inner ℝ (-∇ f x) h := by
  letI : IsSelfConcordantOnWith dom Mf f := hself
  sorry

end

end IsSelfConcordantOnWith

end
