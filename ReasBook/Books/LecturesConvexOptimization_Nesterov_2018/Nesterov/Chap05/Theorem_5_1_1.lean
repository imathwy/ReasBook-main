import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 5.1.1 lies in the Chapter 5 self-concordance calculus domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the chapter owner for self-concordance on an
  open convex domain;
* mathlib `ContDiffOn.add` and `ConvexOn.add`, the canonical additive calculus owners reused by
  self-concordance proofs;
* `quadraticAffineObjective_isSelfConcordantOnWith_zero` from `Example_5_1_2`, the canonical
  zero-self-concordance perturbation owner used downstream in Corollary 5.1.2;
* `IsSelfConcordantOnWith.comp_continuousAffineMap` from `Theorem_5_1_2`, the nearby owner-level
  closure theorem showing the same namespace pattern for derived self-concordance calculus.

Source/core/bridge triage:
* source-facing: the weighted-sum closure theorem for self-concordant functions;
* core/canonical: the owner predicate `IsSelfConcordantOnWith`;
* bridge/view: the unweighted additive specialization `add`.

Primitive data:
* two owner witnesses `h₁ : IsSelfConcordantOnWith dom₁ M₁ f₁` and
  `h₂ : IsSelfConcordantOnWith dom₂ M₂ f₂`;
* positive weights `α` and `β`, carried canonically by `NNRealˣ`.

Derived API:
* the weighted-sum closure theorem itself;
* the additive specialization obtained by setting `α = β = 1`.

The refined file keeps the source-facing weighted theorem as the primary declaration and treats the
plain sum as its thin specialization, rather than as a second independent calculus theorem. -/

namespace IsSelfConcordantOnWith

-- Proof sketch: first rescale each summand by Corollary 5.1.3, which replaces `M₁` and `M₂` by
-- `M₁ / √α` and `M₂ / √β`. Then apply `add` to the rescaled summands on
-- `dom₁ ∩ dom₂`.
/-- Theorem 5.1.1: if `f₁` and `f₂` are self-concordant on `dom₁` and `dom₂` with constants
`M₁` and `M₂`, then for positive weights `α` and `β` the weighted sum
`(α : ℝ) • f₁ + (β : ℝ) • f₂` is self-concordant on the intersection domain `dom₁ ∩ dom₂` with
self-concordance constant `max (M₁ / √α) (M₂ / √β)`. -/
theorem weightedSum
    {dom₁ dom₂ : Set E} {M₁ M₂ : NNReal} {α β : NNRealˣ} {f₁ f₂ : E → ℝ}
    (h₁ : IsSelfConcordantOnWith dom₁ M₁ f₁)
    (h₂ : IsSelfConcordantOnWith dom₂ M₂ f₂) :
    IsSelfConcordantOnWith (dom₁ ∩ dom₂)
      (max (M₁ / NNReal.sqrt α) (M₂ / NNReal.sqrt β))
      ((α : ℝ) • f₁ + (β : ℝ) • f₂) := by
  sorry

-- Proof sketch: specialize `weightedSum` to `α = β = 1`, then simplify the weights, the square
-- roots, and the resulting self-concordance constants.
/-- The owner-level additive specialization of Theorem 5.1.1: if `f₁` and `f₂` are
self-concordant on `dom₁` and `dom₂` with constants `M₁` and `M₂`, then their pointwise sum is
self-concordant on the intersection domain `dom₁ ∩ dom₂` with constant `max M₁ M₂`. -/
theorem add
    {dom₁ dom₂ : Set E} {M₁ M₂ : NNReal} {f₁ f₂ : E → ℝ}
    (h₁ : IsSelfConcordantOnWith dom₁ M₁ f₁)
    (h₂ : IsSelfConcordantOnWith dom₂ M₂ f₂) :
    IsSelfConcordantOnWith (dom₁ ∩ dom₂) (max M₁ M₂) (f₁ + f₂) := by
  have hsum :
      IsSelfConcordantOnWith (dom₁ ∩ dom₂)
        (max (M₁ / NNReal.sqrt (1 : NNRealˣ)) (M₂ / NNReal.sqrt (1 : NNRealˣ)))
        (((1 : NNRealˣ) : ℝ) • f₁ + ((1 : NNRealˣ) : ℝ) • f₂) :=
    h₁.weightedSum h₂
  simpa using hsum

end IsSelfConcordantOnWith

end
