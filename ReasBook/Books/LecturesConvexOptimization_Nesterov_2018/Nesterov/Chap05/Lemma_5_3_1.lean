import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_3_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The ambient exponential transform attached to a barrier candidate `F` and positive parameter
`p`. -/
def barrierExponentialTransform (p : NNRealˣ) (F : E → ℝ) : E → ℝ :=
  fun x ↦ Real.exp (-F x / (p : ℝ))

/- Lemma 5.3.1 lies in the Chapter 5 self-concordant-barrier / exponential-transform domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantOnWith` and `IsStandardSelfConcordantOn` in `Definition_5_1_1`, the chapter
  owners for self-concordance on an open convex domain;
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for a
  `ν`-self-concordant barrier;
* `_root_.barrier_parameter_bound_iff_gradient_inner_sq_le` in `Proposition_5_3_3`, the
  canonical pointwise reformulation of the barrier inequality;
* `isSelfConcordantBarrierOnWith_iff_logarithmic_taylor_lower_bound` in `Theorem_5_3_7`, the
  later source-facing barrier characterization obtained from the same owner.

Best owner abstraction:
* core/canonical: `IsSelfConcordantBarrierOnWith`;
* source-facing: the numbered equivalence between the barrier owner and concavity of the
  exponential transform when the underlying function is already standard self-concordant;
* bridge/view: the ambient exponential-transform owner
  `barrierExponentialTransform p F` together with the owner-level concavity theorem for barrier
  parameters `p ≥ ν`.

Primitive data:
* a domain `dom`;
* a function `F`;
* a barrier parameter `p`;
* the ambient exponential transform `barrierExponentialTransform p F` for `p : NNRealˣ`;
* either the barrier owner `IsSelfConcordantBarrierOnWith dom ν F` or the standard
  self-concordance owner `IsStandardSelfConcordantOn dom F` together with the displayed concavity
  condition.

Derived API:
* concavity of `barrierExponentialTransform p F` for every positive `p ≥ ν`;
* the source-facing equivalence at `p = ν`.

Source/core/bridge triage:
* source-facing: the equivalence in Lemma 5.3.1;
* core/canonical: `IsSelfConcordantBarrierOnWith dom ν F`;
* bridge/view: owner-level concavity of the exponential transform.

This refinement therefore places the auxiliary concavity statement in the barrier owner namespace
and leaves the numbered equivalence as the public source-facing theorem. -/

namespace IsSelfConcordantBarrierOnWith

-- Proof sketch: compute the Hessian quadratic form of `x ↦ exp (-(F x / p))`; the displayed
-- formula in the text shows that concavity follows from the barrier inequality with parameter
-- `ν`, and if `p ≥ ν` then the same estimate remains valid with `p` in place of `ν`.
/-- If `F` is a `ν`-self-concordant barrier on `dom`, then every exponential transform
`x ↦ exp (-(F x / p))` with positive `p ≥ ν` is concave on `dom`. This is the owner-level concavity
companion to Lemma `5.3.1`. -/
theorem concaveOn_exp_neg_div
    {dom : Set E} {ν : NNReal} {p : NNRealˣ} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith dom ν F) (hνp : ν ≤ (p : NNReal)) :
    ConcaveOn ℝ dom (barrierExponentialTransform p F) := sorry

end IsSelfConcordantBarrierOnWith

-- Proof sketch: for the forward implication, specialize the Hessian computation of
-- `x ↦ exp (-(F x / ν))` and rewrite the concavity condition as the barrier inequality from
-- Definition 5.3.2. For the reverse implication, the same computation turns concavity of
-- `x ↦ exp (-(F x / ν))` into the barrier-parameter bound, while the standard self-concordance
-- assumption supplies the remaining part of the barrier structure. The positivity hypothesis on
-- `ν` is essential, because the owner-level transform in the auxiliary API is only defined for a
-- positive parameter, but the numbered equivalence is stated directly with the textbook function
-- `x ↦ exp (-(F x / ν))`.
/-- Lemma 5.3.1: for a standard self-concordant function `F` on `dom` and a positive barrier
parameter `ν`, being a `ν`-self-concordant barrier is equivalent to concavity of the exponential
transform `x ↦ exp (-(F x / ν))` on `dom`. -/
theorem isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hFsc : IsStandardSelfConcordantOn dom F) (hν : 0 < (ν : ℝ)) :
    IsSelfConcordantBarrierOnWith dom ν F ↔
      ConcaveOn ℝ dom (fun x ↦ Real.exp (-(F x / (ν : ℝ)))) := sorry

end
