import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Lemma_5_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 5.3.7 lies in the Chapter 5 self-concordant-barrier / concavity-transform domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for a
  `ν`-self-concordant barrier;
* `IsSelfConcordantBarrierOnWith.concaveOn_exp_neg_div` in `Lemma_5_3_1`, the owner-level
  concavity companion for the exponential transform;
* `isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div` in `Lemma_5_3_1`, the canonical
  source-facing equivalence between the barrier owner and concavity of `x ↦ exp (-(F x / ν))`;
* `ConvexOn.lower_tangent_plane` in `Chap02/Definition_2_2`, together with mathlib
  `ConcaveOn.neg`, which give the canonical first-order tangent inequality for the concave
  exponential transform by passing to its negative.

Best owner abstraction:
* source-facing: Theorem 5.3.7's logarithmic lower Taylor bound for a standard
  self-concordant function;
* core/canonical: `IsSelfConcordantBarrierOnWith dom ν F`;
* bridge/view: `isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div`, followed by the
  first-order tangent inequality for the concave exponential transform.

Primitive data:
* the domain `dom`;
* the function `F`;
* the standard self-concordance owner `hFsc`;
* the positive barrier parameter hypothesis `hν`.

Derived API:
* the barrier owner `IsSelfConcordantBarrierOnWith dom ν F`;
* concavity of `x ↦ exp (-(F x / ν))` on `dom`;
* the source-facing logarithmic lower Taylor bound together with positivity of its logarithm
  argument.

Source/core/bridge triage:
* source-facing: the numbered equivalence in Theorem 5.3.7;
* core/canonical: `IsSelfConcordantBarrierOnWith dom ν F`;
* bridge/view: the exponential-transform concavity criterion from `Lemma_5_3_1`.

This refinement deletes the previous isolated segment-gradient helper lemmas, which had no
downstream users and duplicated the chapter's canonical concavity route. The file now keeps only
the source-facing theorem and states it directly through the existing owner abstraction. -/

-- Proof sketch: apply
-- `isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div` from Lemma 5.3.1 to replace the
-- barrier condition by concavity of `x ↦ exp (-(F x / ν))`. Pass to the negative function and use
-- the Chapter 2 owner `ConvexOn.lower_tangent_plane` to obtain the affine support bound at `x`;
-- then rewrite the gradient by the chain rule, simplify the exponential factor, and take
-- logarithms after first recording positivity of the logarithm argument. The converse follows by
-- exponentiating the displayed logarithmic inequality to recover the same tangent inequality for
-- the exponential transform, hence concavity, and then invoking the owner equivalence from
-- Lemma 5.3.1.
/-- Theorem 5.3.7: for a standard self-concordant function `F`, being a
`ν`-self-concordant barrier is equivalent to the logarithmic lower Taylor bound
`F(y) ≥ F(x) - ν log (1 - ν⁻¹ ⟪∇ F(x), y - x⟫)` on the domain, together with the required
positivity of the logarithm argument. -/
theorem isSelfConcordantBarrierOnWith_iff_logarithmic_taylor_lower_bound
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hFsc : IsStandardSelfConcordantOn dom F) (hν : 0 < (ν : ℝ)) :
    IsSelfConcordantBarrierOnWith dom ν F ↔
      ∀ {x y : E} (hx : x ∈ dom) (hy : y ∈ dom),
        let t := 1 - (1 / (ν : ℝ)) * inner ℝ (∇ F x) (y - x)
        0 < t ∧ F y ≥ F x - (ν : ℝ) * Real.log t := sorry

end
