import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Nesterov.Chap05.Theorem_5_3_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "Z" => WithLp 2 (E × ℝ)
local notation "ofZ" => (WithLp.ofLp : Z → E × ℝ)

-- Proof sketch: repeat the self-concordance part of Theorem 5.3.5 on the canonical `L²`
-- product owner `Z = WithLp 2 (E × ℝ)`, using the canonical raw-pair bridge `ofZ`. View
-- `z ↦ f (ofZ z).1` as the affine pullback of `f` along the first projection, and view
-- `z ↦ -log ((ofZ z).2 - f (ofZ z).1)` as the logarithmic barrier term for the strict epigraph
-- inequality. The affine-precomposition theorem, the logarithmic-barrier theorem, and the sum
-- theorem yield standard self-concordance on the pulled-back strict epigraph domain, and this
-- argument does not use the barrier-parameter inequality for `f`.
/-- Corollary 5.3.1: if `f` is a standard self-concordant function on `dom`, then the epigraph
barrier, viewed on the canonical `L²` product owner `WithLp 2 (E × ℝ)` through `ofZ`, is also
standard self-concordant on the strict epigraph domain from Theorem 5.3.5. -/
theorem epigraphLogBarrier_isStandardSelfConcordantOn
    {dom : Set E} {f : E → ℝ}
    (h : IsStandardSelfConcordantOn dom f) :
    IsStandardSelfConcordantOn
      (ofZ ⁻¹' strictConstrainedEpigraph dom f)
      (epigraphLogBarrier f ∘ ofZ) := sorry

end
