import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Nesterov.Chap05.Definition_5_3_2
import Nesterov.Chap05.Theorem_5_1_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u}

/- Theorem 5.3.5 lies in the Chapter 5 self-concordant-barrier / epigraph-lifting domain.

Sampled owner declarations in this domain:
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for barrier data;
* `sublevelLogBarrier` and `sublevelLogBarrier_isSelfConcordantOnWith` from `Theorem_5_1_4`, the
  canonical strict-sublevel logarithmic-barrier owner and theorem;
* `constrainedEpigraph` from `Chap03/Definition_3_3`, the chapter owner for the closed epigraph,
  whose naming pattern determines the strict epigraph owner in this file;
* mathlib `WithLp 2 (E × ℝ)` together with `WithLp.ofLp`, which supplies the canonical `L²`
  product owner and its bridge back to raw pairs;
* `selfConcordantBarrier_add_linear_isStandardSelfConcordantOn` from `Theorem_5_3_1`, the
  canonical self-concordance theorem for adding a linear term.

Source/core/bridge triage:
* source-facing: the textbook strict epigraph domain on raw pairs and the barrier
  `(x, t) ↦ f x - log (t - f x)`;
* core/canonical: `IsSelfConcordantBarrierOnWith` on the canonical `L²` product owner
  `WithLp 2 (E × ℝ)`;
* bridge/view: the raw-pair formulas transported to that owner through `WithLp.ofLp`.

Primitive data:
* the base domain `dom`;
* the base barrier `f`;
* the barrier parameter `ν`;
* the owner witness `h : IsSelfConcordantBarrierOnWith dom ν f`.

Derived API:
* the source-facing raw-pair strict epigraph `strictConstrainedEpigraph dom f`;
* the source-facing raw-pair barrier `epigraphLogBarrier f`.

This file keeps the strict epigraph domain and barrier as source-facing raw-pair data, but the
main numbered theorem lives on the canonical `L²` product owner `WithLp 2 (E × ℝ)`, so the
barrier statement uses the textbook formulas only through the raw-pair bridge `WithLp.ofLp`. -/

/-- The strict epigraph `{(x, t) | x ∈ dom ∧ f x < t}` on raw pairs. -/
def strictConstrainedEpigraph (dom : Set E) (f : E → ℝ) : Set (E × ℝ) :=
  {p | p.1 ∈ dom ∧ f p.1 < p.2}

/-- Membership in `strictConstrainedEpigraph dom f` is the textbook strict epigraph condition. -/
@[simp] theorem mem_strictConstrainedEpigraph_iff
    {dom : Set E} {f : E → ℝ} {p : E × ℝ} :
    p ∈ strictConstrainedEpigraph dom f ↔ p.1 ∈ dom ∧ f p.1 < p.2 :=
  Iff.rfl

/-- The textbook epigraph barrier on raw pairs `(x, t) ↦ f x - log (t - f x)`, implemented as
the sum of the base term `x ↦ f x` and the canonical strict-sublevel barrier for the epigraph
gap `f x - t`. -/
def epigraphLogBarrier (f : E → ℝ) : E × ℝ → ℝ :=
  fun p ↦ f p.1 + sublevelLogBarrier (fun q : E × ℝ ↦ f q.1 - q.2) 0 p

/-- Evaluating `epigraphLogBarrier f` recovers the textbook raw-pair formula. -/
@[simp] theorem epigraphLogBarrier_apply (f : E → ℝ) (p : E × ℝ) :
    epigraphLogBarrier f p = f p.1 - Real.log (p.2 - f p.1) :=
  by
    simp [epigraphLogBarrier, sublevelLogBarrier, sub_eq_add_neg, add_comm]

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "Z" => WithLp 2 (E × ℝ)
local notation "ofZ" => (WithLp.ofLp : Z → E × ℝ)

-- Proof sketch: regard `z ↦ f (ofZ z).1` as the pullback of the given barrier along the first
-- projection on the canonical `L²` product owner `Z = WithLp 2 (E × ℝ)`, and regard
-- `sublevelLogBarrier (fun q ↦ f q.1 - q.2) 0` as the logarithmic barrier of the strict
-- sublevel set of the epigraph gap. The pullback theorem, the logarithmic-barrier theorem, and
-- the barrier-sum theorem then give a self-concordant barrier with parameter `ν + 1` on the
-- pulled-back strict epigraph domain.
/-- Theorem 5.3.5: if `f` is a `ν`-self-concordant barrier on `dom`, then
the textbook epigraph barrier, viewed on the canonical `L²` product owner
`WithLp 2 (E × ℝ)` through `WithLp.ofLp`, is a `(\nu + 1)`-self-concordant barrier on the
strict epigraph domain. -/
theorem epigraphLogBarrier_isSelfConcordantBarrierOnWith
    {dom : Set E} {ν : NNReal} {f : E → ℝ}
    (h : IsSelfConcordantBarrierOnWith dom ν f) :
    IsSelfConcordantBarrierOnWith
      (ofZ ⁻¹' strictConstrainedEpigraph dom f)
      (ν + 1)
      (epigraphLogBarrier f ∘ ofZ) := sorry

end
