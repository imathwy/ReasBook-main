import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_19_17 (from Items/Chap19) -/
universe u

noncomputable section

namespace ProbabilityTheory

variable {E : Type u} [Fintype E]

/- Definition 19.17 (1): for a chosen flow `I`, the textbook effective conductance toward `A₁`
is the canonical boundary current `netFlowOnSet I A₁`. This item is therefore a bridge to the
owner declaration `netFlowOnSet`, not a second owner-level definition. -/
recall ProbabilityTheory.netFlowOnSet {E : Type u} [Fintype E] (I : E → E → ℝ) (A₁ : Set E) : ℝ

/- Definition 19.17 (2): for the same chosen flow `I`, the textbook effective resistance toward
`A₁` is the reciprocal `1 / netFlowOnSet I A₁`. -/
#check fun (I : E → E → ℝ) (A₁ : Set E) ↦ (1 / netFlowOnSet I A₁ : ℝ)

end ProbabilityTheory
