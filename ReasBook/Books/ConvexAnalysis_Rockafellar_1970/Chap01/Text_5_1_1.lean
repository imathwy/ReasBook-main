import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.1.1 says that `h(x) = e^{f(x)}` is a proper convex function whenever
  `f` is.
- `core/canonical`: the owner abstractions are `Function.IsProper.comp_extendBotTop` for
  properness and `Function.IsConvex.comp_toWithTopBot_extendBotTop_of_monotone` for
  convexity,
  both on the canonical `WithTopBot ℝ` codomain.
- `bridge/view`: the outer exponential is the finite branch `Real.exp`, seen on the extended
  codomain through `((Real.exp).toWithTopBot).extendBotTop`.

Domain-style sampling used here:
- `Function.IsProper` and `Function.IsProper.comp_extendBotTop` from `Definition_4_6`;
- `Function.IsConvex` from `Theorem_4_2`, reused through `Theorem_5_1`;
- `Function.IsConvex.comp_toWithTopBot_extendBotTop_of_monotone` from `Theorem_5_1`;
- the canonical codomain lift `Function.toWithTopBot` and boundary-preserving extension
  `Function.extendBotTop`.

Primitive data vs derived API:
- primitive data: the finite outer branch `Real.exp`;
- derived API: properness and convexity of the canonical composite.

Layer target: `source-facing`, expressed directly through the chapter owners rather than through a
parallel exponential-specific wrapper API.
-/

private theorem exp_convexOn_univ :
    ConvexOn ℝ (Set.univ : Set ℝ) Real.exp := by
  simpa using (convexOn_exp : ConvexOn ℝ Set.univ Real.exp)

variable {E : Type u}

namespace Function

section Convex

/- Properness branch for Text 5.1.1 on the canonical owner surface. -/
theorem IsProper.comp_exp {f : E → WithTopBot ℝ} (hf : f.IsProper) :
    ((((Real.exp).toWithTopBot).extendBotTop) ∘ f).IsProper := by
  simpa using hf.comp_extendBotTop Real.exp

variable [AddCommMonoid E] [Module ℝ E]

set_option maxHeartbeats 800000 in
/-- Convexity branch for Text 5.1.1 on the canonical owner surface. -/
theorem IsConvex.comp_exp {f : E → WithTopBot ℝ} (hf : f.IsConvex ℝ) :
    ((((Real.exp).toWithTopBot).extendBotTop) ∘ f).IsConvex ℝ := by
  simpa using hf.comp_toWithTopBot_extendBotTop_of_monotone
    exp_convexOn_univ Real.exp_monotone

/-- Text 5.1.1: if `f : E → WithTopBot ℝ` is proper and convex, then the canonical exponential
composite `((Real.exp).toWithTopBot).extendBotTop ∘ f` is again a proper convex function. This is
the project-level `WithTopBot ℝ` owner form of the textbook statement `h(x) = e^{f(x)}`. -/
theorem exp_comp_isProper_and_isConvex
    {f : E → WithTopBot ℝ} (hf_proper : f.IsProper) (hf_convex : f.IsConvex ℝ) :
    ((((Real.exp).toWithTopBot).extendBotTop) ∘ f).IsProper ∧
      ((((Real.exp).toWithTopBot).extendBotTop) ∘ f).IsConvex ℝ := by
  exact ⟨hf_proper.comp_exp, hf_convex.comp_exp⟩

end Convex

end Function

end
