import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_17
import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_6_29_6

noncomputable section

open scoped Rockafellar

universe u v w

namespace Bifunction

section

variable {U : Type u} {X : Type v} {α : Type w}
variable [ConditionallyCompleteLattice α] [Zero U]

/-!
Source/core/bridge triage:

- `source-facing`: Lemma 6.29.7 says that a generalized convex program cannot have a finite
  optimal value unless its objective `F₀` is proper.
- `core/canonical`: the owner theorem should live on chapter owners
  `Bifunction.IsConsistent`/`Bifunction.optimalValue` together with the Chapter 1 properness owner
  `Function.IsProper`.
- `bridge/view`: finite-optimal-value hypotheses are a derived route to consistency via
  `isConsistent_of_optimalValue_lt_top`.

Domain-style sampling used here:
- `Bifunction.IsConsistent`;
- `Bifunction.isConsistent_iff_dom_objective_nonempty`;
- `Bifunction.isConsistent_of_optimalValue_lt_top`;
- `Bifunction.optimalValue` and `optimalValue_eq_iInf`;
- `iInf_le`;
- `Function.IsProper` and `Function.isProper_iff_nonempty_dom_and_bot_lt`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → WithBotTop α`;
- primitive owner hypotheses: program consistency `IsConsistent F` and the lower bound
  `⊥ < optimalValue F`;
- derived bridge hypothesis: the upper bound `optimalValue F < ⊤`, converted to consistency using
  `isConsistent_of_optimalValue_lt_top`;
- derived conclusion: properness of `(F)₀`.

Layer target:
- a primitive `core/canonical` theorem stated on `IsConsistent F` and `optimalValue F`;
- the source-facing finite-optimal-value statement as a thin bridge corollary.
-/

-- Proof sketch (core): consistency provides nonempty `dom((F)₀)` via
-- `isConsistent_iff_dom_objective_nonempty`; then the pointwise lower bound follows from
-- `optimalValue F = ⨅ y, (F)₀ y` and `optimalValue F ≤ (F)₀ y`.
/-- Core owner form: if the generalized convex program attached to `F` is consistent and the
optimal value is strictly above `⊥`, then the objective `F₀` is proper. -/
theorem objective_isProper_of_isConsistent_and_optimalValue_bot_lt
    {F : U → X → WithBotTop α}
    (hcons : IsConsistent F)
    (hbot : ⊥ < optimalValue F) :
    ((F)₀).IsProper := by
  rw [Function.isProper_iff_nonempty_dom_and_bot_lt]
  refine ⟨(isConsistent_iff_dom_objective_nonempty F).1 hcons, ?_⟩
  intro y
  exact lt_of_lt_of_le hbot <| by
    rw [optimalValue_eq_iInf]
    exact iInf_le (F)₀ y

-- Proof sketch (bridge): convert `optimalValue F < ⊤` to consistency using
-- `isConsistent_of_optimalValue_lt_top`, then apply the core theorem above.
/-- Lemma 6.29.7, canonical owner form: if the optimal value of the generalized convex program
attached to `F` is finite, then its objective function `F₀` is proper. -/
theorem objective_isProper_of_optimalValue_bounds
    {F : U → X → WithBotTop α}
    (hbot : ⊥ < optimalValue F)
    (htop : optimalValue F < ⊤) :
    ((F)₀).IsProper := by
  exact objective_isProper_of_isConsistent_and_optimalValue_bot_lt
    (isConsistent_of_optimalValue_lt_top htop) hbot

/-- Lemma 6.29.7, source-facing finite-optimal-value form. -/
theorem objective_isProper_of_optimalValue_finite
    {F : U → X → WithBotTop α}
    (hopt : ⊥ < optimalValue F ∧ optimalValue F < ⊤) :
    ((F)₀).IsProper := by
  exact objective_isProper_of_optimalValue_bounds hopt.1 hopt.2

end

end Bifunction
