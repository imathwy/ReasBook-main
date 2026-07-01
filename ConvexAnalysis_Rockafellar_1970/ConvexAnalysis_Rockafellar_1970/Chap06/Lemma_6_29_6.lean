import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_15

noncomputable section

universe u v w

namespace Bifunction

section

variable {U : Type u} {X : Type v} {β : Type w}
variable [CompleteLattice β] [Zero U]

/-!
Source/core/bridge triage:

- `source-facing`: Lemma 6.29.6 states that the generalized convex program `(P)` is consistent if
  and only if its optimal value is strictly below `⊤` (specializing to `+∞` on `WithBotTop`).
- `core/canonical`: the existing Chapter 6 owners are `Bifunction.IsConsistent` from
  Definition 6.29.1 and `Bifunction.optimalValue` from Definition 6.29.15.
- `bridge/view`: the source wording is exactly the comparison between those two owners, since
  `optimalValue F = perturbationFunction F 0`.

Domain-style sampling used here:
- `Bifunction.IsConsistent`;
- `Bifunction.IsConsistent.optimalValue_lt_top`;
- `Bifunction.isConsistent_of_optimalValue_lt_top`;
- `Bifunction.isConsistent_iff_lt_top`;
- `Bifunction.optimalValue`;
- `Bifunction.optimalValue_eq_perturbationFunction_zero`.

Primitive data vs derived API:
- primitive source data: the bifunction `F : U → X → β`;
- primitive owners: `IsConsistent F` and `optimalValue F`;
- derived API: their equivalence via the zero-perturbation value `perturbationFunction F 0`.

Layer target: `bridge/view`, stated directly on the existing canonical owners with no new wrapper.
-/

-- Proof sketch: unfold `IsConsistent` through `isConsistent_iff_lt_top`, then rewrite the
-- zero-perturbation value `perturbationFunction F 0` as `optimalValue F` using
-- `optimalValue_eq_perturbationFunction_zero`.
/-- Lemma 6.29.6: the generalized convex program attached to `F` is consistent if and only if its
optimal value is strictly below `⊤` (equivalently below `+∞` in the `WithBotTop` codomain
specialization). -/
@[simp]
theorem isConsistent_iff_optimalValue_lt_top
    (F : U → X → β) :
    IsConsistent F ↔ optimalValue F < ⊤ := by
  simpa [optimalValue_eq_perturbationFunction_zero] using isConsistent_iff_lt_top F

/-- Owner-form elimination: consistency forces the optimal value to lie strictly below `⊤`. -/
theorem IsConsistent.optimalValue_lt_top
    {F : U → X → β}
    (h : IsConsistent F) :
    optimalValue F < ⊤ :=
  (isConsistent_iff_optimalValue_lt_top F).1 h

/-- Owner-form introduction: an optimal value strictly below `⊤` forces consistency. -/
theorem isConsistent_of_optimalValue_lt_top
    {F : U → X → β}
    (h : optimalValue F < ⊤) :
    IsConsistent F :=
  (isConsistent_iff_optimalValue_lt_top F).2 h

end

end Bifunction
