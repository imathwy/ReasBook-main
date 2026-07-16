import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_16

noncomputable section

universe u v w

namespace Bifunction

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.17 says that the generalized convex program `(P)` is
  consistent exactly when it has at least one feasible solution, equivalently when the feasible-set
  owner `feasibleSet F = dom((F)₀)` is nonempty.
- `core/canonical`: the Chapter 6 consistency owner already exists as `Bifunction.IsConsistent`
  from Definition 6.29.1, and Definition 6.29.8 provides the source-facing bifunction-domain
  owner `dom F`.
- `bridge/view`: Definition 6.29.16 introduced the feasible-set owner `Bifunction.feasibleSet`;
  this file bridges it first to `(0 : U) ∈ dom F`, then exposes the thin
  `dom((F)₀)` companion theorem via definitional unfolding.

Domain-style sampling used here:
- `Bifunction.IsConsistent`;
- `Bifunction.dom`;
- `Bifunction.feasibleSet`;
- `Bifunction.objective`;
- `Bifunction.isConsistent_iff_zero_mem_dom`.

Primitive data vs derived API:
- primitive owner: `IsConsistent F`;
- source-facing domain bridge: `(0 : U) ∈ dom F`;
- derived feasible-set bridge: nonemptiness of `feasibleSet F`;
- derived companion view: nonemptiness of `dom((F)₀)`.

Layer target: `core/canonical recall/use`, with one source-facing bridge theorem and one thin
bridge/view companion.
-/

section

variable {U : Type u} {X : Type v} {β : Type w}
variable [Zero U] [Top β] [LT β]

/- Definition 6.29.17: the generalized convex program `(P)` is consistent exactly when the
already existing Chapter 6 owner `Bifunction.IsConsistent F` holds; the present item re-expresses
that owner through the feasible-set language, with `feasibleSet F = dom((F)₀)` available
as the defining expansion. -/
recall IsConsistent

/-- The source-facing bifunction-domain condition at zero is exactly nonemptiness of the feasible
set. -/
@[simp] theorem zero_mem_dom_iff_feasibleSet_nonempty (F : U → X → β) :
    (0 : U) ∈ dom F ↔ (feasibleSet F).Nonempty := by
  simp [mem_dom, feasibleSet, objective]

/-- Definition 6.29.17 (1): ordinary consistency is exactly nonemptiness of the feasible set. -/
theorem isConsistent_iff_feasibleSet_nonempty (F : U → X → β) :
    IsConsistent F ↔ (feasibleSet F).Nonempty := by
  rw [isConsistent_iff_zero_mem_dom, zero_mem_dom_iff_feasibleSet_nonempty]

/-- Definition 6.29.17 (2): ordinary consistency is exactly nonemptiness of the zero-slice domain
`dom((F)₀)`. -/
theorem isConsistent_iff_dom_objective_nonempty (F : U → X → β) :
    IsConsistent F ↔ (dom((F)₀)).Nonempty := by
  rw [isConsistent_iff_feasibleSet_nonempty, feasibleSet]

-- Proof sketch: this is the objective-notation restatement of the primitive consistency bridge
-- `isConsistent_iff_exists_lt_top` from Definition 6.29.1.
/-- Ordinary consistency is exactly existence of a point where the objective `F₀` is finite. -/
theorem isConsistent_iff_exists_objective_lt_top (F : U → X → β) :
    IsConsistent F ↔ ∃ x : X, (F)₀ x < ⊤ := by
  rw [isConsistent_iff_exists_lt_top]
  simp [objective]

end

end Bifunction
