import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_12

noncomputable section

universe u v w

namespace Bifunction

open scoped Rockafellar

section

variable {U : Type u} {X : Type v} {β : Type w}
variable [Zero U] [Top β] [LT β]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.16 introduces the feasible solutions of the generalized convex
  program `(P)` as the points of the effective domain of the zero-slice objective `F₀`.
- `core/canonical`: the existing owners are the Chapter 6 zero-slice objective
  `Bifunction.objective` from Definition 6.29.12 and the Chapter 1 effective-domain owner
  `dom(·)` from Definition 4.4.
- `bridge/view`: the textbook inequality `F₀(x) < +∞` is exactly membership in
  `dom((F)₀)`.

Domain-style sampling used here:
- `Bifunction.objective`;
- `Bifunction.objective_apply`;
- `effectiveDomain`, notation `dom(·)`, and `mem_effectiveDomain`.

Primitive data vs derived API:
- primitive source-facing owner: `feasibleSet F`;
- canonical defining owner expression: `dom((F)₀)`;
- downstream membership/value API should reuse the canonical Chapter 1 bridge
  `mem_effectiveDomain` on `dom((F)₀)` rather than a parallel local theorem.

Layer target: `source-facing`. This item introduces genuine chapter vocabulary for the primal
feasible set, but it should be defined directly from the existing owners rather than through a new
program wrapper.
-/

/-- Definition 6.29.16: the feasible solutions of the generalized convex program attached to a
bifunction `F` are the points of the effective domain of its objective function `F₀`. -/
def feasibleSet (F : U → X → β) : Set X :=
  dom((F)₀)

/-- A point is feasible exactly when its objective value is strictly below `⊤`. -/
@[simp] theorem mem_feasibleSet {F : U → X → β} {x : X} :
    x ∈ feasibleSet F ↔ (F)₀ x < ⊤ := by
  simp [feasibleSet]

end

end Bifunction
