import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_12

universe u v w

namespace Bifunction

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.14 does not introduce a new mathematical object; it only names
  the zero-slice `F₀` for `(P)` as the objective function.
- `core/canonical`: that owner is already the Chapter 6 declaration `Bifunction.objective`,
  introduced in Definition 6.29.12 and reused in Definition 6.29.13.
- `bridge/view`: the displayed source equation for the zero slice is exactly the existing
  owner-side evaluation theorem `Bifunction.objective_apply`.

Domain-style sampling used here:
- `Bifunction.objective`;
- `Bifunction.objective_apply`.

Primitive data vs derived API:
- primitive data: a bifunction `F : U → X → Y` with zero parameter in `U`;
- owner: `objective F`;
- derived API: the owner-side pointwise identity `objective_apply`.

Layer target: `core/canonical recall/use`.
-/

section

variable {U : Type u} {X : Type v} {Y : Type w}
variable [Zero U]
variable (F : U → X → Y)

/- Definition 6.29.14: the function `F₀` attached to the generalized convex program `(P)` is the
already existing zero-slice owner `Bifunction.objective F`; this item simply calls it the
objective function for `(P)`. -/
#check F ₀
#check objective_apply F

recall objective

/- The displayed source evaluation of `F₀` is the owner-side theorem
`Bifunction.objective_apply`. -/
recall objective_apply

end

end Bifunction
