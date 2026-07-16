import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Operations
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition_36_4_1
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_0_4
import ConvexAnalysis_Rockafellar_1970.Chap08.Theorem_38_5

noncomputable section

universe u v w r

open scoped Rockafellar

namespace Bifunction

section

variable {U : Type u} {X : Type v} {Y : Type w}
variable {α : Type r}
variable [ConditionallyCompleteLinearOrder α] [AddCommGroup α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.4.2 states that the inverse bifunction of the product `GF`
  agrees with the source concave-side product `F_* G_*`.
- `core/canonical`: the chapter owner abstractions already present are `Bifunction.comp` for the
  source product `GF`, `Bifunction.image` for the underlying one-step elimination, and
  `Bifunction.inverse` for `F_*`.
- `bridge/view`: the right-hand side still has no separate concave-side product owner in the
  chapter, so the source `F_* G_*` is rendered by its explicit supremum formula. The left-hand
  side should nevertheless use the established owner `comp G F` rather than repeating its
  implementation.

Primary mathematical domain:
- product and inversion operations for convex/concave bifunctions in the Chapter 38 algebra.

Domain-style sampling used here:
- `Bifunction.comp` and `Bifunction.comp_apply_eq_iInf` from `Theorem_38_5`;
- `Bifunction.image` and `Bifunction.image_apply` from `Definition_38_0_4`;
- `Bifunction.inverse` and `Bifunction.inverse_apply` from `Definition_36_4_1`;
- the Chapter 6/7 pattern of keeping concave-side source formulas explicit when no canonical owner
  has been introduced yet.

Primitive data vs derived API:
- primitive source data: bifunctions `F : U → X → WithBotTop α` and
  `G : X → Y → WithBotTop α`;
- primitive owner expression: `(comp G F) _*`;
- derived source formula: `fun y u ↦ ⨆ x, G _* y x + F _* x u`;
- derived API: no extra structure beyond the owner equality itself.

Layer target: `bridge/view`.

Redundant-source-assumption check:
- the textbook mentions proper convexity, but the displayed identity is algebraic in the product
  and inverse operations, so those hypotheses are removed from the public Lean statement.
-/

-- Proof sketch: unfold `inverse` and `image`. The left-hand side becomes
-- `- (⨅ x, F u x + G x y)`, which is the supremum of the negated summands on `WithBotTop α`.
-- Rewrite those negated slice values with `inverse_apply` to obtain
-- `⨆ x, G _* y x + F _* x u`.
/-- Proposition 38.4.2: the inverse of the source product `GF`, owned here by `comp G F`, is the
source supremum-side product `F_* G_*`, rendered explicitly because the chapter has no separate
owner for that concave-side product. -/
theorem inverse_comp_eq_iSup_inverse_add_inverse
    (F : U → X → WithBotTop α) (G : X → Y → WithBotTop α) :
    (comp G F) _* = fun y u ↦ ⨆ x : X, G _* y x + F _* x u := sorry

end

end Bifunction
