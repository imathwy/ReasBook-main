import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item introduces the adjective "improper" for a convex function that fails to
  be proper.
- `core/canonical`: the owner predicate is `Function.IsProper` on functions `f : E → β`, with only
  the codomain order/top/bottom data required by the owner and its domain notation.
- `bridge/view`: the source adjective carries no new owner data; downstream statements should use
  the direct negation `¬ f.IsProper` rather than a parallel alias.
- Layer target: `bridge/view`, since this item only names the negation of the owner predicate from
  Definition 4.6 and should not introduce a second public owner.

Mathlib/project sampling used here:
- `Function.IsProper` from the immediately preceding item `Definition_4_6`;
- the specification theorem `Function.isProper_iff` for that owner;
- the consequence `Function.IsProper.bot_lt`, used as a derived strict-lower-bound bridge when the
  codomain has an order bottom.
- Primitive data vs derived API: there is no new primitive owner here. The source-facing adjective
  "improper" is only the direct negation of the existing properness owner.
-/

namespace Function

variable {E : Type u} {β : Type v}

/-- Canonical bridge for Definition 4.7: a function is improper exactly when it fails either
primitive clause in `Function.IsProper` (nonempty effective domain and nowhere `⊥`). -/
theorem not_isProper_iff [LT β] [Top β] [Bot β] (f : E → β) :
    (¬ f.IsProper) ↔ ¬ dom(f).Nonempty ∨ ∃ x, f x = ⊥ := by
  rw [isProper_iff, not_and_or, not_forall]
  simp

/-- Bridge form of Definition 4.7 using `dom(f) = ∅`. -/
theorem not_isProper_iff_dom_eq_empty_or_exists_eq_bot
    [LT β] [Top β] [Bot β] (f : E → β) :
    (¬ f.IsProper) ↔ dom(f) = ∅ ∨ ∃ x, f x = ⊥ := by
  simpa [Set.not_nonempty_iff_eq_empty] using (not_isProper_iff f)

/-- Logical form of Definition 4.7 using failure of domain nonemptiness. -/
theorem not_isProper_iff_not_nonempty_dom_or_exists_eq_bot
    [LT β] [Top β] [Bot β] (f : E → β) :
    (¬ f.IsProper) ↔ ¬ dom(f).Nonempty ∨ ∃ x, f x = ⊥ := by
  simpa using (not_isProper_iff f)

/-- Bridge form of improperness phrased by failure of strict lower bound and `dom(f) = ∅`. -/
theorem not_isProper_iff_dom_eq_empty_or_exists_not_bot_lt
    [PartialOrder β] [Top β] [OrderBot β] (f : E → β) :
    (¬ f.IsProper) ↔ dom(f) = ∅ ∨ ∃ x, ¬ ⊥ < f x := by
  simpa [bot_lt_iff_ne_bot] using
    (not_isProper_iff_dom_eq_empty_or_exists_eq_bot (f := f))

end Function
