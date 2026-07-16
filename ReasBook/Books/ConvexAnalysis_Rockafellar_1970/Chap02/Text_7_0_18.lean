import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

/-- Text 7.0.18: if `α` lies strictly below `inf f`, then the canonical closed `α`-sublevel set
`{x | f x ≤ α}` is empty, so the sublevel-set formulas from Theorem 7.6 are vacuous. -/
-- Proof sketch: if `x` belonged to the closed `α`-sublevel set, then
-- `⨅ y, f y ≤ f x ≤ α`, contradicting the strict inequality `α < ⨅ y, f y`.
theorem closedSublevel_eq_empty_of_lt_iInf
    {E : Type u} {β : Type*} [CompleteSemilatticeInf β] (f : E → β) (α : β)
    (hα : α < ⨅ x : E, f x) :
    {x | f x ≤ α} = (∅ : Set E) := by
  ext x
  constructor
  · intro hx
    have hInf_le : (⨅ y : E, f y) ≤ f x := by
      change sInf (Set.range f) ≤ f x
      exact sInf_le (s := Set.range f) (Set.mem_range.mpr ⟨x, rfl⟩)
    exact (not_le_of_gt hα) (hInf_le.trans hx)
  · intro hx
    exact False.elim hx

/- The boundary case `α = inf f` is genuinely different: Text 7.0.17 gives a concrete
counterexample showing that, at this boundary level, the closure and relative-interior formulas
from Theorem 7.6 can fail. -/

end
