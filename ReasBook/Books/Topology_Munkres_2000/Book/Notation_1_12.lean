module

import Mathlib.Data.Real.Basic

universe u v

/- Notation 1.12: The expression `(a, b)` may denote either an ordered pair or,
for real numbers, the open interval of `x` satisfying `a < x < b`. The source
proposes `a × b` for the ordered pair when ambiguity is possible; Lean instead
uses `(a, b)` for the pair and `Set.Ioo a b` for the interval. -/
#check fun {α : Type u} {β : Type v} (a : α) (b : β) ↦ (a, b)
#check fun (a b : ℝ) ↦ Set.Ioo a b
