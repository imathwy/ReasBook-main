import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/- Theorem 8-8.3-5: every finite `p`-group is nilpotent, via the canonical mathlib theorem
`IsPGroup.isNilpotent`. -/
recall IsPGroup.isNilpotent

end
