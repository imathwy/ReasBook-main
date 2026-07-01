import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (p : ℕ) (G : Type u) [Group G]

/- Definition 8-8.3-4: the canonical owner for the notion of a `p`-group is `IsPGroup p G`.
Under the source convention that `p` is prime, this is exactly the textbook definition. -/
recall IsPGroup

variable [Fact p.Prime] [Finite G]

/- For finite groups, the source-facing cardinality formulation is derived API: it is exactly the
canonical bridge theorem `IsPGroup.iff_card`, not a second owner declaration. -/
recall IsPGroup.iff_card

end
