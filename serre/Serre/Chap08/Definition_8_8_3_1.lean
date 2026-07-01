import Mathlib.GroupTheory.Solvable
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (G : Type u) [Group G]

/- Definition 8-8.3-1: a group is solvable if it satisfies the canonical mathlib class
`IsSolvable G`; equivalently, its derived series becomes trivial after finitely many steps,
matching the usual finite normal series with abelian successive quotients. -/
recall IsSolvable

/- Mathlib's defining characterization of a solvable group is that its derived series is eventually
trivial. -/
recall isSolvable_def

end
