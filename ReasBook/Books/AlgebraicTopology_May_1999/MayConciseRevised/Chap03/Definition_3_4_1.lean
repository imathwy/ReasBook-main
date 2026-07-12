import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable (G : Type u) (S : Type v) [Group G]

/- Definition 3.4.1: A left action of a group `G` on a set `S` is the canonical mathlib typeclass
`MulAction G S`, written using the action notation `g • s`, with axioms `1 • s = s` and
`(g' * g) • s = g' • (g • s)`. -/
#check (MulAction G S)
