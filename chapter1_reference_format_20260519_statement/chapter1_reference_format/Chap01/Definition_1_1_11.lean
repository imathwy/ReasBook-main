import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 1.1.11: a partial order on `S` is the canonical `PartialOrder S` structure, namely
a relation `≤` on `S` satisfying reflexivity, antisymmetry, and transitivity. -/
recall PartialOrder (S : Type u) : Type u

/- A total order on `S` is the canonical `LinearOrder S` structure, i.e. a partial order in which
any two elements are comparable. -/
recall LinearOrder (S : Type u) : Type u
