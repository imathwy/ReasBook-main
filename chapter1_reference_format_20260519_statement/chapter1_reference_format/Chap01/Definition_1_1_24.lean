import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 1.1.24: a group structure on `G` is the canonical `Group G` structure, namely a
binary operation on `G` that is associative, has a two-sided unit, and assigns to each element an
inverse. -/
recall Group (G : Type u) : Type u

/- An abelian group structure on `G` is the canonical `CommGroup G` structure, namely a group
structure whose multiplication is commutative. -/
recall CommGroup (G : Type u) : Type u
