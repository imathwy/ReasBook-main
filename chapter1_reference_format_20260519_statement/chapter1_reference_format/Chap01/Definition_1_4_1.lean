import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable (K : Type u) (V : Type v) [Field K] [AddCommGroup V]

/- Definition 1.4.1 is source-facing: a `K`-vector-space structure on `V` is the canonical
mathlib typeclass `Module K V`, specialized to scalar fields and additive commutative groups. -/
#check Module K V
