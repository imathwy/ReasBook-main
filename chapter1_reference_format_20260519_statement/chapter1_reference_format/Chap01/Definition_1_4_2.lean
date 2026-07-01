import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable (K : Type u) (V : Type v) [Field K] [AddCommGroup V] [Module K V]

/- Definition 1.4.2 is source-facing: a sub vector space of the `K`-vector space `V` is the
canonical bundled mathlib type `Subspace K V`, i.e. the vector-space specialization of the core
owner `Submodule K V`. -/
#check (Subspace K V)
