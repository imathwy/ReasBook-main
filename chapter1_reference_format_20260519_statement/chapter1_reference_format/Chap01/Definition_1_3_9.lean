import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {K : Type u} [Field K]

/- Definition 1.3.9: a polynomial `P ∈ K[X]` is irreducible when it is nonconstant and every
factor of `P` in `K[X]` is either a nonzero constant or associated to `P`; this is the canonical
predicate `Irreducible P`. -/
#check (Irreducible : Polynomial K → Prop)
