import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

-- Source/core/bridge triage:
-- * source-facing: the subring of elements of `R` integral over `ℤ`.
-- * core/canonical: `integralClosure ℤ R : Subalgebra ℤ R`.
-- * bridge/view: `Subalgebra.toSubring`.
-- Primitive data live in the owner `integralClosure ℤ R`; the membership characterization is
-- already derived canonically by `mem_integralClosure_iff` and `Subalgebra.mem_toSubring`.

variable {R : Type u} [CommRing R]

/- Corollary 6-6.4-3: the elements of a commutative ring that are integral over `ℤ` form a
subring. This is the canonical subring view of `integralClosure ℤ R`. -/
#check (integralClosure ℤ R).toSubring

end
