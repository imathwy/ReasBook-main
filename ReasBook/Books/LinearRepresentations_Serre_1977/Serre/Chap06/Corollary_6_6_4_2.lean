import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [Ring R] [Module.Finite ℤ R]

-- Source/core/bridge triage:
-- * source-facing: Corollary 6-6.4-2, specialized to the base ring `ℤ`.
-- * core/canonical owner: `Algebra.IsIntegral ℤ R`.
-- * bridge/view: the elementwise theorem `IsIntegral.of_finite ℤ`.
-- Primitive data are only the finite `ℤ`-module structure on `R`; elementwise integrality is
-- derived canonically from the ambient integral-extension owner.
/- Corollary 6-6.4-2: if a ring is finitely generated as a `ℤ`-module, then it is an integral
extension of `ℤ`, so in particular each of its elements is integral over `ℤ`. This is the
integer-base specialization of the canonical owner instance `Algebra.IsIntegral.of_finite`. -/
#check (Algebra.IsIntegral.of_finite ℤ R : Algebra.IsIntegral ℤ R)

end
