import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Polynomial

universe u

variable (K : Type u) [Field K]

/- Corollary 1.3.6: over a field `K`, the univariate polynomial ring `K[X]` is a principal
ideal domain, formalized canonically in mathlib by the instance `IsPrincipalIdealRing K[X]`. -/
#check (inferInstance : IsPrincipalIdealRing K[X])
