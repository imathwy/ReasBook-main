import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 1.1.47: the ring of integers `ℤ` is a principal ideal ring. This is the canonical
instance obtained from the Euclidean domain structure on `ℤ` via
`EuclideanDomain.to_principal_ideal_domain`. -/
#check (inferInstance : IsPrincipalIdealRing ℤ)
