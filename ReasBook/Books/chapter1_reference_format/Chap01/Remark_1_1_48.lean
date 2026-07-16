import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-
Remark 1.1.48: more generally, every Euclidean domain is a principal ideal ring. In mathlib this is
the canonical bridge instance `EuclideanDomain.to_principal_ideal_domain`, landing in the owner
property `IsPrincipalIdealRing`.
-/
recall EuclideanDomain.to_principal_ideal_domain
