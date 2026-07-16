import Mathlib

open Polynomial

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 1.4.64: the field of complex numbers `ℂ` is algebraically closed. Equivalently, every
polynomial in `ℂ[X]` factors as a scalar times a finite product of linear factors. -/
#check (inferInstance : IsAlgClosed ℂ)

/- The equivalent root factorization is the canonical mathlib theorem obtained by combining
`IsAlgClosed.splits` with `Polynomial.Splits.eq_prod_roots`. -/
#check fun P : ℂ[X] ↦ (IsAlgClosed.splits P).eq_prod_roots
