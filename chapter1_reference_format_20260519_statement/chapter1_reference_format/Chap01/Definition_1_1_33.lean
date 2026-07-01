import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Definition 1.1.33: a ring isomorphism from `R` to `S` is the canonical bundled ring
equivalence `RingEquiv R S`, written `R ≃+* S`; equivalently, any bijective ring homomorphism
determines such an isomorphism. -/
recall RingEquiv (R : Type u) (S : Type v) [Mul R] [Mul S] [Add R] [Add S] : Type (max u v)

variable {R : Type u} {S : Type v} [NonAssocSemiring R] [NonAssocSemiring S]

/- The standard notation for a ring isomorphism is `R ≃+* S`. -/
#check (R ≃+* S)

/- Any bijective ring homomorphism gives the corresponding bundled ring isomorphism by
`RingEquiv.ofBijective`. -/
#check (RingEquiv.ofBijective : (f : R →+* S) → Function.Bijective f → R ≃+* S)
