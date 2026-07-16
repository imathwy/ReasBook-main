import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {n : ℕ} {K : Type u} [Field K]

/- Definition 1.3.50: a polynomial `P ∈ K[X₁, …, Xₙ]` is irreducible when it is nonconstant and
every factor of `P` in `K[X₁, …, Xₙ]` is either a nonzero constant or associated to `P`; this is
exactly the canonical predicate `Irreducible P` on `MvPolynomial (Fin n) K`. In the field setting,
`MvPolynomial.isUnit_iff_eq_C_of_isReduced` identifies units with nonzero constants, so this
recall matches the textbook formulation. -/
#check (Irreducible : MvPolynomial (Fin n) K → Prop)
