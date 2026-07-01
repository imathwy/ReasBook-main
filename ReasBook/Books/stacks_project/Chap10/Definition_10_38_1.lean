import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v

open Polynomial

variable {R : Type u} {S : Type v} [CommRing R] [Ring S]

namespace RingHom

/-- Definition 10.38.1: an element `g : S` is integral over an ideal `I` with respect to a ring
homomorphism `φ : R →+* S` if `g` satisfies a monic polynomial relation over `R` whose
`X^j`-coefficient lies in `I ^ (d - j)`, where `d` is the degree of the polynomial.

This is the source-facing coefficient formulation; ordinary integrality remains owned by
`RingHom.IsIntegralElem`, and Lemma 10.38.2 later identifies this notion with integrality over the
Rees algebra. -/
def IsIntegralOverIdeal (φ : R →+* S) (I : Ideal R) (g : S) : Prop :=
  ∃ P : R[X], P.Monic ∧ eval₂ φ g P = 0 ∧ ∀ j : ℕ, P.coeff j ∈ I ^ (P.natDegree - j)

end RingHom

end
