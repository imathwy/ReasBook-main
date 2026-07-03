import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Lemma 10.37.7 (1): if a polynomial `f ∈ K[X]` is integral over `R[X]`, then every coefficient
`αᵢ = f.coeff i` is integral over `R`. The owner abstraction is the canonical predicate
`IsIntegral R[X] f`, and the coefficientwise conclusion is exactly the derived theorem
`IsIntegral.coeff`; the textbook fraction-field case is its specialization. -/
recall IsIntegral.coeff

/- Lemma 10.37.7 (2): if a polynomial `f ∈ K[X]` is almost integral over `R[X]`, then every
coefficient `αᵢ = f.coeff i` is almost integral over `R`. Here the owner abstraction is
`IsAlmostIntegral R[X] f`, and the coefficient statement is exactly the canonical derived theorem
`IsAlmostIntegral.coeff`. -/
recall IsAlmostIntegral.coeff

end
