import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Polynomial

namespace Polynomial

-- Proof sketch: `Polynomial.cardPowDegree_nonzero` identifies `Polynomial.cardPowDegree P` with
-- `(Fintype.card Fq : ℤ) ^ P.natDegree` for nonzero polynomials over a finite field, so equal
-- `natDegree` values give equal `cardPowDegree` values by rewriting.
/-- Remark 1.3.23: over a finite field, the canonical quantity `Polynomial.cardPowDegree P`
attached to a nonzero polynomial `P` depends only on the degree of `P`; equivalently, nonzero
polynomials of the same degree have the same `cardPowDegree`. -/
theorem cardPowDegree_eq_of_natDegree_eq
    {Fq : Type*} [Field Fq] [Fintype Fq] {P Q : Fq[X]}
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hdeg : P.natDegree = Q.natDegree) :
    cardPowDegree P = cardPowDegree Q := by
  rw [cardPowDegree_nonzero P hP, cardPowDegree_nonzero Q hQ, hdeg]

end Polynomial
