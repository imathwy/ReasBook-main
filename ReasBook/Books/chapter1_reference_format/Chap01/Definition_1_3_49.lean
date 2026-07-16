import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {n : ℕ} {K : Type u} [CommSemiring K]

/- Definition 1.3.49: divisibility in the multivariable polynomial ring `K[X₁, ..., Xₙ]` is the
canonical relation `(· ∣ ·)` on `MvPolynomial (Fin n) K`; thus `P ∣ Q` means that `Q = P * S` for
some polynomial `S`, and then `P` is a factor of `Q`. -/
#check ((· ∣ ·) : MvPolynomial (Fin n) K → MvPolynomial (Fin n) K → Prop)

/- In a multivariable polynomial ring, divisibility is equivalent to the existence of a polynomial
quotient on the right. -/
#check (dvd_iff_exists_eq_mul_right :
  ∀ {P Q : MvPolynomial (Fin n) K},
    P ∣ Q ↔ ∃ S : MvPolynomial (Fin n) K, Q = P * S)
