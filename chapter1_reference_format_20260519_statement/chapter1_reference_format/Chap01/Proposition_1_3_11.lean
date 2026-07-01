import Mathlib

open scoped Polynomial

universe u

-- Declarations for this item will be appended below by the statement pipeline.

/-- Proposition 1.3.11: The quotient ring `K[X] / (P)` is a field if and only if `P` is an
irreducible polynomial. -/
-- Proof sketch: use `Ideal.Quotient.maximal_ideal_iff_isField_quotient` to rewrite the quotient
-- field condition as maximality of the principal ideal `(P)`, then use the PID structure on
-- `K[X]` to identify maximal principal ideals with irreducible generators.
theorem polynomial_quotient_isField_iff_irreducible {K : Type u} [Field K] (P : K[X]) :
    IsField (K[X] ⧸ Ideal.span {P}) ↔ Irreducible P := by
  constructor
  · intro hField
    have hP0 : P ≠ 0 := by
      intro hP
      exact Ideal.polynomial_not_isField <|
        (((Ideal.quotEquivOfEq (Ideal.span_singleton_eq_bot.mpr hP)).trans
            (RingEquiv.quotientBot K[X])).symm.toMulEquiv.isField hField)
    have hPrime : Prime P :=
      (Ideal.span_singleton_prime hP0).mp
        ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr hField).isPrime
    exact irreducible_iff_prime.mpr hPrime
  · intro hP
    exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp
      (PrincipalIdealRing.isMaximal_of_irreducible hP)
