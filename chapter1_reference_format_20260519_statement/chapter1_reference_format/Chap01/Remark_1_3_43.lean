import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Polynomial
open Polynomial

/-
Remark 1.3.43: the canonical owner theorem for a polynomial with vanishing formal derivative is
`Polynomial.eq_C_of_derivative_eq_zero`; the field-of-characteristic-`0` statement below is its
standard specialization.
-/
recall Polynomial.eq_C_of_derivative_eq_zero {R : Type u} [Semiring R] [IsAddTorsionFree R]
  {f : Polynomial R} (h : derivative f = 0) : f = C (f.coeff 0)

/-- Over an additive-torsion-free semiring, a polynomial has vanishing formal derivative exactly
when it is a constant polynomial. -/
theorem derivative_eq_zero_iff_exists_eq_C {R : Type u} [Semiring R] [IsAddTorsionFree R]
    (P : Polynomial R) :
    derivative P = 0 ↔ ∃ a : R, P = C a := by
  constructor
  · intro h
    exact ⟨P.coeff 0, eq_C_of_derivative_eq_zero h⟩
  · rintro ⟨a, rfl⟩
    simp

/-- Over `𝔽_p`, the polynomial `X^p + 1` is a nonconstant polynomial whose formal derivative
vanishes. -/
-- Proof sketch: compute the derivative of `X ^ p` using `Polynomial.derivative_X_pow`; in
-- characteristic `p`, the coefficient `p` becomes zero, so the whole derivative vanishes. The
-- polynomial is not constant because its leading term is `X ^ p`.
theorem derivative_zero_x_pow_add_one_over_zmod (p : ℕ) [Fact p.Prime] :
    derivative ((X : Polynomial (ZMod p)) ^ p + 1) = 0 ∧
      ¬ ∃ a : ZMod p, ((X : Polynomial (ZMod p)) ^ p + 1) = C a := by
  have hp : Nat.Prime p := Fact.out
  refine ⟨by simp [derivative_X_pow], ?_⟩
  rintro ⟨a, ha⟩
  have hnatDegree : (((X : Polynomial (ZMod p)) ^ p + 1).natDegree) = p := by
    simpa using
      (natDegree_X_pow_add_C :
        (((X : Polynomial (ZMod p)) ^ p + C (1 : ZMod p)).natDegree = p))
  rw [ha, natDegree_C] at hnatDegree
  exact hp.ne_zero hnatDegree.symm
