import Mathlib

universe u

namespace Polynomial

-- Proof sketch: apply `Polynomial.coeff_eq_esymm_roots_of_splits` to the coefficient
-- `p.coeff (p.natDegree - i)`, then divide by `p.leadingCoeff`, using `hp` to ensure that the
-- leading coefficient is nonzero.
/-- Theorem 1.3.41: for a nonzero split polynomial over a field, the `i`-th elementary symmetric
sum of its roots, counted with multiplicity, is `(-1)^i` times the coefficient of degree
`p.natDegree - i`, divided by the leading coefficient. In particular, this recovers the usual
formulas for the sum and product of the roots. -/
theorem esymm_roots_eq_signed_coeff_div_leadingCoeff {K : Type u} [Field K] {p : K[X]}
    (hp : p ≠ 0) (hsplit : p.Splits) {i : ℕ} (hle : i ≤ p.natDegree) :
    p.roots.esymm i = (-1 : K) ^ i * (p.coeff (p.natDegree - i) / p.leadingCoeff) := by
  have hlead : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have hsub : p.natDegree - (p.natDegree - i) = i := by
    omega
  let k := p.natDegree - i
  have hk : k ≤ p.natDegree := Nat.sub_le _ _
  have hcoeff :
      p.coeff (p.natDegree - i) = p.leadingCoeff * (-1 : K) ^ i * p.roots.esymm i := by
    simpa [k, hsub, mul_assoc, mul_left_comm, mul_comm] using
      coeff_eq_esymm_roots_of_splits hsplit hk
  have hdiv : p.coeff (p.natDegree - i) / p.leadingCoeff = (-1 : K) ^ i * p.roots.esymm i := by
    rw [div_eq_iff hlead]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcoeff
  have hsign : (-1 : K) ^ i * (-1 : K) ^ i = 1 := by
    calc
      (-1 : K) ^ i * (-1 : K) ^ i = (-1 : K) ^ (i + i) := by
        rw [← pow_add]
      _ = (-1 : K) ^ (2 * i) := by
        rw [two_mul]
      _ = ((-1 : K) ^ 2) ^ i := by
        rw [pow_mul]
      _ = 1 := by
        simp
  calc
    p.roots.esymm i = 1 * p.roots.esymm i := by
      simp
    _ = ((-1 : K) ^ i * (-1 : K) ^ i) * p.roots.esymm i := by
      rw [hsign]
    _ = (-1 : K) ^ i * ((-1 : K) ^ i * p.roots.esymm i) := by
      simp [mul_assoc]
    _ = (-1 : K) ^ i * (p.coeff (p.natDegree - i) / p.leadingCoeff) := by
      rw [hdiv]

end Polynomial
