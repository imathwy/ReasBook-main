import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Polynomial
open scoped BigOperators

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace RingHom

/-- Lemma 10.123.1: if `φ : R →+* S` and `t : S` satisfy a polynomial relation
`φ(a₀) + φ(a₁) t + ⋯ + φ(aₙ) tⁿ = 0`, then `φ(aₙ) * t` is integral over `R` with respect to
`φ`. -/
-- Proof sketch: package the displayed relation as `p.eval₂ φ t = 0` for the polynomial
-- `p = ∑ i, C (aᵢ) X^i`, observe that `p` has leading coefficient `aₙ`, and then apply the
-- canonical owner theorem `RingHom.isIntegralElem_leadingCoeff_mul`.
@[stacks 00PQ]
theorem isIntegralElem_mul_lastCoeff_of_sum_eq_zero (φ : R →+* S) {t : S} {n : ℕ}
    (a : Fin (n + 1) → R) (h : ∑ i : Fin (n + 1), φ (a i) * t ^ (i : ℕ) = 0) :
    φ.IsIntegralElem (φ (a ⟨n, Nat.lt_succ_self n⟩) * t) := by
  let p : R[X] := ∑ i : Fin (n + 1), C (a i) * X ^ (i : ℕ)
  let i0 : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
  have hp_eval : p.eval₂ φ t = ∑ i : Fin (n + 1), φ (a i) * t ^ (i : ℕ) := by
    simp [p, Polynomial.eval₂_finset_sum]
  have hp : p.eval₂ φ t = 0 := hp_eval.trans h
  by_cases han : a i0 = 0
  · simpa [i0, han] using φ.isIntegralElem_zero
  · have hcoeff : p.coeff n = a i0 := by
      calc
        p.coeff n = ∑ i : Fin (n + 1), (C (a i) * X ^ (i : ℕ) : R[X]).coeff n := by simp [p]
        _ = (C (a i0) * X ^ n : R[X]).coeff n := by
            refine Fintype.sum_eq_single i0 ?_
            intro i hi
            rw [coeff_C_mul, coeff_X_pow]
            by_cases hni : n = (i : ℕ)
            · exact (hi (Fin.ext hni.symm)).elim
            · simp [hni]
        _ = a i0 := by simp [i0, coeff_C_mul, coeff_X_pow]
    have hdeg_le : p.natDegree ≤ n := by
      simpa [p] using
        (natDegree_sum_le_of_forall_le _ _ fun i _ ↦
            (natDegree_C_mul_X_pow_le (a i) (i : ℕ)).trans (Nat.le_of_lt_succ i.2))
    have hdeg : p.natDegree = n :=
      natDegree_eq_of_le_of_coeff_ne_zero hdeg_le (by simpa [hcoeff] using han)
    have hlead : p.leadingCoeff = a i0 := by
      rw [Polynomial.leadingCoeff, hdeg, hcoeff]
    simpa [i0, hlead] using φ.isIntegralElem_leadingCoeff_mul p t hp

end RingHom

end
