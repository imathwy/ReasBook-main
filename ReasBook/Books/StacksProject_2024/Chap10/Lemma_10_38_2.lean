import Mathlib
import stacks_project.Chap10.Definition_10_38_1

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

namespace RingHom

private lemma term_eval_eq (s : S) (a : R) (d i : ℕ) (hi : i ≤ d) :
    eval₂ (algebraMap S[X] S[X]) (C s * X)
      (C (C ((algebraMap R S) a) * X ^ (d - i) : S[X]) * X ^ i) =
    C ((algebraMap R S) a * s ^ i) * X ^ d := by
  simp only [eval₂_mul, eval₂_C, eval₂_X_pow]
  calc
    (C ((algebraMap R S) a) * X ^ (d - i) : S[X]) * (C s * X) ^ i
        = (C ((algebraMap R S) a) * X ^ (d - i) : S[X]) * (C (s ^ i) * X ^ i) := by
            rw [mul_pow, ← C_pow]
    _ = C ((algebraMap R S) a * s ^ i) * X ^ ((d - i) + i) := by
          rw [C_mul_X_pow_eq_monomial, C_mul_X_pow_eq_monomial, C_mul_X_pow_eq_monomial]
          simp [monomial_mul_monomial, add_comm, mul_comm]
    _ = C ((algebraMap R S) a * s ^ i) * X ^ d := by rw [Nat.sub_add_cancel hi]

-- Proof sketch: for the forward direction, translate a defining polynomial relation for
-- `(algebraMap R S).IsIntegralOverIdeal I s` into a monic polynomial relation for `C s * X` over
-- the canonical Rees algebra `reesAlgebra I`. For the reverse direction, rewrite back to the
-- textbook generator presentation and apply
-- `Polynomial.exists_monic_aeval_eq_zero_forall_mem_pow_of_isIntegral`.
attribute [local instance] Polynomial.algebra in
/-- Lemma 10.38.2: an element `s : S` is integral over the ideal `I` in the sense that it satisfies
a monic polynomial relation with coefficients in the powers `I ^ (d - i)` if and only if the
polynomial element `C s * X : S[X]` is integral over the canonical Rees algebra
`reesAlgebra I ⊆ R[X]`. -/
lemma isIntegralOverIdeal_iff_isIntegral_C_mul_X (I : Ideal R) (s : S) :
    (algebraMap R S).IsIntegralOverIdeal I s ↔
      _root_.IsIntegral (reesAlgebra I) (C s * X : S[X]) := by
  constructor
  · rintro ⟨p, hpM, hp0, hpI⟩
    let A : Subalgebra R R[X] := reesAlgebra I
    let f : ℕ → A[X] := fun i ↦
      C ⟨C (p.coeff i) * X ^ (p.natDegree - i), by
          simpa [A, C_mul_X_pow_eq_monomial] using (reesAlgebra.monomial_mem).2 (hpI i)⟩ * X ^ i
    let q : A[X] := ∑ i ∈ Finset.range (p.natDegree + 1), f i
    change (algebraMap A S[X]).IsIntegralElem (C s * X : S[X])
    refine ⟨q, ?_, ?_⟩
    · refine monic_of_natDegree_le_of_coeff_eq_one p.natDegree ?_ ?_
      · simpa [q, f] using
          (natDegree_sum_le_of_forall_le (Finset.range (p.natDegree + 1)) f fun i hi ↦
            (natDegree_C_mul_X_pow_le _ _).trans (by simpa [Nat.lt_succ_iff] using hi))
      · ext
        simp [q, f, hpM]
    · have hqsum : eval₂ (algebraMap A S[X]) (C s * X) q
          = ∑ i ∈ Finset.range (p.natDegree + 1), eval₂ (algebraMap A S[X]) (C s * X) (f i) := by
          simpa [q] using
            (Polynomial.eval₂_finset_sum (algebraMap A S[X]) (Finset.range (p.natDegree + 1))
              f (C s * X))
      calc
        eval₂ (algebraMap A S[X]) (C s * X) q
            = ∑ i ∈ Finset.range (p.natDegree + 1),
                C ((algebraMap R S) (p.coeff i) * s ^ i) * X ^ p.natDegree := by
                  rw [hqsum]
                  refine Finset.sum_congr rfl fun i hi ↦ ?_
                  have hi' : i ≤ p.natDegree := by simpa [Nat.lt_succ_iff] using hi
                  simpa [f] using term_eval_eq s (p.coeff i) p.natDegree i hi'
        _ = C ((aeval s) p) * X ^ p.natDegree := by
              rw [← Finset.sum_mul]
              congr 1
              simp [aeval_def, eval₂_eq_sum_range, map_sum]
        _ = 0 := by
              have hp0' : aeval s p = 0 := by simpa [aeval_def] using hp0
              rw [hp0']
              simp
  · intro hs
    have hrees :
        Algebra.adjoin R { C r * X | r ∈ I } = reesAlgebra I := by
      simpa [Set.ext_iff, C_mul_X_eq_monomial] using adjoin_monomial_eq_reesAlgebra I
    rw [← hrees] at hs
    exact exists_monic_aeval_eq_zero_forall_mem_pow_of_isIntegral hs

end RingHom

end
