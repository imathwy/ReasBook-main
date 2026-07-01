import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

/-- Lemma 1.3.27: an irreducible polynomial in `ℤ[X]` is either a constant polynomial equal to
`±p` for some prime number `p`, or it is primitive. -/
-- Proof sketch: split on whether `f.natDegree = 0`. In the constant case, identify `f` with a
-- constant polynomial `C z`; irreducibility of `f` implies irreducibility, hence primality, of
-- `z ∈ ℤ`, so `z = ±p` for some prime `p`. In the positive-degree case, apply
-- `Irreducible.isPrimitive`.
theorem int_irreducible_eq_signed_prime_or_isPrimitive {f : ℤ[X]} (hf : Irreducible f) :
    (∃ p : ℕ, Nat.Prime p ∧ (f = C (p : ℤ) ∨ f = -C (p : ℤ))) ∨ f.IsPrimitive := by
  by_cases hdeg : f.natDegree = 0
  · left
    have hC : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero hdeg
    have hirr : Irreducible (f.coeff 0) := by
      rw [hC] at hf
      exact (prime_C_iff.mp (irreducible_iff_prime.mp hf)).irreducible
    have hconst : ∃ p : ℕ, Nat.Prime p ∧ (f.coeff 0 = p ∨ f.coeff 0 = -(p : ℤ)) := by
      have hprime : Prime (f.coeff 0) := irreducible_iff_prime.mp hirr
      refine ⟨(f.coeff 0).natAbs, Int.prime_iff_natAbs_prime.mp hprime, ?_⟩
      rcases Int.natAbs_eq (f.coeff 0) with h | h
      · left
        exact h
      · right
        simpa [neg_neg] using h
    rcases hconst with ⟨p, hp, hp'⟩
    refine ⟨p, hp, ?_⟩
    rcases hp' with hpos | hneg
    · left
      calc
        f = C (f.coeff 0) := hC
        _ = C (p : ℤ) := by rw [hpos]
    · right
      calc
        f = C (f.coeff 0) := hC
        _ = C (-(p : ℤ)) := by rw [hneg]
        _ = -C (p : ℤ) := by simp
  · right
    exact hf.isPrimitive hdeg
