import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped BigOperators Polynomial

noncomputable section

open Polynomial
open UniqueFactorizationMonoid

variable {K : Type u} [Field K]

attribute [local instance] Classical.decEq

-- Proof sketch: use the canonical normalized factorization `factorization P`. Since the normalized
-- factors of a nonzero polynomial over a field are monic irreducibles, the scalar factor is forced
-- to be `P.leadingCoeff`, and uniqueness reduces to equality of multisets of normalized factors.
/-- Theorem 1.3.10: every nonzero polynomial in `K[X]` admits a unique factorization, up to order,
into a unit times powers of pairwise distinct monic irreducible polynomials. -/
theorem polynomial_existsUnique_unit_monic_irreducible_factorization
    (P : Polynomial K) (hP : P ≠ 0) :
    ∃! ν : Polynomial K →₀ ℕ,
      C P.leadingCoeff * ν.prod (fun p n ↦ p ^ n) = P ∧
        ∀ p ∈ ν.support, Irreducible p ∧ p.Monic := by
  refine ⟨factorization P, ?_, ?_⟩
  · constructor
    · have hprod :
          (factorization P).prod (fun p n ↦ p ^ n) = (normalizedFactors P).prod := by
          rw [factorization]
          simpa using
            (Finsupp.prod_toMultiset (Multiset.toFinsupp (normalizedFactors P))).symm
      rw [hprod]
      exact leadingCoeff_mul_prod_normalizedFactors P
    · intro p hp
      have hp' : p ∈ normalizedFactors P := by
        simpa [support_factorization] using hp
      have hp'' := (Polynomial.mem_normalizedFactors_iff hP).mp hp'
      exact ⟨hp''.1, hp''.2.1⟩
  · intro ν hν
    have hC : C P.leadingCoeff ≠ (0 : Polynomial K) := by
      exact C_ne_zero.mpr (leadingCoeff_ne_zero.mpr hP)
    have hνprod : ν.prod (fun p n ↦ p ^ n) = ν.toMultiset.prod := by
      exact (Finsupp.prod_toMultiset ν).symm
    have hprod : ν.toMultiset.prod = (normalizedFactors P).prod := by
      apply mul_left_cancel₀ hC
      rw [← hνprod, hν.1, leadingCoeff_mul_prod_normalizedFactors]
    have hνirr : ∀ p ∈ ν.toMultiset, Irreducible p := by
      intro p hp
      exact (hν.2 p (by simpa using hp)).1
    have hνmonic : ∀ p ∈ ν.toMultiset, p.Monic := by
      intro p hp
      exact (hν.2 p (by simpa using hp)).2
    have hνnormalize : ν.toMultiset.map normalize = ν.toMultiset := by
      simpa using
        (Multiset.map_congr rfl fun p hp ↦ (hνmonic p hp).normalize_eq_self)
    have hPnormalize : (normalizedFactors P).map normalize = normalizedFactors P := by
      simpa using
        (Multiset.map_congr rfl fun p hp ↦
          normalize_normalized_factor p hp)
    have hmultiset : ν.toMultiset = normalizedFactors P := by
      calc
        ν.toMultiset = ν.toMultiset.map normalize := hνnormalize.symm
        _ = normalizedFactors ν.toMultiset.prod := (normalizedFactors_prod_eq _ hνirr).symm
        _ = normalizedFactors ((normalizedFactors P).prod) := by rw [hprod]
        _ = (normalizedFactors P).map normalize := by
          rw [normalizedFactors_prod_eq _ fun p hp ↦ irreducible_of_normalized_factor p hp]
        _ = normalizedFactors P := hPnormalize
    exact (Finsupp.toMultiset_eq_iff).mp hmultiset
