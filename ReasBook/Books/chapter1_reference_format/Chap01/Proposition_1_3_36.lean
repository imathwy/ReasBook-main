import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Polynomial
open scoped BigOperators

section

variable {K : Type u} [Field K]

/-- Proposition 1.3.36 (1): factoring out the linear factors indexed by a finite set `s` with the
exponents given by `rootMultiplicity` leaves a quotient that does not vanish on `s`.

For the textbook formulation where `s` is a finite set of distinct roots of `P`, the omitted
root-membership hypothesis is redundant: elements of `s` outside the root set contribute exponent
`0`. -/
theorem exists_factorization_by_distinct_roots
    (P : K[X]) (hP : P ≠ 0) (s : Finset K) :
    ∃ G : K[X],
      P = G * ∏ a ∈ s, (X - C a) ^ P.rootMultiplicity a ∧
      ∀ a ∈ s, G.eval a ≠ 0 := by
  classical
  let F : K → K[X] := fun a ↦ (X - C a) ^ P.rootMultiplicity a
  have hpairwise :
      Set.Pairwise (↑s : Set K) (Function.onFun IsCoprime F) := by
    intro a ha b hb hab
    exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne hab).isUnit).pow
  have hprod_dvd : ∏ a ∈ s, F a ∣ P := by
    refine Finset.prod_dvd_of_coprime hpairwise ?_
    intro a ha
    exact Polynomial.pow_rootMultiplicity_dvd P a
  obtain ⟨G, hPG⟩ := hprod_dvd
  refine ⟨G, ?_, ?_⟩
  · simpa [F, mul_comm] using hPG
  · intro a ha hGa
    have hpow_dvd : (X - C a) ^ P.rootMultiplicity a ∣ ∏ b ∈ s, F b :=
      Finset.dvd_prod_of_mem F ha
    have hdivG : X - C a ∣ G := by
      rw [Polynomial.dvd_iff_isRoot]
      simpa [Polynomial.IsRoot] using hGa
    have hsucc_dvd' :
        (X - C a) ^ P.rootMultiplicity a * (X - C a) ∣ (∏ b ∈ s, F b) * G :=
      mul_dvd_mul hpow_dvd hdivG
    have hsucc_dvd : (X - C a) ^ (P.rootMultiplicity a + 1) ∣ P := by
      rw [pow_succ]
      exact hPG ▸ hsucc_dvd'
    exact (Polynomial.pow_rootMultiplicity_not_dvd hP a) hsucc_dvd

end

/-- Proposition 1.3.36 (2): a polynomial of degree `n` has at most `n` distinct roots in the
target domain. -/
theorem rootSet_ncard_le_of_natDegree_eq
    {A B : Type u} [CommRing A] [CommRing B] [IsDomain B] [Algebra A B]
    (P : A[X]) {n : ℕ} (hdeg : P.natDegree = n) : (P.rootSet B).ncard ≤ n := by
  simpa [hdeg] using ncard_rootSet_le P B
