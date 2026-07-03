import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Ideal IsLocalRing

section

variable {R : Type u} [CommRing R] [IsDomain R] [Finite (MaximalSpectrum R)]

/-- In a nonfield domain with finite maximal spectrum, the Jacobson radical is nonzero. -/
-- Proof sketch: enumerate the finitely many maximal ideals, show their product ideal is contained
-- in the Jacobson radical, and use that in a domain the product of finitely many nonzero ideals is
-- nonzero.
private theorem bot_lt_ringJacobson_of_finite_maximalSpectrum_of_not_isField
    (hR : ¬ IsField R) :
    (⊥ : Ideal R) < Ring.jacobson R := sorry

/-- Example 10.35.8: a domain with finitely many maximal ideals is not a Jacobson ring unless it
is a field. -/
-- Proof sketch: if `R` were Jacobson, then `⊥` would equal the infimum of the maximal ideals.
-- With only finitely many maximal ideals, this infimum contains the product of all maximal ideals,
-- and in a domain that product is nonzero when `R` is not a field, so `⊥` cannot be that
-- intersection.
theorem not_isJacobsonRing_of_finite_maximalSpectrum_of_not_isField
    (hR : ¬ IsField R) :
    ¬ IsJacobsonRing R := by
  intro hJacobson
  letI : IsJacobsonRing R := hJacobson
  have hradical :
      Ring.jacobson R = (⊥ : Ideal R) := by
    simpa [Ideal.jacobson_bot, Ideal.radical_bot_of_noZeroDivisors] using
      (Ideal.radical_eq_jacobson (⊥ : Ideal R)).symm
  have hlt := bot_lt_ringJacobson_of_finite_maximalSpectrum_of_not_isField hR
  rw [hradical] at hlt
  exact (lt_irrefl (⊥ : Ideal R)) hlt

end

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A local ring with a prime ideal distinct from its maximal ideal is not Jacobson. -/
-- Proof sketch: in a Jacobson local ring every prime ideal would equal its Jacobson radical, but
-- the Jacobson radical of any proper ideal in a local ring is the maximal ideal, forcing every
-- prime ideal to be maximal. A distinct prime ideal contradicts this.
theorem not_isJacobsonRing_of_isLocalRing_of_exists_prime_ne_maximalIdeal
    (hP : ∃ P : Ideal R, P.IsPrime ∧ P ≠ maximalIdeal R) :
    ¬ IsJacobsonRing R := by
  rintro hJacobson
  letI : IsJacobsonRing R := hJacobson
  rcases hP with ⟨P, hPprime, hPne⟩
  exact hPne <|
    calc
      P = P.jacobson := by
        simpa [hPprime.radical] using (Ideal.radical_eq_jacobson P)
      _ = maximalIdeal R := jacobson_eq_maximalIdeal P hPprime.ne_top

end

section

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- A discrete valuation ring is not a Jacobson ring. -/
-- Proof sketch: a discrete valuation ring is local and not a field, so its maximal spectrum is a
-- singleton. Apply the finite-maximal-spectrum theorem to conclude that it cannot be Jacobson.
theorem IsDiscreteValuationRing.not_isJacobsonRing :
    ¬ IsJacobsonRing R :=
  not_isJacobsonRing_of_isLocalRing_of_exists_prime_ne_maximalIdeal
    ⟨⊥, Ideal.isPrime_bot, fun h ↦ IsDiscreteValuationRing.not_a_field R h.symm⟩

end
