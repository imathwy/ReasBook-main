import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Ideal IsLocalRing

section

variable {R : Type u} [CommRing R] [IsDomain R] [Finite (MaximalSpectrum R)]

omit [Finite (MaximalSpectrum R)] in
/-- Helper for Chap10 Example 10 35 8: in a nonfield domain, the product of all maximal ideals
indexed by a finite maximal spectrum is nonzero. -/
private lemma maximalSpectrumAsIdealProd_ne_bot_of_not_isField
    [Fintype (MaximalSpectrum R)] (hR : ¬ IsField R) :
    (∏ m : MaximalSpectrum R, m.asIdeal) ≠ (⊥ : Ideal R) := by
  -- Convert nonvanishing of the finite product into the absence of `⊥` among its factors.
  rw [Ne, Finset.prod_eq_multiset_prod, Ideal.multiset_prod_eq_bot]
  intro hbot_mem
  rcases Multiset.mem_map.mp hbot_mem with ⟨m, _hm, hm_bot⟩
  -- A maximal ideal in a nonfield domain cannot be the zero ideal.
  exact Ring.ne_bot_of_isMaximal_of_not_isField m.isMaximal hR hm_bot

omit [IsDomain R] [Finite (MaximalSpectrum R)] in
/-- Helper for Chap10 Example 10 35 8: the product of all maximal ideals is contained in the
Jacobson radical. -/
private lemma maximalSpectrumAsIdealProd_le_ringJacobson
    [Fintype (MaximalSpectrum R)] :
    (∏ m : MaximalSpectrum R, m.asIdeal) ≤ Ring.jacobson R := by
  -- Rewrite the Jacobson radical as the infimum of all maximal ideals.
  rw [Ring.jacobson_eq_sInf_isMaximal]
  refine le_sInf ?_
  intro I hI
  -- Every maximal ideal appears as `m.asIdeal` for some point of the maximal spectrum.
  have hI_mem : I ∈ Set.range (MaximalSpectrum.asIdeal (R := R)) := by
    rw [MaximalSpectrum.range_asIdeal R]
    exact hI
  rcases hI_mem with ⟨m, rfl⟩
  -- The finite product is below the finite infimum, hence below each indexed maximal ideal.
  have hm_univ : m ∈ (Finset.univ : Finset (MaximalSpectrum R)) := by
    simp
  exact Ideal.prod_le_inf.trans
    (Finset.inf_le (f := fun m : MaximalSpectrum R => m.asIdeal) (s := Finset.univ) hm_univ)

/-- Chap10 Example 10 35 8: in a nonfield domain with finite maximal spectrum, the Jacobson
radical is nonzero. -/
-- Proof sketch: enumerate the finitely many maximal ideals, show their product ideal is contained
-- in the Jacobson radical, and use that in a domain the product of finitely many nonzero ideals is
-- nonzero.
private theorem bot_lt_ringJacobson_of_finite_maximalSpectrum_of_not_isField
    (hR : ¬ IsField R) :
    (⊥ : Ideal R) < Ring.jacobson R := by
  -- Use the given finiteness of the maximal spectrum to form the finite product of all factors.
  letI : Fintype (MaximalSpectrum R) := Fintype.ofFinite (MaximalSpectrum R)
  have hprod_ne_bot := maximalSpectrumAsIdealProd_ne_bot_of_not_isField hR
  have hprod_le :
      (∏ m : MaximalSpectrum R, m.asIdeal) ≤ Ring.jacobson R :=
    maximalSpectrumAsIdealProd_le_ringJacobson
  -- The nonzero product gives a strict ideal above `⊥`, and containment transfers this to
  -- the Jacobson radical.
  exact (bot_lt_iff_ne_bot.mpr hprod_ne_bot).trans_le hprod_le

/-- Helper for Chap10 Example 10 35 8: a domain with finitely many maximal ideals is not a
Jacobson ring unless it is a field. -/
-- Proof sketch: if `R` were Jacobson, then `⊥` would equal the infimum of the maximal ideals.
-- With only finitely many maximal ideals, this infimum contains the product of all maximal ideals,
-- and in a domain that product is nonzero when `R` is not a field, so `⊥` cannot be that
-- intersection.
@[stacks 00G5]
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
