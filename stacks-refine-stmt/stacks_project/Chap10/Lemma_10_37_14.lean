import Mathlib
import stacks_project.Chap10.Definition_10_37_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Polynomial

variable {R : Type u} [CommRing R] [IsNormalRing R]

private theorem isNormalLocalizationAtPrime_polynomial
    (q : PrimeSpectrum (Polynomial R)) :
    IsDomain (Localization.AtPrime q.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime q.asIdeal) := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap C q
  let I : Ideal R := p.asIdeal
  let Rₚ := Localization.AtPrime I
  let S := Polynomial Rₚ
  let M : Submonoid (Polynomial R) := I.primeCompl.map C
  letI : Algebra (Polynomial R) S :=
    (Polynomial.mapRingHom (algebraMap R Rₚ)).toAlgebra
  letI : IsLocalization M S := Polynomial.isLocalization I.primeCompl Rₚ
  let q' : Ideal S := Ideal.map (algebraMap (Polynomial R) S) q.asIdeal
  have hdisj : Disjoint (M : Set (Polynomial R)) q.asIdeal := by
    refine Set.disjoint_left.mpr fun f hf hfq ↦ ?_
    rcases hf with ⟨g, hg, rfl⟩
    exact hg (by simpa [p, I] using hfq)
  have hq' : Ideal.comap (algebraMap (Polynomial R) S) q' = q.asIdeal := by
    simpa [q'] using
      IsLocalization.comap_map_of_isPrime_disjoint M S q.2 hdisj
  letI : q'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M S q.asIdeal q.2 hdisj
  letI : IsLocalization.AtPrime (Localization.AtPrime q') q.asIdeal := by
    simpa [hq'] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        M _ q')
  let e : Localization.AtPrime q.asIdeal ≃ₐ[Polynomial R] Localization.AtPrime q' :=
    IsLocalization.algEquiv q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q')
  letI : IsDomain Rₚ := isDomain_localizationAtPrime p
  letI : IsIntegrallyClosed Rₚ := isIntegrallyClosed_localizationAtPrime p
  letI : IsNormalRing S := inferInstance
  letI : IsNormalRing (Localization.AtPrime q') := inferInstance
  exact ⟨MulEquiv.isDomain _ e.toMulEquiv,
    (show IsIntegrallyClosed (Localization.AtPrime q') from inferInstance).of_equiv
      e.symm.toRingEquiv⟩

-- Proof sketch: for a prime ideal `q` of `Polynomial R`, let `p` be its contraction to `R`.
-- Then `Localization.AtPrime p` is a normal domain because `R` is a normal ring. By
-- `Lemma 10.37.8`, the polynomial ring over that normal domain is normal, and by
-- `Lemma 10.37.5` the further localization at `q` is again a normal domain.
/-- Lemma 10.37.14: if `R` is a normal ring, then the polynomial ring `Polynomial R` is a normal
ring. -/
theorem isNormalRing_polynomial : IsNormalRing (Polynomial R) := by
  exact ⟨isNormalLocalizationAtPrime_polynomial⟩

/-- Polynomial rings over normal rings carry the canonical normal-ring instance. -/
instance : IsNormalRing (Polynomial R) := isNormalRing_polynomial

end
