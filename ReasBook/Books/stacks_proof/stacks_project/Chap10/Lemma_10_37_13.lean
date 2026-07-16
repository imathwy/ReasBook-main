import stacks_proof.stacks_project.Chap10.Definition_10_37_11
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable (M : Submonoid R)

/- Lemma 10.37.13 is `source-facing`: it asserts that the chapter owner predicate
`IsNormalRing` is stable under localization. The primitive data are just the ambient
localization witness `[IsLocalization M S]`. The `core/canonical` ingredients are the
prime-localization API from `Definition 10.37.11` together with mathlib's standard
identification of a prime localization of `S` with the corresponding prime localization of `R`. -/
/-- Lemma 10.37.13: a localization of a normal ring is again a normal ring. -/
@[stacks 037C]
theorem isNormalRing_of_isLocalization [IsLocalization M S] [IsNormalRing R] :
    IsNormalRing S := by
  refine ⟨fun q ↦ ?_⟩
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  letI : IsLocalization.AtPrime (Localization.AtPrime q.asIdeal) p.asIdeal :=
    by
      simpa [p] using
        (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
          (Localization.AtPrime q.asIdeal) q.asIdeal)
  let e : Localization.AtPrime p.asIdeal ≃ₐ[R] Localization.AtPrime q.asIdeal :=
    IsLocalization.algEquiv p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal)
  exact ⟨Function.Injective.isDomain e.symm e.symm.injective,
    (isIntegrallyClosed_localizationAtPrime p).of_equiv e.toRingEquiv⟩

instance [IsNormalRing R] : IsNormalRing (Localization M) :=
  isNormalRing_of_isLocalization M

end
