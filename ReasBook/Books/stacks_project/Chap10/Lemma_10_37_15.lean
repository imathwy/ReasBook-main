import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Localization.AtPrime.Basic
import stacks_project.Chap10.Definition_10_37_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {ι : Type u} [Finite ι]
variable {R : ι → Type v} [∀ i, CommRing (R i)] [∀ i, IsNormalRing (R i)]

open Localization.AtPrime

private theorem isNormalLocalizationAtPrime_pi
    (p : PrimeSpectrum (Π i, R i)) :
    IsDomain (Localization.AtPrime p.asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime p.asIdeal) := by
  obtain ⟨i, q, rfl⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq p
  letI := isDomain_localizationAtPrime q
  letI := isIntegrallyClosed_localizationAtPrime q
  let e :
      Localization.AtPrime (Ideal.comap (Pi.evalRingHom R i) q.asIdeal) ≃+*
        Localization.AtPrime q.asIdeal :=
    RingEquiv.ofBijective (mapPiEvalRingHom q.asIdeal) (mapPiEvalRingHom_bijective q.asIdeal)
  exact ⟨Function.Injective.isDomain e e.injective, IsIntegrallyClosed.of_equiv e.symm⟩

/-- Lemma 10.37.15: a finite product of normal rings is normal. -/
theorem isNormalRing_pi : IsNormalRing (Π i, R i) :=
  ⟨isNormalLocalizationAtPrime_pi⟩

/-- A finite product of normal rings carries the canonical normal-ring instance. -/
instance : IsNormalRing (Π i, R i) := isNormalRing_pi

end
