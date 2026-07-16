import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_82_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_39_18

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace LinearMap

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M]
variable {M' : Type x} [AddCommGroup M'] [Module S M']

-- Proof sketch: localize the tensor map `M ⊗[R] Q → M' ⊗[R] Q` at primes or maximal ideals of
-- `S`, identify these localizations with the tensor maps of the localized morphisms, and then use
-- exactness of localization together with the local criterion that a module is zero iff all of its
-- maximal localizations are zero.
/-- Lemma 10.82.11: for an `R`-algebra `S` and an `S`-linear map `M → M'`, universal injectivity
over `R` is equivalent to universal injectivity after localizing at every prime or maximal ideal of
`S`, either as a map of `R`-modules or as a map over the local rings `R_(q ∩ R)` and `R_(m ∩ R)`.
-/
theorem universallyInjective_localizedModule_atPrime_over_under_tfae (f : M →ₗ[S] M') :
    letI : Module R M := Module.restrictScalars R S M
    letI : Module R M' := Module.restrictScalars R S M'
    letI : IsScalarTower R S M := IsScalarTower.restrictScalars R S M
    letI : IsScalarTower R S M' := IsScalarTower.restrictScalars R S M'
    List.TFAE [
      UniversallyInjective (f.restrictScalars R),
      ∀ q : PrimeSpectrum S,
        UniversallyInjective ((LocalizedModule.map q.asIdeal.primeCompl f).restrictScalars R),
      ∀ m : MaximalSpectrum S,
        UniversallyInjective ((LocalizedModule.map m.asIdeal.primeCompl f).restrictScalars R),
      ∀ q : PrimeSpectrum S,
        UniversallyInjective
          ((LocalizedModule.map q.asIdeal.primeCompl f).restrictScalars
            (Localization.AtPrime (q.asIdeal.under R))),
      ∀ m : MaximalSpectrum S,
        UniversallyInjective
          ((LocalizedModule.map m.asIdeal.primeCompl f).restrictScalars
            (Localization.AtPrime (m.asIdeal.under R)))
    ] := sorry

end

end LinearMap
