import Mathlib
import stacks_project.Chap15.Lemma_15_25_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open PrimeSpectrum

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: choose a surjection `MvPolynomial (Fin n) R →ₐ[R] S` from the finite-type
-- hypothesis, view `S` as a finite `MvPolynomial (Fin n) R`-module via this quotient, and apply
-- Lemma `15.25.1` to that module. The localized finite-presentation assumption on
-- `Localization.AtPrime p.asIdeal ⊗[R] S` gives the module-theoretic local finite-presentation
-- hypothesis over `MvPolynomial (Fin n) (Localization.AtPrime p.asIdeal)`, and the conclusion
-- identifies `S` as a finitely presented `R`-algebra.
/-- Lemma 15.25.2: if `R → S` is of finite type, `S` is flat over `R`, a finite family of prime
localizations of `R` detects equality, and for every prime `p` of `R` the localized algebra
`Localization.AtPrime p.asIdeal ⊗[R] S` is of finite presentation over `Localization.AtPrime
p.asIdeal`, then `S` is of finite presentation over `R`. -/
theorem finitePresentation_of_flat_of_finiteType_of_localizedAtPrimes_finitePresentation
    (hdetect : primeLocalizationsDetectEquality R)
    [Algebra.FiniteType R S] [Module.Flat R S]
    (hloc :
      ∀ p : PrimeSpectrum R,
        Algebra.FinitePresentation (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal ⊗[R] S)) :
    Algebra.FinitePresentation R S := sorry

end
