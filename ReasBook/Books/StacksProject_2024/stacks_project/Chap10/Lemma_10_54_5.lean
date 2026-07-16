import StacksProject_2024.stacks_project.Chap10.Definition_10_54_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

-- Proof sketch: choose an essential finite type presentation of `φ`, reduce to a localization of a
-- finite polynomial algebra over `R`, and then use the local hypotheses together with the valuation
-- ring argument from the text to find a maximal ideal of the polynomial ring lying over
-- `maximalIdeal R`. The resulting local ring maps to `S`, and `S` is explicitly a localization of
-- a quotient of that local ring.
/-- Lemma 10.54.5: if `φ : R →+* S` is essentially of finite type and `R` and `S` are local,
then there is a maximal ideal `m` of a finite polynomial ring over `R` lying over
`maximalIdeal R` such that `φ` factors through `Localization.AtPrime m.asIdeal`, and `S` is a
localization of a quotient of that local ring. -/
theorem exists_localized_polynomial_quotient_presentation
    (φ : R →+* S) (hφ : φ.EssFiniteType) :
    ∃ (n : ℕ)
      (m : { m : MaximalSpectrum (MvPolynomial (Fin n) R) //
        Ideal.comap MvPolynomial.C m.asIdeal = maximalIdeal R })
      (ψ : Localization.AtPrime m.1.asIdeal →+* S),
        RingHom.IsLocalizationOfQuotient ψ ∧
          φ = ψ.comp (algebraMap R (Localization.AtPrime m.1.asIdeal)) :=
  sorry

end
