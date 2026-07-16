import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Noetherian.Basic
import stacks_proof.stacks_project.Chap10.Definition_10_66_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (R : Type u) [CommRing R]

/- Domain-style sampling for Remark 15.25.5:
* primary domain: commutative algebra of prime localizations and weakly associated primes;
* sampled upstream owners:
  - `weaklyAssociatedPrimes R M` from Definition `10.66.1`,
  - `weaklyAssociatedPrimes_localizationMap_injective` from Lemma `10.66.17`,
  - `algebraMap_embedding_into_product_of_fields` from Lemma `10.25.2`,
  - `exists_injective_awayMap_atPrime_of_noetherian_or_reduced_finiteMinimalPrimes`
    from Lemma `10.31.9`;
* source-facing layer here: the existential condition that some finite family of prime
  localizations detects equality in `R`;
* best owner abstraction for that finite family: `Finset (PrimeSpectrum R)`, while the canonical
  chapter index owners for the main applications are `weaklyAssociatedPrimes R R` and
  `minimalPrimes R`;
* primitive data: only a finite family `s : Finset (PrimeSpectrum R)`;
* derived API: the injectivity of the induced map `R → ∀ p : s, Localization.AtPrime p.1.asIdeal`,
  together with the sufficient criteria below.
-/

/-- Remark 15.25.5: the condition used in Lemmas 15.25.1, 15.25.2, and 15.25.4 is that some
finite family of prime localizations of `R` detects equality in `R`. -/
@[stacks 05GS]
def primeLocalizationsDetectEquality : Prop :=
  ∃ s : Finset (PrimeSpectrum R),
    Function.Injective
      (fun r : R ↦
        fun p : s ↦ algebraMap R (Localization.AtPrime p.1.asIdeal) r)

section Local

variable [IsLocalRing R]

-- Proof sketch: use the singleton family consisting of the maximal ideal of the local ring. Since
-- every element outside the maximal ideal is a unit, localization at that prime is canonically the
-- ring itself, so the localization map is injective.
/-- A local ring satisfies the finite-prime localization-detection condition. -/
theorem primeLocalizationsDetectEquality_of_isLocalRing :
    primeLocalizationsDetectEquality R := sorry

end Local

section Noetherian

variable [IsNoetherianRing R]

-- Proof sketch: in a Noetherian ring, associated primes and weakly associated primes of the
-- regular module coincide, hence there are finitely many weakly associated primes. Apply the
-- injectivity statement of Lemma 10.66.17 to the canonical owner
-- `weaklyAssociatedPrimes R R`.
/-- A Noetherian ring satisfies the finite-prime localization-detection condition. -/
theorem primeLocalizationsDetectEquality_of_isNoetherianRing :
    primeLocalizationsDetectEquality R := sorry

end Noetherian

section Domain

variable [IsDomain R]

-- Proof sketch: use the singleton family containing the zero prime. Localization at `(0)` is the
-- total quotient ring of the domain, and the canonical map from a domain to its fraction field is
-- injective.
/-- A domain satisfies the finite-prime localization-detection condition. -/
theorem primeLocalizationsDetectEquality_of_isDomain :
    primeLocalizationsDetectEquality R := sorry

end Domain

section Reduced

variable [IsReduced R]

-- Proof sketch: take the finite family of minimal primes. For a reduced ring, Lemma 10.25.2 gives
-- injectivity of the canonical map from `R` to the product of the localizations indexed by the
-- owner type `minimalPrimes R`.
/-- A reduced ring with finitely many minimal primes satisfies the finite-prime
localization-detection condition. -/
theorem primeLocalizationsDetectEquality_of_isReduced_of_finite_minimalPrimes
    (hfinite : (minimalPrimes R).Finite) :
    primeLocalizationsDetectEquality R := sorry

end Reduced

section WeakAss

-- Proof sketch: index the family by the weakly associated primes of the regular module `R` and
-- apply Lemma 10.66.17 specialized to the owner `weaklyAssociatedPrimes R R`.
/-- A ring with finitely many weakly associated primes satisfies the finite-prime
localization-detection condition. -/
theorem primeLocalizationsDetectEquality_of_finite_weaklyAssociatedPrimes
    (hfinite : (weaklyAssociatedPrimes R R).Finite) :
    primeLocalizationsDetectEquality R := sorry

end WeakAss

end
