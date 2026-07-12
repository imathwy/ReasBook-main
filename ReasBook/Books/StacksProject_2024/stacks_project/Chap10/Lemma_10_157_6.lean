import Mathlib
import StacksProject_2024.Chap10.Definition_10_67_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

/- Domain-style sampling:
- primary domain: commutative algebra of Noetherian normal domains, with principal quotients,
  embedded associated primes, fraction fields, principal submodules in the fraction field, and
  height-one localizations;
- sampled owner/bridge declarations:
  `embeddedAssociatedPrimes`,
  `embeddedAssociatedPrimes_eq_empty_iff`,
  `Module.embeddedAssociatedPrimes_eq_empty_iff_serreConditionS_one`,
  `Submodule.comap`,
  `Algebra.linearMap`,
  `moduleHeightOneLocalizationIntersection`,
  and `(algebraMap A K).range` as the canonical image owner used in `Lemma_10_50_11`;
- best owner abstractions:
  `embeddedAssociatedPrimes R M` for the no-embedded-primes clause,
  `(algebraMap R K).range` for image-membership in ambient fraction fields/localizations,
  `{ p : PrimeSpectrum R // p.asIdeal.height = 1 }` for the height-one-prime quantification,
  and the contracted principal `R`-submodule
  `((R ∙ x).comap (Algebra.linearMap R (FractionRing R)) : Ideal R)` for `R ∩ xR`;
- primitive data vs. derived API:
  the quotient modules, the principal `R`-submodule `R ∙ x ⊆ FractionRing R`, and the canonical
  algebra-map images are primitive here,
  while the older "every associated prime is minimal" packaging and `Set.range (algebraMap ...)`
  are bridge-level restatements that should not remain the public surface.

Source/core/bridge triage:
- `source-facing`: the three Stacks statements about principal quotients and height-one
  localization tests in a normal domain;
- `core/canonical`: `embeddedAssociatedPrimes`, `associatedPrimes`, `Ideal.comap`,
  `Submodule.comap`, the principal submodule owner `R ∙ x`, and ring-hom ranges;
- `bridge/view`: the height-one-prime subtype used to index those localizations and the
  membership criterion for the fraction field.
-/

/-- Lemma 10.157.6 (1): for a nonzero element `a` of a Noetherian normal domain `R`, the quotient
`R / aR` has no embedded associated primes, and every associated prime of `R / aR` has height
`1`. -/
-- Proof sketch: Serre's criterion gives `(S_2)` for `R`, and Lemma `10.72.6` descends this to
-- `(S_1)` for `R / aR`. Then Lemma `10.157.2` removes embedded primes, while Lemma `10.60.11`
-- shows that minimal primes over `(a)` have height at most `1`; since `a ≠ 0` in a domain, any
-- associated prime of `R / aR` is nonzero and hence has height exactly `1`.
theorem quotient_span_singleton_has_no_embedded_primes_and_associatedPrimes_height_eq_one
    {a : R} (ha : a ≠ 0) :
    embeddedAssociatedPrimes R (R ⧸ Ideal.span ({a} : Set R)) = ∅ ∧
      ∀ p ∈ associatedPrimes R (R ⧸ Ideal.span ({a} : Set R)), p.height = 1 := sorry

/-- Lemma 10.157.6 (2): an element of the fraction field of a Noetherian normal domain belongs to
`R` exactly when it belongs to every localization `R_𝔭` at a height-one prime `𝔭`. -/
-- Proof sketch: write the element as `b / a` with `a ≠ 0`. Apply part (1) to identify the
-- associated primes of `R / aR` with height-one primes and then use Lemma `10.63.19` in the cyclic
-- module `R / aR` to test membership in `aR` after localizing at those primes.
theorem mem_range_algebraMap_iff_mem_range_localizationAtPrime_forall_height_one
    (x : FractionRing R) :
    x ∈ (algebraMap R (FractionRing R)).range ↔
      ∀ p : { p : PrimeSpectrum R // p.asIdeal.height = 1 },
        x ∈ (algebraMap (Localization.AtPrime p.1.asIdeal) (FractionRing R)).range := sorry

/-- Lemma 10.157.6 (3): for a nonzero element `x` of the fraction field of a Noetherian normal
domain `R`, the quotient by the contraction of the principal `R`-submodule `xR ⊆ FractionRing R`,
namely `R / (R ∩ xR)`, has no embedded associated primes, and every associated prime of this
quotient has height `1`. -/
-- Proof sketch: write `x = a / b` and use part (2) to express `R ∩ xR` as an intersection over
-- the height-one primes minimal over `(ab)`. This embeds `R / (R ∩ xR)` into a finite direct sum
-- of quotients by symbolic powers of those primes, whose associated primes are singletons by Lemma
-- `10.64.2`; hence every associated prime is height one and none is embedded.
theorem quotient_fractionRing_principalSubmoduleContraction_has_no_embedded_primes_and_associatedPrimes_height_eq_one
    {x : FractionRing R} (hx : x ≠ 0) :
    embeddedAssociatedPrimes R
        (R ⧸
          ((R ∙ x).comap (Algebra.linearMap R (FractionRing R)) : Ideal R)) = ∅ ∧
      ∀ p ∈ associatedPrimes R
          (R ⧸
            ((R ∙ x).comap (Algebra.linearMap R (FractionRing R)) : Ideal R)),
        p.height = 1 := sorry

end
