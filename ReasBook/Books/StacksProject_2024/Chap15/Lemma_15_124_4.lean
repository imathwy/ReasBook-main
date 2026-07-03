import Mathlib
import StacksProject_2024.Chap10.Definition_10_37_11
import StacksProject_2024.Chap15.Definition_15_124_1

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal
open IsExtensionOfValuationRings

universe u v

section

variable {R : Type u}
variable [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsNormalRing R]

/- Domain-style sampling for Lemma 15.124.4:
- primary domain: height-one localizations of Noetherian normal domains and weakly unramified
  extensions of valuation rings;
- sampled owner declarations:
  `IsExtensionOfDiscreteValuationRings`,
  `IsExtensionOfValuationRings`,
  `IsExtensionOfValuationRings.WeaklyUnramified`,
  `Localization.AtPrime.algebraOfLiesOver`,
  `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`;
- best owner abstraction: the localized branch should use the discrete-valuation-ring owner
  `IsExtensionOfDiscreteValuationRings`, with the valuation-ring owner
  `IsExtensionOfValuationRings` and the weakly-unramified predicate derived from it; the localized
  algebra is already the canonical `Localization.AtPrime` owner instance from the lying-over
  hypothesis rather than local wrapper data;
- primitive-vs-derived split: the primitive source data are the height-one points
  `p : { p : PrimeSpectrum _ // p.asIdeal.height = 1 }` and
  `q : { q : PrimeSpectrum _ // q.asIdeal.height = 1 }` together with the lying-over condition
  `q.1.asIdeal.LiesOver p.1.asIdeal`; the localized algebra, valuation-ring structure,
  extension-of-discrete-valuation-rings instance, and weakly unramified predicate are derived
  API on that owner.

Source/core/bridge triage:
- `source-facing`: `IsWeaklyUnramifiedHeightOneBranch` and
  `HasWeaklyUnramifiedHeightOneBranches`;
- `core/canonical`: `IsExtensionOfDiscreteValuationRings`, `IsExtensionOfValuationRings`, and
  `IsExtensionOfValuationRings.WeaklyUnramified`;
- `bridge/view`: the canonical localized `Algebra` structure
  `Localization.AtPrime p → Localization.AtPrime q` induced by `q.LiesOver p`. -/

/-- A height-one localization of a Noetherian normal domain is a discrete valuation ring. -/
private instance localizationAtHeightOnePrime_isDiscreteValuationRing
    (p : { p : PrimeSpectrum R // p.asIdeal.height = 1 }) :
    IsDiscreteValuationRing (Localization.AtPrime p.1.asIdeal) := by
  sorry

end

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [IsNoetherianRing A] [IsNoetherianRing B]
variable [IsDomain A] [IsDomain B]
variable [IsNormalRing A] [IsNormalRing B]
variable [Module.Flat A B]

/-- The canonical localized algebra for a height-one branch `q` lying over `p`. -/
private noncomputable instance localizationAtHeightOnePrime_algebra
    (p : { p : PrimeSpectrum A // p.asIdeal.height = 1 })
    (q : { q : PrimeSpectrum B // q.asIdeal.height = 1 }) [q.1.asIdeal.LiesOver p.1.asIdeal] :
    Algebra (Localization.AtPrime p.1.asIdeal) (Localization.AtPrime q.1.asIdeal) :=
  (Localization.localRingHom p.1.asIdeal q.1.asIdeal (algebraMap A B) Ideal.LiesOver.over).toAlgebra

/-- A height-one branch lying over another height-one branch induces an extension of discrete
valuation rings on localizations. -/
private instance localizationAtHeightOnePrime_isExtensionOfDiscreteValuationRings
    (p : { p : PrimeSpectrum A // p.asIdeal.height = 1 })
    (q : { q : PrimeSpectrum B // q.asIdeal.height = 1 }) [q.1.asIdeal.LiesOver p.1.asIdeal] :
    IsExtensionOfDiscreteValuationRings
      (Localization.AtPrime p.1.asIdeal) (Localization.AtPrime q.1.asIdeal) := by
  sorry

variable (A) (B) in
/-- A height-one branch `q` over `p` is weakly unramified when the induced localization
`A_p → B_q` is weakly unramified. -/
def IsWeaklyUnramifiedHeightOneBranch
    (p : { p : PrimeSpectrum A // p.asIdeal.height = 1 })
    (q : { q : PrimeSpectrum B // q.asIdeal.height = 1 })
    (hq : q.1.asIdeal.LiesOver p.1.asIdeal) : Prop :=
  letI : q.1.asIdeal.LiesOver p.1.asIdeal := hq
  let _ : Algebra (Localization.AtPrime p.1.asIdeal) (Localization.AtPrime q.1.asIdeal) :=
    localizationAtHeightOnePrime_algebra p q
  let _ : IsExtensionOfDiscreteValuationRings
      (Localization.AtPrime p.1.asIdeal) (Localization.AtPrime q.1.asIdeal) :=
    localizationAtHeightOnePrime_isExtensionOfDiscreteValuationRings p q
  WeaklyUnramified (Localization.AtPrime p.1.asIdeal) (Localization.AtPrime q.1.asIdeal)

variable (A) (B) in
/-- Every height-one prime of `A` admits a height-one branch in `B` whose localized extension is
weakly unramified. -/
def HasWeaklyUnramifiedHeightOneBranches : Prop :=
  ∀ p : { p : PrimeSpectrum A // p.asIdeal.height = 1 },
    ∃ q : { q : PrimeSpectrum B // q.asIdeal.height = 1 },
      ∃ hq : q.1.asIdeal.LiesOver p.1.asIdeal,
        IsWeaklyUnramifiedHeightOneBranch A B p q hq

-- Proof sketch: for each height-one point `p` of `Spec A`, use normality and Noetherianness to
-- view `A_p` and the chosen `B_q` as discrete valuation rings. Weak unramifiedness forces the
-- valuation of `f` in `A_p` to be divisible by `n`. Intersect the corresponding symbolic powers
-- over all minimal height-one primes of `f`, tensor the resulting ideal with `B`, and use the
-- flat local hypothesis to descend that this ideal is free of rank one. A generator `g ∈ A` then
-- has local valuations equal to those of `h`, so `f` differs from `g ^ n` by a unit of `A`.
/-- Lemma 15.124.4: let `A → B` be a flat local homomorphism of Noetherian local normal domains.
If `f ∈ A` becomes a unit times an `n`-th power in `B`, and every height-one
prime of `A` has a height-one prime of `B` above it with weakly unramified localized extension,
then `f` is already a unit times an `n`-th power in `A`. -/
theorem exists_unit_mul_pow_in_source_of_exists_unit_mul_pow_in_target
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    {f : A} {h : B} {n : ℕ}
    (hbranch : HasWeaklyUnramifiedHeightOneBranches A B)
    (hpow : ∃ w : Bˣ, algebraMap A B f = (w : B) * h ^ n) :
    ∃ (g : A) (u : Aˣ), f = (u : A) * g ^ n := sorry

end
