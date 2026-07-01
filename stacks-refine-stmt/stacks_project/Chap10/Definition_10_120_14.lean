import Mathlib.RingTheory.DedekindDomain.Factorization

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R]

namespace Ideal

/- A multiset factorization of an ideal is source-facing data: the factor ideals themselves and
their product. The canonical owner abstractions governing existence and uniqueness are upstream. -/
/-- A multiset `f` is a prime-ideal factorization of `I` if its entries are nonzero prime ideals
and its product is `I`. Equality of multisets records uniqueness up to permutation. -/
def IsPrimeFactorization (I : Ideal R) (f : Multiset (Ideal R)) : Prop :=
  (∀ P ∈ f, P ≠ ⊥ ∧ P.IsPrime) ∧ f.prod = I

end Ideal

end

section

variable (R : Type u) [CommRing R]

/-
Domain-style sampling:
- primary domain: Dedekind domains and factorization of ideals in commutative algebra;
- sampled owner API:
  `IsDedekindDomain`,
  `Ideal.uniqueFactorizationMonoid`,
  `UniqueFactorizationMonoid.factors_unique`,
  `Ideal.finprod_heightOneSpectrum_factorization`;
- source-facing: `IsDedekindDomainByFactorization R`, a domain whose nonzero ideals factor as a
  finite product of nonzero prime ideals, uniquely up to permutation;
- core/canonical: `IsDedekindDomain`;
- bridge/view: `HasUniquePrimeIdealFactorization R`, which isolates just the ideal-factorization
  clause from the full source-facing notion.

Primitive data are the prime-ideal factorizations themselves. The unique-factorization monoid
structure on ideals and the height-one-spectrum factorization formula are derived upstream API and
should remain companion canonical tools rather than replacing the source-facing statement. The
domain hypothesis belongs in the main source-facing owner, not in the bridge predicate alone.
-/

/-- Bridge predicate: every nonzero ideal admits a finite
factorization into nonzero prime ideals, uniquely up to permutation. -/
def HasUniquePrimeIdealFactorization : Prop :=
  ∀ I : Ideal R, I ≠ ⊥ → ∃! f : Multiset (Ideal R), I.IsPrimeFactorization f

/-- Definition 10.120.14, source-facing owner: a Dedekind domain is a domain whose nonzero ideals
factor uniquely into nonzero prime ideals. -/
def IsDedekindDomainByFactorization : Prop :=
  IsDomain R ∧ HasUniquePrimeIdealFactorization R

end

section

variable (R : Type u) [CommRing R] [IsDedekindDomain R]

open UniqueFactorizationMonoid

private theorem isPrimeFactorization_factors (R : Type u) [CommRing R] [IsDedekindDomain R]
    {I : Ideal R} (hI : I ≠ ⊥) :
    I.IsPrimeFactorization (factors I) := by
  refine ⟨?_, associated_iff_eq.mp ?_⟩
  · intro P hP
    have hprime : Prime P := prime_of_factor P hP
    exact ⟨by simpa [Ideal.zero_eq_bot] using hprime.ne_zero, Ideal.isPrime_of_prime hprime⟩
  · exact factors_prod (by simpa [Ideal.zero_eq_bot] using hI)

private theorem irreducible_of_mem_isPrimeFactorization
    (R : Type u) [CommRing R] [IsDedekindDomain R] {I : Ideal R} {f : Multiset (Ideal R)}
    (hf : I.IsPrimeFactorization f) {P : Ideal R} (hP : P ∈ f) : Irreducible P := by
  exact (Ideal.prime_of_isPrime (hf.1 P hP).1 (hf.1 P hP).2).irreducible

/-- In a Dedekind domain, every nonzero ideal admits a unique factorization into nonzero prime
ideals. This is the source-facing ideal-factorization bridge from the canonical owner
`IsDedekindDomain`. -/
theorem hasUniquePrimeIdealFactorization_of_isDedekindDomain :
    HasUniquePrimeIdealFactorization R := by
  intro I hI
  refine ⟨factors I, ?_, ?_⟩
  · exact isPrimeFactorization_factors R hI
  · intro g hg
    have hfactors : I.IsPrimeFactorization (factors I) := isPrimeFactorization_factors R hI
    have hrel : Multiset.Rel Associated (factors I) g := by
      apply factors_unique
      · intro P hP
        exact irreducible_of_mem_isPrimeFactorization R hfactors hP
      · intro P hP
        exact irreducible_of_mem_isPrimeFactorization R hg hP
      · exact associated_iff_eq.mpr (hfactors.2.trans hg.2.symm)
    have hfg : factors I = g := by
      simpa only [← Multiset.rel_eq, ← associated_eq_eq] using hrel
    exact hfg.symm

/-- A Dedekind domain satisfies the textbook factorization characterization of
Definition 10.120.14. -/
theorem isDedekindDomainByFactorization_of_isDedekindDomain :
    IsDedekindDomainByFactorization R :=
  ⟨inferInstance, hasUniquePrimeIdealFactorization_of_isDedekindDomain R⟩

variable (R : Type u) [CommRing R]

/-- Definition 10.120.14 is equivalent to the canonical owner `IsDedekindDomain`, but the
textbook factorization characterization remains the main public entry of this file. -/
theorem isDedekindDomain_iff_isDedekindDomainByFactorization :
    IsDedekindDomain R ↔ IsDedekindDomainByFactorization R := by
  constructor
  · intro hDed
    letI := hDed
    exact isDedekindDomainByFactorization_of_isDedekindDomain R
  · intro hfactor
    letI : IsDomain R := hfactor.1
    sorry

end
