import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsDomain R]

/- Lemma 10.120.5 lives in commutative factorization theory for domains.

Domain-style sampling:
- `UniqueFactorizationMonoid` is the `core/canonical` owner abstraction for unique factorization.
- `UniqueFactorizationMonoid.irreducible_iff_prime` is the owner theorem identifying
  irreducibles with primes inside a UFD.
- `UniqueFactorizationMonoid.of_exists_prime_factors` is the owner constructor from existence of
  prime factorizations.
- `exists_irreducible_factorization_of_accp` is the earlier chapter bridge producing the
  source-facing factorization hypothesis used here.

Layer triage:
- `source-facing`: the hypothesis that every nonzero nonunit factors into irreducibles.
- `core/canonical`: `UniqueFactorizationMonoid`.
- `bridge/view`: this lemma upgrades the source-facing factorization hypothesis to the owner
  abstraction once irreducibles are known to be prime. -/
/-- A domain has irreducible factorizations if every nonzero nonunit element is a product of
irreducible elements. -/
@[stacks 034T]
def HasIrreducibleFactorizations (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  ∀ a : R, a ≠ 0 → ¬ IsUnit a →
    ∃ f : Multiset R, (∀ b ∈ f, Irreducible b) ∧ f.prod = a

/-- Lemma 10.120.5: in an integral domain where every nonzero nonunit admits a
factorization into irreducibles, being a unique factorization domain is equivalent to every
irreducible element being prime. -/
-- Proof sketch: for the forward implication, use
-- `UniqueFactorizationMonoid.irreducible_iff_prime`. For the reverse implication, turn the given
-- irreducible factorization of each nonzero nonunit into a prime factorization using the
-- hypothesis that irreducibles are prime, then apply
-- `UniqueFactorizationMonoid.of_exists_prime_factors`.
@[stacks 034T]
theorem uniqueFactorizationMonoid_iff_forall_irreducible_prime_of_exists_irreducible_factorization
    (hfactor : HasIrreducibleFactorizations R) :
    UniqueFactorizationMonoid R ↔ ∀ a : R, Irreducible a → Prime a := by
  constructor
  · intro hufd a ha
    letI := hufd
    exact UniqueFactorizationMonoid.irreducible_iff_prime.mp ha
  · intro hirrPrime
    exact UniqueFactorizationMonoid.of_exists_prime_factors fun a ha ↦ by
      by_cases hua : IsUnit a
      · exact ⟨∅, by simpa using (associated_one_iff_isUnit.2 hua).symm⟩
      · obtain ⟨f, hf, hprod⟩ := hfactor a ha hua
        refine ⟨f, ?_, ?_⟩
        · intro b hb
          exact hirrPrime b (hf b hb)
        · simp [hprod]

end
