import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Etale R S]

/- Domain-style sampling:
* primary domain: étale morphisms of commutative rings, localized standard étale neighborhoods,
  and finite flat covers with surjective spectrum map;
* sampled declarations:
  `Etale`,
  `IsEtaleAt.exists_isStandardEtale`,
  `exists_finitePresentation_flat_surjective_extension_lifting_primes`,
  `Module.Finite`,
  `Algebra.FinitePresentation`,
  `Module.Flat`;
* best owner abstraction:
  the source map is already controlled by the canonical owner `Etale R S`, and the target
  extension data should stay in the existing owner predicates `Module.Finite`, `Algebra.FinitePresentation`,
  `Module.Flat`, and the canonical spectrum-surjectivity predicate, rather than being repackaged
  into a new local class;
* source/core/bridge triage:
  this lemma is `source-facing`; the local factorization clause is the genuinely new source
  content, while the finiteness / flatness conditions are derived owner data on the chosen
  extension `S'`;
* primitive-vs-derived split:
  primitive existential data are only the extension ring `S'` and its `R`-algebra structure;
  the algebraic properties of `S'` and the spectrum-surjectivity statement belong in separate
  canonical predicates in the theorem output.
-/

-- Proof sketch: use Proposition `10.144.4` and quasi-compactness of `Spec(S)` to cover `Spec(S)`
-- by finitely many basic opens on which `R → S` becomes standard étale. Apply Lemma `10.144.5` to
-- each standard étale localization, then tensor the resulting finite flat covers over `R`. For a
-- prime of the tensor product, pick one factor lying over its image in `Spec(R)` and use the
-- corresponding localized factorization through that standard étale piece.
/-- Lemma 10.144.6: if `R → S` is étale and `Spec(S) → Spec(R)` is surjective, then there exists a
finite, finitely presented, flat `R`-algebra `S'` whose spectrum still surjects onto `Spec(R)`
and such that for every prime `q' ⊂ S'` there is an element `g' ∉ q'` for which the localized map
`R → S'[1 / g']` factors as `R → S → S'[1 / g']`. -/
theorem exists_finitePresentation_flat_surjective_localFactorization_extension
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S))) :
    ∃ (S' : Type (max u v)) (_ : CommRing S') (_ : Algebra R S')
      (_ : Module.Finite R S') (_ : Algebra.FinitePresentation R S')
      (_ : Module.Flat R S')
      (_ : Function.Surjective (PrimeSpectrum.comap (algebraMap R S'))),
        ∀ q' : PrimeSpectrum S',
          ∃ (g' : S') (_ : g' ∉ q'.asIdeal), Nonempty (S →ₐ[R] Localization.Away g') := sorry

end

end Algebra
