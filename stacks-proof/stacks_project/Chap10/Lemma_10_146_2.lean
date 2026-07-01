import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v

namespace Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/- Domain-style sampling:
* primary domain: étale neighborhoods of local rings, prime/maximal-ideal factorization after
  finite faithfully flat extension, and localization maps to local rings;
* sampled declarations:
  `IsEtaleAt.exists_isStandardEtale`,
  `exists_finitePresentation_flat_surjective_extension_lifting_primes`,
  `AlgHom.comp_algebraMap`,
  `Localization.localRingHom`,
  `Localization.isLocalHom_localRingHom`;
* best owner abstraction:
  the primewise finite faithfully flat extension theorem from Lemma `10.144.5`, together with the
  canonical factorization owner `S →ₐ[R] Localization.AtPrime m'.asIdeal`, whose base-ring
  compatibility is already built into `AlgHom`;
* source/core/bridge triage:
  this file is `source-facing`, since it specializes the primewise owner theorem to the local-ring
  situation and extracts the factorization morphisms for maximal ideals of the auxiliary extension;
  the core/canonical layer is the primewise theorem from Lemma `10.144.5`, while the present file
  is the bridge from prime fibers to local factorizations;
* primitive-vs-derived split:
  primitive existential data are only the auxiliary `R`-algebra `S'` and its standard owner
  witnesses `Module.Finite`, `Algebra.FinitePresentation`, and
  `(algebraMap R S').FaithfullyFlat`;
  the source-facing output is the canonical factorization morphism
  `S →ₐ[R] Localization.AtPrime m'.asIdeal`, while locality of its underlying ring hom is a
  derived companion consequence.
-/

-- Proof sketch: write `S` as a localization of an étale `R`-algebra `T`. By Proposition
-- `10.144.4`, near the prime corresponding to the maximal ideal of `S`, the map `R → T` becomes
-- standard étale. Apply Lemma `10.144.5` to obtain a finite, finitely presented, faithfully flat
-- `R`-algebra `S'` with the required prime-lifting property, and then localize at each maximal
-- ideal of `S'` to induce the desired factorization morphism `S →ₐ[R] S'_{m'}`.
/-- Lemma 10.146.2: if `R → S` is a local homomorphism of local rings and `S` is a localization of
an étale `R`-algebra, then there exists a finite, finitely presented, faithfully flat `R`-algebra
`S'` such that for every maximal ideal `m'` of `S'`, the canonical map `R → S'_{m'}` factors
through `S` via an `R`-algebra map `S → S'_{m'}`. -/
theorem exists_finite_finitePresentation_faithfullyFlat_extension_with_factorizations
    (hS :
      ∃ (T : Type (max u v)) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra T S)
        (_ : IsScalarTower R T S) (_ : Algebra.Etale R T) (M : Submonoid T),
          IsLocalization M S) :
    ∃ (S' : Type (max u v)) (_ : CommRing S') (_ : Algebra R S')
      (_ : Module.Finite R S') (_ : Algebra.FinitePresentation R S')
      (_ : (algebraMap R S').FaithfullyFlat),
        ∀ m' : MaximalSpectrum S',
          Nonempty (S →ₐ[R] Localization.AtPrime m'.asIdeal) := sorry

/-- Companion to Lemma 10.146.2: the factorization through each local ring `S'_{m'}` may moreover
be chosen to be a local homomorphism. -/
theorem exists_finite_finitePresentation_faithfullyFlat_extension_with_local_factorizations
    (hS :
      ∃ (T : Type (max u v)) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra T S)
        (_ : IsScalarTower R T S) (_ : Algebra.Etale R T) (M : Submonoid T),
          IsLocalization M S) :
    ∃ (S' : Type (max u v)) (_ : CommRing S') (_ : Algebra R S')
      (_ : Module.Finite R S') (_ : Algebra.FinitePresentation R S')
      (_ : (algebraMap R S').FaithfullyFlat),
        ∀ m' : MaximalSpectrum S',
          ∃ φ : S →ₐ[R] Localization.AtPrime m'.asIdeal,
            IsLocalHom φ.toRingHom := sorry

end

end Algebra
