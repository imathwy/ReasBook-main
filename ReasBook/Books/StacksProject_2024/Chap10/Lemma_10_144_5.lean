import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsStandardEtale R S]

/- Domain-style sampling:
* primary domain: standard étale morphisms and prime lifting after finite flat base change in
  commutative algebra;
* sampled declarations:
  `IsStandardEtale`,
  `StandardEtalePresentation`,
  `Ideal.primesOver`,
  `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`,
  `Polynomial.exists_syntomic_finiteFree_faithfullyFlat_split_extension_of_monic`,
  `Algebra.HasGoingDown.of_flat`;
* best owner abstraction:
  the source algebra is controlled by the canonical owner `IsStandardEtale R S`, while the
  auxiliary extension should expose the existing owner predicates `Module.Finite`,
  `Algebra.FinitePresentation`, and `(algebraMap R S').FaithfullyFlat` directly, while primes over
  `p` should be indexed by the canonical owner fibers `p.asIdeal.primesOver _` instead of by raw
  spectrum points plus equalities;
* source/core/bridge triage:
  this lemma is `source-facing`; the extra localized prime-lifting clause is genuine new source
  content, while finiteness / finite presentation / faithful flatness are derived owner data on
  the chosen extension `S'`;
* primitive-vs-derived split:
  primitive existential data are only the extension ring `S'` and its `R`-algebra structure;
  the canonical algebraic properties above should remain separate owner witnesses, not primitive
  public fields of a new packaged predicate.
-/

-- Proof sketch: choose a standard étale presentation `S ≃ R[x, 1 / g]/(f)` with `f` monic.
-- Apply Lemma `10.136.14` to `f` to obtain a finite free faithfully flat extension `R → S'`
-- splitting `f`; this gives finite presentation and the canonical faithfully flat owner, from
-- which spectrum-surjectivity is derived by
-- `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`. For primes
-- `q ⊂ S` and `q' ⊂ S'` in the owner fibers over the same `p ⊂ R`, pick a root of the split polynomial over
-- `κ(q')` that lies on the irreducible factor corresponding to `q` and does not vanish on the
-- chosen denominator, yielding `g' ∉ q'` and an `R`-algebra map `S → S'_{g'}` whose inverse image
-- of the localized prime over `q'` is `q`.
/-- Lemma 10.144.5: for a standard étale morphism `R → S`, there exists an `R`-algebra `S'` that
is finite, finitely presented, and faithfully flat over `R`, hence has surjective spectrum map,
and such that for every prime `p` of `R`, every prime `q` of `S` over `p`, and every prime `q'`
of `S'` over `p`, one can localize `S'` away from an element outside `q'` so that the resulting
map `R → S'_{g'}` factors through an `R`-algebra map `S → S'_{g'}` carrying the localized prime
over `q'` back to `q`. -/
theorem exists_finitePresentation_flat_surjective_extension_lifting_primes :
    ∃ (S' : Type (max u v)) (_ : CommRing S') (_ : Algebra R S')
      (_ : Module.Finite R S') (_ : Algebra.FinitePresentation R S')
      (_ : (algebraMap R S').FaithfullyFlat),
        ∀ (p : PrimeSpectrum R) (q : p.asIdeal.primesOver S) (q' : p.asIdeal.primesOver S'),
          ∃ (g' : S') (_ : g' ∉ q'.1) (φ : S →ₐ[R] Localization.Away g'),
            Ideal.comap φ.toRingHom (Ideal.map (algebraMap S' (Localization.Away g')) q'.1) =
              q.1 := sorry

end

end Algebra
