import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_168_10 (from Chap10) -/
universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Domain-style sampling:
* primary domain: faithfully flat finitely presented ring maps and quasi-finite factorization in
  commutative algebra;
* sampled owner declarations:
  `RingHom.FaithfullyFlat`,
  `RingHom.FinitePresentation`,
  `RingHom.QuasiFinite`,
  `Algebra.FiniteType.QuasiFinite`;
* best owner abstraction:
  - `source-facing`: the existence of a factorization of `f` through a quasi-finite faithfully flat
    finitely presented map;
  - `core/canonical`: the ring-hom owner predicates `RingHom.FaithfullyFlat`,
    `RingHom.FinitePresentation`, and `RingHom.QuasiFinite`;
  - `bridge/view`: the comparison morphism `φ : S →+* S'`.
* primitive vs. derived:
  - primitive data: the target ring `S'` and the factor map `φ : S →+* S'`;
  - derived API: the induced composite `φ.comp f` and its owner properties.
-/

-- Proof sketch: first descend the faithfully flat finitely presented map `f` to a finitely
-- generated `ℤ`-model using Lemma `10.168.2`, reducing to the Noetherian case by base change.
-- Then use the Cohen--Macaulay open locus from Lemma `10.130.4` and openness of flatness and
-- quasi-finiteness to construct, for each prime of `R`, a localization-and-quotient of `S`
-- through which `f` factors and which is quasi-finite, flat, and of finite presentation near that
-- prime. Finally cover `Spec R` by finitely many such opens and take their product to recover
-- faithful flatness.
/-- Lemma 10.168.10: if `f : R →+* S` is faithfully flat and of finite presentation, then there
exists a commutative triangle `R → S → S'` such that the induced map `R → S'` is quasi-finite,
faithfully flat, and of finite presentation. -/
theorem exists_factorization_as_quasiFinite_faithfullyFlat_finitePresentation
    (f : R →+* S) (hff : f.FaithfullyFlat) (hfp : f.FinitePresentation) :
    ∃ (S' : Type (max u v)) (_ : CommRing S') (φ : S →+* S'),
      (φ.comp f).QuasiFinite ∧ (φ.comp f).FaithfullyFlat ∧ (φ.comp f).FinitePresentation := sorry

end
