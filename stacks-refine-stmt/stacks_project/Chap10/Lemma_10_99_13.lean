import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ModuleCat

noncomputable section

universe u

section

variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M]

/-
Domain triage:
- primary domain: change-of-rings / base-change comparison on `Tor₁` for quotient modules;
- sampled owner declarations of the same kind:
  `CategoryTheory.Tor`,
  `CategoryTheory.tor_flip_iso`,
  `torBaseChangeHom`,
  `torOneBaseChangeMap`;
- best owner abstraction: the canonical bifunctor owner `CategoryTheory.Tor`, with
  `tor_flip_iso`, `torBaseChangeHom`, and `torOneBaseChangeMap` providing the existing
  `bridge/view` change-of-rings machinery in the chapter;
- primitive data: the ring map `R → S`, the ideal `I`, and the `R`-module `M`;
- derived API: the source-facing existence and surjectivity statement for the natural comparison
  morphism `Tor₁^R(S / IS, M) → Tor₁^S(S / IS, S ⊗[R] M)`.

Layering:
- `source-facing`: the surjective comparison morphism of Lemma 10.99.13;
- `core/canonical`: the owner bifunctor `Tor'`;
- `bridge/view`: `tor_flip_iso`, `torBaseChangeHom`, and any quotient-tensor identifications used
  to build the map belong in the proof, not as a parallel public owner.
-/

private abbrev extendedIdeal (I : Ideal R) : Ideal S :=
  Ideal.map (algebraMap R S) I

private abbrev quotientModule (I : Ideal R) : ModuleCat S :=
  ModuleCat.of S (S ⧸ extendedIdeal I)

private abbrev baseChangedModule : ModuleCat S :=
  (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R M)

private abbrev torOneQuotientSource (I : Ideal R) : ModuleCat R :=
  (((Tor (ModuleCat R) 1).obj
      (ModuleCat.of R (S ⧸ extendedIdeal I))).obj
    (ModuleCat.of R M))

private abbrev torOneQuotientTarget (I : Ideal R) : ModuleCat S :=
  (((Tor (ModuleCat S) 1).obj (quotientModule I)).obj
    (@baseChangedModule R S M _ _ _ _ _))

private abbrev torOneQuotientTargetRestrict (I : Ideal R) : ModuleCat R :=
  (ModuleCat.restrictScalars (algebraMap R S)).obj
    ((@torOneQuotientTarget R S M _ _ _ _ _ I) : ModuleCat S)

-- Proof sketch: resolve `M` by a free `R`-resolution, tensor termwise with `S / IS`, and compare
-- the resulting complex with an `S`-free resolution of `S ⊗[R] M` extending the scalar-extended
-- resolution. The induced map on degree-one homology is the textbook comparison map, and the extra
-- free summand in degree two makes that map surjective.
/-- Lemma 10.99.13: with `I' = IS` and `M' = S ⊗[R] M`, there exists a natural comparison map
`Tor₁^R(S / I', M) → Tor₁^S(S / I', M')`, written in Lean using the canonical owner
`CategoryTheory.Tor`; the target is viewed over `R` using the canonical
`ModuleCat.restrictScalars` functor. This comparison is surjective. The chapter already contains
the owner-level `Tor`/base-change machinery, but this particular quotient-coefficient comparison is
recorded here only at the source-facing existence/surjectivity layer to avoid introducing a
noncanonical chosen witness as public API. -/
theorem exists_surjective_torOne_quotient_baseChangeComparison (I : Ideal R) :
    ∃ comparison :
      ((@torOneQuotientSource R S M _ _ _ _ _ I) : ModuleCat R) ⟶
        ((@torOneQuotientTargetRestrict R S M _ _ _ _ _ I) : ModuleCat R),
      Function.Surjective comparison := sorry

end
