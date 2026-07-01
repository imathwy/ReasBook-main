import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling:
- primary domain: local étale / unramified behavior of prime ideals and residue fields in
  commutative algebra;
- sampled owner declarations:
  `Algebra.IsEtaleAt`,
  `Algebra.isUnramifiedAt_iff_map_eq`,
  `Algebra.FormallyUnramified.map_maximalIdeal`,
  `Localization.AtPrime.map_eq_maximalIdeal`;
- best owner abstraction: the core owner is local formal étaleness
  `Algebra.IsEtaleAt R q`, but the source-facing notion used in these two consequences is the
  existence of an étale basic-open neighborhood of `q`;
- source/core/bridge triage:
  - `source-facing`: an explicit witness `g ∉ q` with `R → S_g` étale;
  - `core/canonical`: `Algebra.IsEtaleAt`, `Algebra.IsUnramifiedAt`, and the local-ring owner
    API for maximal ideals and residue fields;
  - `bridge/view`: transporting the global étale neighborhood to the local ring `S_q`.
- primitive vs. derived:
  - primitive data: the prime `q` and an étale neighborhood `S_g` of `q`;
  - derived API: the equality `(q ∩ R) S_q = 𝔪_{S_q}` and finiteness/separability of
    `κ(q) / κ(q ∩ R)`.

The raw owner `Algebra.IsEtaleAt R q` is too weak by itself for the residue-field finiteness
conclusion, so this file should keep the source-facing neighborhood hypothesis rather than expose a
stronger conclusion from a weaker owner.
-/

-- Proof sketch: choose an étale basic-open neighborhood `S_g` of `q`. Étale implies unramified
-- on that neighborhood, so after localizing further at the prime over `q` the local criterion
-- `Algebra.isUnramifiedAt_iff_map_eq` gives `(q ∩ R) S_q = 𝔪_{S_q}`.
/-- Lemma 10.143.5 (1): if some neighborhood `R → S_g` with `g ∉ q` is étale, then the extended
ideal `(q ∩ R) S_q` is the maximal ideal of the local ring `S_q`. Equivalently,
`(q ∩ R) S_q = q S_q`. -/
theorem map_eq_maximalIdeal_of_exists_etale_away
    (q : Ideal S) [q.IsPrime]
    (hEt : ∃ g : S, g ∉ q ∧ Algebra.Etale R (Localization.Away g)) :
    (q.under R).map (algebraMap R (Localization.AtPrime q)) =
      maximalIdeal (Localization.AtPrime q) := sorry

-- Proof sketch: choose an étale neighborhood `S_g` of `q`, localize it at the prime over `q`,
-- and apply the local unramified field criterion there. The residue-field extension is unchanged
-- by inverting `g ∉ q`, so `κ(q) / κ(q ∩ R)` is finite and separable.
/-- Lemma 10.143.5 (2): if some neighborhood `R → S_g` with `g ∉ q` is étale, then the
residue-field extension `κ(q) / κ(q ∩ R)` is finite and separable. -/
theorem residueField_finite_and_separable_of_exists_etale_away
    (q : Ideal S) [q.IsPrime]
    (hEt : ∃ g : S, g ∉ q ∧ Algebra.Etale R (Localization.Away g)) :
    Module.Finite (q.under R).ResidueField q.ResidueField ∧
      Algebra.IsSeparable (q.under R).ResidueField q.ResidueField := sorry

end
