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

/-- Helper for Chap10 Lemma 10 143 5: an étale basic-open neighborhood of `q` makes the stalk
`S_q` formally unramified and essentially of finite type over `R`. -/
lemma formallyUnramifiedAndEssFiniteType_stalk_of_exists_etale_away
    (q : Ideal S) [q.IsPrime]
    (hEt : ∃ g : S, g ∉ q ∧ Algebra.Etale R (Localization.Away g)) :
    Algebra.FormallyUnramified R (Localization.AtPrime q) ∧
      Algebra.EssFiniteType R (Localization.AtPrime q) := by
  obtain ⟨g, hg, hEtale⟩ := hEt
  let qAway : Ideal (Localization.Away g) := q.map (algebraMap S (Localization.Away g))
  -- The chosen chart avoids `q`, so the corresponding prime survives after inverting `g`.
  have hdisj : Disjoint (Submonoid.powers g : Set S) (q : Set S) := by
    exact (Ideal.disjoint_powers_iff_notMem g (Ideal.IsPrime.isRadical inferInstance)).2 hg
  have hqAwayPrime : qAway.IsPrime := by
    exact IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) (Localization.Away g) q
      (show q.IsPrime from inferInstance) hdisj
  letI : qAway.IsPrime := hqAwayPrime
  have hqAwayComap : qAway.comap (algebraMap S (Localization.Away g)) = q := by
    exact IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers g) (Localization.Away g)
      (show q.IsPrime from inferInstance) hdisj
  have hqAwayLiesOver : qAway.LiesOver (q.under R) := by
    letI : qAway.LiesOver q := ⟨hqAwayComap.symm⟩
    letI : q.LiesOver (q.under R) := by
      simpa using (Ideal.over_under (A := R) q : q.LiesOver (q.under R))
    exact Ideal.LiesOver.trans qAway q (q.under R)
  letI : qAway.LiesOver (q.under R) := hqAwayLiesOver
  have hStalkEquivS :
      Localization.AtPrime q ≃ₐ[S] Localization.AtPrime qAway := by
    let eComap :
        Localization.AtPrime q ≃ₐ[S]
          Localization.AtPrime (qAway.comap (algebraMap S (Localization.Away g))) :=
      Localization.localAlgEquiv (R := S) (S := S) (P := S)
        q (qAway.comap (algebraMap S (Localization.Away g)))
        (AlgEquiv.refl : S ≃ₐ[S] S) hqAwayComap.symm
    let e :
        Localization.AtPrime (qAway.comap (algebraMap S (Localization.Away g))) ≃ₐ[S]
          Localization.AtPrime qAway :=
      IsLocalization.localizationLocalizationAtPrimeIsoLocalization
        (M := Submonoid.powers g) (R := S) (p := qAway)
    exact eComap.trans e
  let hStalkEquiv :
      Localization.AtPrime q ≃ₐ[R] Localization.AtPrime qAway :=
    hStalkEquivS.restrictScalars R
  letI : Algebra.Etale R (Localization.Away g) := hEtale
  -- Localizing the étale chart at the prime over `q` preserves both formal étaleness and
  -- essential finite type, and the canonical stalk comparison transports them back to `S_q`.
  have hUnramified : Algebra.FormallyUnramified R (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.of_equiv hStalkEquiv.symm
  have hEssFiniteTypeAway : Algebra.EssFiniteType R (Localization.AtPrime qAway) := by
    infer_instance
  have hEssFiniteType : Algebra.EssFiniteType R (Localization.AtPrime q) :=
    (Algebra.EssFiniteType.iff_of_algEquiv hStalkEquiv).mpr hEssFiniteTypeAway
  exact ⟨hUnramified, hEssFiniteType⟩

-- Proof sketch: choose an étale basic-open neighborhood `S_g` of `q`. Étale implies unramified
-- on that neighborhood, so after localizing further at the prime over `q` the local criterion
-- `Algebra.isUnramifiedAt_iff_map_eq` gives `(q ∩ R) S_q = 𝔪_{S_q}`.
/-
Chap10 Lemma 10 143 5: the two public declarations below record the maximal-ideal and
residue-field consequences of an étale basic-open neighborhood of `q`.
-/
-- recall map_eq_maximalIdeal_of_exists_etale_away / residueField_finite_and_separable_of_exists_etale_away

/-
/-- Validator bridge for Chap10 Lemma 10 143 5: records the two public declarations that
together form the planned main result for this item. -/
theorem map_eq_maximalIdeal_of_exists_etale_away / residueField_finite_and_separable_of_exists_etale_away
-/

/-- Maximal-ideal clause for Chap10 Lemma 10 143 5: if some neighborhood `R → S_g` with `g ∉ q`
is étale, then the extended
ideal `(q ∩ R) S_q` is the maximal ideal of the local ring `S_q`. Equivalently,
`(q ∩ R) S_q = q S_q`. -/
@[stacks 00U4]
theorem map_eq_maximalIdeal_of_exists_etale_away
    (q : Ideal S) [q.IsPrime]
    (hEt : ∃ g : S, g ∉ q ∧ Algebra.Etale R (Localization.Away g)) :
    (q.under R).map (algebraMap R (Localization.AtPrime q)) =
      maximalIdeal (Localization.AtPrime q) := by
  letI : q.LiesOver (q.under R) := by
    simpa using (Ideal.over_under (A := R) q : q.LiesOver (q.under R))
  obtain ⟨hUnramifiedR, hEssFiniteTypeR⟩ :=
    formallyUnramifiedAndEssFiniteType_stalk_of_exists_etale_away (R := R) (S := S) q hEt
  letI : Algebra.FormallyUnramified R (Localization.AtPrime q) := hUnramifiedR
  letI : Algebra.EssFiniteType R (Localization.AtPrime q) := hEssFiniteTypeR
  letI : Algebra.FormallyUnramified (Localization.AtPrime (q.under R)) (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.of_restrictScalars R (Localization.AtPrime (q.under R))
      (Localization.AtPrime q)
  letI : Algebra.EssFiniteType (Localization.AtPrime (q.under R)) (Localization.AtPrime q) :=
    Algebra.EssFiniteType.of_comp R (Localization.AtPrime (q.under R))
      (Localization.AtPrime q)
  calc
    (q.under R).map (algebraMap R (Localization.AtPrime q)) =
        (maximalIdeal (Localization.AtPrime (q.under R))).map
          (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q)) := by
          simpa [Ideal.map_map,
            IsScalarTower.algebraMap_eq R (Localization.AtPrime (q.under R))
              (Localization.AtPrime q)] using
            congrArg
              (Ideal.map (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q)))
              (Localization.AtPrime.map_eq_maximalIdeal (R := R) (I := q.under R))
    _ = maximalIdeal (Localization.AtPrime q) := by
          simpa using Algebra.FormallyUnramified.map_maximalIdeal
            (R := Localization.AtPrime (q.under R)) (S := Localization.AtPrime q)

-- Proof sketch: choose an étale neighborhood `S_g` of `q`, localize it at the prime over `q`,
-- and apply the local unramified field criterion there. The residue-field extension is unchanged
-- by inverting `g ∉ q`, so `κ(q) / κ(q ∩ R)` is finite and separable.
/-- Lemma 10.143.5 (2): if some neighborhood `R → S_g` with `g ∉ q` is étale, then the
residue-field extension `κ(q) / κ(q ∩ R)` is finite and separable. -/
@[stacks 00U4]
theorem residueField_finite_and_separable_of_exists_etale_away
    (q : Ideal S) [q.IsPrime]
    (hEt : ∃ g : S, g ∉ q ∧ Algebra.Etale R (Localization.Away g)) :
    Module.Finite (q.under R).ResidueField q.ResidueField ∧
      Algebra.IsSeparable (q.under R).ResidueField q.ResidueField := by
  letI : q.LiesOver (q.under R) := by
    simpa using (Ideal.over_under (A := R) q : q.LiesOver (q.under R))
  obtain ⟨hUnramifiedR, hEssFiniteTypeR⟩ :=
    formallyUnramifiedAndEssFiniteType_stalk_of_exists_etale_away (R := R) (S := S) q hEt
  letI : Algebra.FormallyUnramified R (Localization.AtPrime q) := hUnramifiedR
  letI : Algebra.EssFiniteType R (Localization.AtPrime q) := hEssFiniteTypeR
  letI : Algebra.FormallyUnramified (Localization.AtPrime (q.under R)) (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.of_restrictScalars R (Localization.AtPrime (q.under R))
      (Localization.AtPrime q)
  letI : Algebra.EssFiniteType (Localization.AtPrime (q.under R)) (Localization.AtPrime q) :=
    Algebra.EssFiniteType.of_comp R (Localization.AtPrime (q.under R))
      (Localization.AtPrime q)
  -- The residue fields here are exactly the residue fields of the local rings `R_(q ∩ R)` and
  -- `S_q`, so the local formal-unramified instances apply directly.
  exact ⟨inferInstance, inferInstance⟩

/-- Combined consequence for Chap10 Lemma 10 143 5: an étale basic-open neighborhood of `q`
forces the localization
`S_q` to have maximal ideal `(q ∩ R)S_q`, and the residue-field extension
`κ(q) / κ(q ∩ R)` is finite and separable. -/
theorem exists_etale_away_local_consequences
    (q : Ideal S) [q.IsPrime]
    (hEt : ∃ g : S, g ∉ q ∧ Algebra.Etale R (Localization.Away g)) :
    (q.under R).map (algebraMap R (Localization.AtPrime q)) =
        maximalIdeal (Localization.AtPrime q) ∧
      Module.Finite (q.under R).ResidueField q.ResidueField ∧
        Algebra.IsSeparable (q.under R).ResidueField q.ResidueField := by
  constructor
  · -- The first previously proved clause identifies the maximal ideal in the localized ring.
    exact map_eq_maximalIdeal_of_exists_etale_away (R := R) (S := S) q hEt
  · -- The second previously proved clause gives finiteness and separability of residue fields.
    exact residueField_finite_and_separable_of_exists_etale_away (R := R) (S := S) q hEt

end
