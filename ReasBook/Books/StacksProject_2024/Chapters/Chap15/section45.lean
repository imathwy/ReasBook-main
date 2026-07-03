import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_45_1 (from Chap15) -/
open IsLocalRing
open RingHom

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {Rh : Type u} [CommRing Rh] [Algebra R Rh]
variable {Rsh : Type u} [CommRing Rsh] [Algebra R Rsh]

local notation "mR" => maximalIdeal R
local notation "mRh" => maximalIdeal Rh
local notation "mRsh" => maximalIdeal Rsh

/-
Domain-style sampling:
- primary domain: local henselization and strict henselization maps of local rings, together with
  their maximal-ideal and Artinian-quotient behavior;
- sampled owner declarations of the same kind:
  `isWeaklyEtale_of_isFilteredColimitOfEtale`,
  `IsHenselizationOf.map_maximalIdeal`,
  `IsStrictHenselizationOf.map_maximalIdeal`,
  `RingHom.formallyEtale_quotientMap_pow_bijective`,
  `strictHenselization_over_henselization_isStrictHenselizationOf`;
- best owner abstraction: the primitive source data is carried by `IsHenselizationOf` and
  `IsStrictHenselizationOf`; weakly étale and formally étale consequences, faithful flatness,
  maximal-ideal extension, and quotient comparison are derived API from those owners;
- primitive data: locality of the structural map, filtered-colimit-of-etale presentation,
  maximal-ideal image, and for henselizations the residue-field bijectivity;
- derived API: faithful flatness of the structural maps and the induced comparison on quotients by
  powers of the maximal ideal.

Layer triage:
- `source-facing`: parts (4), (6), and (7) of Lemma 15.45.1;
- `core/canonical`: `IsHenselizationOf`, `IsStrictHenselizationOf`,
  `isWeaklyEtale_of_isFilteredColimitOfEtale`,
  `Module.FaithfullyFlat.of_flat_of_isLocalHom`,
  `RingHom.formallyEtale_quotientMap_pow_bijective`;
- `bridge/view`: parts (1), (2), (3), and (5) as direct owner specializations, together with
  `strictHenselization_over_henselization_isStrictHenselizationOf`.
-/

section Henselization

variable [IsHenselizationOf R Rh]

/-- Lemma 15.45.1 (1): the canonical map from a local ring to its henselization is faithfully
flat. -/
theorem henselizationMap_faithfullyFlat :
    (algebraMap R Rh).FaithfullyFlat := by
  let _ : Algebra.IsWeaklyEtale R Rh :=
    isWeaklyEtale_of_isFilteredColimitOfEtale
      IsHenselizationOf.isFilteredColimitOfEtale
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

section StrictHenselization

variable {Rsh : Type u} [CommRing Rsh] [Algebra R Rsh]
variable [IsStrictHenselizationOf R Rsh]

/-- Lemma 15.45.1 (2): the canonical map from a local ring to its strict henselization is
faithfully flat. -/
theorem strictHenselizationMap_faithfullyFlat :
    (algebraMap R Rsh).FaithfullyFlat := by
  let _ : Algebra.IsWeaklyEtale R Rsh :=
    isWeaklyEtale_of_isFilteredColimitOfEtale
      IsStrictHenselizationOf.isFilteredColimitOfEtale
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

end StrictHenselization

section StrictOverHenselization
variable [Algebra Rh Rsh] [IsScalarTower R Rh Rsh]

-- Proof sketch: this is one of the defining properties of `IsHenselizationOf`.
/- Lemma 15.45.1 (3): the maximal ideal of a henselization is the extension of the maximal ideal
of the base local ring. -/
recall IsHenselizationOf.map_maximalIdeal

-- Proof sketch:
-- `strictHenselization_over_henselization_isStrictHenselizationOf` upgrades `R → Rsh` to a strict
-- henselization, so both sides identify with `maximalIdeal Rsh` via the owner theorem
-- `IsStrictHenselizationOf.map_maximalIdeal`.
/-- Lemma 15.45.1 (4): if `Rh` is a henselization of `R` and `Rsh` is a strict henselization of
`Rh`, then the image of the maximal ideal of `R` in `Rsh` is the image of the maximal ideal of
`Rh`. -/
theorem strictHenselizationOverHenselization_map_baseMaximalIdeal :
    Ideal.map (algebraMap R Rsh) mR = Ideal.map (algebraMap Rh Rsh) mRh := by
  calc
    Ideal.map (algebraMap R Rsh) mR =
        Ideal.map (algebraMap Rh Rsh) (Ideal.map (algebraMap R Rh) mR) := by
      simpa [Ideal.map_map, IsScalarTower.algebraMap_eq R Rh Rsh]
    _ = Ideal.map (algebraMap Rh Rsh) mRh := by
      rw [IsHenselizationOf.map_maximalIdeal]

variable [IsStrictHenselizationOf Rh Rsh]

-- Proof sketch: this is one of the defining properties of `IsStrictHenselizationOf` applied to
-- the henselian local ring `Rh`.
/- Lemma 15.45.1 (5): the maximal ideal of a strict henselization over `Rh` is the extension of
the maximal ideal of `Rh`. -/
recall IsStrictHenselizationOf.map_maximalIdeal

end StrictOverHenselization

-- Proof sketch: `RingHom.formallyEtale_of_isFilteredColimitOfEtale` makes the henselization map
-- `R → Rh` formally étale, and the induced map on closed fibers `R → Rh / maximalIdeal Rh` is
-- surjective because the residue-field map of a henselization is bijective. Apply the owner
-- theorem `RingHom.formallyEtale_quotientMap_pow_bijective` with `J = maximalIdeal Rh`.
/-- Lemma 15.45.1 (6): for every `n`, the canonical map
`R / maximalIdeal R ^ n → Rh / maximalIdeal Rh ^ n` is bijective. -/
theorem henselizationQuotientPowMap_bijective (n : ℕ) :
    Function.Bijective
      (Ideal.quotientMap (mRh ^ n) (algebraMap R Rh)
        (pow_maximalIdeal_le_comap_pow_maximalIdeal (algebraMap R Rh) n)) := sorry

end Henselization

section StrictHenselizationQuotients

-- For part `(7)`, use the canonical quotient owner
-- `Ideal.Quotient.algebraQuotientOfLEComap` as local instance data rather than a named local
-- wrapper.
local instance [IsStrictHenselizationOf R Rsh] (n : ℕ) :
    Algebra (R ⧸ mR ^ n) (Rsh ⧸ mRsh ^ n) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (pow_maximalIdeal_le_comap_pow_maximalIdeal (algebraMap R Rsh) n)

/-- Lemma 15.45.1 (7): there is a single family of elements of `Rˢʰ` whose classes modulo
`maximalIdeal Rˢʰ ^ n` form a basis of `Rˢʰ / maximalIdeal Rˢʰ ^ n` over
`R / maximalIdeal R ^ n` for every `n`. -/
theorem strictHenselization_exists_basis_lift_family [IsStrictHenselizationOf R Rsh] :
    ∃ (ι : Type u) (x : ι → Rsh), ∀ n : ℕ,
      ∃ b : Module.Basis ι (R ⧸ mR ^ n) (Rsh ⧸ mRsh ^ n),
        ∀ i, b i = Ideal.Quotient.mk _ (x i) := sorry

end StrictHenselizationQuotients

end

/-! ### Lemma_15_45_2 (from Chap15) -/
open IsLocalRing
open RingHom

universe u

/-
Domain-style sampling:
- primary domain: local commutative algebra of henselizations and strict henselizations, together
  with the owner predicates `FormallyEtale` and `RingHom.formally_smooth_for_adic`;
- sampled owner declarations of the same kind:
  `IsHenselizationOf`,
  `IsStrictHenselizationOf`,
  `Ring.DirectLimit.formallyEtale`,
  `RingHom.formallyEtale_of_isFilteredColimitOfEtale`,
  `RingHom.IsFilteredColimitOfEtale`,
  `RingHom.formally_smooth_for_adic`,
  `RingHom.formally_smooth_for_adic_maximalIdeal_of_formallyEtale`;
- best owner abstraction: the primitive source data are the henselization/strict-henselization
  owners, while formal étaleness and maximal-ideal-adic formal smoothness are derived API of the
  structural maps;
- primitive data: local-ring structure and the filtered-colimit-of-étale presentations stored in
  `IsHenselizationOf` / `IsStrictHenselizationOf`;
- derived API: the six source-facing formal-étale and maximal-ideal-adic formal-smoothness
  statements below.

Layer triage:
- `source-facing`: the six numbered parts of Lemma 15.45.2;
- `core/canonical`: `IsHenselizationOf`, `IsStrictHenselizationOf`,
  `RingHom.IsFilteredColimitOfEtale`, `FormallyEtale`, and `RingHom.formally_smooth_for_adic`;
- `bridge/view`: passage from the henselization owners to the formal-étale owner theorem
  `Ring.DirectLimit.formallyEtale`, and then to the maximal-ideal-adic formal-smoothness
  statements.
-/

section

variable {R : Type u}
variable [CommRing R] [IsLocalRing R]

section Henselization

variable {Rh : Type u}
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]

/-- Lemma 15.45.2 (1): the canonical map from a local ring to its henselization is formally
étale. -/
theorem henselizationMap_formallyEtale :
    (algebraMap R Rh).FormallyEtale :=
  formallyEtale_of_isFilteredColimitOfEtale
    IsHenselizationOf.isFilteredColimitOfEtale

/-- Lemma 15.45.2 (4): the canonical map from a local ring to its henselization is formally
smooth for the `maximalIdeal Rh`-adic topology. -/
theorem henselizationMap_formallySmooth_for_maximalIdeal_adic :
    (algebraMap R Rh).formally_smooth_for_adic (maximalIdeal Rh) :=
  formally_smooth_for_adic_maximalIdeal_of_formallyEtale
    henselizationMap_formallyEtale

end Henselization

section StrictHenselization

variable {Rsh : Type u}
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/-- Lemma 15.45.2 (3): the canonical map from a local ring to its strict henselization is
formally étale. -/
theorem strictHenselizationMap_formallyEtale :
    (algebraMap R Rsh).FormallyEtale :=
  formallyEtale_of_isFilteredColimitOfEtale
    IsStrictHenselizationOf.isFilteredColimitOfEtale

/-- Lemma 15.45.2 (6): the canonical map from a local ring to its strict henselization is
formally smooth for the `maximalIdeal Rsh`-adic topology. -/
theorem strictHenselizationMap_formallySmooth_for_maximalIdeal_adic :
    (algebraMap R Rsh).formally_smooth_for_adic (maximalIdeal Rsh) :=
  formally_smooth_for_adic_maximalIdeal_of_formallyEtale
    strictHenselizationMap_formallyEtale

end StrictHenselization

section StrictOverHenselization

variable {Rh Rsh : Type u}
variable [CommRing Rh] [IsLocalRing Rh]
variable [CommRing Rsh] [Algebra Rh Rsh] [IsStrictHenselizationOf Rh Rsh]

/-- Lemma 15.45.2 (2): the canonical comparison map from a henselization to a strict
henselization is formally étale. -/
theorem strictHenselizationOverHenselizationMap_formallyEtale :
    (algebraMap Rh Rsh).FormallyEtale :=
  formallyEtale_of_isFilteredColimitOfEtale
    IsStrictHenselizationOf.isFilteredColimitOfEtale

/- Lemma 15.45.2 (5): the canonical comparison map from a henselization to a strict
henselization is formally smooth for the `maximalIdeal Rsh`-adic topology. -/
recall strictHenselizationMap_formallySmooth_for_maximalIdeal_adic

end StrictOverHenselization

end

/-! ### Lemma_15_45_3 (from Chap15) -/
universe u

section

variable {R Rh Rsh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/-
Domain-style sampling:
- primary domain: local commutative algebra of henselizations, strict henselizations, and
  Noetherianity;
- sampled owner declarations of the same kind:
  `IsHenselizationOf`,
  `IsStrictHenselizationOf`,
  `List.TFAE`,
  `maximalIdealCompletionMap_bijective_of_flat_of_residueFieldBijective`,
  `henselizationMap_faithfullyFlat`;
- best owner abstraction: the source-facing content of this item is the `List.TFAE` statement for
  the canonical predicates `IsNoetherianRing R`, `IsNoetherianRing Rh`, and
  `IsNoetherianRing Rsh`;
- primitive data: the local ring `R` together with chosen henselization and strict henselization
  owners;
- derived API: completion comparison, flatness, and formal-smoothness facts already belong to
  their upstream owner files and should be reused directly rather than duplicated here.

Source/core/bridge triage:
- `source-facing`: the `List.TFAE` equivalence of Noetherianity for `R`, `Rh`, and `Rsh`;
- `core/canonical`: `IsHenselizationOf`, `IsStrictHenselizationOf`, and `IsNoetherianRing`;
- `bridge/view`: completion-comparison and faithful-flatness lemmas from the earlier chapter
  owners.
-/
-- Proof sketch: faithful flatness of the henselization and strict henselization maps gives the
-- implications from `Rh` or `Rsh` back to `R` by Noetherian descent. Conversely, when `R` is
-- Noetherian, both `Rh` and `Rsh` are filtered colimits of étale local `R`-algebras with maximal
-- ideal extended from `R`, so the Stacks proof shows their maximal-ideal completions are
-- Noetherian and then descends Noetherianity back to `Rh` and `Rsh`.
/-- Lemma 15.45.3: for a local ring `R`, the following are equivalent: `R` is Noetherian, a
henselization `Rh` of `R` is Noetherian, and a strict henselization `Rsh` of `R` is Noetherian.
-/
theorem isNoetherianRing_tfae_of_henselization_and_strictHenselization :
    List.TFAE [IsNoetherianRing R, IsNoetherianRing Rh, IsNoetherianRing Rsh] := sorry

end

section

/-- A henselization of a Noetherian local ring is Noetherian. -/
theorem isNoetherianRing_henselization
    (R : Type u) [CommRing R] [IsLocalRing R]
    (Rh : Type u) [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
    [IsNoetherianRing R] : IsNoetherianRing Rh := by
  obtain ⟨Rsh, _, _, _⟩ := exists_strictHenselization R
  have hTFAE : List.TFAE [IsNoetherianRing R, IsNoetherianRing Rh, IsNoetherianRing Rsh] :=
    isNoetherianRing_tfae_of_henselization_and_strictHenselization
  have hR : IsNoetherianRing R := inferInstance
  exact (hTFAE.out 0 1).mp hR

end

section

/-- A strict henselization of a Noetherian local ring is Noetherian. -/
theorem isNoetherianRing_strictHenselization
    (R : Type u) [CommRing R] [IsLocalRing R]
    (Rsh : Type u) [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]
    [IsNoetherianRing R] : IsNoetherianRing Rsh := by
  obtain ⟨Rh, _, _, _⟩ := exists_henselization R
  have hTFAE : List.TFAE [IsNoetherianRing R, IsNoetherianRing Rh, IsNoetherianRing Rsh] :=
    isNoetherianRing_tfae_of_henselization_and_strictHenselization
  have hR : IsNoetherianRing R := inferInstance
  exact (hTFAE.out 0 2).mp hR

end

/-! ### Lemma_15_45_4 (from Chap15) -/
universe u

section

/- Domain triage:
- primary domain: commutative algebra of reduced rings under henselization and strict
  henselization;
- sampled owner declarations:
  `IsHenselizationOf`,
  `IsStrictHenselizationOf`,
  `isReduced_of_faithfullyFlat`,
  `isReduced_of_isWeaklyEtale`,
  `isWeaklyEtale_of_isFilteredColimitOfEtale`;
- best owner abstraction: the source-facing TFAE statement should be phrased directly in terms of
  the canonical reducedness owner `IsReduced` on the three rings, with henselization data carried
  only by the ambient owner classes; ascent should factor through the chapter owner
  `Algebra.IsWeaklyEtale`, not through a parallel local ind-etale wrapper;
- primitive data: the local ring `R` and the chosen henselization / strict henselization rings;
  faithful flatness and weakly-etale reducedness ascent are derived API, not extra public data;
- `source-facing`: the three-way `List.TFAE` from the Stacks lemma;
- `core/canonical`: `IsReduced`, `RingHom.FaithfullyFlat`, and `Algebra.IsWeaklyEtale`;
- `bridge/view`: the pairwise `↔` consequences extracted canonically from the source-facing TFAE.
-/

variable {R Rh Rsh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

-- Proof sketch: reducedness descends from `Rh` to `R` by faithful flatness of flat local maps,
-- and descends from `Rsh` to `R` by the same faithfully-flat descent applied to the flat local
-- map `R → Rsh`. Conversely, the
-- filtered-colimit-of-etale presentations of `Rh` and `Rsh` upgrade to the chapter owner
-- `Algebra.IsWeaklyEtale`, so Lemma `15.105.8` ascends reducedness from `R` to both chosen
-- henselizations.
/-- Lemma 15.45.4: for a local ring `R`, the following are equivalent: `R` is reduced, a
henselization `Rh` of `R` is reduced, and a strict henselization `Rsh` of `R` is reduced. -/
theorem isReduced_tfae_henselization_strictHenselization :
    List.TFAE [IsReduced R, IsReduced Rh, IsReduced Rsh] := sorry

end

section

variable {R Rh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]

-- The `0 ↔ 1` implication extracted from the source-facing `TFAE`.
/-- A local ring is reduced if and only if any henselization is reduced. -/
theorem isReduced_iff_isReduced_henselization :
    IsReduced R ↔ IsReduced Rh := by
  obtain ⟨Rsh, hRshComm, hRshAlg, hRsh⟩ := exists_strictHenselization R
  let _ : CommRing Rsh := hRshComm
  let _ : Algebra R Rsh := hRshAlg
  let _ : IsStrictHenselizationOf R Rsh := hRsh
  have hTfae : List.TFAE [IsReduced R, IsReduced Rh, IsReduced Rsh] :=
    isReduced_tfae_henselization_strictHenselization
  exact hTfae.out 0 1

end

section

variable {R Rsh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

-- The `0 ↔ 2` implication extracted from the source-facing `TFAE`.
/-- A local ring is reduced if and only if any strict henselization is reduced. -/
theorem isReduced_iff_isReduced_strictHenselization :
    IsReduced R ↔ IsReduced Rsh := by
  obtain ⟨Rh, hRhComm, hRhAlg, hRh⟩ := exists_henselization R
  let _ : CommRing Rh := hRhComm
  let _ : Algebra R Rh := hRhAlg
  let _ : IsHenselizationOf R Rh := hRh
  have hTfae : List.TFAE [IsReduced R, IsReduced Rh, IsReduced Rsh] :=
    isReduced_tfae_henselization_strictHenselization
  exact hTfae.out 0 2

end

/-! ### Lemma_15_45_5 (from Chap15) -/
universe u

section

open IsLocalRing

variable {R Rh Rsh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/- Domain triage:
- primary domain: commutative algebra of nilradicals under henselization and strict
  henselization;
- sampled owner declarations:
  `Ideal.map_isLocallyNilpotent`,
  `Ideal.isRadical_iff_quotient_reduced`,
  `henselization_quotient_isHenselizationOf_quotient`,
  `strictHenselization_quotient_isStrictHenselizationOf_quotient`;
- best owner abstraction: the public statements should stay source-facing equalities of nilradicals,
  while the proof factors through the canonical owners `IsReduced`, `IsHenselizationOf`, and
  `IsStrictHenselizationOf` on the quotient rings;
- primitive data: only the local ring `R` and the chosen henselization / strict henselization;
  local nilpotence and reducedness of the quotient are derived API, not primitive fields.
-/

omit [IsLocalRing R] in
private theorem map_nilradical_eq_nilradical_of_isReduced_quotient
    {S : Type u} [CommRing S] [Algebra R S]
    (hReduced : IsReduced (S ⧸ Ideal.map (algebraMap R S) (nilradical R))) :
    Ideal.map (algebraMap R S) (nilradical R) = nilradical S := by
  apply le_antisymm
  · exact Ideal.map_isLocallyNilpotent (algebraMap R S) le_rfl
  · have hRadical : (Ideal.map (algebraMap R S) (nilradical R)).IsRadical :=
      (Ideal.isRadical_iff_quotient_reduced _).2 hReduced
    calc
      nilradical S = (⊥ : Ideal S).radical := rfl
      _ ≤ (Ideal.map (algebraMap R S) (nilradical R)).radical := Ideal.radical_mono bot_le
      _ = Ideal.map (algebraMap R S) (nilradical R) := Ideal.radical_eq_iff.mpr hRadical

private theorem nilradical_le_maximalIdeal : nilradical R ≤ maximalIdeal R := by
  simpa [IsLocalRing.ringJacobson_eq_maximalIdeal] using
    (nilradical_le_jacobson R : nilradical R ≤ Ring.jacobson R)

private theorem nilradical_ne_top : nilradical R ≠ ⊤ :=
  ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top nilradical_le_maximalIdeal

omit [IsLocalRing R] in
private theorem reduced_quotient_nilradical : IsReduced (R ⧸ nilradical R) := by
  exact (Ideal.isRadical_iff_quotient_reduced (nilradical R)).1 <| by
    simpa [nilradical] using (Ideal.radical_isRadical (⊥ : Ideal R))

-- Proof sketch: `nilradical R` is locally nilpotent by definition, so its extension to `Rh`
-- lies in `nilradical Rh` by `Ideal.map_isLocallyNilpotent`. The quotient
-- `Rh ⧸ Ideal.map (algebraMap R Rh) (nilradical R)` is a henselization of `R ⧸ nilradical R` by
-- Lemma `10.156.2`, and `R ⧸ nilradical R` is reduced because `nilradical R` is radical. Choose
-- any strict henselization of `R ⧸ nilradical R` via the owner-level existence theorem
-- `exists_strictHenselization`; then Lemma `15.45.4` makes the quotient of `Rh` reduced, so the
-- extended ideal is radical and hence equals `nilradical Rh`.
/-- Lemma 15.45.5 (1): for a local ring `R`, the extension of the nilradical of `R` to a
henselization `Rh` is the nilradical of `Rh`. -/
theorem henselization_map_nilradical :
    Ideal.map (algebraMap R Rh) (nilradical R) = nilradical Rh := by
  let I : Ideal R := nilradical R
  let _ : IsLocalRing (R ⧸ I) :=
    IsLocalRing.quotient I nilradical_ne_top
  let _ : IsHenselizationOf (R ⧸ I) (Rh ⧸ Ideal.map (algebraMap R Rh) I) :=
    henselization_quotient_isHenselizationOf_quotient I nilradical_ne_top
  have hReducedBase : IsReduced (R ⧸ I) := by
    simpa [I] using reduced_quotient_nilradical
  have hReducedQuotient : IsReduced (Rh ⧸ Ideal.map (algebraMap R Rh) I) :=
    isReduced_iff_isReduced_henselization.mp hReducedBase
  have hMap : Ideal.map (algebraMap R Rh) I = nilradical Rh :=
    map_nilradical_eq_nilradical_of_isReduced_quotient hReducedQuotient
  simpa [I] using hMap

-- Proof sketch: the strict quotient is a strict henselization of `R ⧸ nilradical R` by
-- Lemma `10.156.4`; choosing any henselization of the same reduced quotient and applying the
-- `0 ↔ 2` implication from Lemma `15.45.4` makes the strict quotient reduced.
/-- Lemma 15.45.5 (2): for a local ring `R`, the extension of the nilradical of `R` to a strict
henselization `Rsh` is the nilradical of `Rsh`. -/
theorem strictHenselization_map_nilradical :
    Ideal.map (algebraMap R Rsh) (nilradical R) = nilradical Rsh := by
  let I : Ideal R := nilradical R
  let _ : IsLocalRing (R ⧸ I) :=
    IsLocalRing.quotient I nilradical_ne_top
  let _ : IsStrictHenselizationOf (R ⧸ I) (Rsh ⧸ Ideal.map (algebraMap R Rsh) I) :=
    strictHenselization_quotient_isStrictHenselizationOf_quotient I nilradical_ne_top
  have hReducedBase : IsReduced (R ⧸ I) := by
    simpa [I] using reduced_quotient_nilradical
  have hReducedQuotient : IsReduced (Rsh ⧸ Ideal.map (algebraMap R Rsh) I) :=
    isReduced_iff_isReduced_strictHenselization.mp hReducedBase
  have hMap : Ideal.map (algebraMap R Rsh) I = nilradical Rsh :=
    map_nilradical_eq_nilradical_of_isReduced_quotient hReducedQuotient
  simpa [I] using hMap

end

/-! ### Lemma_15_45_6 (from Chap15) -/
universe u

section

variable {R Rh Rsh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/- Domain triage:
* primary domain: normality for local rings under henselization and strict henselization;
* sampled owner-style declarations: `IsNormalRing`, `IsHenselizationOf`,
  `IsStrictHenselizationOf`, `isNormalRing_of_faithfullyFlat`,
  `isNormalRing_of_smooth`, and `isNormalRing_of_isColimit_filtered_system`;
* core/canonical owners: `IsNormalRing` for the property being compared, and
  `IsHenselizationOf` / `IsStrictHenselizationOf` for the chosen algebra objects;
* primitive vs. derived API: the primitive inputs are only the chosen henselization and strict
  henselization instances; faithful-flat descent via `isNormalRing_of_faithfullyFlat` and
  smooth/filtered-colimit ascent via `isNormalRing_of_smooth` and
  `isNormalRing_of_isColimit_filtered_system` are canonical derived chapter API and should not be
  repackaged locally;
* layer split: the three-way `List.TFAE` is the `source-facing` statement, and pairwise
  equivalences are derived canonically via `List.TFAE.out` rather than kept as parallel local
  wrappers.
-/
-- Proof sketch: the maps `R → Rh` and `R → Rsh` are faithfully flat local maps because
-- henselizations and strict henselizations are filtered colimits of étale algebras. Normality then
-- descends from `Rh` or `Rsh` to `R` by faithful flatness. Conversely, if `R` is normal, each
-- étale stage in the filtered-colimit presentations of `Rh` and `Rsh` is normal by smooth ascent,
-- and the directed colimit remains normal. For a local ring, `IsNormalRing` is equivalent to the
-- textbook phrase “normal domain”.
/-- Lemma 15.45.6: for a local ring `R`, the following are equivalent: `R` is a normal ring, a
henselization `Rh` of `R` is a normal ring, and a strict henselization `Rsh` of `R` is a normal
ring. For local rings this matches the textbook formulation in terms of normal domains. -/
theorem isNormalRing_tfae_henselization_strictHenselization :
    List.TFAE [IsNormalRing R, IsNormalRing Rh, IsNormalRing Rsh] := by
  sorry

end

section

variable {R Rh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]

-- The `0 ↔ 1` implication extracted from the source-facing `TFAE`.
/-- A local ring is normal if and only if any henselization is normal. -/
theorem isNormalRing_iff_isNormalRing_henselization :
    IsNormalRing R ↔ IsNormalRing Rh := by
  obtain ⟨Rsh, _, _, _⟩ := exists_strictHenselization R
  have hTFAE : List.TFAE [IsNormalRing R, IsNormalRing Rh, IsNormalRing Rsh] :=
    isNormalRing_tfae_henselization_strictHenselization
  exact hTFAE.out 0 1

end

section

variable {R Rsh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

-- The `0 ↔ 2` implication extracted from the source-facing `TFAE`.
/-- A local ring is normal if and only if any strict henselization is normal. -/
theorem isNormalRing_iff_isNormalRing_strictHenselization :
    IsNormalRing R ↔ IsNormalRing Rsh := by
  obtain ⟨Rh, _, _, _⟩ := exists_henselization R
  have hTFAE : List.TFAE [IsNormalRing R, IsNormalRing Rh, IsNormalRing Rsh] :=
    isNormalRing_tfae_henselization_strictHenselization
  exact hTFAE.out 0 2

end

/-! ### Lemma_15_45_7 (from Chap15) -/
open IsLocalRing

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {Rh : Type u} [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable {Rsh : Type u} [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/- Domain triage:
* primary domain: Krull dimension of local rings under henselization and strict henselization;
* sampled owner declarations:
  `IsLocalRing.maximalIdeal_height_eq_ringKrullDim`,
  `IsLocalization.AtPrime.ringKrullDim_eq_height`,
  `henselizationMap_faithfullyFlat`,
  `strictHenselizationMap_faithfullyFlat`,
  `IsHenselizationOf.map_maximalIdeal`,
  `IsStrictHenselizationOf.map_maximalIdeal`;
* owner abstraction: the source-facing statements compare the two local rings by first comparing
  their closed-point localizations, then transporting that equality back to the ambient local rings
  through `IsLocalRing.maximalIdeal_height_eq_ringKrullDim`; faithful-flatness and maximal-ideal
  image are derived owner data supplying that closed-point comparison.
* primitive data: the local ring `R` and the chosen owner instances
  `IsHenselizationOf R Rh` / `IsStrictHenselizationOf R Rsh`;
* derived API: faithful-flatness of the structural maps, extension of the maximal ideal, and the
  zero-dimensional closed fiber at the closed point.

Layer triage:
* `source-facing`: the two equality statements for `ringKrullDim`;
* `core/canonical`: the local owner `ringKrullDim` together with the closed-point localization
  comparison;
* `bridge/view`: the passage between a local ring and the localization at its maximal ideal.
-/

-- Proof sketch: compare the two local rings at their closed points. Lemma `15.45.1` gives
-- faithful flatness of `R → Rh`, hence going down for the maximal ideal of `Rh`, and
-- `IsHenselizationOf.map_maximalIdeal` identifies the closed fiber with the residue field of the
-- localization at `maximalIdeal Rh`, so the closed-point comparison reduces to a zero-dimensional
-- fiber, after which the local and localized Krull dimensions are identified canonically by
-- `IsLocalRing.maximalIdeal_height_eq_ringKrullDim` and
-- `IsLocalization.AtPrime.ringKrullDim_eq_height`.
/-- Lemma 15.45.7 (1): a chosen henselization `Rh` of a local ring `R` has the same Krull
dimension as `R`. -/
theorem ringKrullDim_henselization_eq :
    ringKrullDim R = ringKrullDim Rh := by
  sorry

-- Proof sketch: as in part `(1)`, the canonical owner is the closed-point comparison
-- `Localization.AtPrime (maximalIdeal R) → Localization.AtPrime (maximalIdeal Rsh)`. The maximal
-- ideal of `Rsh` is the extension of `maximalIdeal R` by
-- `IsStrictHenselizationOf.map_maximalIdeal`, so the closed fiber is the residue field of the
-- localized target and has Krull dimension `0`; the ambient local equality again follows by the
-- canonical identification of a local ring with its closed-point localization on Krull dimension.
/-- Lemma 15.45.7 (2): a chosen strict henselization `Rsh` of a local ring `R` has the same Krull
dimension as `R`. -/
theorem ringKrullDim_strictHenselization_eq :
    ringKrullDim R = ringKrullDim Rsh := by
  sorry

end

/-! ### Lemma_15_45_8 (from Chap15) -/
open IsLocalRing

universe u

section

variable {R : Type u}
variable [CommRing R] [IsLocalRing R]

/- Domain-style sampling:
- primary domain: local commutative algebra of depth under flat local base change through
  henselization and strict henselization;
- sampled owner declarations:
  `moduleDepth`,
  `depth_target_eq_depth_source_add_depth_closed_fiber`,
  `closedFiberQuotAlgEquiv`,
  `henselizationMap_faithfullyFlat`,
  `strictHenselizationMap_faithfullyFlat`,
  `isNoetherianRing_tfae_of_henselization_and_strictHenselization`;
- best owner abstraction: the public statements should be the atomic equalities on the owner
  `moduleDepth`; the closed fiber belongs on the canonical owner
  `Ideal.Fiber (maximalIdeal R) S`, and the quotient by the extended maximal ideal is only an
  internal bridge used to show that fiber is a field;
- primitive data: the Noetherian local ring `R` and the chosen henselization and strict
  henselization owner instances;
- derived API: faithful flatness of the structural maps, Noetherianity of the target local rings,
  and the field structure on the closed fibers coming from the maximal-ideal image equalities.

Source/core/bridge triage:
- `source-facing`: the two depth equalities for henselization and strict henselization;
- `core/canonical`: `moduleDepth` and the closed-fiber owner `Ideal.Fiber`;
- `bridge/view`: `closedFiberQuotAlgEquiv` and the maximal-ideal image equalities from
  `IsHenselizationOf` and `IsStrictHenselizationOf`.
-/

private theorem moduleDepth_self_eq_zero_of_field (K : Type u) [Field K] :
    moduleDepth K K = 0 := by
  let _ : Ring.KrullDimLE 0 K :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr <| ringKrullDim_eq_zero_of_field K
  have hCM : Module.CohenMacaulay K K := self_cohenMacaulay_of_krullDimLE_zero K
  have hdepth : ringKrullDim K = .some (moduleDepth K K) :=
    (Module.supportDim_self_eq_ringKrullDim K).symm.trans hCM.supportDim_eq_moduleDepth
  rw [ringKrullDim_eq_zero_of_field K] at hdepth
  simpa using hdepth.symm

private noncomputable def closedFiberMaximalIdealQuotEquiv
    {S : Type u} [CommRing S] [Algebra R S] [IsLocalRing S]
    (hmap : Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S) :
    Ideal.Fiber (maximalIdeal R) S ≃+* S ⧸ maximalIdeal S :=
  (closedFiberQuotAlgEquiv :
      Ideal.Fiber (maximalIdeal R) S ≃ₐ[R]
        S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)).toRingEquiv.trans <|
    Ideal.quotEquivOfEq hmap

private theorem closedFiber_isLocalRing_aux
    {S : Type u} [CommRing S] [Algebra R S] [IsLocalRing S] [IsLocalHom (algebraMap R S)] :
    IsLocalRing (Ideal.Fiber (maximalIdeal R) S) := by
  let e :
      Ideal.Fiber (maximalIdeal R) S ≃ₐ[R]
        S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R) :=
    closedFiberQuotAlgEquiv
  letI : IsLocalRing (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) := by
    have hmap : Ideal.map (algebraMap R S) (maximalIdeal R) < (⊤ : Ideal S) :=
      IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S)
    have : Nontrivial (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)) :=
      Ideal.Quotient.nontrivial_iff.2 hmap.ne
    exact IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (Ideal.map (algebraMap R S) (maximalIdeal R)))
      Ideal.Quotient.mk_surjective
  exact
    (e.toRingEquiv.symm :
      S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R) ≃+*
        Ideal.Fiber (maximalIdeal R) S).isLocalRing

private theorem moduleDepth_closedFiber_eq_zero_of_map_maximalIdeal
    {S : Type u} [CommRing S] [Algebra R S] [IsLocalRing S]
    [IsLocalRing (Ideal.Fiber (maximalIdeal R) S)]
    (hmap : Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S) :
    moduleDepth (Ideal.Fiber (maximalIdeal R) S) (Ideal.Fiber (maximalIdeal R) S) = 0 := by
  let e : Ideal.Fiber (maximalIdeal R) S ≃+* S ⧸ maximalIdeal S :=
    closedFiberMaximalIdealQuotEquiv hmap
  letI : Field (S ⧸ maximalIdeal S) := Ideal.Quotient.field (maximalIdeal S)
  letI : Field (Ideal.Fiber (maximalIdeal R) S) :=
    IsField.toField <| e.toMulEquiv.isField (Field.toIsField _)
  simpa using moduleDepth_self_eq_zero_of_field (Ideal.Fiber (maximalIdeal R) S)

section Henselization

variable {Rh : Type u}
variable [IsNoetherianRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]

-- Proof sketch: apply the flat local depth formula of Lemma `10.163.2` to `R → Rh`. By
-- Lemma `15.45.3`, the chosen henselization is Noetherian, and Lemma `15.45.1` gives flatness of
-- the structural map. The defining maximal-ideal equality for a henselization identifies the
-- closed fiber with the residue-field quotient of `Rh`, hence with a field, so its depth is `0`.
/-- Lemma 15.45.8 (1): if `R` is a Noetherian local ring, then the depth of `R` equals the depth
of any chosen henselization `Rh`. -/
theorem moduleDepth_henselization_eq :
    moduleDepth R R = moduleDepth Rh Rh := by
  obtain ⟨Rsh, _, _, _⟩ := exists_strictHenselization R
  have hTFAE : List.TFAE [IsNoetherianRing R, IsNoetherianRing Rh, IsNoetherianRing Rsh] :=
    isNoetherianRing_tfae_of_henselization_and_strictHenselization
  have hR : IsNoetherianRing R := inferInstance
  let _ : IsNoetherianRing Rh :=
    (hTFAE.out 0 1).mp hR
  have hflat : (algebraMap R Rh).Flat :=
    (henselizationMap_faithfullyFlat : (algebraMap R Rh).FaithfullyFlat).flat
  letI : Module.Flat R Rh := RingHom.flat_algebraMap_iff.mp hflat
  let _ : IsLocalRing (Ideal.Fiber (maximalIdeal R) Rh) := closedFiber_isLocalRing_aux
  have hdepth :
      moduleDepth Rh Rh =
        moduleDepth R R +
          moduleDepth (Ideal.Fiber (maximalIdeal R) Rh) (Ideal.Fiber (maximalIdeal R) Rh) :=
    depth_target_eq_depth_source_add_depth_closed_fiber
  simpa [moduleDepth_closedFiber_eq_zero_of_map_maximalIdeal
      IsHenselizationOf.map_maximalIdeal] using hdepth.symm

end Henselization

section StrictHenselization

variable {Rsh : Type u}
variable [IsNoetherianRing R]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

-- Proof sketch: as in part `(1)`, apply Lemma `10.163.2` to `R → Rsh`. Lemma `15.45.3` supplies
-- Noetherianity of the strict henselization and Lemma `15.45.1` gives flatness. The defining
-- equality `Ideal.map (algebraMap R Rsh) (maximalIdeal R) = maximalIdeal Rsh` makes the closed
-- fiber a residue-field quotient of `Rsh`, hence a field of depth `0`.
/-- Lemma 15.45.8 (2): if `R` is a Noetherian local ring, then the depth of `R` equals the depth
of any chosen strict henselization `Rsh`. -/
theorem moduleDepth_strictHenselization_eq :
    moduleDepth R R = moduleDepth Rsh Rsh := by
  obtain ⟨Rh, _, _, _⟩ := exists_henselization R
  have hTFAE : List.TFAE [IsNoetherianRing R, IsNoetherianRing Rh, IsNoetherianRing Rsh] :=
    isNoetherianRing_tfae_of_henselization_and_strictHenselization
  have hR : IsNoetherianRing R := inferInstance
  let _ : IsNoetherianRing Rsh :=
    (hTFAE.out 0 2).mp hR
  have hflat : (algebraMap R Rsh).Flat :=
    (strictHenselizationMap_faithfullyFlat : (algebraMap R Rsh).FaithfullyFlat).flat
  letI : Module.Flat R Rsh := RingHom.flat_algebraMap_iff.mp hflat
  let _ : IsLocalRing (Ideal.Fiber (maximalIdeal R) Rsh) := closedFiber_isLocalRing_aux
  have hdepth :
      moduleDepth Rsh Rsh =
        moduleDepth R R +
          moduleDepth (Ideal.Fiber (maximalIdeal R) Rsh) (Ideal.Fiber (maximalIdeal R) Rsh) :=
    depth_target_eq_depth_source_add_depth_closed_fiber
  simpa [moduleDepth_closedFiber_eq_zero_of_map_maximalIdeal
      IsStrictHenselizationOf.map_maximalIdeal] using hdepth.symm

end StrictHenselization

end

/-! ### Lemma_15_45_9 (from Chap15) -/
open IsLocalRing

universe u

section

variable {R Rh Rsh : Type u}
variable [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

local notation "ClosedFiberH" => Ideal.Fiber (maximalIdeal R) Rh
local notation "ClosedFiberSh" => Ideal.Fiber (maximalIdeal R) Rsh

private noncomputable def closedFiberMaximalIdealQuotEquiv
    {S : Type u} [CommRing S] [Algebra R S] [IsLocalRing S]
    (hmap : Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S) :
    Ideal.Fiber (maximalIdeal R) S ≃+* S ⧸ maximalIdeal S :=
  (closedFiberQuotAlgEquiv :
      Ideal.Fiber (maximalIdeal R) S ≃ₐ[R]
        S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)).toRingEquiv.trans <|
    Ideal.quotEquivOfEq hmap

/-- A Noetherian local ring is Cohen-Macaulay if and only if any henselization is
Cohen-Macaulay. -/
theorem cohenMacaulayRing_iff_henselization :
    Module.CohenMacaulay R R ↔ Module.CohenMacaulay Rh Rh := by
  letI : IsNoetherianRing Rh := isNoetherianRing_henselization R Rh
  let _ : Module.Flat R Rh := RingHom.flat_algebraMap_iff.mp
    henselizationMap_faithfullyFlat.flat
  let e : ClosedFiberH ≃+* Rh ⧸ maximalIdeal Rh :=
    closedFiberMaximalIdealQuotEquiv IsHenselizationOf.map_maximalIdeal
  letI : Field (Rh ⧸ maximalIdeal Rh) := Ideal.Quotient.field (maximalIdeal Rh)
  letI : Field ClosedFiberH := IsField.toField <| e.toMulEquiv.isField (Field.toIsField _)
  have hiff :
      Module.CohenMacaulay Rh Rh ↔
        Module.CohenMacaulay R R ∧ Module.CohenMacaulay ClosedFiberH ClosedFiberH :=
    cohenMacaulayRing_iff_source_and_closedFiber
  have hfiber : Module.CohenMacaulay ClosedFiberH ClosedFiberH :=
    self_cohenMacaulay_of_krullDimLE_zero ClosedFiberH
  constructor
  · intro hR
    exact hiff.2 ⟨hR, hfiber⟩
  · intro hRh
    exact (hiff.1 hRh).1

/-- A Noetherian local ring is Cohen-Macaulay if and only if any strict henselization is
Cohen-Macaulay. -/
theorem cohenMacaulayRing_iff_strictHenselization :
    Module.CohenMacaulay R R ↔ Module.CohenMacaulay Rsh Rsh := by
  letI : IsNoetherianRing Rsh := isNoetherianRing_strictHenselization R Rsh
  let _ : Module.Flat R Rsh := RingHom.flat_algebraMap_iff.mp
    strictHenselizationMap_faithfullyFlat.flat
  let e : ClosedFiberSh ≃+* Rsh ⧸ maximalIdeal Rsh :=
    closedFiberMaximalIdealQuotEquiv IsStrictHenselizationOf.map_maximalIdeal
  letI : Field (Rsh ⧸ maximalIdeal Rsh) := Ideal.Quotient.field (maximalIdeal Rsh)
  letI : Field ClosedFiberSh := IsField.toField <| e.toMulEquiv.isField (Field.toIsField _)
  have hiff :
      Module.CohenMacaulay Rsh Rsh ↔
        Module.CohenMacaulay R R ∧ Module.CohenMacaulay ClosedFiberSh ClosedFiberSh :=
    cohenMacaulayRing_iff_source_and_closedFiber
  have hfiber : Module.CohenMacaulay ClosedFiberSh ClosedFiberSh :=
    self_cohenMacaulay_of_krullDimLE_zero ClosedFiberSh
  constructor
  · intro hR
    exact hiff.2 ⟨hR, hfiber⟩
  · intro hRsh
    exact (hiff.1 hRsh).1

-- Proof sketch: specialize the flat-local Cohen-Macaulay criterion
-- `cohenMacaulayRing_iff_source_and_closedFiber` to the henselization and strict-henselization
-- maps. Lemma `15.45.3` supplies the canonical Noetherianity instances for the target rings, and
-- Lemma `15.45.1` gives faithful flatness. In both cases the closed fiber identifies with the
-- residue field of the target local ring via the maximal-ideal image equality, hence is a field
-- and therefore Cohen-Macaulay.
/-- Lemma 15.45.9: for a Noetherian local ring `R`, the following are equivalent:
`R` is Cohen-Macaulay, a chosen henselization `Rh` of `R` is Cohen-Macaulay, and a chosen strict
henselization `Rsh` of `R` is Cohen-Macaulay. -/
theorem cohenMacaulayRing_tfae_of_henselization_and_strictHenselization :
    List.TFAE
      [Module.CohenMacaulay R R, Module.CohenMacaulay Rh Rh, Module.CohenMacaulay Rsh Rsh] := by
  letI : IsNoetherianRing Rh := isNoetherianRing_henselization R Rh
  letI : IsNoetherianRing Rsh := isNoetherianRing_strictHenselization R Rsh
  tfae_have 1 ↔ 2 := cohenMacaulayRing_iff_henselization
  tfae_have 1 ↔ 3 := cohenMacaulayRing_iff_strictHenselization
  tfae_finish

end

/-! ### Lemma_15_45_10 (from Chap15) -/
universe u

open IsLocalRing

section

variable {R Rh Rsh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/- Domain-style sampling:
* primary domain: regular local rings under henselization and strict henselization in local
  commutative algebra;
* sampled owner declarations:
  `IsRegularLocalRing`,
  `isRegularLocalRing_of_flat_localHom_of_regularTarget`,
  `isRegularLocalRing_of_flat_localHom_of_regular_closedFiber`,
  `isRegularLocalRing_closedFiber_of_quotient`;
* best owner abstraction: the source-facing statement should stay directly on the canonical owner
  `IsRegularLocalRing`; the theorem should therefore quantify only over the local ring and the
  chosen henselization / strict-henselization owners, recovering flatness, target Noetherianity,
  and closed-fiber regularity internally instead of exposing parallel auxiliary hypotheses;
* primitive data: the local base ring `R` and the chosen henselization / strict henselization
  owners;
* derived API: faithful flatness of `R → Rh` and `R → Rsh`, Noetherianity of `Rh` and `Rsh`, and
  regularity of the closed fibers through their quotient-field presentations.

Source/core/bridge triage:
* `source-facing`: the three-way `List.TFAE` for `IsRegularLocalRing`;
* `core/canonical`: `IsRegularLocalRing`;
* `bridge/view`: the closed-fiber owner `Ideal.Fiber (maximalIdeal R) S` together with the
  maximal-ideal image equalities for henselization and strict henselization.
-/

-- Proof sketch: for the backward implications, apply the canonical flat-local descent theorem for
-- regular local rings to the faithfully flat henselization and strict-henselization maps. For the
-- forward implications, apply the flat-local ascent theorem with regular closed fiber; the closed
-- fiber is canonically a residue-field quotient because the maximal ideal extends to the maximal
-- ideal of the henselization / strict henselization, hence it is a field and therefore a regular
-- local ring.
/-- Lemma 15.45.10: for a local ring `R`, the following are equivalent: `R` is a
regular local ring, a chosen henselization `Rh` of `R` is a regular local ring, and a chosen
strict henselization `Rsh` of `R` is a regular local ring. -/
theorem isRegularLocalRing_tfae_of_henselization_and_strictHenselization :
    List.TFAE [IsRegularLocalRing R, IsRegularLocalRing Rh, IsRegularLocalRing Rsh] := by
  sorry

end

/-! ### Lemma_15_45_11 (from Chap15) -/
universe u

section

variable {R Rh Rsh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/- Domain-style sampling:
* primary domain: local commutative algebra of discrete valuation rings under henselization and
  strict henselization;
* sampled owner declarations:
  `IsDiscreteValuationRing`,
  `discreteValuationRing_iff_regularLocalRing_dim_one`,
  `isRegularLocalRing_tfae_of_henselization_and_strictHenselization`,
  `ringKrullDim_henselization_eq`,
  `ringKrullDim_strictHenselization_eq`;
* best owner abstraction: the source-facing DVR clauses should be compared through the canonical
  owner pair `IsRegularLocalRing` and `ringKrullDim`, not by a parallel local DVR-specific bridge;
* primitive data: the local ring `R` and the chosen henselization / strict henselization owners;
* derived API: the equivalence between DVRs and one-dimensional regular local rings, together with
  the chapter's regular-local and Krull-dimension invariance theorems.

Source/core/bridge triage:
* `source-facing`: the three-way `List.TFAE` for the DVR condition;
* `core/canonical`: `IsRegularLocalRing` and `ringKrullDim`;
* `bridge/view`: `discreteValuationRing_iff_regularLocalRing_dim_one`,
  `isRegularLocalRing_tfae_of_henselization_and_strictHenselization`,
  `ringKrullDim_henselization_eq`, and `ringKrullDim_strictHenselization_eq`.
-/
-- Proof sketch: apply Lemma `10.119.7` to characterize discrete valuation rings as the
-- one-dimensional regular local rings, then use Lemma `15.45.10` for
-- preservation and reflection of regularity along henselization and strict henselization and
-- Lemma `15.45.7` for equality of Krull dimensions.
/-- Lemma 15.45.11: for a local ring `R`, the following are equivalent: `R` is a
discrete valuation ring, a chosen henselization `Rh` of `R` is a discrete valuation ring, and a
chosen strict henselization `Rsh` of `R` is a discrete valuation ring. -/
theorem discreteValuationRing_tfae_of_henselization_and_strictHenselization :
    List.TFAE
      [(∃ (_ : IsDomain R), IsDiscreteValuationRing R),
        (∃ (_ : IsDomain Rh), IsDiscreteValuationRing Rh),
        (∃ (_ : IsDomain Rsh), IsDiscreteValuationRing Rsh)] := by
  have hdimRh : ringKrullDim R = ringKrullDim Rh := ringKrullDim_henselization_eq
  have hdimRsh : ringKrullDim R = ringKrullDim Rsh := ringKrullDim_strictHenselization_eq
  have hRegular :
      List.TFAE [IsRegularLocalRing R, IsRegularLocalRing Rh, IsRegularLocalRing Rsh] :=
    isRegularLocalRing_tfae_of_henselization_and_strictHenselization
  have h12 :
      (∃ (_ : IsDomain R), IsDiscreteValuationRing R) ↔
        ∃ (_ : IsDomain Rh), IsDiscreteValuationRing Rh := by
    calc
      (∃ (_ : IsDomain R), IsDiscreteValuationRing R) ↔
          IsRegularLocalRing R ∧ ringKrullDim R = 1 :=
        discreteValuationRing_iff_regularLocalRing_dim_one
      _ ↔ IsRegularLocalRing Rh ∧ ringKrullDim R = 1 := by
        constructor
        · intro h
          exact ⟨(hRegular.out 0 1).mp h.1, h.2⟩
        · intro h
          exact ⟨(hRegular.out 0 1).mpr h.1, h.2⟩
      _ ↔ IsRegularLocalRing Rh ∧ ringKrullDim Rh = 1 := by
        constructor
        · intro h
          refine ⟨h.1, ?_⟩
          rw [← hdimRh]
          exact h.2
        · intro h
          refine ⟨h.1, ?_⟩
          rw [hdimRh]
          exact h.2
      _ ↔ (∃ (_ : IsDomain Rh), IsDiscreteValuationRing Rh) :=
        discreteValuationRing_iff_regularLocalRing_dim_one.symm
  have h13 :
      (∃ (_ : IsDomain R), IsDiscreteValuationRing R) ↔
        ∃ (_ : IsDomain Rsh), IsDiscreteValuationRing Rsh := by
    calc
      (∃ (_ : IsDomain R), IsDiscreteValuationRing R) ↔
          IsRegularLocalRing R ∧ ringKrullDim R = 1 :=
        discreteValuationRing_iff_regularLocalRing_dim_one
      _ ↔ IsRegularLocalRing Rsh ∧ ringKrullDim R = 1 := by
        constructor
        · intro h
          exact ⟨(hRegular.out 0 2).mp h.1, h.2⟩
        · intro h
          exact ⟨(hRegular.out 0 2).mpr h.1, h.2⟩
      _ ↔ IsRegularLocalRing Rsh ∧ ringKrullDim Rsh = 1 := by
        constructor
        · intro h
          refine ⟨h.1, ?_⟩
          rw [← hdimRsh]
          exact h.2
        · intro h
          refine ⟨h.1, ?_⟩
          rw [hdimRsh]
          exact h.2
      _ ↔ (∃ (_ : IsDomain Rsh), IsDiscreteValuationRing Rsh) :=
        discreteValuationRing_iff_regularLocalRing_dim_one.symm
  have h23 :
      (∃ (_ : IsDomain Rh), IsDiscreteValuationRing Rh) ↔
        ∃ (_ : IsDomain Rsh), IsDiscreteValuationRing Rsh :=
    h12.symm.trans h13
  intro x hx y hy
  simp only [List.mem_cons] at hx hy
  rcases hx with rfl | rfl | hx
  · rcases hy with rfl | rfl | hy
    · exact Iff.rfl
    · exact h12
    · rcases hy with rfl | hy
      · exact h13
      · cases hy
  · rcases hy with rfl | rfl | hy
    · exact h12.symm
    · exact Iff.rfl
    · rcases hy with rfl | hy
      · exact h23
      · cases hy
  · rcases hx with rfl | hx
    · rcases hy with rfl | rfl | hy
      · exact h13.symm
      · exact h23.symm
      · rcases hy with rfl | hy
        · exact Iff.rfl
        · cases hy
    · cases hx

end

/-! ### Lemma_15_45_12 (from Chap15) -/
universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

namespace PrimeSpectrum

/- Domain triage:
* primary domain: fibers `κ(p) ⊗[A] B`, primes of `B` lying over `p`, and their residue fields;
* source-facing items in this file: finiteness of the fiber over `p`, the resulting product
  decomposition of the fiber ring, and separable algebraicity of the residue-field extensions;
* sampled owners for the refinement:
  `RingHom.IsFilteredColimitOfEtale`,
  `isWeaklyEtale_of_isFilteredColimitOfEtale`,
  `Ideal.primesOver`,
  `Ideal.Fiber`,
  `IsArtinianRing.equivPi`;
* bridge/view data removed by this refinement: arbitrary indexing types, bijections for the
  product decomposition, and the existence-only wrapper around the decomposition map. The
  canonical owner data are `Ideal.Fiber p B` and `p.primesOver B`; the primitive bridge data are
  the coordinate maps from the fiber ring to each residue field over `p`, and part `(2)` derives
  the product map from those owners instead of treating the whole product packaging as primitive.

Primitive data are `A`, `B`, the filtered-colimit-of-étale hypothesis on `algebraMap A B`, and the
chosen prime `p : PrimeSpectrum A`. The product decomposition in part `(2)` is therefore stated
directly over the owner set `p.asIdeal.primesOver B`, rather than via an auxiliary `ι` and a
reindexing bijection, with the canonical product map exposed as data and bijectivity as the
source-facing theorem. -/

/- Lemma 15.45.12 (1): if `B` is a filtered colimit of étale `A`-algebras and the fiber ring
`p.asIdeal.Fiber B` is Noetherian, then only finitely many primes of `B` lie over `p`.

 Proof sketch: base change the filtered-colimit-of-étale presentation of `B` along
 `A → κ(p)` to see that the fiber ring `p.asIdeal.Fiber B` is a filtered colimit of étale
 `κ(p)`-algebras. Each stage is a finite product of finite separable field extensions, hence has
 discrete spectrum. The Noetherian fiber ring therefore has finitely many primes, and
 `PrimeSpectrum.primesOverOrderIsoFiber` identifies those primes with the primes of `B` over `p`. -/
theorem primesOver_finite_of_isFilteredColimitOfEtale_of_isNoetherianFiber
    (hcolim : (algebraMap A B).IsFilteredColimitOfEtale)
    (p : PrimeSpectrum A) [IsNoetherianRing (p.asIdeal.Fiber B)] :
    Finite (p.asIdeal.primesOver B) := sorry

end PrimeSpectrum

namespace Ideal

/-- The canonical ring homomorphism from the fiber ring `p.Fiber B = κ(p) ⊗[A] B` to the product
of the residue fields of the primes of `B` lying over `p`, indexed by the canonical owner set
`p.primesOver B`. -/
noncomputable def fiberToPiResidueField (p : Ideal A) [p.IsPrime]
    (B : Type v) [CommRing B] [Algebra A B] :
    p.Fiber B →+* ∀ q : p.primesOver B, q.1.ResidueField :=
  let φ : ∀ q : p.primesOver B, p.Fiber B →+* q.1.ResidueField :=
    fun q ↦
      (Algebra.TensorProduct.lift
        (Ideal.ResidueField.mapₐ p q.1 (Algebra.ofId _ _) (q.1.over_def p))
        (IsScalarTower.toAlgHom _ _ _)
        (fun _ _ ↦ Commute.all _ _)).toRingHom
  Pi.ringHom φ

end Ideal

namespace PrimeSpectrum

-- Proof sketch: the fiber ring `p.asIdeal.Fiber B = κ(p) ⊗[A] B` is both Noetherian and a
-- filtered colimit of étale `κ(p)`-algebras, so it is reduced with finitely many prime ideals, all
-- of which are maximal. Hence it is canonically a finite product of fields. Transport the index
-- set of those factors back to the canonical owner set `p.asIdeal.primesOver B` using
-- `PrimeSpectrum.primesOverOrderIsoFiber`, and then identify the canonical coordinate map
-- `Ideal.fiberToPiResidueField` with the reduced Artinian-ring product decomposition
-- `IsArtinianRing.equivPi`.
/-- Lemma 15.45.12 (2): if `B` is a filtered colimit of étale `A`-algebras and the fiber ring
`p.asIdeal.Fiber B` is Noetherian, then the canonical map from `p.asIdeal.Fiber B` to the finite
product of the residue fields of the primes of `B` lying over `p` is bijective. -/
theorem fiberToPiResidueField_bijective_of_isFilteredColimitOfEtale_of_isNoetherianFiber
    (hcolim : (algebraMap A B).IsFilteredColimitOfEtale)
    (p : PrimeSpectrum A) [IsNoetherianRing (p.asIdeal.Fiber B)] :
    Function.Bijective (p.asIdeal.fiberToPiResidueField B) := sorry

-- Proof sketch: a filtered colimit of étale `A`-algebras is weakly étale, so the source-facing
-- statement is a direct bridge to the chapter owner
-- `residueField_isAlgebraic_and_separable_of_isWeaklyEtale`. The Noetherian hypothesis used in
-- parts `(1)` and `(2)` is not part of the mathematical content of this residue-field claim.
/-- Lemma 15.45.12 (3): if `B` is a filtered colimit of étale `A`-algebras, then for every prime
`p` of `A` and every prime `q` of `B` lying over `p`, the residue field extension `κ(q) / κ(p)`
is separable algebraic. -/
theorem residueField_isAlgebraic_and_separable_of_isFilteredColimitOfEtale
    (hcolim : (algebraMap A B).IsFilteredColimitOfEtale)
    (p : PrimeSpectrum A) (q : p.asIdeal.primesOver B) :
    Algebra.IsAlgebraic p.asIdeal.ResidueField q.1.ResidueField ∧
      Algebra.IsSeparable p.asIdeal.ResidueField q.1.ResidueField := sorry

end PrimeSpectrum

end

/-! ### Lemma_15_45_13 (from Chap15) -/
universe u

section

open PrimeSpectrum
open scoped TensorProduct

variable {R Rh Rsh : Type u}
variable [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/- Domain triage:
- primary domain: local commutative algebra of henselizations, strict henselizations, and fibers
  over a prime;
- sampled owner declarations:
  `IsHenselizationOf`,
  `IsStrictHenselizationOf`,
  `PrimeSpectrum.primesOver_finite_of_isFilteredColimitOfEtale_of_isNoetherianFiber`,
  `PrimeSpectrum.fiberToPiResidueField_bijective_of_isFilteredColimitOfEtale_of_isNoetherianFiber`,
  `residueField_isAlgebraic_and_separable_of_isWeaklyEtale`;
- best owner abstraction: this file is `source-facing`; its theorems should specialize the chapter
  owners above to henselizations and strict henselizations, with no new wrapper around primes over
  a fiber or the canonical fiber-to-product map;
- primitive data: the local Noetherian ring `R`, a prime `p : PrimeSpectrum R`, and chosen
  henselization / strict henselization owners;
- derived API: Noetherianity of `Rh` and `Rsh` from Lemma `15.45.3`, Noetherianity of
  `p.asIdeal.Fiber B` from the canonical tensor-product owner, and weakly étale residue-field
  control from the filtered-colimit owner.

Source/core/bridge triage:
- `source-facing`: the six specialized statements below;
- `core/canonical`: `IsHenselizationOf`, `IsStrictHenselizationOf`, `Ideal.primesOver`,
  `Ideal.fiberToPiResidueField`, and `Algebra.IsWeaklyEtale`;
- `bridge/view`: Lemma `15.45.3` upgrading `R`-Noetherianity to `Rh` and `Rsh`, and the tensor
  commutation equivalence identifying `p.asIdeal.Fiber B` with `B ⊗[R] p.asIdeal.ResidueField`.
-/
private theorem fiber_isNoetherianRing
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] [IsNoetherianRing B]
    (p : PrimeSpectrum A) : IsNoetherianRing (p.asIdeal.Fiber B) := by
  let _ : Algebra.EssFiniteType B (B ⊗[A] p.asIdeal.ResidueField) := inferInstance
  let _ : IsNoetherianRing (B ⊗[A] p.asIdeal.ResidueField) :=
    Algebra.EssFiniteType.isNoetherianRing B (B ⊗[A] p.asIdeal.ResidueField)
  exact
    isNoetherianRing_of_ringEquiv (B ⊗[A] p.asIdeal.ResidueField)
      (Algebra.TensorProduct.comm A p.asIdeal.ResidueField B).toRingEquiv.symm

-- Proof sketch: Lemma `15.45.3` upgrades `R`-Noetherianity to `Rh`, the local tensor-product
-- instance above makes the fiber `p.asIdeal.Fiber Rh` Noetherian, and Lemma `15.45.12 (1)` then
-- applies directly to the filtered-colimit-of-étale owner `IsHenselizationOf.isFilteredColimitOfEtale`.
/-- For a Noetherian local ring `R`, a prime `p : Spec R`, and a chosen henselization `Rh` of
`R`, only finitely many primes of `Rh` lie over `p`. -/
theorem henselization_primesOver_finite
    (p : PrimeSpectrum R) :
    Finite (p.asIdeal.primesOver Rh) := by
  let _ : IsNoetherianRing Rh := isNoetherianRing_henselization R Rh
  let _ : IsNoetherianRing (p.asIdeal.Fiber Rh) := fiber_isNoetherianRing R Rh p
  simpa using
    primesOver_finite_of_isFilteredColimitOfEtale_of_isNoetherianFiber
      IsHenselizationOf.isFilteredColimitOfEtale p

-- Proof sketch: the same owner data as above feed directly into Lemma `15.45.12 (2)`, whose
-- canonical map is already `p.asIdeal.fiberToPiResidueField Rh`.
/-- For a Noetherian local ring `R`, a prime `p : Spec R`, and a chosen henselization `Rh` of
`R`, the canonical map from the fiber ring `p.asIdeal.Fiber Rh` to the product of the residue
fields of the primes of `Rh` lying over `p` is bijective. -/
theorem fiberToPiResidueField_henselization_bijective
    (p : PrimeSpectrum R) :
    Function.Bijective (p.asIdeal.fiberToPiResidueField Rh) := by
  let _ : IsNoetherianRing Rh := isNoetherianRing_henselization R Rh
  let _ : IsNoetherianRing (p.asIdeal.Fiber Rh) := fiber_isNoetherianRing R Rh p
  simpa using
    fiberToPiResidueField_bijective_of_isFilteredColimitOfEtale_of_isNoetherianFiber
      IsHenselizationOf.isFilteredColimitOfEtale p

-- Proof sketch: exactly as for henselizations, Lemma `15.45.3` first upgrades Noetherianity to
-- `Rsh`, then the local tensor-product owner gives Noetherianity of `p.asIdeal.Fiber Rsh`, and
-- Lemma `15.45.12 (1)` applies through `IsStrictHenselizationOf.isFilteredColimitOfEtale`.
/-- For a Noetherian local ring `R`, a prime `p : Spec R`, and a chosen strict henselization
`Rsh` of `R`, only finitely many primes of `Rsh` lie over `p`. -/
theorem strictHenselization_primesOver_finite
    (p : PrimeSpectrum R) :
    Finite (p.asIdeal.primesOver Rsh) := by
  let _ : IsNoetherianRing Rsh := isNoetherianRing_strictHenselization R Rsh
  let _ : IsNoetherianRing (p.asIdeal.Fiber Rsh) := fiber_isNoetherianRing R Rsh p
  simpa using
    primesOver_finite_of_isFilteredColimitOfEtale_of_isNoetherianFiber
      IsStrictHenselizationOf.isFilteredColimitOfEtale p

-- Proof sketch: apply the strict-henselization owner to the same generic fiber decomposition
-- theorem `15.45.12 (2)`.
/-- For a Noetherian local ring `R`, a prime `p : Spec R`, and a chosen strict henselization
`Rsh` of `R`, the canonical map from the fiber ring `p.asIdeal.Fiber Rsh` to the product of the
residue fields of the primes of `Rsh` lying over `p` is bijective. -/
theorem fiberToPiResidueField_strictHenselization_bijective
    (p : PrimeSpectrum R) :
    Function.Bijective (p.asIdeal.fiberToPiResidueField Rsh) := by
  let _ : IsNoetherianRing Rsh := isNoetherianRing_strictHenselization R Rsh
  let _ : IsNoetherianRing (p.asIdeal.Fiber Rsh) := fiber_isNoetherianRing R Rsh p
  simpa using
    fiberToPiResidueField_bijective_of_isFilteredColimitOfEtale_of_isNoetherianFiber
      IsStrictHenselizationOf.isFilteredColimitOfEtale p

end

section

open PrimeSpectrum

variable {R Rh Rsh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

-- Proof sketch: the residue-field statement is already a consequence of the canonical weakly
-- étale owner. A henselization is weakly étale because it is a filtered colimit of étale
-- `R`-algebras, so we reuse `residueField_isAlgebraic_and_separable_of_isWeaklyEtale` directly.
/-- For a prime of `Rh` lying over `p`, the induced residue field extension is algebraic and
separable over the residue field of `p`. -/
theorem henselization_residueField_isAlgebraic_and_separable
    (p : PrimeSpectrum R)
    (q : p.asIdeal.primesOver Rh) :
    Algebra.IsAlgebraic p.asIdeal.ResidueField q.1.ResidueField ∧
      Algebra.IsSeparable p.asIdeal.ResidueField q.1.ResidueField := by
  let _ : Algebra.IsWeaklyEtale R Rh :=
    isWeaklyEtale_of_isFilteredColimitOfEtale IsHenselizationOf.isFilteredColimitOfEtale
  simpa using
    residueField_isAlgebraic_and_separable_of_isWeaklyEtale p.asIdeal q

-- Proof sketch: the same weakly-étale owner argument applies to strict henselizations.
/-- For a prime of `Rsh` lying over `p`, the induced residue field extension is algebraic and
separable over the residue field of `p`. -/
theorem strictHenselization_residueField_isAlgebraic_and_separable
    (p : PrimeSpectrum R)
    (r : p.asIdeal.primesOver Rsh) :
    Algebra.IsAlgebraic p.asIdeal.ResidueField r.1.ResidueField ∧
      Algebra.IsSeparable p.asIdeal.ResidueField r.1.ResidueField := by
  let _ : Algebra.IsWeaklyEtale R Rsh :=
    isWeaklyEtale_of_isFilteredColimitOfEtale IsStrictHenselizationOf.isFilteredColimitOfEtale
  simpa using
    residueField_isAlgebraic_and_separable_of_isWeaklyEtale p.asIdeal r

end
