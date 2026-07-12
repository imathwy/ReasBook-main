import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap10.Definition_10_160_1
import StacksProject_2024.Chap10.Lemma_10_39_6
import StacksProject_2024.Chap10.Lemma_10_96_3
import StacksProject_2024.Chap10.Lemma_10_96_4
import StacksProject_2024.Chap10.Lemma_10_97_2
import StacksProject_2024.Chap10.Lemma_10_97_5
import StacksProject_2024.Chap10.Lemma_10_155_1
import StacksProject_2024.Chap10.Lemma_10_155_2
import StacksProject_2024.Chap10.Lemma_10_155_6
import StacksProject_2024.Chap10.Lemma_10_164_1
import StacksProject_2024.Chap15.Lemma_15_3_3
import StacksProject_2024.Chap15.Lemma_15_45_1
import StacksProject_2024.Chap15.Lemma_15_43_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing
open scoped DirectSum

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
/-- Helper for Lemma 15.45.3: the maximal-ideal completion map of any local ring is a local
homomorphism. -/
lemma completion_isLocalHom_of_local_ring
    {S : Type u} [CommRing S] [IsLocalRing S] :
    IsLocalHom (algebraMap S (AdicCompletion (maximalIdeal S) S)) := by
  let φ : AdicCompletion (maximalIdeal S) S →+* S ⧸ maximalIdeal S :=
    (AdicCompletion.evalOneₐ (maximalIdeal S)).toRingHom
  have hcomp :
      φ.comp (algebraMap S (AdicCompletion (maximalIdeal S) S)) =
        Ideal.Quotient.mk (maximalIdeal S) := by
    -- Proof comment: reducing a completed element modulo the closed point agrees with the usual
    -- quotient map on the original ring.
    ext x
    simp [φ]
  haveI : IsLocalHom (Ideal.Quotient.mk (maximalIdeal S)) :=
    Function.Surjective.isLocalHom _ Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (φ.comp (algebraMap S (AdicCompletion (maximalIdeal S) S))) := by
    -- Proof comment: transport locality across the comparison with the quotient map.
    simpa [hcomp]
  -- Proof comment: a map whose composition with a local map is local is itself local.
  exact isLocalHom_of_comp (algebraMap S (AdicCompletion (maximalIdeal S) S)) φ

/-- Helper for Lemma 15.45.3: if the maximal ideal of a local ring is finitely generated, then
its maximal-ideal completion is Noetherian. -/
lemma completion_noetherian_of_maximalIdeal_fg
    {S : Type u} [CommRing S] [IsLocalRing S] (hfg : (maximalIdeal S).FG) :
    IsNoetherianRing (AdicCompletion (maximalIdeal S) S) := by
  let _ : Field (S ⧸ maximalIdeal S) := Ideal.Quotient.field (maximalIdeal S)
  let _ : IsNoetherianRing (S ⧸ maximalIdeal S) := inferInstance
  -- Proof comment: Lemma `10.97.5` applies because the closed-point quotient is a field and the
  -- maximal ideal is finitely generated.
  exact
    (adicCompletion_isNoetherian_and_isAdicComplete
      (R := S) (I := maximalIdeal S) hfg).1

/-- Helper for Lemma 15.45.3: the image of the maximal ideal in the maximal-ideal completion is
maximal once the maximal ideal is finitely generated. -/
lemma completion_map_maximalIdeal_isMaximal_of_maximalIdeal_fg
    {S : Type u} [CommRing S] [IsLocalRing S] (hfg : (maximalIdeal S).FG) :
    Ideal.IsMaximal
      (Ideal.map (algebraMap S (AdicCompletion (maximalIdeal S) S)) (maximalIdeal S)) := by
  let _ : Field (S ⧸ maximalIdeal S) := Ideal.Quotient.field (maximalIdeal S)
  let _ : Field (S ⧸ maximalIdeal S ^ 1) := by
    let e : S ⧸ maximalIdeal S ^ 1 ≃+* S ⧸ maximalIdeal S :=
      Ideal.quotEquivOfEq (pow_one (maximalIdeal S))
    exact IsField.toField (e.toMulEquiv.isField (Field.toIsField _))
  have hker :
      Ideal.map (algebraMap S (AdicCompletion (maximalIdeal S) S)) (maximalIdeal S) =
        RingHom.ker (AdicCompletion.evalₐ (maximalIdeal S) 1) := by
    -- Proof comment: the first completion quotient is exactly the quotient by the maximal ideal.
    simpa [pow_one] using
      completionIdeal_pow_eq_ker_evalₐ (I := maximalIdeal S) hfg 1
  -- Proof comment: the first evaluation map is surjective onto a field, so its kernel is maximal.
  simpa [hker] using
    (RingHom.ker_isMaximal_of_surjective
      (AdicCompletion.evalₐ (maximalIdeal S) 1)
      (AdicCompletion.surjective_evalₐ (maximalIdeal S) 1) :
        Ideal.IsMaximal (RingHom.ker (AdicCompletion.evalₐ (maximalIdeal S) 1)))

/-- Helper for Lemma 15.45.3: if the maximal ideal is finitely generated, then the maximal-ideal
completion is a complete local ring. -/
lemma completion_isCompleteLocalRing_of_maximalIdeal_fg
    {S : Type u} [CommRing S] [IsLocalRing S] (hfg : (maximalIdeal S).FG) :
    IsCompleteLocalRing (AdicCompletion (maximalIdeal S) S) := by
  let Shat := AdicCompletion (maximalIdeal S) S
  let mhat : Ideal Shat := Ideal.map (algebraMap S Shat) (maximalIdeal S)
  have hmax : Ideal.IsMaximal mhat :=
    completion_map_maximalIdeal_isMaximal_of_maximalIdeal_fg (S := S) hfg
  letI : Ideal.IsMaximal mhat := hmax
  let _ : Field (S ⧸ maximalIdeal S) := Ideal.Quotient.field (maximalIdeal S)
  let _ : IsNoetherianRing (S ⧸ maximalIdeal S) := inferInstance
  have hcomplete : IsAdicComplete mhat Shat :=
    (adicCompletion_isNoetherian_and_isAdicComplete
      (R := S) (I := maximalIdeal S) hfg).2
  letI : IsAdicComplete mhat Shat := hcomplete
  letI : IsLocalRing Shat := by
    -- Proof comment: a ring complete for a maximal ideal of definition is local.
    exact @isLocalRing_of_isAdicComplete_maximal Shat _ mhat hmax hcomplete
  have hmhat : mhat = maximalIdeal Shat := IsLocalRing.eq_maximalIdeal inferInstance
  refine
    { toIsLocalRing := inferInstance
      toIsAdicComplete := ?_ }
  -- Proof comment: transport completeness from the image ideal to the actual maximal ideal.
  simpa [mhat, hmhat] using hcomplete

/-- Helper for Lemma 15.45.3: Noetherianity descends from the maximal-ideal completion once the
completion map is flat. -/
lemma isNoetherianRing_of_noetherian_completion_and_flat_completion_map
    {S : Type u} [CommRing S] [IsLocalRing S]
    [IsLocalRing (AdicCompletion (maximalIdeal S) S)]
    [IsNoetherianRing (AdicCompletion (maximalIdeal S) S)]
    (hflat : Module.Flat S (AdicCompletion (maximalIdeal S) S)) :
    IsNoetherianRing S := by
  let _ : Module.Flat S (AdicCompletion (maximalIdeal S) S) := hflat
  let _ : IsLocalHom (algebraMap S (AdicCompletion (maximalIdeal S) S)) :=
    completion_isLocalHom_of_local_ring (S := S)
  have hff :
      (algebraMap S (AdicCompletion (maximalIdeal S) S)).FaithfullyFlat := by
    -- Proof comment: a flat local map is faithfully flat.
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom
  -- Proof comment: faithful flat descent then brings Noetherianity back to the source.
  exact
    isNoetherianRing_of_faithfullyFlat
      (algebraMap S (AdicCompletion (maximalIdeal S) S)) hff

/-- Helper for Lemma 15.45.3: the maximal ideal of a henselization is finitely generated when the
base local ring is Noetherian. -/
lemma henselization_maximalIdeal_fg_of_base_noetherian
    [IsNoetherianRing R] :
    (maximalIdeal Rh).FG := by
  -- Proof comment: the henselization maximal ideal is the image of the finitely generated base
  -- maximal ideal.
  rw [← IsHenselizationOf.map_maximalIdeal (R := R) (S := Rh)]
  exact Ideal.FG.map (Ideal.fg_of_isNoetherianRing (maximalIdeal R)) (algebraMap R Rh)

/-- Helper for Lemma 15.45.3: the maximal ideal of a strict henselization is finitely generated
when the base local ring is Noetherian. -/
lemma strictHenselization_maximalIdeal_fg_of_base_noetherian
    [IsNoetherianRing R] :
    (maximalIdeal Rsh).FG := by
  -- Proof comment: the strict henselization maximal ideal is likewise the image of the base
  -- maximal ideal.
  rw [← IsStrictHenselizationOf.map_maximalIdeal (R := R) (S := Rsh)]
  exact Ideal.FG.map (Ideal.fg_of_isNoetherianRing (maximalIdeal R)) (algebraMap R Rsh)

/-- Helper for Lemma 15.45.3: a local `R`-algebra endomorphism of any chosen henselization is the
identity. -/
lemma henselization_endomorphism_eq_id
    {T : Type u} [CommRing T] [Algebra R T] [IsHenselizationOf R T]
    (f : T →ₐ[R] T) (hf : IsLocalHom (f : T →+* T)) :
    f = AlgHom.id R T := by
  -- Proof comment: uniqueness in the henselization universal property over `R → R` leaves only
  -- the identity local `R`-algebra endomorphism.
  rcases
      existsUnique_algHom_between_henselizations_of_localHom
        (R := R) (S := R) (Rh := T) (Sh := T) with
    ⟨g, hg_local, hg_unique⟩
  have hid_local : IsLocalHom (((AlgHom.id R T : T →ₐ[R] T) : T →+* T)) := by
    simpa using (show IsLocalHom (algebraMap T T) by infer_instance)
  calc
    f = g := hg_unique f hf
    _ = AlgHom.id R T := (hg_unique (AlgHom.id R T) hid_local).symm

/-- Helper for Lemma 15.45.3: the maximal-ideal completion of a Noetherian local ring is flat over
the source ring. -/
lemma maximalIdeal_completion_flat_of_isNoetherian
    {S : Type u} [CommRing S] [IsLocalRing S] [IsNoetherianRing S] :
    Module.Flat S (AdicCompletion (maximalIdeal S) S) := by
  -- Proof comment: this is exactly the Noetherian completion-flatness theorem from
  -- Lemma `10.97.2`, rewritten in module form.
  exact RingHom.flat_algebraMap_iff.mp
    (adicCompletion_algebraMap_flat (R := S) (I := maximalIdeal S))

/-- Helper for Lemma 15.45.3: a bijective maximal-ideal completion comparison map can be reused as
an explicit ring equivalence. -/
noncomputable def completion_comparison_equiv_of_bijective
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] :
    Function.Bijective (maximalIdealCompletionMap (algebraMap A B)) →
      AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal B) B := by
  intro hbij
  -- Proof comment: a bijective ring hom canonically packages into the corresponding ring
  -- equivalence.
  exact RingEquiv.ofBijective _ hbij

/-- Helper for Lemma 15.45.3: for flat local maps with unchanged closed fiber, the induced
comparison on maximal-ideal completions is an equivalence. -/
noncomputable def completion_comparison_equiv_of_flat_of_residueFieldBijective
    {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B]
    (hmax : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B)
    (hres : Function.Bijective (ResidueField.map (algebraMap A B))) :
    AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal B) B := by
  -- Proof comment: Lemma `15.43.9` provides bijectivity of the completion comparison; we record
  -- the equivalent reusable ring-equivalence form needed for stagewise transport.
  exact
    completion_comparison_equiv_of_bijective (A := A) (B := B)
      (maximalIdealCompletionMap_bijective_of_flat_of_residueFieldBijective
        (A := A) (B := B) hmax hres)

/-- Helper for Lemma 15.45.3: flatness transports across a target ring equivalence once the
structure map is normalized. -/
lemma moduleFlat_target_of_ringEquiv
    {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (e : B ≃+* C)
    (he : e.toRingHom.comp (algebraMap A B) = algebraMap A C)
    [Module.Flat A B] :
    Module.Flat A C := by
  have hflatComp : (e.toRingHom.comp (algebraMap A B)).Flat := by
    -- Proof comment: compose the flat source map with the ring-equivalence target map.
    exact
      RingHom.Flat.comp
        (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat A B))
        (RingHom.Flat.of_bijective e.bijective)
  have hflatAC : (algebraMap A C).Flat := by
    -- Proof comment: normalize the transported composite back to the chosen algebra map.
    rw [← he]
    exact hflatComp
  exact RingHom.flat_algebraMap_iff.mp hflatAC

/-- Helper for Lemma 15.45.3: a bijective ring map is ind-étale, so it can be inserted as a
harmless transport factor when packaging henselization owners. -/
lemma isFilteredColimitOfEtale_of_bijective
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (hbij : Function.Bijective f) :
    f.IsFilteredColimitOfEtale := by
  have hEtale : CommRingCat.etale (CommRingCat.ofHom f) := by
    -- Proof comment: a bijective ring map is étale, hence belongs to the ind-étale closure.
    dsimp [CommRingCat.etale]
    exact RingHom.Etale.of_bijective hbij
  -- Proof comment: every étale map is automatically in the ind-étale closure.
  dsimp [RingHom.IsFilteredColimitOfEtale]
  exact CategoryTheory.MorphismProperty.le_ind (P := CommRingCat.etale) _ hEtale

/-- Helper for Lemma 15.45.3: a henselization owner transports across an algebra equivalence once
the target ring is already known to be henselian local. -/
lemma isHenselizationOf_of_algEquiv
    {A B C : Type u}
    [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B] [IsHenselizationOf A B]
    [CommRing C] [IsLocalRing C] [Algebra A C] [HenselianLocalRing C]
    (e : C ≃ₐ[A] B) :
    IsHenselizationOf A C := by
  have hcomp :
      e.symm.toRingHom.comp (algebraMap A B) = algebraMap A C := by
    -- Proof comment: the inverse algebra equivalence identifies the transported structure map
    -- with the chosen `A`-algebra structure on `C`.
    ext x
    exact e.symm.commutes x
  letI : IsLocalHom e.symm.toRingHom :=
    Function.Surjective.isLocalHom _ e.symm.surjective
  have hlocal_comp : IsLocalHom (e.symm.toRingHom.comp (algebraMap A B)) :=
    RingHom.isLocalHom_comp e.symm.toRingHom (algebraMap A B)
  have hlocal_C : IsLocalHom (algebraMap A C) := by
    -- Proof comment: locality transports across the normalized comparison of structure maps.
    simpa [hcomp] using hlocal_comp
  refine
    { toHenselianLocalRing := inferInstance
      toIsLocalHom := hlocal_C
      isFilteredColimitOfEtale := ?_
      map_maximalIdeal := ?_
      residueField_bijective := ?_ }
  · have he :
        e.symm.toRingHom.IsFilteredColimitOfEtale :=
      isFilteredColimitOfEtale_of_bijective e.symm.toRingHom e.symm.bijective
    have hcomp_etale :
        (e.symm.toRingHom.comp (algebraMap A B)).IsFilteredColimitOfEtale :=
      RingHom.isFilteredColimitOfEtale_comp
        (algebraMap A B) e.symm.toRingHom
        IsHenselizationOf.isFilteredColimitOfEtale he
    -- Proof comment: compose the ind-étale presentation of `B` with the harmless bijective
    -- transport map back to `C`.
    simpa [hcomp] using hcomp_etale
  · -- Proof comment: maximal ideals transport through the surjective local comparison map.
    calc
      Ideal.map (algebraMap A C) (maximalIdeal A) =
          Ideal.map e.symm.toRingHom (Ideal.map (algebraMap A B) (maximalIdeal A)) := by
            rw [hcomp, Ideal.map_map]
      _ = Ideal.map e.symm.toRingHom (maximalIdeal B) := by
            rw [IsHenselizationOf.map_maximalIdeal]
      _ = maximalIdeal C := by
            simpa using
              IsLocalRing.map_maximalIdeal_of_surjective
                e.symm.toRingHom e.symm.surjective
  · have he_res :
        Function.Bijective (ResidueField.map e.symm.toRingHom) :=
      residueField_bijective_of_surjective_localHom
        (f := e.symm.toRingHom) e.symm.surjective
    have hcomp_res :
        (ResidueField.map e.symm.toRingHom).comp
            (ResidueField.map (algebraMap A B)) =
          ResidueField.map (algebraMap A C) := by
      -- Proof comment: the residue-field map for `A → C` is the composite of the one for
      -- `A → B` with the residue-field map induced by the surjective transport map.
      ext x
      simp [hcomp]
    exact hcomp_res.symm ▸ he_res.comp IsHenselizationOf.residueField_bijective

/-- Helper for Lemma 15.45.3: once a closed-point localized stage henselization is compared with
`Rh` by an algebra equivalence, the henselization owner transports to `Rh`. -/
lemma stage_henselization_of_closed_point_localization
    {Sj Sjh : Type u}
    [CommRing Sj] [IsLocalRing Sj]
    [CommRing Sjh] [Algebra Sj Sjh] [IsHenselizationOf Sj Sjh]
    [Algebra Sj Rh]
    (e : Sjh ≃ₐ[Sj] Rh) :
    IsHenselizationOf Sj Rh := by
  let _ : HenselianLocalRing Rh := inferInstance
  exact
    isHenselizationOf_of_algEquiv
      (A := Sj) (B := Sjh) (C := Rh) e.symm

/-- Helper for Lemma 15.45.3: after installing the localized closed-point stage as a
henselization of the stage base, the existing base-flat completion theorem applies verbatim. -/
lemma stage_completion_flat_of_henselization_owner
    {Sj : Type u}
    [CommRing Sj] [IsLocalRing Sj] [Algebra Sj Rh]
    [IsHenselizationOf Sj Rh] [IsNoetherianRing Sj] :
    Module.Flat Sj (AdicCompletion (maximalIdeal Rh) Rh) := by
  -- Proof comment: this is exactly the already-proved base-flat completion statement, now viewed
  -- at the localized stage ring.
  simpa using henselization_completion_flat_over_base (R := Sj) (Rh := Rh)

/-- Helper for Lemma 15.45.3: the strict branch uses the same owner-level bridge once a localized
stage is recognized as a strict henselization of the stage base. -/
lemma stage_completion_flat_of_strict_henselization_owner
    {Sj : Type u}
    [CommRing Sj] [IsLocalRing Sj] [Algebra Sj Rsh]
    [IsStrictHenselizationOf Sj Rsh] [IsNoetherianRing Sj] :
    Module.Flat Sj (AdicCompletion (maximalIdeal Rsh) Rsh) := by
  -- Proof comment: the strict base-flat completion statement is already available and only needs
  -- the localized strict-henselization owner.
  simpa using strict_henselization_completion_flat_over_base (R := Sj) (Rsh := Rsh)

/-- Helper for Lemma 15.45.3: if a local algebra map `A → B` factors through an intermediate
stage `C`, then the prime of `C` cut out by the closed point of `B` contracts to the closed point
of `A`. -/
lemma closed_point_stage_under_base_maximalIdeal
    {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] :
    (Ideal.comap (algebraMap C B) (maximalIdeal B)).under A = maximalIdeal A := by
  -- Proof comment: contracting the closed point of `B` through the factorization `A → C → B`
  -- is the same as contracting it directly along `A → B`.
  change
    Ideal.comap (algebraMap A C)
        (Ideal.comap (algebraMap C B) (maximalIdeal B)) =
      maximalIdeal A
  simpa [Ideal.comap_comap, IsScalarTower.algebraMap_eq A C B] using
    IsLocalRing.maximalIdeal_comap (algebraMap A B)

/-- Helper for Lemma 15.45.3: localizing an intermediate stage at the prime cut out by the closed
point of a local target produces a local algebra over the original base local ring. -/
lemma closed_point_stage_localization_base_isLocalHom
    {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] :
    IsLocalHom
      (algebraMap A
        (Localization.AtPrime (Ideal.comap (algebraMap C B) (maximalIdeal B)))) := by
  let q : Ideal C := Ideal.comap (algebraMap C B) (maximalIdeal B)
  have hq : q.under A = maximalIdeal A :=
    closed_point_stage_under_base_maximalIdeal (A := A) (B := B) (C := C)
  -- Proof comment: after identifying the contracted prime with `maximalIdeal A`, the canonical
  -- localization map at that prime is the standard local ring homomorphism.
  simpa [q, hq, RingHom.algebraMap_toAlgebra] using
    (Localization.isLocalHom_localRingHom
      (maximalIdeal A) q (algebraMap A C) hq.symm)

/-- Helper for Lemma 15.45.3: quotient-stage evaluations on an adic completion commute with the
transition maps of the inverse system. -/
lemma completion_eval_factor
    {S : Type u} [CommRing S] (I : Ideal S)
    {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion I S) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  let p : AdicCompletion I S → Prop := fun y =>
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n y) =
      AdicCompletion.evalₐ I m y
  change p x
  -- Proof comment: descend to a Cauchy representative and use the defining compatibility of its
  -- quotient classes.
  refine AdicCompletion.induction_on (I := I) (M := S) x ?_
  intro f
  change
    Ideal.Quotient.factorPow I hle
        (AdicCompletion.evalₐ I n (AdicCompletion.mk I S f)) =
      AdicCompletion.evalₐ I m (AdicCompletion.mk I S f)
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  simpa using AdicCompletion.Ideal.mk_eq_mk (I := I) hle f

/-- Helper for Lemma 15.45.3: agreement on the dense image `AdicCompletion.of` determines a map
out of a completion once the target is already complete. -/
lemma completion_linearMap_ext_of_complete_target
    {S : Type u} [CommRing S] (I : Ideal S)
    {M Q : Type u} [AddCommGroup M] [Module S M] [AddCommGroup Q] [Module S Q]
    [IsAdicComplete I Q]
    {f g : AdicCompletion I M →ₗ[S] Q}
    (hfg : f.comp (AdicCompletion.of I M) = g.comp (AdicCompletion.of I M)) :
    f = g := by
  have hcomp :
      (AdicCompletion.of I Q).comp f = (AdicCompletion.of I Q).comp g := by
    -- Proof comment: equality on the dense image is enough after re-embedding the complete
    -- target into its own completion.
    apply AdicCompletion.map_ext''
    simpa [LinearMap.comp_assoc, LinearMap.comp_apply] using
      congrArg (fun u ↦ (AdicCompletion.of I Q).comp u) hfg
  ext x
  -- Proof comment: the canonical map into the completion is injective on an already complete
  -- target.
  exact ((AdicCompletion.ofLinearEquiv I Q).symm.injective
    (LinearMap.congr_fun hcomp x))

/-- Helper for Lemma 15.45.3: the canonical quotient-power map from `R` to its henselization is
the quotient of the structure map `R → Rh`. -/
noncomputable abbrev henselization_quotientPowMap
    (n : ℕ) :
    R ⧸ maximalIdeal R ^ n →+* Rh ⧸ maximalIdeal Rh ^ n :=
  Ideal.quotientMap (maximalIdeal Rh ^ n) (algebraMap R Rh)
    (pow_maximalIdeal_le_comap_pow_maximalIdeal (algebraMap R Rh) n)

/-- Helper for Lemma 15.45.3: evaluating the completion map `R^∧ → (R^h)^∧` at stage `n` is
exactly the canonical quotient map `R / m^n → R^h / (m^h)^n`. -/
lemma henselization_completionMap_eval_stage
    (n : ℕ) (x : AdicCompletion (maximalIdeal R) R) :
    AdicCompletion.evalₐ (maximalIdeal Rh) n
        ((maximalIdealCompletionMap (algebraMap R Rh)) x) =
      henselization_quotientPowMap (R := R) (Rh := Rh) n
        (AdicCompletion.evalₐ (maximalIdeal R) n x) := by
  let p : AdicCompletion (maximalIdeal R) R → Prop := fun y =>
    AdicCompletion.evalₐ (maximalIdeal Rh) n
        ((maximalIdealCompletionMap (algebraMap R Rh)) y) =
      henselization_quotientPowMap (R := R) (Rh := Rh) n
        (AdicCompletion.evalₐ (maximalIdeal R) n y)
  change p x
  -- Proof comment: descend to a Cauchy representative, where the completion comparison is
  -- defined stagewise by the same quotient map.
  refine AdicCompletion.induction_on (I := maximalIdeal R) (M := R) x ?_
  intro f
  change
    AdicCompletion.evalₐ (maximalIdeal Rh) n
        ((maximalIdealCompletionMap (algebraMap R Rh))
          (AdicCompletion.mk (maximalIdeal R) R f)) =
      henselization_quotientPowMap (R := R) (Rh := Rh) n
        (AdicCompletion.evalₐ (maximalIdeal R) n
          (AdicCompletion.mk (maximalIdeal R) R f))
  simp only [AdicCompletion.map_mk, AdicCompletion.evalₐ_mk,
    henselization_quotientPowMap]

/-- Helper for Lemma 15.45.3: the quotient-power maps to a henselization commute with the
transition maps `Ideal.Quotient.factorPow`. -/
lemma henselization_quotientPowMap_factorPow_compat
    {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal Rh) hle).comp
        (henselization_quotientPowMap (R := R) (Rh := Rh) n) =
      (henselization_quotientPowMap (R := R) (Rh := Rh) m).comp
        (Ideal.Quotient.factorPow (maximalIdeal R) hle) := by
  -- Proof comment: both quotient routes send the class of `x` to the class of its image in the
  -- smaller henselization quotient.
  apply Ideal.Quotient.ringHom_ext
  ext x
  rfl

/-- Helper for Lemma 15.45.3: the inverse quotient-stage maps used in the henselization
completion comparison are compatible with the transition maps. -/
lemma henselization_completion_stage_compat
    {m n : ℕ} (hle : m ≤ n)
    (x : AdicCompletion (maximalIdeal Rh) Rh) :
    Ideal.Quotient.factorPow (maximalIdeal R) hle
        (((RingEquiv.ofBijective
            (henselization_quotientPowMap (R := R) (Rh := Rh) n)
            (henselizationQuotientPowMap_bijective (R := R) (Rh := Rh) n)).symm.toRingHom.comp
          (AdicCompletion.evalₐ (maximalIdeal Rh) n)) x) =
      ((RingEquiv.ofBijective
          (henselization_quotientPowMap (R := R) (Rh := Rh) m)
          (henselizationQuotientPowMap_bijective (R := R) (Rh := Rh) m)).symm.toRingHom.comp
        (AdicCompletion.evalₐ (maximalIdeal Rh) m)) x := by
  let e : ∀ k : ℕ, R ⧸ maximalIdeal R ^ k ≃+* Rh ⧸ maximalIdeal Rh ^ k :=
    fun k ↦ RingEquiv.ofBijective
      (henselization_quotientPowMap (R := R) (Rh := Rh) k)
      (henselizationQuotientPowMap_bijective (R := R) (Rh := Rh) k)
  -- Proof comment: compare after postcomposing with the quotient bijection at stage `m`, where
  -- the result reduces to the evaluation compatibility in the completion inverse system.
  apply (henselizationQuotientPowMap_bijective (R := R) (Rh := Rh) m).injective
  calc
    henselization_quotientPowMap (R := R) (Rh := Rh) m
        (Ideal.Quotient.factorPow (maximalIdeal R) hle
          (((e n).symm.toRingHom.comp (AdicCompletion.evalₐ (maximalIdeal Rh) n)) x)) =
      (Ideal.Quotient.factorPow (maximalIdeal Rh) hle)
        (henselization_quotientPowMap (R := R) (Rh := Rh) n
          (((e n).symm.toRingHom.comp (AdicCompletion.evalₐ (maximalIdeal Rh) n)) x)) := by
            symm
            exact DFunLike.congr_fun
              (henselization_quotientPowMap_factorPow_compat
                (R := R) (Rh := Rh) hle)
              (((e n).symm.toRingHom.comp (AdicCompletion.evalₐ (maximalIdeal Rh) n)) x)
    _ = (Ideal.Quotient.factorPow (maximalIdeal Rh) hle)
          (AdicCompletion.evalₐ (maximalIdeal Rh) n x) := by
            congr 1
            exact RingEquiv.apply_symm_apply (e n) (AdicCompletion.evalₐ (maximalIdeal Rh) n x)
    _ = AdicCompletion.evalₐ (maximalIdeal Rh) m x := by
            simpa using completion_eval_factor (S := Rh) (I := maximalIdeal Rh) hle x
    _ = henselization_quotientPowMap (R := R) (Rh := Rh) m
          (((e m).symm.toRingHom.comp (AdicCompletion.evalₐ (maximalIdeal Rh) m)) x) := by
            exact
              (RingEquiv.apply_symm_apply
                (e m) (AdicCompletion.evalₐ (maximalIdeal Rh) m x)).symm

/-- Helper for Lemma 15.45.3: the maximal-ideal completions of a local ring and its henselization
are canonically identified by the quotient-power bijections from Lemma `15.45.1`. -/
noncomputable def henselization_completion_equiv :
    AdicCompletion (maximalIdeal R) R ≃+* AdicCompletion (maximalIdeal Rh) Rh := by
  classical
  let e : ∀ n : ℕ, R ⧸ maximalIdeal R ^ n ≃+* Rh ⧸ maximalIdeal Rh ^ n :=
    fun n ↦ RingEquiv.ofBijective
      (henselization_quotientPowMap (R := R) (Rh := Rh) n)
      (henselizationQuotientPowMap_bijective (R := R) (Rh := Rh) n)
  let q : ∀ n : ℕ, AdicCompletion (maximalIdeal Rh) Rh →+* R ⧸ maximalIdeal R ^ n :=
    fun n ↦ (e n).symm.toRingHom.comp (AdicCompletion.evalₐ (maximalIdeal Rh) n)
  have hq_compat :
      ∀ {m n : ℕ} (hle : m ≤ n),
        (Ideal.Quotient.factorPow (maximalIdeal R) hle).comp (q n) = q m := by
    intro m n hle
    ext x
    -- Proof comment: the inverse quotient-stage maps now commute by the dedicated compatibility
    -- lemma extracted from the source-faithful completion comparison.
    simpa [q] using
      henselization_completion_stage_compat
        (R := R) (Rh := Rh) hle x
  let ψ : AdicCompletion (maximalIdeal Rh) Rh →+* AdicCompletion (maximalIdeal R) R :=
    AdicCompletion.liftRingHom (maximalIdeal R) q hq_compat
  let φ : AdicCompletion (maximalIdeal R) R →+* AdicCompletion (maximalIdeal Rh) Rh :=
    maximalIdealCompletionMap (algebraMap R Rh)
  have hleft : ψ.comp φ = RingHom.id _ := by
    apply DFunLike.ext
    intro x
    -- Proof comment: both completion endomorphisms agree on every quotient stage of `R^`.
    apply AdicCompletion.ext_evalₐ (I := maximalIdeal R)
    intro n
    calc
      AdicCompletion.evalₐ (maximalIdeal R) n ((ψ.comp φ) x)
          = q n (φ x) := by
              simp [ψ]
      _ = (e n).symm (AdicCompletion.evalₐ (maximalIdeal Rh) n (φ x)) := by
              rfl
      _ = (e n).symm
            (henselization_quotientPowMap (R := R) (Rh := Rh) n
              (AdicCompletion.evalₐ (maximalIdeal R) n x)) := by
                simpa [φ] using
                  henselization_completionMap_eval_stage
                    (R := R) (Rh := Rh) n x
      _ = AdicCompletion.evalₐ (maximalIdeal R) n x := by
              exact
                RingEquiv.symm_apply_apply
                  (e n) (AdicCompletion.evalₐ (maximalIdeal R) n x)
    -- Proof comment: the target stage is exactly the evaluation of `x`.
  have hright : φ.comp ψ = RingHom.id _ := by
    apply DFunLike.ext
    intro x
    -- Proof comment: the same quotientwise computation shows the opposite composite is the
    -- identity on `Rh^`.
    apply AdicCompletion.ext_evalₐ (I := maximalIdeal Rh)
    intro n
    calc
      AdicCompletion.evalₐ (maximalIdeal Rh) n ((φ.comp ψ) x)
          = henselization_quotientPowMap (R := R) (Rh := Rh) n
              (AdicCompletion.evalₐ (maximalIdeal R) n (ψ x)) := by
                simpa [φ] using
                  henselization_completionMap_eval_stage
                    (R := R) (Rh := Rh) n (ψ x)
      _ = henselization_quotientPowMap (R := R) (Rh := Rh) n (q n x) := by
              simp [ψ]
      _ = henselization_quotientPowMap (R := R) (Rh := Rh) n
            ((e n).symm (AdicCompletion.evalₐ (maximalIdeal Rh) n x)) := by
              rfl
      _ = AdicCompletion.evalₐ (maximalIdeal Rh) n x := by
              exact
                RingEquiv.apply_symm_apply
                  (e n) (AdicCompletion.evalₐ (maximalIdeal Rh) n x)
  refine RingEquiv.ofBijective φ ?_
  constructor
  · -- Proof comment: a left inverse for `φ` gives injectivity.
    exact Function.LeftInverse.injective (fun x ↦ by
      simpa using DFunLike.congr_fun hleft x)
  · -- Proof comment: a right inverse for `φ` gives surjectivity.
    exact Function.RightInverse.surjective (fun x ↦ by
      simpa using DFunLike.congr_fun hright x)

/-- Helper for Lemma 15.45.3: once `R` is Noetherian, the completion of its henselization is
already flat over the base ring `R`. -/
lemma henselization_completion_flat_over_base
    [IsNoetherianRing R] :
    Module.Flat R (AdicCompletion (maximalIdeal Rh) Rh) := by
  let e :
      AdicCompletion (maximalIdeal R) R ≃+*
        AdicCompletion (maximalIdeal Rh) Rh :=
    henselization_completion_equiv (R := R) (Rh := Rh)
  have he :
      e.toRingHom.comp (algebraMap R (AdicCompletion (maximalIdeal R) R)) =
        algebraMap R (AdicCompletion (maximalIdeal Rh) Rh) := by
    -- Proof comment: the completion comparison extends the original map `R → Rh`.
    simpa [henselization_completion_equiv] using
      maximalIdealCompletionMap_comp (algebraMap R Rh)
  let _ : Module.Flat R (AdicCompletion (maximalIdeal R) R) :=
    maximalIdeal_completion_flat_of_isNoetherian (S := R)
  -- Proof comment: transport flatness of `R^` across the canonical completion equivalence.
  exact moduleFlat_target_of_ringEquiv (A := R) (B := AdicCompletion (maximalIdeal R) R)
    (C := AdicCompletion (maximalIdeal Rh) Rh) e he

/-- Helper for Lemma 15.45.3: the maximal-ideal completion of a henselization is flat over the
henselization. -/
lemma henselization_completion_flat :
    [IsNoetherianRing R] →
    Module.Flat Rh (AdicCompletion (maximalIdeal Rh) Rh) := by
  intro
  -- Route correction: the failed pair-henselization pivot is abandoned here in favor of the source
  -- argument through local ind-étale stages and stagewise completion comparisons.
  have hcompletion :
      AdicCompletion (maximalIdeal R) R ≃+* AdicCompletion (maximalIdeal Rh) Rh :=
    henselization_completion_equiv (R := R) (Rh := Rh)
  -- Proof comment: the source proof writes `Rh` as a filtered colimit of étale local
  -- `R`-algebras, identifies each stage completion with the common completion via the comparison
  -- theorem, and then applies the stagewise-flat colimit criterion.
  -- TODO: unpack `IsHenselizationOf.isFilteredColimitOfEtale`, pass to the closed-point
  -- localization `Sj := Localization.AtPrime qj` cut out by `maximalIdeal Rh`, and construct the
  -- stage comparison `Sjh ≃ₐ[Sj] Rh` for a chosen stage henselization `Sjh` by combining:
  -- `existsUnique_algHom_to_henselization_of_etale_of_residueFieldMap_bijective`,
  -- `existsUnique_algHom_between_henselizations_of_localHom`, and
  -- `existsUnique_algHom_of_filteredColimitOfEtale_of_henselianLocal_of_residueFieldMap`.
  -- After transporting stage completion flatness across the induced completion equivalence, apply
  -- `flat_of_stagewise_restrictScalars_flat` to the original ind-étale presentation.
  sorry

-- Route correction: the next helper block isolates the strict-branch quotient algebra before the
-- completion comparison is assembled.
/-- Helper for Lemma 15.45.3: a finitely supported family of coefficients lies in `J • ⊤`
exactly when each coordinate lies in `J`. -/
lemma mem_smul_top_directSum_iff
    {ι : Type u} (J : Ideal R) (x : ⨁ _ : ι, R) :
    x ∈ J • (⊤ : Submodule R (⨁ _ : ι, R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    -- Proof comment: membership in `J • ⊤` is preserved by the generators of the smul submodule,
    -- so each coordinate lies in `J`.
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha y hy i
      simpa [smul_eq_mul] using J.mul_mem_right (y i) ha
    · intro y z hy hz i
      exact J.add_mem (hy i) (hz i)
  · intro hx
    -- Proof comment: rebuild the finitely supported family as a sum of its coordinate basis
    -- vectors and place each summand in `J • ⊤` using the coordinate membership.
    rw [← Finsupp.sum_single x]
    refine Submodule.sum_mem _ ?_
    intro i hi
    have hsingle :
        Finsupp.single i (x i) =
          x i • (Finsupp.single i (1 : R) : ⨁ _ : ι, R) := by
      ext j
      by_cases h : j = i
      · subst h
        simp
      · simp [h]
    rw [hsingle]
    exact
      Submodule.smul_mem_smul (I := J)
        (N := (⊤ : Submodule R (⨁ _ : ι, R))) (hx i) (by simp)

/-- Helper for Lemma 15.45.3: quotienting the free direct sum coordinatewise gives the canonical
map to the direct sum of the quotient rings. -/
noncomputable def directSum_quotient_map
    {ι : Type u} (J : Ideal R) :
    (⨁ _ : ι, R) →ₗ[R] (⨁ _ : ι, (R ⧸ J)) :=
  DirectSum.lmap fun _ : ι ↦ (Ideal.Quotient.mkₐ R J).toLinearMap

/-- Helper for Lemma 15.45.3: the coordinatewise quotient map sends one basis vector to the
matching quotient basis vector. -/
@[simp] lemma directSum_quotient_map_lof
    {ι : Type u} (J : Ideal R) (i : ι) (r : R) :
    directSum_quotient_map (R := R) (ι := ι) J
        (DirectSum.lof R ι (fun _ : ι ↦ R) i r) =
      DirectSum.lof R ι (fun _ : ι ↦ R ⧸ J) i (Ideal.Quotient.mk J r) := by
  -- Proof comment: the coordinatewise quotient map only changes the coefficient in the chosen
  -- summand.
  simp [directSum_quotient_map]

/-- Helper for Lemma 15.45.3: the kernel of the coordinatewise quotient map on the free direct
sum is exactly `J • ⊤`. -/
lemma ker_directSum_quotient_map
    {ι : Type u} (J : Ideal R) :
    LinearMap.ker (directSum_quotient_map (R := R) (ι := ι) J) =
      J • (⊤ : Submodule R (⨁ _ : ι, R)) := by
  ext x
  constructor
  · intro hx
    change directSum_quotient_map (R := R) (ι := ι) J x = 0 at hx
    rw [mem_smul_top_directSum_iff (R := R) (J := J) x]
    intro i
    have hxi : (directSum_quotient_map (R := R) (ι := ι) J x) i = 0 := by
      simpa using congrFun hx i
    exact (Ideal.Quotient.eq_zero_iff_mem (I := J)).mp <| by
      simpa [directSum_quotient_map] using hxi
  · intro hx
    change directSum_quotient_map (R := R) (ι := ι) J x = 0
    ext i
    exact (Ideal.Quotient.eq_zero_iff_mem (I := J)).mpr <|
      (mem_smul_top_directSum_iff (R := R) (J := J) x).mp hx i

/-- Helper for Lemma 15.45.3: the coordinatewise quotient map from the free direct sum is
surjective. -/
lemma directSum_quotient_map_surjective
    {ι : Type u} (J : Ideal R) :
    Function.Surjective (directSum_quotient_map (R := R) (ι := ι) J) := by
  classical
  intro y
  -- Proof comment: build a preimage by induction on the finitely supported quotient family.
  refine Finsupp.induction_linear ?_ ?_ ?_ y
  · exact ⟨0, by simp [directSum_quotient_map]⟩
  · intro y z hy hz
    rcases hy with ⟨xy, rfl⟩
    rcases hz with ⟨xz, rfl⟩
    refine ⟨xy + xz, ?_⟩
    simp [directSum_quotient_map]
  · intro i q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨DirectSum.lof R ι (fun _ : ι ↦ R) i r, ?_⟩
    simpa using directSum_quotient_map_lof (R := R) (ι := ι) J i r

/-- Helper for Lemma 15.45.3: quotienting the free direct sum by `J • ⊤` identifies it with the
direct sum of the quotient rings. -/
lemma directSum_quotient_smul_top_linearEquiv
    {ι : Type u} (J : Ideal R) :
    ((⨁ _ : ι, R) ⧸ J • (⊤ : Submodule R (⨁ _ : ι, R))) ≃ₗ[R]
      (⨁ _ : ι, (R ⧸ J)) := by
  let π : (⨁ _ : ι, R) →ₗ[R] (⨁ _ : ι, R ⧸ J) :=
    directSum_quotient_map (R := R) (ι := ι) J
  let hker :
      LinearMap.ker π =
        J • (⊤ : Submodule R (⨁ _ : ι, R)) :=
    ker_directSum_quotient_map (R := R) (ι := ι) J
  let hrange : LinearMap.range π = ⊤ :=
    LinearMap.range_eq_top.2 (directSum_quotient_map_surjective (R := R) (ι := ι) J)
  -- Proof comment: rewrite the quotient by `J • ⊤` to the actual kernel of the coordinatewise
  -- quotient map, then collapse the full range back to the target direct sum.
  exact
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      (π.quotKerEquivRange.trans ((LinearEquiv.ofEq _ _ hrange).trans Submodule.topEquiv))

/-- Helper for Lemma 15.45.3: the quotient/direct-sum identification is already linear over the
quotient ring `R ⧸ J`. -/
lemma directSum_quotient_smul_top_linearEquiv_over_quotient
    {ι : Type u} (J : Ideal R) :
    ((⨁ _ : ι, R) ⧸ J • (⊤ : Submodule R (⨁ _ : ι, R))) ≃ₗ[R ⧸ J]
      (⨁ _ : ι, (R ⧸ J)) := by
  -- Proof comment: the ambient `R`-linear equivalence is already compatible with the quotient
  -- scalar action, so the standard restriction-of-scalars upgrade applies.
  exact
    quotientByIdealTopLinearEquiv_over_quotient (R := R) (I := J)
      (directSum_quotient_smul_top_linearEquiv (R := R) (ι := ι) J)

/-- Helper for Lemma 15.45.3: the quotient/direct-sum identification sends one basis vector class
to the matching quotient basis vector. -/
@[simp] lemma directSum_quotient_smul_top_linearEquiv_over_quotient_mk_lof
    {ι : Type u} (J : Ideal R) (i : ι) (r : R) :
    directSum_quotient_smul_top_linearEquiv_over_quotient (R := R) (ι := ι) J
        ((J • (⊤ : Submodule R (⨁ _ : ι, R))).mkQ
          (DirectSum.lof R ι (fun _ : ι ↦ R) i r)) =
      Finsupp.single i (Ideal.Quotient.mk J r) := by
  -- Proof comment: unfold the quotient/direct-sum comparison and evaluate it on the obvious
  -- quotient class represented by one direct-sum generator.
  simp [directSum_quotient_smul_top_linearEquiv_over_quotient,
    directSum_quotient_smul_top_linearEquiv, directSum_quotient_map]

/-- Helper for Lemma 15.45.3: after the quotient/direct-sum identification, the adic-completion
transition map on the completed free module is just coordinatewise `factorPow`. -/
lemma directSum_quotient_transition_compat
    {ι : Type u} {m n : ℕ} (hle : m ≤ n)
    (z : ((⨁ _ : ι, R) ⧸ ((maximalIdeal R ^ n) • (⊤ : Submodule R (⨁ _ : ι, R))))) :
    directSum_quotient_smul_top_linearEquiv_over_quotient
        (R := R) (ι := ι) (maximalIdeal R ^ m)
        (AdicCompletion.transitionMap (maximalIdeal R) (⨁ _ : ι, R) hle z) =
      Finsupp.mapRange (Ideal.Quotient.factorPow (maximalIdeal R) hle) (by simp)
        (directSum_quotient_smul_top_linearEquiv_over_quotient
          (R := R) (ι := ι) (maximalIdeal R ^ n) z) := by
  refine Quotient.inductionOn z ?_
  intro y
  -- Proof comment: reduce to a representative in the free direct sum and then expand it as a
  -- finite sum of basis vectors, where the transition map is just quotient reduction.
  induction y using Finsupp.induction_linear with
  | zero =>
      simp [AdicCompletion.transitionMap, Submodule.factorPow]
  | add y w hy hw =>
      simp [hy, hw]
  | single i r =>
      simp [AdicCompletion.transitionMap, Submodule.factorPow,
        directSum_quotient_smul_top_linearEquiv_over_quotient_mk_lof]

/-- Helper for Lemma 15.45.3: the fixed lift family from the strict henselization gives
quotientwise coordinates on every Artinian quotient, and each chosen lift maps to the
corresponding standard basis vector. -/
lemma strict_henselization_quotient_linearEquiv_family_of_fixed_lifts :
    ∃ (ι : Type u) (x : ι → Rsh), ∀ n : ℕ,
      ∃ e : (Rsh ⧸ maximalIdeal Rsh ^ n) ≃ₗ[R ⧸ maximalIdeal R ^ n]
        (⨁ _ : ι, R ⧸ maximalIdeal R ^ n),
        ∀ i, e (Ideal.Quotient.mk _ (x i)) = Finsupp.single i 1 := by
  classical
  obtain ⟨ι, x, hx⟩ := strictHenselization_exists_basis_lift_family (R := R) (Rsh := Rsh)
  refine ⟨ι, x, ?_⟩
  intro n
  obtain ⟨b, hb⟩ := hx n
  refine ⟨by simpa using b.repr, ?_⟩
  intro i
  -- Proof comment: the quotient basis from Lemma `15.45.1` sends each chosen lift class to the
  -- matching standard basis vector in the direct sum of coefficients.
  simpa [hb i] using (Module.Basis.repr_self b i)

/-- Helper for Lemma 15.45.3: the fixed quotient coordinates for a strict henselization commute
with the inverse-system transition maps `Ideal.Quotient.factorPow`. -/
lemma strict_henselization_quotient_linearEquiv_family_factorPow_compat :
    ∃ (ι : Type u) (x : ι → Rsh), ∀ {m n : ℕ} (hle : m ≤ n),
      ∃ em : (Rsh ⧸ maximalIdeal Rsh ^ m) ≃ₗ[R ⧸ maximalIdeal R ^ m]
          (⨁ _ : ι, R ⧸ maximalIdeal R ^ m),
        ∃ en : (Rsh ⧸ maximalIdeal Rsh ^ n) ≃ₗ[R ⧸ maximalIdeal R ^ n]
            (⨁ _ : ι, R ⧸ maximalIdeal R ^ n),
          (∀ i, em (Ideal.Quotient.mk _ (x i)) = Finsupp.single i 1) ∧
          (∀ i, en (Ideal.Quotient.mk _ (x i)) = Finsupp.single i 1) ∧
          ∀ y : Rsh ⧸ maximalIdeal Rsh ^ n,
            em ((Ideal.Quotient.factorPow (maximalIdeal Rsh) hle) y) =
              Finsupp.mapRange (Ideal.Quotient.factorPow (maximalIdeal R) hle)
                (by simp) (en y) := by
  classical
  obtain ⟨ι, x, hx⟩ :=
    strict_henselization_quotient_linearEquiv_family_of_fixed_lifts (R := R) (Rsh := Rsh)
  refine ⟨ι, x, ?_⟩
  intro m n hle
  obtain ⟨em, hem⟩ := hx m
  obtain ⟨en, hen⟩ := hx n
  refine ⟨em, en, hem, hen, ?_⟩
  have hen_symm_single_one (i : ι) :
      en.symm (Finsupp.single i (1 : R ⧸ maximalIdeal R ^ n)) =
        Ideal.Quotient.mk _ (x i) := by
    -- Proof comment: the inverse coordinate map sends the standard basis vector back to the
    -- chosen lift class at the `n`th quotient stage.
    apply en.injective
    simpa [hen i]
  intro y
  -- Proof comment: rewrite `y` using its fixed coordinates and compare the two transition routes
  -- by induction on the finitely supported coordinate vector `en y`.
  rw [← LinearEquiv.symm_apply_apply en y]
  let z : ⨁ _ : ι, R ⧸ maximalIdeal R ^ n := en y
  change
    em ((Ideal.Quotient.factorPow (maximalIdeal Rsh) hle) (en.symm z)) =
      Finsupp.mapRange (Ideal.Quotient.factorPow (maximalIdeal R) hle) (by simp) z
  clear y
  induction z using Finsupp.induction_linear with
  | zero =>
      simp
  | add z w hz hw =>
      simp [hz, hw]
  | single i a =>
      have hsingle :
          en.symm (Finsupp.single i a) =
            a • Ideal.Quotient.mk (maximalIdeal Rsh ^ n) (x i) := by
        calc
          en.symm (Finsupp.single i a) =
              en.symm (a • Finsupp.single i (1 : R ⧸ maximalIdeal R ^ n)) := by
                simp
          _ = a • en.symm (Finsupp.single i (1 : R ⧸ maximalIdeal R ^ n)) := by
                simp
          _ = a • Ideal.Quotient.mk (maximalIdeal Rsh ^ n) (x i) := by
                rw [hen_symm_single_one i]
      -- Proof comment: on one coordinate, both sides send the chosen lift class to the same
      -- standard basis vector and transport the coefficient via `factorPow`.
      calc
        em ((Ideal.Quotient.factorPow (maximalIdeal Rsh) hle) (en.symm (Finsupp.single i a))) =
            em ((Ideal.Quotient.factorPow (maximalIdeal Rsh) hle)
              (a • Ideal.Quotient.mk (maximalIdeal Rsh ^ n) (x i))) := by
                rw [hsingle]
        _ = em (((Ideal.Quotient.factorPow (maximalIdeal R) hle) a) •
              Ideal.Quotient.mk (maximalIdeal Rsh ^ m) (x i)) := by
                simp [smul_eq_mul]
        _ = ((Ideal.Quotient.factorPow (maximalIdeal R) hle) a) •
              em (Ideal.Quotient.mk (maximalIdeal Rsh ^ m) (x i)) := by
                simp
        _ = ((Ideal.Quotient.factorPow (maximalIdeal R) hle) a) • Finsupp.single i 1 := by
                rw [hem i]
        _ = Finsupp.single i ((Ideal.Quotient.factorPow (maximalIdeal R) hle) a) := by
                simp
        _ = Finsupp.mapRange (Ideal.Quotient.factorPow (maximalIdeal R) hle)
              (by simp) (Finsupp.single i a) := by
                simp

/-- Helper for Lemma 15.45.3: a fixed basis-lift family determines the canonical coordinate
linear equivalence on each strict-henselization Artinian quotient. -/
noncomputable def strict_henselization_stage_linearEquiv
    {ι : Type u} (x : ι → Rsh)
    (hx : ∀ n : ℕ,
      ∃ b : Module.Basis ι (R ⧸ maximalIdeal R ^ n) (Rsh ⧸ maximalIdeal Rsh ^ n),
        ∀ i, b i = Ideal.Quotient.mk _ (x i))
    (n : ℕ) :
    (Rsh ⧸ maximalIdeal Rsh ^ n) ≃ₗ[R ⧸ maximalIdeal R ^ n]
      (⨁ _ : ι, R ⧸ maximalIdeal R ^ n) := by
  classical
  obtain ⟨b, hb⟩ := hx n
  -- Proof comment: the basis provided by Lemma `15.45.1 (7)` is converted to its coordinate
  -- linear equivalence.
  simpa using b.repr

/-- Helper for Lemma 15.45.3: the canonical stage coordinate equivalence sends each chosen lift
class to the matching standard basis vector. -/
@[simp] lemma strict_henselization_stage_linearEquiv_mk
    {ι : Type u} (x : ι → Rsh)
    (hx : ∀ n : ℕ,
      ∃ b : Module.Basis ι (R ⧸ maximalIdeal R ^ n) (Rsh ⧸ maximalIdeal Rsh ^ n),
        ∀ i, b i = Ideal.Quotient.mk _ (x i))
    (n : ℕ) (i : ι) :
    strict_henselization_stage_linearEquiv (R := R) (Rsh := Rsh) x hx n
        (Ideal.Quotient.mk _ (x i)) =
      Finsupp.single i 1 := by
  classical
  obtain ⟨b, hb⟩ := hx n
  -- Proof comment: the chosen lifts are literally the basis vectors for the fixed stage basis.
  simpa [strict_henselization_stage_linearEquiv, hb i] using Module.Basis.repr_self b i

/-- Helper for Lemma 15.45.3: the canonical stage coordinate equivalences commute with the
transition maps `Ideal.Quotient.factorPow`. -/
lemma strict_henselization_stage_linearEquiv_factorPow_compat
    {ι : Type u} (x : ι → Rsh)
    (hx : ∀ n : ℕ,
      ∃ b : Module.Basis ι (R ⧸ maximalIdeal R ^ n) (Rsh ⧸ maximalIdeal Rsh ^ n),
        ∀ i, b i = Ideal.Quotient.mk _ (x i))
    {m n : ℕ} (hle : m ≤ n)
    (y : Rsh ⧸ maximalIdeal Rsh ^ n) :
    strict_henselization_stage_linearEquiv (R := R) (Rsh := Rsh) x hx m
        ((Ideal.Quotient.factorPow (maximalIdeal Rsh) hle) y) =
      Finsupp.mapRange (Ideal.Quotient.factorPow (maximalIdeal R) hle) (by simp)
        (strict_henselization_stage_linearEquiv (R := R) (Rsh := Rsh) x hx n y) := by
  classical
  let em :=
    strict_henselization_stage_linearEquiv (R := R) (Rsh := Rsh) x hx m
  let en :=
    strict_henselization_stage_linearEquiv (R := R) (Rsh := Rsh) x hx n
  have hen_symm_single_one (i : ι) :
      en.symm (Finsupp.single i (1 : R ⧸ maximalIdeal R ^ n)) =
        Ideal.Quotient.mk _ (x i) := by
    -- Proof comment: the inverse coordinate map sends the standard basis vector back to the fixed
    -- lift class at stage `n`.
    apply en.injective
    simpa [en] using
      strict_henselization_stage_linearEquiv_mk
        (R := R) (Rsh := Rsh) x hx n i
  rw [← en.symm_apply_apply y]
  let z : ⨁ _ : ι, R ⧸ maximalIdeal R ^ n := en y
  change
    em ((Ideal.Quotient.factorPow (maximalIdeal Rsh) hle) (en.symm z)) =
      Finsupp.mapRange (Ideal.Quotient.factorPow (maximalIdeal R) hle)
        (by simp) z
  clear y
  induction z using Finsupp.induction_linear with
  | zero =>
      simp
  | add z w hz hw =>
      simp [hz, hw]
  | single i a =>
      have hsingle :
          en.symm (Finsupp.single i a) =
            a • Ideal.Quotient.mk (maximalIdeal Rsh ^ n) (x i) := by
        calc
          en.symm (Finsupp.single i a) =
              en.symm (a • Finsupp.single i (1 : R ⧸ maximalIdeal R ^ n)) := by
                simp
          _ = a • en.symm (Finsupp.single i (1 : R ⧸ maximalIdeal R ^ n)) := by
                simp
          _ = a • Ideal.Quotient.mk (maximalIdeal Rsh ^ n) (x i) := by
                rw [hen_symm_single_one i]
      -- Proof comment: both sides now transport one coordinate coefficient through `factorPow`
      -- and keep the same basis vector indexed by `i`.
      calc
        em ((Ideal.Quotient.factorPow (maximalIdeal Rsh) hle) (en.symm (Finsupp.single i a))) =
            em ((Ideal.Quotient.factorPow (maximalIdeal Rsh) hle)
              (a • Ideal.Quotient.mk (maximalIdeal Rsh ^ n) (x i))) := by
                rw [hsingle]
        _ = em (((Ideal.Quotient.factorPow (maximalIdeal R) hle) a) •
              Ideal.Quotient.mk (maximalIdeal Rsh ^ m) (x i)) := by
                simp [smul_eq_mul]
        _ = ((Ideal.Quotient.factorPow (maximalIdeal R) hle) a) •
              em (Ideal.Quotient.mk (maximalIdeal Rsh ^ m) (x i)) := by
                simp
        _ = ((Ideal.Quotient.factorPow (maximalIdeal R) hle) a) • Finsupp.single i 1 := by
                rw [strict_henselization_stage_linearEquiv_mk
                  (R := R) (Rsh := Rsh) x hx m i]
        _ = Finsupp.single i ((Ideal.Quotient.factorPow (maximalIdeal R) hle) a) := by
                simp
        _ = Finsupp.mapRange (Ideal.Quotient.factorPow (maximalIdeal R) hle)
              (by simp) (Finsupp.single i a) := by
                simp

/-- Helper for Lemma 15.45.3: the inverse quotient-stage map in the strict branch is the fixed
stage coordinate inverse packaged as a single `R`-linear map. -/
noncomputable abbrev strict_henselization_inverse_stageMap
    {ι : Type u} (x : ι → Rsh)
    (hx : ∀ n : ℕ,
      ∃ b : Module.Basis ι (R ⧸ maximalIdeal R ^ n) (Rsh ⧸ maximalIdeal Rsh ^ n),
        ∀ i, b i = Ideal.Quotient.mk _ (x i))
    (n : ℕ) :
    AdicCompletion (maximalIdeal Rsh) Rsh →ₗ[R]
      ((⨁ _ : ι, R) ⧸ ((maximalIdeal R ^ n) • (⊤ : Submodule R (⨁ _ : ι, R)))) :=
  (((directSum_quotient_smul_top_linearEquiv_over_quotient
      (R := R) (ι := ι) (maximalIdeal R ^ n)).symm.restrictScalars R).toLinearMap).comp
    ((((strict_henselization_stage_linearEquiv
        (R := R) (Rsh := Rsh) x hx n).restrictScalars R).toLinearMap).comp
      ((AdicCompletion.evalₐ (maximalIdeal Rsh) n).restrictScalars R))

/-- Helper for Lemma 15.45.3: the inverse quotient-stage maps for the strict completion
comparison satisfy the compatibility required by `AdicCompletion.lift`. -/
lemma strict_henselization_inverse_stage_family_compat
    {ι : Type u} (x : ι → Rsh)
    (hx : ∀ n : ℕ,
      ∃ b : Module.Basis ι (R ⧸ maximalIdeal R ^ n) (Rsh ⧸ maximalIdeal Rsh ^ n),
        ∀ i, b i = Ideal.Quotient.mk _ (x i))
    {m n : ℕ} (hle : m ≤ n) :
    (AdicCompletion.transitionMap (maximalIdeal R) (⨁ _ : ι, R) hle).comp
        (strict_henselization_inverse_stageMap
          (R := R) (Rsh := Rsh) x hx n) =
      strict_henselization_inverse_stageMap
        (R := R) (Rsh := Rsh) x hx m := by
  ext z
  apply
    (directSum_quotient_smul_top_linearEquiv_over_quotient
      (R := R) (ι := ι) (maximalIdeal R ^ m)).injective
  -- Proof comment: after applying the stage-`m` quotient/direct-sum coordinates, the left side
  -- becomes the coordinatewise `factorPow` transition, which matches the strict stage coordinates
  -- by the fixed-lift compatibility and `completion_eval_factor`.
  calc
    directSum_quotient_smul_top_linearEquiv_over_quotient
        (R := R) (ι := ι) (maximalIdeal R ^ m)
        ((AdicCompletion.transitionMap (maximalIdeal R) (⨁ _ : ι, R) hle).comp
          (strict_henselization_inverse_stageMap
            (R := R) (Rsh := Rsh) x hx n) z) =
      Finsupp.mapRange (Ideal.Quotient.factorPow (maximalIdeal R) hle) (by simp)
        (strict_henselization_stage_linearEquiv
          (R := R) (Rsh := Rsh) x hx n
          (AdicCompletion.evalₐ (maximalIdeal Rsh) n z)) := by
            simpa using
              directSum_quotient_transition_compat
                (R := R) (ι := ι) hle
                (strict_henselization_inverse_stageMap
                  (R := R) (Rsh := Rsh) x hx n z)
    _ = strict_henselization_stage_linearEquiv
          (R := R) (Rsh := Rsh) x hx m
          ((Ideal.Quotient.factorPow (maximalIdeal Rsh) hle)
            (AdicCompletion.evalₐ (maximalIdeal Rsh) n z)) := by
            symm
            exact
              strict_henselization_stage_linearEquiv_factorPow_compat
                (R := R) (Rsh := Rsh) x hx hle
                (AdicCompletion.evalₐ (maximalIdeal Rsh) n z)
    _ = strict_henselization_stage_linearEquiv
          (R := R) (Rsh := Rsh) x hx m
          (AdicCompletion.evalₐ (maximalIdeal Rsh) m z) := by
            rw [completion_eval_factor (S := Rsh) (I := maximalIdeal Rsh) hle z]
    _ = directSum_quotient_smul_top_linearEquiv_over_quotient
          (R := R) (ι := ι) (maximalIdeal R ^ m)
          (strict_henselization_inverse_stageMap
            (R := R) (Rsh := Rsh) x hx m z) := by
            simp [strict_henselization_inverse_stageMap]

/-- Helper for Lemma 15.45.3: a fixed family of lifts in the strict henselization determines the
raw `R`-linear map from the free direct sum to `Rˢʰ`. -/
noncomputable abbrev strict_henselization_lift_family_rawMap
    {ι : Type u} (x : ι → Rsh) :
    (⨁ _ : ι, R) →ₗ[R] Rsh :=
  DirectSum.toModule R ι Rsh fun i ↦
    (LinearMap.id : R →ₗ[R] R).smulRight (x i)

/-- Helper for Lemma 15.45.3: on one basis vector of the free direct sum, the raw lift-family map
sends the coefficient to the corresponding chosen strict-henselization lift. -/
@[simp] lemma strict_henselization_lift_family_rawMap_lof
    {ι : Type u} (x : ι → Rsh) (i : ι) (r : R) :
    strict_henselization_lift_family_rawMap (R := R) (Rsh := Rsh) x
        (DirectSum.lof R ι (fun _ : ι ↦ R) i r) =
      r • x i := by
  -- Proof comment: `DirectSum.toModule` is characterized by its values on the canonical summand
  -- inclusions, and here that value is the scalar multiple of the chosen lift.
  simp [strict_henselization_lift_family_rawMap, DirectSum.toModule_lof]

/-- Helper for Lemma 15.45.3: once `R` is Noetherian, the completion of `Rˢʰ` is complete for the
base maximal ideal after restricting scalars along `R → Rˢʰ`. -/
lemma strict_henselization_completion_isAdicComplete_over_base
    [IsNoetherianRing R] :
    IsAdicComplete (maximalIdeal R) (AdicCompletion (maximalIdeal Rsh) Rsh) := by
  have hfgRsh : (maximalIdeal Rsh).FG :=
    strictHenselization_maximalIdeal_fg_of_base_noetherian (R := R) (Rsh := Rsh)
  let _ : Field (Rsh ⧸ maximalIdeal Rsh) := Ideal.Quotient.field (maximalIdeal Rsh)
  let _ : IsNoetherianRing (Rsh ⧸ maximalIdeal Rsh) := inferInstance
  have hcompleteRsh :
      IsAdicComplete
        (Ideal.map (algebraMap Rsh (AdicCompletion (maximalIdeal Rsh) Rsh)) (maximalIdeal Rsh))
        (AdicCompletion (maximalIdeal Rsh) Rsh) :=
    (adicCompletion_isNoetherian_and_isAdicComplete
      (R := Rsh) (I := maximalIdeal Rsh) hfgRsh).2
  have hcompleteBaseMap :
      IsAdicComplete
        (Ideal.map (algebraMap Rsh (AdicCompletion (maximalIdeal Rsh) Rsh))
          (Ideal.map (algebraMap R Rsh) (maximalIdeal R)))
        (AdicCompletion (maximalIdeal Rsh) Rsh) := by
    -- Proof comment: for a strict henselization, the source maximal ideal extends to the target
    -- maximal ideal, so the completion ideal seen over `R` is the same one.
    simpa [IsStrictHenselizationOf.map_maximalIdeal (R := R) (S := Rsh)] using hcompleteRsh
  -- Proof comment: after identifying the transported ideal with the target completion ideal,
  -- completeness can be read back along restriction of scalars.
  exact
    (IsAdicComplete.map_algebraMap_iff (maximalIdeal R)
      (AdicCompletion (maximalIdeal Rsh) Rsh)).1 hcompleteBaseMap

/-- Helper for Lemma 15.45.3: the raw lift-family map extends to a map from the completed free
`R`-module to the completion of the strict henselization. -/
noncomputable abbrev strict_henselization_completion_from_lift_family
    [IsNoetherianRing R] {ι : Type u} (x : ι → Rsh) :
    AdicCompletion (maximalIdeal R) (⨁ _ : ι, R) →ₗ[R]
      AdicCompletion (maximalIdeal Rsh) Rsh :=
  let _ : IsAdicComplete (maximalIdeal R) (AdicCompletion (maximalIdeal Rsh) Rsh) :=
    strict_henselization_completion_isAdicComplete_over_base (R := R) (Rsh := Rsh)
  AdicCompletion.mapToComplete (maximalIdeal R)
    (strict_henselization_lift_family_rawMap (R := R) (Rsh := Rsh) x)

/-- Helper for Lemma 15.45.3: on the dense image of the free direct sum, the completion map from a
strict lift family agrees with the original raw linear combination map. -/
@[simp] lemma strict_henselization_completion_from_lift_family_of
    [IsNoetherianRing R] {ι : Type u} (x : ι → Rsh) (y : ⨁ _ : ι, R) :
    strict_henselization_completion_from_lift_family (R := R) (Rsh := Rsh) x
        (AdicCompletion.of (maximalIdeal R) (⨁ _ : ι, R) y) =
      strict_henselization_lift_family_rawMap (R := R) (Rsh := Rsh) x y := by
  -- Proof comment: `mapToComplete` is the universal completion extension of the raw map, so it
  -- agrees with that raw map on the canonical dense image.
  simpa [strict_henselization_completion_from_lift_family] using
    (AdicCompletion.mapToComplete_of (maximalIdeal R)
      (strict_henselization_lift_family_rawMap (R := R) (Rsh := Rsh) x) y)

/-- Helper for Lemma 15.45.3: on one basis vector of the completed free module, the completion
map from the chosen lift family lands on the matching completed strict-henselization lift. -/
@[simp] lemma strict_henselization_completion_from_lift_family_lof
    [IsNoetherianRing R] {ι : Type u} (x : ι → Rsh) (i : ι) (r : R) :
    strict_henselization_completion_from_lift_family (R := R) (Rsh := Rsh) x
        (AdicCompletion.of (maximalIdeal R) (⨁ _ : ι, R)
          (DirectSum.lof R ι (fun _ : ι ↦ R) i r)) =
      r • x i := by
  -- Proof comment: specialize the dense-image formula to one summand generator and then collapse
  -- the raw direct-sum calculation.
  simpa using
    strict_henselization_completion_from_lift_family_of
      (R := R) (Rsh := Rsh) x
      (DirectSum.lof R ι (fun _ : ι ↦ R) i r)

/-- Helper for Lemma 15.45.3: on dense direct-sum points, the forward completed lift-family map
has the expected stage-`n` quotient coordinates. -/
lemma strict_henselization_completion_from_lift_family_eval_stage_of
    [IsNoetherianRing R] {ι : Type u} (x : ι → Rsh)
    (hx : ∀ n : ℕ,
      ∃ b : Module.Basis ι (R ⧸ maximalIdeal R ^ n) (Rsh ⧸ maximalIdeal Rsh ^ n),
        ∀ i, b i = Ideal.Quotient.mk _ (x i))
    (n : ℕ) (y : ⨁ _ : ι, R) :
    strict_henselization_stage_linearEquiv (R := R) (Rsh := Rsh) x hx n
        (AdicCompletion.evalₐ (maximalIdeal Rsh) n
          (strict_henselization_completion_from_lift_family (R := R) (Rsh := Rsh) x
            (AdicCompletion.of (maximalIdeal R) (⨁ _ : ι, R) y))) =
      directSum_quotient_smul_top_linearEquiv_over_quotient
        (R := R) (ι := ι) (maximalIdeal R ^ n)
        (((maximalIdeal R ^ n) • (⊤ : Submodule R (⨁ _ : ι, R))).mkQ y) := by
  classical
  -- Proof comment: expand the finitely supported direct-sum element and check the coordinate
  -- statement one basis vector at a time.
  induction y using Finsupp.induction_linear with
  | zero =>
      simp
  | add y z hy hz =>
      simp [hy, hz]
  | single i r =>
      -- Proof comment: the forward map sends one basis vector to the chosen lift `x i`, and the
      -- fixed stage coordinates identify that class with the standard basis vector.
      simp [strict_henselization_completion_from_lift_family_lof,
        strict_henselization_stage_linearEquiv_mk,
        directSum_quotient_smul_top_linearEquiv_over_quotient_mk_lof, smul_eq_mul]

/-- Helper for Lemma 15.45.3: the direct sum of the quotient rings `R / m^n` is annihilated by
`m^n`, so it is already complete for the `m`-adic topology. -/
lemma directSum_quotient_target_pow_smul_top_eq_bot
    {ι : Type u} (n : ℕ) :
    maximalIdeal R ^ n •
        (⊤ : Submodule R (⨁ _ : ι, R ⧸ maximalIdeal R ^ n)) =
      ⊥ := by
  ext y
  constructor
  · intro hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro a ha z hz
      ext i
      change a • z i = 0
      refine Quotient.inductionOn (z i) ?_
      intro r
      exact (Ideal.Quotient.eq_zero_iff_mem _).2 <| Ideal.mul_mem_right _ ha
    · intro z w hz hw
      simpa [hz, hw]
  · intro hy
    simpa using hy

/-- Helper for Lemma 15.45.3: the forward completed lift-family map has the expected stage
coordinates on all completed free-module points. -/
lemma strict_henselization_completion_from_lift_family_eval_stage
    [IsNoetherianRing R] {ι : Type u} (x : ι → Rsh)
    (hx : ∀ n : ℕ,
      ∃ b : Module.Basis ι (R ⧸ maximalIdeal R ^ n) (Rsh ⧸ maximalIdeal Rsh ^ n),
        ∀ i, b i = Ideal.Quotient.mk _ (x i))
    (n : ℕ) :
    ((((strict_henselization_stage_linearEquiv
        (R := R) (Rsh := Rsh) x hx n).restrictScalars R).toLinearMap).comp
        ((AdicCompletion.evalₐ (maximalIdeal Rsh) n).restrictScalars R)).comp
        (strict_henselization_completion_from_lift_family (R := R) (Rsh := Rsh) x) =
      (((directSum_quotient_smul_top_linearEquiv_over_quotient
          (R := R) (ι := ι) (maximalIdeal R ^ n)).restrictScalars R).toLinearMap).comp
        ((AdicCompletion.evalₐ (maximalIdeal R) n).restrictScalars R) := by
  letI :
      IsAdicComplete (maximalIdeal R) (⨁ _ : ι, R ⧸ maximalIdeal R ^ n) :=
    isAdicComplete_of_pow_smul_top_eq_bot (I := maximalIdeal R) n
      (directSum_quotient_target_pow_smul_top_eq_bot (R := R) (ι := ι) n)
  apply completion_linearMap_ext_of_complete_target (I := maximalIdeal R)
  ext y
  -- Proof comment: agreement on the dense image is exactly the dense-point stage computation.
  simpa [LinearMap.comp_assoc, LinearMap.comp_apply] using
    strict_henselization_completion_from_lift_family_eval_stage_of
      (R := R) (Rsh := Rsh) x hx n y

/-- Helper for Lemma 15.45.3: the strict henselization is flat over the base local ring. -/
lemma strict_henselization_flat_over_base :
    Module.Flat R Rsh := by
  -- Proof comment: faithful flatness from Lemma `15.45.1` immediately gives the underlying
  -- flatness needed for the strict branch.
  let _ : Module.FaithfullyFlat R Rsh :=
    RingHom.faithfullyFlat_algebraMap_iff.mp strictHenselizationMap_faithfullyFlat
  infer_instance

/-- Helper for Lemma 15.45.3: the closed fiber of the strict henselization is flat over the
residue field of the base local ring. -/
lemma strict_henselization_closedFiber_flat :
    Module.Flat
      (R ⧸ maximalIdeal R)
      (Rsh ⧸ (maximalIdeal R • (⊤ : Submodule R Rsh))) := by
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
  -- Proof comment: every module over the residue field is flat, so the source proof's Artinian
  -- closed-fiber input is already available without additional structure.
  infer_instance

/-- Helper for Lemma 15.45.3: once `R` is Noetherian, the completion of its strict henselization
is already flat over the base ring `R`. -/
lemma strict_henselization_completion_flat_over_base
    [IsNoetherianRing R] :
    Module.Flat R (AdicCompletion (maximalIdeal Rsh) Rsh) := by
  obtain ⟨ι, x, hx⟩ :=
    strictHenselization_exists_basis_lift_family (R := R) (Rsh := Rsh)
  have hφ_stage_of :
      ∀ n : ℕ, ∀ y : ⨁ _ : ι, R,
        strict_henselization_stage_linearEquiv (R := R) (Rsh := Rsh) x hx n
            (AdicCompletion.evalₐ (maximalIdeal Rsh) n
              (strict_henselization_completion_from_lift_family (R := R) (Rsh := Rsh) x
                (AdicCompletion.of (maximalIdeal R) (⨁ _ : ι, R) y))) =
          directSum_quotient_smul_top_linearEquiv_over_quotient
            (R := R) (ι := ι) (maximalIdeal R ^ n)
            (((maximalIdeal R ^ n) • (⊤ : Submodule R (⨁ _ : ι, R))).mkQ y) := by
    intro n y
    -- Proof comment: the forward comparison already has the expected quotient coordinates on the
    -- dense direct-sum generators.
    simpa using
      strict_henselization_completion_from_lift_family_eval_stage_of
        (R := R) (Rsh := Rsh) x hx n y
  -- Proof comment: the source proof compares `(Rˢʰ)^` with the completion of a free `R`-module
  -- using the fixed basis-lift family from Lemma `15.45.1 (7)`, and then transports
  -- `adicCompletion_directSum_flat` across that comparison.
  let _ : Module.Flat R Rsh :=
    strict_henselization_flat_over_base (R := R) (Rsh := Rsh)
  let _ :
      Module.Flat
        (R ⧸ maximalIdeal R)
        (Rsh ⧸ (maximalIdeal R • (⊤ : Submodule R Rsh))) :=
    strict_henselization_closedFiber_flat (R := R) (Rsh := Rsh)
  let φ :
      AdicCompletion (maximalIdeal R) (⨁ _ : ι, R) →ₗ[R]
        AdicCompletion (maximalIdeal Rsh) Rsh :=
    strict_henselization_completion_from_lift_family (R := R) (Rsh := Rsh) x
  let q : ∀ n : ℕ,
      AdicCompletion (maximalIdeal Rsh) Rsh →ₗ[R]
        ((⨁ _ : ι, R) ⧸ ((maximalIdeal R ^ n) • (⊤ : Submodule R (⨁ _ : ι, R)))) :=
    fun n ↦ strict_henselization_inverse_stageMap (R := R) (Rsh := Rsh) x hx n
  have hq_compat :
      ∀ {m n : ℕ} (hle : m ≤ n),
        (AdicCompletion.transitionMap (maximalIdeal R) (⨁ _ : ι, R) hle).comp (q n) =
          q m := by
    intro m n hle
    -- Proof comment: the inverse quotient-stage maps satisfy the exact compatibility needed for
    -- `AdicCompletion.lift`.
    simpa [q] using
      strict_henselization_inverse_stage_family_compat
        (R := R) (Rsh := Rsh) x hx hle
  let ψ :
      AdicCompletion (maximalIdeal Rsh) Rsh →ₗ[R]
        AdicCompletion (maximalIdeal R) (⨁ _ : ι, R) :=
    AdicCompletion.lift (maximalIdeal R) q hq_compat
  have hleft_of :
      (ψ.comp φ).comp (AdicCompletion.of (maximalIdeal R) (⨁ _ : ι, R)) =
        AdicCompletion.of (maximalIdeal R) (⨁ _ : ι, R) := by
    ext y
    apply AdicCompletion.ext_evalₐ (I := maximalIdeal R)
    intro n
    calc
      AdicCompletion.evalₐ (maximalIdeal R) n
          (((ψ.comp φ).comp (AdicCompletion.of (maximalIdeal R) (⨁ _ : ι, R))) y) =
        q n (φ (AdicCompletion.of (maximalIdeal R) (⨁ _ : ι, R) y)) := by
          simp [ψ, q]
      _ =
        ((directSum_quotient_smul_top_linearEquiv_over_quotient
            (R := R) (ι := ι) (maximalIdeal R ^ n)).symm
          (strict_henselization_stage_linearEquiv
            (R := R) (Rsh := Rsh) x hx n
            (AdicCompletion.evalₐ (maximalIdeal Rsh) n
              (φ (AdicCompletion.of (maximalIdeal R) (⨁ _ : ι, R) y))))) := by
          rfl
      _ =
        ((directSum_quotient_smul_top_linearEquiv_over_quotient
            (R := R) (ι := ι) (maximalIdeal R ^ n)).symm
          (directSum_quotient_smul_top_linearEquiv_over_quotient
            (R := R) (ι := ι) (maximalIdeal R ^ n)
            (((maximalIdeal R ^ n) • (⊤ : Submodule R (⨁ _ : ι, R))).mkQ y))) := by
          congr 1
          simpa [φ] using hφ_stage_of n y
      _ =
        AdicCompletion.evalₐ (maximalIdeal R) n
          (AdicCompletion.of (maximalIdeal R) (⨁ _ : ι, R) y) := by
          simp
  have hleft : ψ.comp φ = LinearMap.id := by
    -- Proof comment: agreement on the dense image of the completed free module determines the
    -- whole completed map because the target is already complete.
    exact
      completion_linearMap_ext_of_complete_target
        (I := maximalIdeal R) hleft_of
  have hright_of :
      (φ.comp ψ).comp (AdicCompletion.of (maximalIdeal Rsh) Rsh) =
        AdicCompletion.of (maximalIdeal Rsh) Rsh := by
    ext r
    apply AdicCompletion.ext_evalₐ (I := maximalIdeal Rsh)
    intro n
    apply
      (strict_henselization_stage_linearEquiv
        (R := R) (Rsh := Rsh) x hx n).injective
    calc
      strict_henselization_stage_linearEquiv (R := R) (Rsh := Rsh) x hx n
          (AdicCompletion.evalₐ (maximalIdeal Rsh) n
            (((φ.comp ψ).comp (AdicCompletion.of (maximalIdeal Rsh) Rsh)) r)) =
        directSum_quotient_smul_top_linearEquiv_over_quotient
          (R := R) (ι := ι) (maximalIdeal R ^ n)
          (AdicCompletion.evalₐ (maximalIdeal R) n
            (ψ (AdicCompletion.of (maximalIdeal Rsh) Rsh r))) := by
          have hstage :=
            LinearMap.congr_fun
              (strict_henselization_completion_from_lift_family_eval_stage
                (R := R) (Rsh := Rsh) x hx n)
              (ψ (AdicCompletion.of (maximalIdeal Rsh) Rsh r))
          simpa [φ, LinearMap.comp_apply] using hstage
      _ =
        directSum_quotient_smul_top_linearEquiv_over_quotient
          (R := R) (ι := ι) (maximalIdeal R ^ n)
          (q n (AdicCompletion.of (maximalIdeal Rsh) Rsh r)) := by
          simp [ψ, q]
      _ =
        strict_henselization_stage_linearEquiv
          (R := R) (Rsh := Rsh) x hx n
          (AdicCompletion.evalₐ (maximalIdeal Rsh) n
            (AdicCompletion.of (maximalIdeal Rsh) Rsh r)) := by
          simp [q, strict_henselization_inverse_stageMap]
      _ =
        strict_henselization_stage_linearEquiv
          (R := R) (Rsh := Rsh) x hx n
          (((maximalIdeal Rsh ^ n) • (⊤ : Submodule Rsh Rsh)).mkQ r) := by
          simp
      _ =
        strict_henselization_stage_linearEquiv
          (R := R) (Rsh := Rsh) x hx n
          (AdicCompletion.evalₐ (maximalIdeal Rsh) n
            (AdicCompletion.of (maximalIdeal Rsh) Rsh r)) := by
          simp
  have hright : φ.comp ψ = LinearMap.id := by
    -- Proof comment: the same dense-image argument now runs on the strict-henselization side.
    exact
      completion_linearMap_ext_of_complete_target
        (I := maximalIdeal Rsh) hright_of
  let e :
      AdicCompletion (maximalIdeal R) (⨁ _ : ι, R) ≃ₗ[R]
        AdicCompletion (maximalIdeal Rsh) Rsh :=
    LinearEquiv.ofLinear φ ψ hleft hright
  let _ : Module.Flat R (AdicCompletion (maximalIdeal R) (⨁ _ : ι, R)) :=
    adicCompletion_directSum_flat (R := R) (maximalIdeal R) ι
  -- Proof comment: once the comparison with the completion of the free module is a linear
  -- equivalence, flatness transports from the completed free module to `(Rˢʰ)^`.
  exact Module.Flat.of_linearEquiv e

/-- Helper for Lemma 15.45.3: the maximal-ideal completion of a strict henselization is flat over
the strict henselization. -/
lemma strict_henselization_completion_flat :
    [IsNoetherianRing R] →
    Module.Flat Rsh (AdicCompletion (maximalIdeal Rsh) Rsh) := by
  intro
  -- Route correction: the earlier abstract transport route is replaced by the source proof's
  -- fixed basis-lift family and completed-free-module comparison.
  let _ : Module.Flat R (AdicCompletion (maximalIdeal Rsh) Rsh) :=
    strict_henselization_completion_flat_over_base (R := R) (Rsh := Rsh)
  -- Proof comment: the source proof first shows flatness over `R` by comparing the completion to
  -- the completion of a free `R`-module via the fixed basis-lift family, and then reruns the same
  -- filtered-colimit argument as for henselization to upgrade to flatness over `Rsh`.
  -- TODO: reuse the same closed-point localization wrapper for the strict ind-étale presentation,
  -- first comparing a chosen strict stage over `Sj` with `Rsh` via
  -- `existsUnique_algHom_to_strictHenselization_of_etale_of_residueFieldMap` and
  -- `existsUnique_algHom_between_strictHenselizations_of_residueFieldMap`, then bridging the
  -- chosen strict stage back to `Sj` through
  -- `strictHenselization_over_henselization_isStrictHenselizationOf` and
  -- `henselization_tensor_strictHenselization_isStrictHenselizationOf`.
  -- Once the stage comparison is installed, transport stage completion flatness to
  -- `(Rˢʰ)^` and conclude with `flat_of_stagewise_restrictScalars_flat`.
  sorry

/-- Lemma 15.45.3: for a local ring `R`, the following are equivalent: `R` is Noetherian, a
henselization `Rh` of `R` is Noetherian, and a strict henselization `Rsh` of `R` is Noetherian.
-/
theorem isNoetherianRing_tfae_of_henselization_and_strictHenselization :
    List.TFAE [IsNoetherianRing R, IsNoetherianRing Rh, IsNoetherianRing Rsh] := by
  tfae_have 2 → 1 := by
    intro hRh
    let _ : IsNoetherianRing Rh := hRh
    -- Proof comment: Noetherianity descends along the faithfully flat henselization map.
    exact
      isNoetherianRing_of_faithfullyFlat
        (algebraMap R Rh) henselizationMap_faithfullyFlat
  tfae_have 3 → 1 := by
    intro hRsh
    let _ : IsNoetherianRing Rsh := hRsh
    -- Proof comment: the strict henselization map is likewise faithfully flat.
    exact
      isNoetherianRing_of_faithfullyFlat
        (algebraMap R Rsh) strictHenselizationMap_faithfullyFlat
  tfae_have 1 → 2 := by
    intro hR
    let _ : IsNoetherianRing R := hR
    have hfgRh : (maximalIdeal Rh).FG :=
      henselization_maximalIdeal_fg_of_base_noetherian (R := R) (Rh := Rh)
    let _ : IsNoetherianRing (AdicCompletion (maximalIdeal Rh) Rh) :=
      completion_noetherian_of_maximalIdeal_fg (S := Rh) hfgRh
    let _ : IsCompleteLocalRing (AdicCompletion (maximalIdeal Rh) Rh) :=
      completion_isCompleteLocalRing_of_maximalIdeal_fg (S := Rh) hfgRh
    -- Proof comment: once the completion map `Rh → (Rh)^∧` is flat, faithful-flat descent from
    -- the Noetherian completion gives the Noetherianity of `Rh`.
    exact
      isNoetherianRing_of_noetherian_completion_and_flat_completion_map
        (S := Rh) (henselization_completion_flat (R := R) (Rh := Rh))
  tfae_have 1 → 3 := by
    intro hR
    let _ : IsNoetherianRing R := hR
    have hfgRsh : (maximalIdeal Rsh).FG :=
      strictHenselization_maximalIdeal_fg_of_base_noetherian (R := R) (Rsh := Rsh)
    let _ : IsNoetherianRing (AdicCompletion (maximalIdeal Rsh) Rsh) :=
      completion_noetherian_of_maximalIdeal_fg (S := Rsh) hfgRsh
    let _ : IsCompleteLocalRing (AdicCompletion (maximalIdeal Rsh) Rsh) :=
      completion_isCompleteLocalRing_of_maximalIdeal_fg (S := Rsh) hfgRsh
    -- Proof comment: the strict henselization branch has the same endgame once completion
    -- flatness is available.
    exact
      isNoetherianRing_of_noetherian_completion_and_flat_completion_map
        (S := Rsh) (strict_henselization_completion_flat (R := R) (Rsh := Rsh))
  tfae_finish

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
