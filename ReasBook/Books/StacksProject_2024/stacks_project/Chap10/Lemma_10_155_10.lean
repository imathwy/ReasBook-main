import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_154_6
import StacksProject_2024.stacks_project.Chap10.Lemma_10_155_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open IsLocalRing

section

variable {R : Type u} {S : Type u} {Rsh : Type u} {Ssh : Type u}
variable {K1sep : Type v} {K2sep : Type w}
variable [CommRing R] [CommRing S] [CommRing Rsh] [CommRing Ssh]
variable [Field K1sep] [Field K2sep]
variable [IsLocalRing R] [IsLocalRing S]
variable [Algebra R S] [IsLocalHom (algebraMap R S)]
variable [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]
variable [Algebra S Ssh] [Algebra R Ssh] [IsScalarTower R S Ssh]
variable [IsStrictHenselizationOf S Ssh]
variable [Algebra (ResidueField R) K1sep]
variable [Algebra (ResidueField S) K2sep]

/-
Domain-style sampling:
- primary domain: local commutative algebra of strict henselizations and residue-field-controlled
  comparison maps;
- sampled owner declarations of the same kind:
  `IsStrictHenselizationOf`,
  `existsUnique_algHom_of_filteredColimitOfEtale_of_henselianLocal_of_residueFieldMap`,
  `existsUnique_algHom_between_henselizations_of_localHom`,
  `ResidueField.map`;
- best owner abstraction: the source-facing owner is already `IsStrictHenselizationOf`; this file
  is a residue-field comparison `bridge/view` theorem built from that owner and the universal
  ind-étale lifting lemma `10.154.6`, and because all rings in sight are already local the
  canonical residue-field owner surface is `ResidueField` together with `ResidueField.map` for
  local maps;
- primitive data: the two strict-henselization owner instances and the chosen residue-field
  identifications `ιR`, `ιS` together with the compatibility map `φ`;
- derived API: the unique `R`-algebra map `Rsh → Ssh`, with locality recovered from the maximal-
  ideal pullback equality furnished by the core lifting theorem.

Source/core/bridge triage:
- `source-facing`: the present comparison theorem between chosen strict henselizations;
- `core/canonical`: `IsStrictHenselizationOf`, `IsLocalHom`, `ResidueField.map`, and
  `existsUnique_algHom_of_filteredColimitOfEtale_of_henselianLocal_of_residueFieldMap`;
- `bridge/view`: the chosen residue-field identifications with `K1sep` and `K2sep`.
-/

private noncomputable abbrev maximalIdealResidueFieldEquiv
    (A : Type*) [CommRing A] [IsLocalRing A] :
    (maximalIdeal A).ResidueField ≃+* ResidueField A :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField A) (maximalIdeal A).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))).symm

private theorem maximalIdealResidueFieldEquiv_apply_algebraMap
    (A : Type*) [CommRing A] [IsLocalRing A] (a : A) :
    maximalIdealResidueFieldEquiv A (algebraMap A (maximalIdeal A).ResidueField a) =
      residue A a := by
  rw [show algebraMap A (maximalIdeal A).ResidueField a =
      algebraMap (ResidueField A) (maximalIdeal A).ResidueField (residue A a) by rfl]
  change
    maximalIdealResidueFieldEquiv A ((maximalIdealResidueFieldEquiv A).symm (residue A a)) =
      residue A a
  exact (maximalIdealResidueFieldEquiv A).apply_symm_apply (residue A a)

private theorem maximalIdealResidueFieldEquiv_comp_residueFieldMap
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f] :
    (maximalIdealResidueFieldEquiv B).toRingHom.comp
        (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) f
          (IsLocalRing.maximalIdeal_comap f).symm) =
      (ResidueField.map f).comp (maximalIdealResidueFieldEquiv A).toRingHom := by
  apply Ideal.ResidueField.ringHom_ext
  ext a
  change
    maximalIdealResidueFieldEquiv B
        (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) f
          (IsLocalRing.maximalIdeal_comap f).symm (algebraMap A (maximalIdeal A).ResidueField a)) =
      ResidueField.map f
        (maximalIdealResidueFieldEquiv A (algebraMap A (maximalIdeal A).ResidueField a))
  rw [Ideal.ResidueField.map_algebraMap, maximalIdealResidueFieldEquiv_apply_algebraMap,
    maximalIdealResidueFieldEquiv_apply_algebraMap, IsLocalRing.ResidueField.map_residue]

omit [Algebra (ResidueField R) K1sep] [Algebra (ResidueField S) K2sep] in
private lemma existsUnique_algHom_between_strictHenselizations_of_idealResidueFieldMap
    [Algebra (maximalIdeal R).ResidueField K1sep] [Algebra (maximalIdeal S).ResidueField K2sep]
    (ιR : (maximalIdeal Rsh).ResidueField ≃+* K1sep)
    (hιR :
      ιR.toRingHom.comp
          (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal Rsh) (algebraMap R Rsh)
            (IsLocalRing.maximalIdeal_comap (algebraMap R Rsh)).symm) =
        algebraMap (maximalIdeal R).ResidueField K1sep)
    (ιS : (maximalIdeal Ssh).ResidueField ≃+* K2sep)
    (hιS :
      ιS.toRingHom.comp
          (Ideal.ResidueField.map (maximalIdeal S) (maximalIdeal Ssh) (algebraMap S Ssh)
            (IsLocalRing.maximalIdeal_comap (algebraMap S Ssh)).symm) =
        algebraMap (maximalIdeal S).ResidueField K2sep)
    (φ : K1sep →+* K2sep)
    (hφ :
      φ.comp (algebraMap (maximalIdeal R).ResidueField K1sep) =
        (algebraMap (maximalIdeal S).ResidueField K2sep).comp
          (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) (algebraMap R S)
            (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm)) :
    ∃! f : Rsh →ₐ[R] Ssh,
      ∃ hfq : maximalIdeal Rsh = Ideal.comap (f : Rsh →+* Ssh) (maximalIdeal Ssh),
        ιS.toRingHom.comp
            (Ideal.ResidueField.map (maximalIdeal Rsh) (maximalIdeal Ssh) (f : Rsh →+* Ssh) hfq) =
          φ.comp ιR.toRingHom := by
  let _ : IsLocalHom (algebraMap R Ssh) := by
    simpa [IsScalarTower.algebraMap_eq R S Ssh] using
      (show IsLocalHom ((algebraMap S Ssh).comp (algebraMap R S)) from inferInstance)
  have hqRsh :
      (maximalIdeal Rsh).under R = maximalIdeal R := by
    simpa [Ideal.under_def] using
      (IsLocalRing.maximalIdeal_comap (algebraMap R Rsh))
  have hqSshR :
      maximalIdeal R = (maximalIdeal Ssh).under R := by
    simpa [Ideal.under_def] using
      (IsLocalRing.maximalIdeal_comap (algebraMap R Ssh)).symm
  let τ : (maximalIdeal Rsh).ResidueField →+* (maximalIdeal Ssh).ResidueField :=
    ιS.symm.toRingHom.comp (φ.comp ιR.toRingHom)
  have hqSsh :
      (maximalIdeal Rsh).under R = (maximalIdeal Ssh).under R := by
    rw [hqRsh, hqSshR]
  have hιS' :
      ιS.symm.toRingHom.comp (algebraMap (maximalIdeal S).ResidueField K2sep) =
        Ideal.ResidueField.map (maximalIdeal S) (maximalIdeal Ssh) (algebraMap S Ssh)
          (IsLocalRing.maximalIdeal_comap (algebraMap S Ssh)).symm := by
    refine RingHom.ext fun x ↦ ?_
    apply ιS.injective
    simpa using (congrArg (fun ψ ↦ ψ x) hιS).symm
  have hmap :
      Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal Ssh) (algebraMap R Ssh) hqSshR =
        (Ideal.ResidueField.map (maximalIdeal S) (maximalIdeal Ssh) (algebraMap S Ssh)
          (IsLocalRing.maximalIdeal_comap (algebraMap S Ssh)).symm).comp
          (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) (algebraMap R S)
            (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm) := by
    apply Ideal.ResidueField.ringHom_ext
    ext r
    simp [IsScalarTower.algebraMap_eq R S Ssh]
  have hτ :
      τ.comp
          (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal Rsh) (algebraMap R Rsh)
            (IsLocalRing.maximalIdeal_comap (algebraMap R Rsh)).symm) =
        Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal Ssh) (algebraMap R Ssh) hqSshR := by
    calc
      τ.comp
          (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal Rsh) (algebraMap R Rsh)
            (IsLocalRing.maximalIdeal_comap (algebraMap R Rsh)).symm)
          = ιS.symm.toRingHom.comp
              (φ.comp
                (ιR.toRingHom.comp
                  (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal Rsh) (algebraMap R Rsh)
                    (IsLocalRing.maximalIdeal_comap (algebraMap R Rsh)).symm))) := by
                rw [show τ = ιS.symm.toRingHom.comp (φ.comp ιR.toRingHom) from rfl,
                  RingHom.comp_assoc, RingHom.comp_assoc]
      _ = ιS.symm.toRingHom.comp
            ((algebraMap (maximalIdeal S).ResidueField K2sep).comp
              (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) (algebraMap R S)
                (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm)) := by
              rw [hιR, hφ]
      _ = (ιS.symm.toRingHom.comp (algebraMap (maximalIdeal S).ResidueField K2sep)).comp
            (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) (algebraMap R S)
              (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm) := by
              rw [RingHom.comp_assoc]
      _ = (Ideal.ResidueField.map (maximalIdeal S) (maximalIdeal Ssh) (algebraMap S Ssh)
            (IsLocalRing.maximalIdeal_comap (algebraMap S Ssh)).symm).comp
            (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) (algebraMap R S)
              (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm) := by
              rw [hιS']
      _ = Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal Ssh) (algebraMap R Ssh) hqSshR := by
              rw [hmap]
  have hτ' :
      τ.comp
          (Ideal.ResidueField.map ((maximalIdeal Rsh).under R) (maximalIdeal Rsh)
            (algebraMap R Rsh) rfl) =
        Ideal.ResidueField.map ((maximalIdeal Rsh).under R) (maximalIdeal Ssh)
          (algebraMap R Ssh) hqSsh := by
    apply Ideal.ResidueField.ringHom_ext
    ext r
    apply ιS.injective
    have hr :=
      congrArg (fun ψ ↦ ψ (algebraMap R (maximalIdeal R).ResidueField r)) hτ
    simpa [hqRsh, hqSsh, hqSshR] using hr
  have hRsh : (algebraMap R Rsh).IsFilteredColimitOfEtale :=
    IsStrictHenselizationOf.isFilteredColimitOfEtale
  obtain ⟨f, hf, huniq⟩ :=
    existsUnique_algHom_of_filteredColimitOfEtale_of_henselianLocal_of_residueFieldMap
      hRsh (maximalIdeal Rsh) hqSsh τ hτ'
  refine ⟨f, ?_, ?_⟩
  · rcases hf with ⟨hfq, hres⟩
    refine ⟨hfq, ?_⟩
    calc
      ιS.toRingHom.comp
          (Ideal.ResidueField.map (maximalIdeal Rsh) (maximalIdeal Ssh) (f : Rsh →+* Ssh) hfq)
          = ιS.toRingHom.comp τ := by rw [hres]
      _ = φ.comp ιR.toRingHom := by
            ext x
            simp [τ]
  · intro g hg
    rcases hg with ⟨hgq, hgres⟩
    apply huniq g
    refine ⟨hgq, ?_⟩
    refine RingHom.ext fun x ↦ ?_
    apply ιS.injective
    simpa [τ] using congrArg (fun ψ ↦ ψ x) hgres

-- Proof sketch: apply Lemma `10.154.6` with `A = Rsh`, `q = maximalIdeal Rsh`, and target `Ssh`.
-- The strict henselization hypotheses provide the filtered-colimit-of-etale structure on `Rsh`,
-- the local-map conditions for `R → Rsh` and `S → Ssh`, and the control of maximal ideals. The
-- chosen residue-field identifications `ιR` and `ιS` transport the given `φ : K1sep →+* K2sep`
-- to the residue-field map required by Lemma `10.154.6`, and uniqueness there yields uniqueness
-- of the resulting local `R`-algebra map `Rsh → Ssh`.
/-- Lemma 10.155.10: for a local map `R → S`, chosen separable closures `K1sep` of
`ResidueField R` and `K2sep` of `ResidueField S`, and corresponding strict henselizations `Rsh`
and `Ssh`, any compatible map `φ : K1sep →+* K2sep` induces a unique local `R`-algebra map
`Rsh → Ssh` whose induced residue-field map agrees with `φ` via the chosen identifications
`ResidueField Rsh ≃+* K1sep` and `ResidueField Ssh ≃+* K2sep`. -/
lemma existsUnique_algHom_between_strictHenselizations_of_residueFieldMap
    (ιR : ResidueField Rsh ≃+* K1sep)
    (hιR :
      ιR.toRingHom.comp (ResidueField.map (algebraMap R Rsh)) =
        algebraMap (ResidueField R) K1sep)
    (ιS : ResidueField Ssh ≃+* K2sep)
    (hιS :
      ιS.toRingHom.comp (ResidueField.map (algebraMap S Ssh)) =
        algebraMap (ResidueField S) K2sep)
    (φ : K1sep →+* K2sep)
    (hφ :
      φ.comp (algebraMap (ResidueField R) K1sep) =
        (algebraMap (ResidueField S) K2sep).comp
          (ResidueField.map (algebraMap R S))) :
    ∃! f : Rsh →ₐ[R] Ssh,
      IsLocalHom (f : Rsh →+* Ssh) ∧
        (ιS.toRingHom.comp (residue Ssh)).comp (f : Rsh →+* Ssh) =
          (φ.comp ιR.toRingHom).comp (residue Rsh) := by
  let eR := maximalIdealResidueFieldEquiv R
  let eS := maximalIdealResidueFieldEquiv S
  let eRsh := maximalIdealResidueFieldEquiv Rsh
  let eSsh := maximalIdealResidueFieldEquiv Ssh
  let _ : Algebra (maximalIdeal R).ResidueField K1sep :=
    ((algebraMap (ResidueField R) K1sep).comp eR.toRingHom).toAlgebra
  let _ : Algebra (maximalIdeal S).ResidueField K2sep :=
    ((algebraMap (ResidueField S) K2sep).comp eS.toRingHom).toAlgebra
  let ιR' : (maximalIdeal Rsh).ResidueField ≃+* K1sep := eRsh.trans ιR
  let ιS' : (maximalIdeal Ssh).ResidueField ≃+* K2sep := eSsh.trans ιS
  have hιR' :
      ιR'.toRingHom.comp
          (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal Rsh) (algebraMap R Rsh)
            (IsLocalRing.maximalIdeal_comap (algebraMap R Rsh)).symm) =
        algebraMap (maximalIdeal R).ResidueField K1sep := by
    calc
      ιR'.toRingHom.comp
          (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal Rsh) (algebraMap R Rsh)
            (IsLocalRing.maximalIdeal_comap (algebraMap R Rsh)).symm)
          = ιR.toRingHom.comp
              (eRsh.toRingHom.comp
                (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal Rsh) (algebraMap R Rsh)
                  (IsLocalRing.maximalIdeal_comap (algebraMap R Rsh)).symm)) := by
                rfl
      _ = ιR.toRingHom.comp
            ((ResidueField.map (algebraMap R Rsh)).comp eR.toRingHom) := by
              rw [maximalIdealResidueFieldEquiv_comp_residueFieldMap]
      _ = (ιR.toRingHom.comp (ResidueField.map (algebraMap R Rsh))).comp eR.toRingHom := by
            rw [RingHom.comp_assoc]
      _ = (algebraMap (ResidueField R) K1sep).comp eR.toRingHom := by rw [hιR]
      _ = algebraMap (maximalIdeal R).ResidueField K1sep := by
            rfl
  have hιS' :
      ιS'.toRingHom.comp
          (Ideal.ResidueField.map (maximalIdeal S) (maximalIdeal Ssh) (algebraMap S Ssh)
            (IsLocalRing.maximalIdeal_comap (algebraMap S Ssh)).symm) =
        algebraMap (maximalIdeal S).ResidueField K2sep := by
    calc
      ιS'.toRingHom.comp
          (Ideal.ResidueField.map (maximalIdeal S) (maximalIdeal Ssh) (algebraMap S Ssh)
            (IsLocalRing.maximalIdeal_comap (algebraMap S Ssh)).symm)
          = ιS.toRingHom.comp
              (eSsh.toRingHom.comp
                (Ideal.ResidueField.map (maximalIdeal S) (maximalIdeal Ssh) (algebraMap S Ssh)
                  (IsLocalRing.maximalIdeal_comap (algebraMap S Ssh)).symm)) := by
                rfl
      _ = ιS.toRingHom.comp
            ((ResidueField.map (algebraMap S Ssh)).comp eS.toRingHom) := by
              rw [maximalIdealResidueFieldEquiv_comp_residueFieldMap]
      _ = (ιS.toRingHom.comp (ResidueField.map (algebraMap S Ssh))).comp eS.toRingHom := by
            rw [RingHom.comp_assoc]
      _ = (algebraMap (ResidueField S) K2sep).comp eS.toRingHom := by rw [hιS]
      _ = algebraMap (maximalIdeal S).ResidueField K2sep := by
            rfl
  have hφ' :
      φ.comp (algebraMap (maximalIdeal R).ResidueField K1sep) =
        (algebraMap (maximalIdeal S).ResidueField K2sep).comp
          (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) (algebraMap R S)
            (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm) := by
    calc
      φ.comp (algebraMap (maximalIdeal R).ResidueField K1sep)
          = (φ.comp (algebraMap (ResidueField R) K1sep)).comp eR.toRingHom := by
              rfl
      _ = ((algebraMap (ResidueField S) K2sep).comp (ResidueField.map (algebraMap R S))).comp
            eR.toRingHom := by rw [hφ]
      _ = (algebraMap (ResidueField S) K2sep).comp
            ((ResidueField.map (algebraMap R S)).comp eR.toRingHom) := by
            rw [← RingHom.comp_assoc]
      _ = (algebraMap (ResidueField S) K2sep).comp
            (eS.toRingHom.comp
              (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) (algebraMap R S)
                (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm)) := by
            rw [maximalIdealResidueFieldEquiv_comp_residueFieldMap]
      _ = ((algebraMap (ResidueField S) K2sep).comp eS.toRingHom).comp
            (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) (algebraMap R S)
              (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm) := by
            rw [RingHom.comp_assoc]
      _ = (algebraMap (maximalIdeal S).ResidueField K2sep).comp
            (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) (algebraMap R S)
              (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm) := by
            rfl
  obtain ⟨f, hf, huniq⟩ :=
    existsUnique_algHom_between_strictHenselizations_of_idealResidueFieldMap
      ιR' hιR' ιS' hιS' φ hφ'
  refine ⟨f, ?_, ?_⟩
  · rcases hf with ⟨hfq, hres⟩
    let hlocal : IsLocalHom (f : Rsh →+* Ssh) :=
      ((IsLocalRing.local_hom_TFAE (f : Rsh →+* Ssh)).out 4 0).mp hfq.symm
    letI : IsLocalHom (f : Rsh →+* Ssh) := hlocal
    have hhf : hfq = (IsLocalRing.maximalIdeal_comap (f : Rsh →+* Ssh)).symm := by
      apply Subsingleton.elim
    have hcomp :
        (ιS.toRingHom.comp (ResidueField.map (f : Rsh →+* Ssh))).comp eRsh.toRingHom =
          (φ.comp ιR.toRingHom).comp eRsh.toRingHom := by
      have hmapf :
          eSsh.toRingHom.comp
              (Ideal.ResidueField.map (maximalIdeal Rsh) (maximalIdeal Ssh)
                (f : Rsh →+* Ssh) hfq) =
            (ResidueField.map (f : Rsh →+* Ssh)).comp eRsh.toRingHom := by
        simpa [hhf] using
          maximalIdealResidueFieldEquiv_comp_residueFieldMap (f : Rsh →+* Ssh)
      calc
        (ιS.toRingHom.comp (ResidueField.map (f : Rsh →+* Ssh))).comp eRsh.toRingHom
            = ιS.toRingHom.comp
                (eSsh.toRingHom.comp
                  (Ideal.ResidueField.map (maximalIdeal Rsh) (maximalIdeal Ssh)
                    (f : Rsh →+* Ssh) hfq)) := by
                      rw [hmapf]
                      rw [RingHom.comp_assoc]
        _ = ιS'.toRingHom.comp
              (Ideal.ResidueField.map (maximalIdeal Rsh) (maximalIdeal Ssh) (f : Rsh →+* Ssh) hfq) := by
                rfl
        _ = (φ.comp ιR'.toRingHom) := by rw [hres]
        _ = (φ.comp ιR.toRingHom).comp eRsh.toRingHom := by
              simp [ιR', RingHom.comp_assoc]
    have hmapfinal :
        ιS.toRingHom.comp (ResidueField.map (f : Rsh →+* Ssh)) =
          φ.comp ιR.toRingHom := by
      exact RingHom.ext fun x ↦ by
        have hx := congrArg (fun ψ ↦ ψ (eRsh.symm x)) hcomp
        simpa using hx
    have hfinal :
        (ιS.toRingHom.comp (residue Ssh)).comp (f : Rsh →+* Ssh) =
          (φ.comp ιR.toRingHom).comp (residue Rsh) := by
      refine RingHom.ext fun x ↦ ?_
      have hx := congrArg (fun ψ ↦ ψ (residue Rsh x)) hmapfinal
      simpa [RingHom.comp_assoc, ResidueField.map_residue] using hx
    exact ⟨hlocal, hfinal⟩
  · intro g hg
    rcases hg with ⟨hlocal, hgres⟩
    letI : IsLocalHom (g : Rsh →+* Ssh) := hlocal
    have hgq :
        maximalIdeal Rsh = Ideal.comap (g : Rsh →+* Ssh) (maximalIdeal Ssh) :=
      (IsLocalRing.maximalIdeal_comap (g : Rsh →+* Ssh)).symm
    have hgres' :
        ιS.toRingHom.comp (ResidueField.map (g : Rsh →+* Ssh)) =
          φ.comp ιR.toRingHom := by
      refine RingHom.ext fun x ↦ ?_
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
      have hr := congrArg (fun ψ ↦ ψ r) hgres
      simpa [RingHom.comp_assoc, ResidueField.map_residue] using hr
    apply huniq g
    refine ⟨hgq, ?_⟩
    calc
      ιS'.toRingHom.comp
          (Ideal.ResidueField.map (maximalIdeal Rsh) (maximalIdeal Ssh) (g : Rsh →+* Ssh) hgq)
          = (ιS.toRingHom.comp (ResidueField.map (g : Rsh →+* Ssh))).comp eRsh.toRingHom := by
                calc
                  ιS'.toRingHom.comp
                      (Ideal.ResidueField.map (maximalIdeal Rsh) (maximalIdeal Ssh) (g : Rsh →+* Ssh) hgq)
                      = ιS.toRingHom.comp
                          (eSsh.toRingHom.comp
                            (Ideal.ResidueField.map (maximalIdeal Rsh) (maximalIdeal Ssh)
                              (g : Rsh →+* Ssh) hgq)) := by
                                rfl
                  _ = ιS.toRingHom.comp
                        ((ResidueField.map (g : Rsh →+* Ssh)).comp eRsh.toRingHom) := by
                              rw [maximalIdealResidueFieldEquiv_comp_residueFieldMap]
                  _ = (ιS.toRingHom.comp (ResidueField.map (g : Rsh →+* Ssh))).comp eRsh.toRingHom := by
                              rw [RingHom.comp_assoc]
      _ = (φ.comp ιR.toRingHom).comp eRsh.toRingHom := by rw [hgres']
      _ = φ.comp ιR'.toRingHom := by
            simp [ιR', RingHom.comp_assoc]

end
