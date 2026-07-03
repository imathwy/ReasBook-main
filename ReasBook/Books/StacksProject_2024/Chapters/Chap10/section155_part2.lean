import Mathlib
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.Henselian

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_155_10 (from Chap10) -/
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

/-! ### Lemma_10_155_11 (from Chap10) -/
open CategoryTheory
open CategoryTheory.Limits
open IsLocalRing

universe u

noncomputable section

section LocalRingLocalization

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- A local ring is already a localization at the complement of its maximal ideal. -/
private instance self_isLocalization_primeCompl_maximalIdeal :
    IsLocalization (maximalIdeal A).primeCompl A := sorry

/-- The canonical algebra equivalence from the localization of a local ring at the complement of
its maximal ideal back to the ring itself. -/
private abbrev localRing_atMaximalIdeal_algEquiv :
    Localization.AtPrime (maximalIdeal A) ≃ₐ[A] A :=
  IsLocalization.algEquiv
    (maximalIdeal A).primeCompl
    (Localization.AtPrime (maximalIdeal A))
    A

end LocalRingLocalization

section

variable {R : Type u} [CommRing R]
variable (p : Ideal R) [p.IsPrime]
variable {Ksep : Type u} [Field Ksep]
variable [Algebra R Ksep] [Algebra p.ResidueField Ksep] [IsScalarTower R p.ResidueField Ksep]
variable [IsSepClosure p.ResidueField Ksep]

/- Domain-style sampling:
* primary domain: strict henselization of `Rₚ` presented by the filtered category of étale
  neighborhoods `(S, q, φ)` of the chosen prime `p` equipped with a residue-field map into the
  chosen separable closure `Ksep`;
* sampled owner declarations of the same kind:
  - `selectedAlgebrasOverTargetDiagram`;
  - `etaleResidueFieldNeighborhoodSourceDiagram`;
  - `etaleResidueFieldNeighborhoodLocalizationDiagram`;
  - `existsUnique_algHom_to_strictHenselization_of_etale_of_residueFieldMap`;
* best owner abstraction:
  - `source-facing`: the explicit-prime neighborhood category indexed by triples
    `(S, q, φ)` over the fixed prime `p`, together with its source and localized diagrams;
  - `core/canonical`: the chapter owners `selectedAlgebrasOverTargetDiagram`,
    `IsStrictHenselizationOf`, and the residue-field lifting theorem
    `existsUnique_algHom_to_strictHenselization_of_etale_of_residueFieldMap`;
  - `bridge/view`: the cocones from those source-facing diagrams to a chosen strict henselization
    of `Rₚ`.
 * primitive data:
  - the ambient over-category `Over (CommAlgCat.of R Ksep)`;
  - the internal étale object property on that category;
  - the chosen prime `p`, kept explicit only on the source-facing neighborhood owner because
    `Ksep` is fixed as a separable closure of `κ(p)`.
* derived API:
  - the source diagram in `CommAlgCat R`;
  - the localized diagram in `CommAlgCat Rₚ`;
  - the filteredness theorem and the strict-henselization colimit cocones.

This file therefore follows the owner pattern of `Lemma_10_155_7`: keep `p` explicit, keep the
source and localization diagrams in the ambient algebra categories, and make the strict
henselization output an explicit cocone-plus-`IsColimit` construction rather than an existential
`CommRingCat` package.
-/

/-- Internal shorthand for the ambient over-category of `R`-algebras equipped with a chosen map
to `Ksep`. -/
private abbrev SepClosurePointedAlgebraCategory (R : Type u) [CommRing R]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] :=
  Over (CommAlgCat.of R Ksep)

/-- Internal helper selecting those pointed `R`-algebras over `Ksep` whose structure map from `R`
is étale. -/
private abbrev etaleSepClosurePointedAlgebraProperty (R : Type u) [CommRing R]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] :
    ObjectProperty (SepClosurePointedAlgebraCategory R Ksep) :=
  fun A ↦ RingHom.Etale (algebraMap R A.left)

/-- The category of étale neighborhoods `(S, q, φ)` of `p` with `φ : κ(q) → Ksep`. -/
abbrev EtaleSepClosureNeighborhoodCategory (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep] :=
  (etaleSepClosurePointedAlgebraProperty R Ksep).FullSubcategory

/-- The diagram sending `(S, q, φ)` to the underlying `R`-algebra `S`. -/
abbrev etaleSepClosureNeighborhoodSourceDiagram (R : Type u) [CommRing R] (p : Ideal R)
    [p.IsPrime] (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep] :
    EtaleSepClosureNeighborhoodCategory R p Ksep ⥤ CommAlgCat R :=
  selectedAlgebrasOverTargetDiagram (etaleSepClosurePointedAlgebraProperty R Ksep)

/-- The structure map from an object over `Ksep` to the fixed target `Ksep`. -/
private noncomputable abbrev sepClosurePointedAlgebraToSepClosure
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    (A : SepClosurePointedAlgebraCategory R Ksep) :
    A.left →+* Ksep :=
  let φ := (forget₂ (CommAlgCat R) CommRingCat).map A.hom
  φ.hom

/-- The underlying ring homomorphism of a morphism over `Ksep`. -/
private abbrev sepClosurePointedAlgebraHom (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    {A B : SepClosurePointedAlgebraCategory R Ksep} (f : A ⟶ B) :
    A.left →+* B.left :=
  let φ := f.left
  φ.hom

/-- The underlying ring homomorphism of a morphism in the full subcategory of étale neighborhoods
over `Ksep`. -/
private abbrev etaleSepClosureNeighborhoodHom (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    {A B : EtaleSepClosureNeighborhoodCategory R p Ksep} (f : A ⟶ B) :
    A.obj.left →+* B.obj.left :=
  sepClosurePointedAlgebraHom R p Ksep f.hom

/-- The prime ideal attached to an object over `Ksep` is the kernel of its structural map to
`Ksep`. -/
private noncomputable abbrev sepClosurePointedAlgebraKernel
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    (A : SepClosurePointedAlgebraCategory R Ksep) :
    Ideal A.left :=
  RingHom.ker (sepClosurePointedAlgebraToSepClosure R p Ksep A)

/-- The chosen prime of the source object is the comap of the chosen prime of the target. -/
private theorem sepClosurePointedAlgebraKernel_comap (R : Type u) [CommRing R]
    (p : Ideal R) [p.IsPrime] (Ksep : Type u) [Field Ksep] [Algebra R Ksep]
    [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    {A B : SepClosurePointedAlgebraCategory R Ksep} (f : A ⟶ B) :
    sepClosurePointedAlgebraKernel R p Ksep A =
      Ideal.comap (sepClosurePointedAlgebraHom R p Ksep f)
        (sepClosurePointedAlgebraKernel R p Ksep B) := sorry

/-- The kernel of a map to the field `Ksep` is prime. -/
private instance sepClosurePointedAlgebraKernel_isPrime
    (A : SepClosurePointedAlgebraCategory R Ksep) :
    (sepClosurePointedAlgebraKernel R p Ksep A).IsPrime :=
  RingHom.ker_isPrime _

/-- The chosen prime of an object over `Ksep` lies over the fixed prime `p`. -/
private theorem sepClosurePointedAlgebraKernel_comap_algebraMap
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    (A : SepClosurePointedAlgebraCategory R Ksep) :
    p = Ideal.comap (algebraMap R A.left) (sepClosurePointedAlgebraKernel R p Ksep A) := sorry

/-- The canonical `Rₚ`-algebra map to the localization of an étale neighborhood at its chosen
prime. -/
private noncomputable abbrev etaleSepClosureNeighborhoodLocalizationAlgebraMap
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) :
    Localization.AtPrime p →+* Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj) :=
  Localization.localRingHom
    p
    (sepClosurePointedAlgebraKernel R p Ksep A.obj)
    (algebraMap R A.obj.left)
    (sepClosurePointedAlgebraKernel_comap_algebraMap R p Ksep A.obj)

/-- The localization map induced by the identity morphism is the identity. -/
private theorem sepClosurePointedAlgebraLocalization_map_id (R : Type u) [CommRing R]
    (p : Ideal R) [p.IsPrime] (Ksep : Type u) [Field Ksep] [Algebra R Ksep]
    [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) :
    Localization.localRingHom
        (sepClosurePointedAlgebraKernel R p Ksep A.obj)
        (sepClosurePointedAlgebraKernel R p Ksep A.obj)
        (RingHom.id A.obj.left)
        (sepClosurePointedAlgebraKernel_comap R p Ksep (𝟙 A.obj)) =
      RingHom.id _ := sorry

/-- Localization along a composite morphism agrees with the composite of the localization maps. -/
private theorem sepClosurePointedAlgebraLocalization_map_comp (R : Type u) [CommRing R]
    (p : Ideal R) [p.IsPrime] (Ksep : Type u) [Field Ksep] [Algebra R Ksep]
    [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    {A B C : EtaleSepClosureNeighborhoodCategory R p Ksep} (f : A ⟶ B) (g : B ⟶ C) :
    Localization.localRingHom
        (sepClosurePointedAlgebraKernel R p Ksep A.obj)
        (sepClosurePointedAlgebraKernel R p Ksep C.obj)
        ((etaleSepClosureNeighborhoodHom R p Ksep g).comp
          (etaleSepClosureNeighborhoodHom R p Ksep f))
        (sepClosurePointedAlgebraKernel_comap R p Ksep (f.hom ≫ g.hom)) =
      (Localization.localRingHom
          (sepClosurePointedAlgebraKernel R p Ksep B.obj)
          (sepClosurePointedAlgebraKernel R p Ksep C.obj)
          (etaleSepClosureNeighborhoodHom R p Ksep g)
          (sepClosurePointedAlgebraKernel_comap R p Ksep g.hom)).comp
        (Localization.localRingHom
          (sepClosurePointedAlgebraKernel R p Ksep A.obj)
          (sepClosurePointedAlgebraKernel R p Ksep B.obj)
          (etaleSepClosureNeighborhoodHom R p Ksep f)
          (sepClosurePointedAlgebraKernel_comap R p Ksep f.hom)) := sorry

/-- The transition maps in the localized neighborhood diagram are `Rₚ`-algebra maps. -/
private theorem etaleSepClosureNeighborhoodLocalization_map_commutes
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    {A B : EtaleSepClosureNeighborhoodCategory R p Ksep} (f : A ⟶ B) :
    (Localization.localRingHom
        (sepClosurePointedAlgebraKernel R p Ksep A.obj)
        (sepClosurePointedAlgebraKernel R p Ksep B.obj)
        (etaleSepClosureNeighborhoodHom R p Ksep f)
        (sepClosurePointedAlgebraKernel_comap R p Ksep f.hom)).comp
      (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A) =
        etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep B := sorry

/-- The localized neighborhood `(S, q, φ) ↦ S_q` viewed as an `Rₚ`-algebra. -/
private noncomputable abbrev etaleSepClosureNeighborhoodLocalizationObject
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) :
    CommAlgCat (Localization.AtPrime p) :=
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) :=
    RingHom.toAlgebra (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
  CommAlgCat.of (Localization.AtPrime p)
    (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj))

/-- The induced `Rₚ`-algebra map on localized neighborhoods. -/
private noncomputable abbrev etaleSepClosureNeighborhoodLocalizationMorphism
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep]
    {A B : EtaleSepClosureNeighborhoodCategory R p Ksep} (f : A ⟶ B) :
    etaleSepClosureNeighborhoodLocalizationObject R p Ksep A ⟶
      etaleSepClosureNeighborhoodLocalizationObject R p Ksep B :=
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) :=
    RingHom.toAlgebra (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep B.obj)) :=
    RingHom.toAlgebra (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep B)
  CommAlgCat.ofHom <|
    { toRingHom :=
        Localization.localRingHom
          (sepClosurePointedAlgebraKernel R p Ksep A.obj)
          (sepClosurePointedAlgebraKernel R p Ksep B.obj)
          (etaleSepClosureNeighborhoodHom R p Ksep f)
        (sepClosurePointedAlgebraKernel_comap R p Ksep f.hom)
      commutes' := by
        intro x
        exact congrArg
          (fun g :
            Localization.AtPrime p →+*
              Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep B.obj) ↦ g x)
          (etaleSepClosureNeighborhoodLocalization_map_commutes R p Ksep f) }

/-- The localized neighborhood diagram sending `(S, q, φ)` to the `Rₚ`-algebra `S_q`. -/
noncomputable def etaleSepClosureNeighborhoodLocalizationDiagram
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (Ksep : Type u) [Field Ksep] [Algebra R Ksep] [Algebra p.ResidueField Ksep]
    [IsScalarTower R p.ResidueField Ksep] :
    EtaleSepClosureNeighborhoodCategory R p Ksep ⥤ CommAlgCat (Localization.AtPrime p) where
  obj A := etaleSepClosureNeighborhoodLocalizationObject R p Ksep A
  map f := etaleSepClosureNeighborhoodLocalizationMorphism R p Ksep f
  map_id A := by
    apply CommAlgCat.hom_ext
    exact DFunLike.ext _ _ fun x ↦
      congrArg
        (fun g :
          Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj) →+*
            Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj) ↦ g x)
        (sepClosurePointedAlgebraLocalization_map_id R p Ksep A)
  map_comp {A B C} f g := by
    apply CommAlgCat.hom_ext
    exact DFunLike.ext _ _ fun x ↦
      congrArg
        (fun h :
          Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj) →+*
            Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep C.obj) ↦ h x)
        (sepClosurePointedAlgebraLocalization_map_comp R p Ksep f g)

/-- The canonical equivalence between the residue field of the local ring `A` and the residue
field defined using its maximal ideal. -/
private noncomputable abbrev maximalIdealResidueFieldEquiv
    (A : Type*) [CommRing A] [IsLocalRing A] :
    (maximalIdeal A).ResidueField ≃+* ResidueField A :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField A) (maximalIdeal A).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))).symm

/-- The canonical equivalence carries residue classes of elements to their local-ring residues. -/
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

/-- For local maps, the maximal-ideal residue-field map agrees with the local-ring
residue-field map through the canonical equivalences. -/
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

/-- For a prime localization, the residue field of the maximal ideal is the prime residue field. -/
private noncomputable abbrev primeLocalizationMaximalResidueFieldEquiv
    {A : Type*} [CommRing A] (I : Ideal A) [I.IsPrime] :
    (maximalIdeal (Localization.AtPrime I)).ResidueField ≃+* I.ResidueField := by
  change (maximalIdeal (Localization.AtPrime I)).ResidueField ≃+*
      IsLocalRing.ResidueField (Localization.AtPrime I)
  exact maximalIdealResidueFieldEquiv (Localization.AtPrime I)

/-- For a prime localization, the local-ring residue field is canonically the prime residue
field. -/
private noncomputable abbrev primeLocalizationResidueFieldEquiv
    {A : Type*} [CommRing A] (I : Ideal A) [I.IsPrime] :
    ResidueField (Localization.AtPrime I) ≃+* I.ResidueField :=
  (maximalIdealResidueFieldEquiv (Localization.AtPrime I)).symm.trans
    (primeLocalizationMaximalResidueFieldEquiv I)

/-- The canonical map from the residue field of `Rₚ` to the chosen separable closure `Ksep`. -/
private noncomputable abbrev localizationAtPrimeMaximalResidueFieldToSepClosure
    (p : Ideal R) [p.IsPrime] (Ksep : Type u) [Field Ksep] [Algebra R Ksep]
    [Algebra p.ResidueField Ksep] :
    (maximalIdeal (Localization.AtPrime p)).ResidueField →+* Ksep :=
  (algebraMap p.ResidueField Ksep).comp
    (primeLocalizationMaximalResidueFieldEquiv p).toRingHom

/-- The canonical map from the local-ring residue field of `Rₚ` to the chosen separable closure
`Ksep`. -/
private noncomputable abbrev localizationAtPrimeResidueFieldToSepClosure
    (p : Ideal R) [p.IsPrime] (Ksep : Type u) [Field Ksep] [Algebra R Ksep]
    [Algebra p.ResidueField Ksep] :
    ResidueField (Localization.AtPrime p) →+* Ksep :=
  (algebraMap p.ResidueField Ksep).comp
    (primeLocalizationResidueFieldEquiv p).toRingHom

/-- The canonical map from `ResidueField (Rₚ)` restricts along the maximal-ideal residue-field
equivalence to the canonical map from `κ(p)`. -/
private theorem localizationAtPrimeResidueFieldToSepClosure_comp_maximalIdealResidueFieldEquiv
    (p : Ideal R) [p.IsPrime] (Ksep : Type u) [Field Ksep] [Algebra R Ksep]
    [Algebra p.ResidueField Ksep] :
    (localizationAtPrimeResidueFieldToSepClosure p Ksep).comp
        (maximalIdealResidueFieldEquiv (Localization.AtPrime p)).toRingHom =
      localizationAtPrimeMaximalResidueFieldToSepClosure p Ksep := by
  ext x
  simp [localizationAtPrimeResidueFieldToSepClosure,
    localizationAtPrimeMaximalResidueFieldToSepClosure, primeLocalizationResidueFieldEquiv]

/-- The canonical map from the residue field `κ(q)` of the chosen prime of an object over `Ksep`
to `Ksep`. -/
private theorem sepClosurePointedAlgebraKernel_le_ker
    (A : SepClosurePointedAlgebraCategory R Ksep) :
    sepClosurePointedAlgebraKernel R p Ksep A ≤
      RingHom.ker (sepClosurePointedAlgebraToSepClosure R p Ksep A) := by
  intro x hx
  exact hx

/-- Elements outside the kernel map to units in the field `Ksep`. -/
private theorem sepClosurePointedAlgebraKernelPrimeCompl_toSepClosure_units
    (A : SepClosurePointedAlgebraCategory R Ksep) :
    (sepClosurePointedAlgebraKernel R p Ksep A).primeCompl ≤
      (IsUnit.submonoid Ksep).comap (sepClosurePointedAlgebraToSepClosure R p Ksep A) := by
  intro x hx
  exact isUnit_iff_ne_zero.mpr fun hx0 ↦ hx <| by
    simpa [sepClosurePointedAlgebraKernel] using hx0

/-- The residue-field map `κ(q) → Ksep` induced by the structural map `S → Ksep`. -/
private noncomputable abbrev sepClosurePointedAlgebraKernelResidueFieldToSepClosure
    (A : SepClosurePointedAlgebraCategory R Ksep) :
    (sepClosurePointedAlgebraKernel R p Ksep A).ResidueField →+* Ksep :=
  Ideal.ResidueField.lift
    (sepClosurePointedAlgebraKernel R p Ksep A)
    (sepClosurePointedAlgebraToSepClosure R p Ksep A)
    (sepClosurePointedAlgebraKernel_le_ker p A)
    (sepClosurePointedAlgebraKernelPrimeCompl_toSepClosure_units p A)

/-- The localization `S_q` of an étale neighborhood is étale over `Rₚ`. -/
private theorem etaleSepClosureNeighborhoodLocalization_etale
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) :
    let _ : Algebra (Localization.AtPrime p)
        (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) :=
      RingHom.toAlgebra (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
    Algebra.Etale (Localization.AtPrime p)
      (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) := by
  sorry

/-- The maximal ideal of `S_q` lies over the maximal ideal of `Rₚ`. -/
private theorem etaleSepClosureNeighborhoodLocalization_maximalIdeal_under
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) :
    let _ : Algebra (Localization.AtPrime p)
        (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) :=
      RingHom.toAlgebra (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
    (maximalIdeal (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj))).under
        (Localization.AtPrime p) =
      maximalIdeal (Localization.AtPrime p) := by
  sorry

/-- The residue-field map from `κ(maximalIdeal S_q)` to `Ksep`. -/
private noncomputable abbrev etaleSepClosureNeighborhoodLocalizationResidueFieldToSepClosure
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) :
    (maximalIdeal (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj))).ResidueField →+*
      Ksep :=
  (sepClosurePointedAlgebraKernelResidueFieldToSepClosure p A.obj).comp
    (primeLocalizationMaximalResidueFieldEquiv
      (sepClosurePointedAlgebraKernel R p Ksep A.obj)).toRingHom

/-- The localized residue-field map is compatible with the canonical map from `κ(p)` to `Ksep`. -/
private theorem etaleSepClosureNeighborhoodLocalization_residueFieldToSepClosure_comp
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) :
    let _ : Algebra (maximalIdeal (Localization.AtPrime p)).ResidueField Ksep :=
      RingHom.toAlgebra (localizationAtPrimeMaximalResidueFieldToSepClosure p Ksep)
    (etaleSepClosureNeighborhoodLocalizationResidueFieldToSepClosure p A).comp
        (Ideal.ResidueField.map
          (maximalIdeal (Localization.AtPrime p))
          (maximalIdeal (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)))
          (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
          (etaleSepClosureNeighborhoodLocalization_maximalIdeal_under p A).symm) =
      (algebraMap (maximalIdeal (Localization.AtPrime p)).ResidueField Ksep).comp
        (Ideal.ResidueField.map
          (maximalIdeal (Localization.AtPrime p))
          (maximalIdeal (Localization.AtPrime p))
          (algebraMap (Localization.AtPrime p) (Localization.AtPrime p))
          (IsLocalRing.maximalIdeal_comap
            (algebraMap (Localization.AtPrime p) (Localization.AtPrime p))).symm) := by
  sorry

section StrictHenselizationTarget

/-- The canonical residue-field identification of a chosen strict henselization, expressed on the
maximal-ideal residue field for use with the source lifting theorem. -/
private noncomputable abbrev strictHenselizationMaximalIdealResidueFieldEquiv
    (Rsh : Type u) [CommRing Rsh] [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (ι : ResidueField Rsh ≃+* Ksep) :
    (maximalIdeal Rsh).ResidueField ≃+* Ksep :=
  (maximalIdealResidueFieldEquiv Rsh).trans ι

/-- The local-ring residue-field compatibility rewrites to the maximal-ideal residue-field form
required by `Lemma_10_155_9`. -/
private theorem strictHenselizationMaximalIdealResidueFieldCompat
    (Rsh : Type u) [CommRing Rsh] [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (ι : ResidueField Rsh ≃+* Ksep)
    (hι :
      ι.toRingHom.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rsh)) =
        localizationAtPrimeResidueFieldToSepClosure p Ksep) :
    (strictHenselizationMaximalIdealResidueFieldEquiv p Rsh ι).toRingHom.comp
        (Ideal.ResidueField.map (maximalIdeal (Localization.AtPrime p)) (maximalIdeal Rsh)
          (algebraMap (Localization.AtPrime p) Rsh)
          (IsLocalRing.maximalIdeal_comap (algebraMap (Localization.AtPrime p) Rsh)).symm) =
      localizationAtPrimeMaximalResidueFieldToSepClosure p Ksep := by
  calc
    (strictHenselizationMaximalIdealResidueFieldEquiv p Rsh ι).toRingHom.comp
        (Ideal.ResidueField.map (maximalIdeal (Localization.AtPrime p)) (maximalIdeal Rsh)
          (algebraMap (Localization.AtPrime p) Rsh)
          (IsLocalRing.maximalIdeal_comap (algebraMap (Localization.AtPrime p) Rsh)).symm)
      = ι.toRingHom.comp
          ((ResidueField.map (algebraMap (Localization.AtPrime p) Rsh)).comp
            (maximalIdealResidueFieldEquiv (Localization.AtPrime p)).toRingHom) := by
          change
            (ι.toRingHom.comp (maximalIdealResidueFieldEquiv Rsh).toRingHom).comp
                (Ideal.ResidueField.map (maximalIdeal (Localization.AtPrime p)) (maximalIdeal Rsh)
                  (algebraMap (Localization.AtPrime p) Rsh)
                  (IsLocalRing.maximalIdeal_comap (algebraMap (Localization.AtPrime p) Rsh)).symm) =
              _
          rw [RingHom.comp_assoc]
          rw [maximalIdealResidueFieldEquiv_comp_residueFieldMap
            (algebraMap (Localization.AtPrime p) Rsh)]
    _ = (ι.toRingHom.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rsh))).comp
          (maximalIdealResidueFieldEquiv (Localization.AtPrime p)).toRingHom := by
          rw [RingHom.comp_assoc]
    _ = (localizationAtPrimeResidueFieldToSepClosure p Ksep).comp
          (maximalIdealResidueFieldEquiv (Localization.AtPrime p)).toRingHom := by
          rw [hι]
    _ = localizationAtPrimeMaximalResidueFieldToSepClosure p Ksep := by
          rw [localizationAtPrimeResidueFieldToSepClosure_comp_maximalIdealResidueFieldEquiv]

/-- The localized neighborhood `S_q` admits a unique `Rₚ`-algebra map to a chosen strict
henselization of `Rₚ` compatible with the chosen residue-field map to `Ksep`. -/
private theorem etaleSepClosureNeighborhoodLocalization_existsUnique_toStrictHenselization
    (Rsh : Type u) [CommRing Rsh] [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (ι : ResidueField Rsh ≃+* Ksep)
    (hι :
      ι.toRingHom.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rsh)) =
        localizationAtPrimeResidueFieldToSepClosure p Ksep)
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) :
    let _ : Algebra (Localization.AtPrime p)
        (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) :=
      RingHom.toAlgebra (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
    ∃! f :
        Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj) →ₐ[Localization.AtPrime p] Rsh,
      ∃ hfq :
          maximalIdeal (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) =
            Ideal.comap (f : Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj) →+* Rsh)
              (maximalIdeal Rsh),
        (strictHenselizationMaximalIdealResidueFieldEquiv p Rsh ι).toRingHom.comp
            (Ideal.ResidueField.map
              (maximalIdeal (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)))
              (maximalIdeal Rsh)
              (f : Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj) →+* Rsh)
              hfq) =
          etaleSepClosureNeighborhoodLocalizationResidueFieldToSepClosure p A := by
  let _ : Algebra (maximalIdeal (Localization.AtPrime p)).ResidueField Ksep :=
    RingHom.toAlgebra (localizationAtPrimeMaximalResidueFieldToSepClosure p Ksep)
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) :=
    RingHom.toAlgebra (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
  let _ : Algebra.Etale (Localization.AtPrime p)
      (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) :=
    etaleSepClosureNeighborhoodLocalization_etale p A
  exact
    existsUnique_algHom_to_strictHenselization_of_etale_of_residueFieldMap
      (maximalIdeal (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)))
      (etaleSepClosureNeighborhoodLocalization_maximalIdeal_under p A)
      (strictHenselizationMaximalIdealResidueFieldEquiv p Rsh ι)
      (strictHenselizationMaximalIdealResidueFieldCompat p Rsh ι hι)
      (etaleSepClosureNeighborhoodLocalizationResidueFieldToSepClosure p A)
      (etaleSepClosureNeighborhoodLocalization_residueFieldToSepClosure_comp p A)

/-- The canonical morphism from the localized neighborhood `S_q` to a chosen strict
henselization `(Rₚ)^sh`. -/
private noncomputable abbrev etaleSepClosureNeighborhoodLocalizationToStrictHenselizationHom
    (Rsh : Type u) [CommRing Rsh] [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (ι : ResidueField Rsh ≃+* Ksep)
    (hι :
      ι.toRingHom.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rsh)) =
        localizationAtPrimeResidueFieldToSepClosure p Ksep)
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) :
    (etaleSepClosureNeighborhoodLocalizationDiagram R p Ksep).obj A ⟶
      CommAlgCat.of (Localization.AtPrime p) Rsh :=
  let _ : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)) :=
    RingHom.toAlgebra (etaleSepClosureNeighborhoodLocalizationAlgebraMap R p Ksep A)
  CommAlgCat.ofHom <|
    Classical.choose <|
      etaleSepClosureNeighborhoodLocalization_existsUnique_toStrictHenselization p Rsh ι hι A

/-- The chosen strict henselization `(Rₚ)^sh`, viewed as an `R`-algebra by restriction of
scalars. -/
private noncomputable abbrev etaleSepClosureNeighborhoodSourceStrictHenselizationPoint
    (Rsh : Type u) [CommRing Rsh] [Algebra (Localization.AtPrime p) Rsh] :
    CommAlgCat R :=
  let _ : Algebra R Rsh :=
    RingHom.toAlgebra <|
      (algebraMap (Localization.AtPrime p) Rsh).comp (algebraMap R (Localization.AtPrime p))
  CommAlgCat.of R Rsh

/-- The canonical morphism from the source neighborhood `S` to a chosen strict henselization
`(Rₚ)^sh`, obtained by composing `S → S_q` with the canonical localized map `S_q → (Rₚ)^sh`. -/
private noncomputable def etaleSepClosureNeighborhoodSourceToStrictHenselizationHom
    (Rsh : Type u) [CommRing Rsh] [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (ι : ResidueField Rsh ≃+* Ksep)
    (hι :
      ι.toRingHom.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rsh)) =
        localizationAtPrimeResidueFieldToSepClosure p Ksep)
    (A : EtaleSepClosureNeighborhoodCategory R p Ksep) :
    (etaleSepClosureNeighborhoodSourceDiagram R p Ksep).obj A ⟶
      etaleSepClosureNeighborhoodSourceStrictHenselizationPoint p Rsh :=
  let _ : Algebra R Rsh :=
    RingHom.toAlgebra <|
      (algebraMap (Localization.AtPrime p) Rsh).comp (algebraMap R (Localization.AtPrime p))
  CommAlgCat.ofHom <|
    { toRingHom :=
        (etaleSepClosureNeighborhoodLocalizationToStrictHenselizationHom
          p Rsh ι hι A).hom.toRingHom.comp
          (algebraMap A.obj.left (Localization.AtPrime (sepClosurePointedAlgebraKernel R p Ksep A.obj)))
      commutes' := by
        sorry }

/-- The canonical cocone from the localized neighborhood diagram to a chosen strict
henselization `(Rₚ)^sh`. -/
noncomputable def etaleSepClosureNeighborhoodLocalizationCoconeToStrictHenselization
    (Rsh : Type u) [CommRing Rsh] [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (ι : ResidueField Rsh ≃+* Ksep)
    (hι :
      ι.toRingHom.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rsh)) =
        localizationAtPrimeResidueFieldToSepClosure p Ksep) :
    Cocone (etaleSepClosureNeighborhoodLocalizationDiagram R p Ksep) where
  pt := CommAlgCat.of (Localization.AtPrime p) Rsh
  ι :=
    { app := etaleSepClosureNeighborhoodLocalizationToStrictHenselizationHom
        p Rsh ι hι
      naturality := by
        intro A B f
        apply CommAlgCat.hom_ext
        sorry }

/-- The canonical cocone from the source neighborhood diagram to a chosen strict henselization
`(Rₚ)^sh`, viewed in `CommAlgCat R`. -/
noncomputable def etaleSepClosureNeighborhoodSourceCoconeToStrictHenselization
    (Rsh : Type u) [CommRing Rsh] [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (ι : ResidueField Rsh ≃+* Ksep)
    (hι :
      ι.toRingHom.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rsh)) =
        localizationAtPrimeResidueFieldToSepClosure p Ksep) :
    Cocone (etaleSepClosureNeighborhoodSourceDiagram R p Ksep) where
  pt := etaleSepClosureNeighborhoodSourceStrictHenselizationPoint p Rsh
  ι :=
    { app := etaleSepClosureNeighborhoodSourceToStrictHenselizationHom
        p Rsh ι hι
      naturality := by
        intro A B f
        apply CommAlgCat.hom_ext
        sorry }

-- Proof sketch: the triple `(R, p, κ(p) → Ksep)` gives an initial source of objects; tensor
-- products of étale neighborhoods remain étale and their induced maps to `Ksep` determine common
-- refinements; and the standard iterated fiber-product construction over `Ksep` equalizes
-- parallel morphisms.
/-- Lemma 10.155.11 (1): the category of triples `(S, q, φ)` with `R → S` étale, `q` lying over
`p`, and `φ : κ(q) → Ksep` a `κ(p)`-algebra map is filtered. -/
theorem etaleSepClosureNeighborhoodCategory_isFiltered :
    IsFiltered (EtaleSepClosureNeighborhoodCategory R p Ksep) := sorry

-- Proof sketch: localizing at the chosen prime of each triple produces the standard strict
-- étale-neighborhood diagram of `Rₚ`; the chosen map to `Ksep` fixes the residue-field comparison
-- to the strict henselization; and Lemma `10.155.9` gives the compatible maps into a chosen
-- strict henselization with residue field identified with `Ksep`.
/-- Lemma 10.155.11 (2): the canonical cocone from the source diagram `(S, q, φ) ↦ S` to a chosen
strict henselization `(Rₚ)^sh`, viewed in `CommAlgCat R`, is colimiting. -/
noncomputable def etaleSepClosureNeighborhoodSourceCoconeToStrictHenselizationIsColimit
    (Rsh : Type u) [CommRing Rsh] [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (ι : ResidueField Rsh ≃+* Ksep)
    (hι :
      ι.toRingHom.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rsh)) =
        localizationAtPrimeResidueFieldToSepClosure p Ksep) :
    IsColimit (etaleSepClosureNeighborhoodSourceCoconeToStrictHenselization p Rsh ι hι) := by
  sorry

-- Proof sketch: after replacing each object `(S, q, φ)` by its localization `S_q`, the filtered
-- diagram is the standard strict étale-neighborhood presentation of `(Rₚ)^sh`; the residue-field
-- comparison with `Ksep` fixes the canonical morphisms into the chosen strict henselization.
/-- Lemma 10.155.11 (3): the canonical cocone from the localized neighborhood diagram
`(S, q, φ) ↦ S_q` to a chosen strict henselization `(Rₚ)^sh` is colimiting. -/
noncomputable def etaleSepClosureNeighborhoodLocalizationCoconeToStrictHenselizationIsColimit
    (Rsh : Type u) [CommRing Rsh] [Algebra (Localization.AtPrime p) Rsh]
    [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
    (ι : ResidueField Rsh ≃+* Ksep)
    (hι :
      ι.toRingHom.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rsh)) =
        localizationAtPrimeResidueFieldToSepClosure p Ksep) :
    IsColimit (etaleSepClosureNeighborhoodLocalizationCoconeToStrictHenselization p Rsh ι hι) := by
  sorry

end StrictHenselizationTarget

end

/-! ### Lemma_10_155_12 (from Chap10) -/
open scoped TensorProduct
open Algebra.TensorProduct
open IsLocalRing

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

noncomputable section

section LocalRingLocalization

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- A local ring is already a localization at the complement of its maximal ideal. -/
private instance self_isLocalization_primeCompl_maximalIdeal :
    IsLocalization (maximalIdeal A).primeCompl A := sorry

end LocalRingLocalization

section

variable {R S Rsh Ssh : Type u}
variable [CommRing R] [CommRing S] [CommRing Rsh] [CommRing Ssh]
variable [Algebra R S]
variable (p : Ideal R) [p.IsPrime]
variable (q : Ideal S) [q.IsPrime] [q.LiesOver p]
variable [Algebra R Rsh] [Algebra R Ssh] [Algebra S Ssh]
variable [Algebra (Localization.AtPrime p) Rsh]
variable [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
variable [Algebra (Localization.AtPrime q) Ssh]
variable [IsStrictHenselizationOf (Localization.AtPrime q) Ssh]
variable [IsScalarTower R (Localization.AtPrime p) Rsh]
variable [IsScalarTower R (Localization.AtPrime q) Ssh]
variable [IsScalarTower R S Ssh]

local notation "Rp" => Localization.AtPrime p
local notation "Sq" => Localization.AtPrime q
local notation "TensorRing" => Rsh ⊗[R] S

noncomputable local instance localizationAtPrime_algebra :
    Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
  (Localization.localRingHom p q (algebraMap R S) (q.over_def p)).toAlgebra

local instance localizationAtPrime_isLocalHom :
    IsLocalHom (algebraMap Rp Sq) := by
  simpa [RingHom.algebraMap_toAlgebra] using
    (Localization.isLocalHom_localRingHom p q (algebraMap R S) (q.over_def p))

noncomputable local instance residueFieldSourceAlgebra :
    Algebra (ResidueField Rp) (ResidueField Rsh) :=
  (ResidueField.map (algebraMap Rp Rsh)).toAlgebra

noncomputable local instance residueFieldTargetAlgebra :
    Algebra (ResidueField Sq) (ResidueField Ssh) :=
  (ResidueField.map (algebraMap Sq Ssh)).toAlgebra

variable (φ : ResidueField Rsh →+* ResidueField Ssh)
variable (hφ :
  φ.comp (ResidueField.map (algebraMap (Localization.AtPrime p) Rsh)) =
    (ResidueField.map (algebraMap (Localization.AtPrime q) Ssh)).comp
      (ResidueField.map
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))))

/-- The canonical comparison map `Rˢʰ → Sˢʰ` induced by the compatible residue-field map `φ`. -/
noncomputable abbrev strictHenselizationComparison :
    let _ : Algebra Rp Ssh :=
      ((algebraMap Sq Ssh).comp (algebraMap Rp Sq)).toAlgebra
    let _ : IsScalarTower Rp Sq Ssh := IsScalarTower.of_algebraMap_eq' rfl
    Rsh →ₐ[Rp] Ssh := by
  letI : Algebra Rp Ssh := ((algebraMap Sq Ssh).comp (algebraMap Rp Sq)).toAlgebra
  letI : IsScalarTower Rp Sq Ssh := IsScalarTower.of_algebraMap_eq' rfl
  exact Classical.choose <|
    ExistsUnique.exists <|
      existsUnique_algHom_between_strictHenselizations_of_residueFieldMap
        (RingEquiv.refl _) rfl
        (RingEquiv.refl _) rfl
        φ hφ

/-- The canonical map `S → S_q → Sˢʰ` over `R`. -/
noncomputable def sourceToLocalizedStrictHenselization : S →ₐ[R] Ssh where
  toRingHom := (algebraMap Sq Ssh).comp (algebraMap S Sq)
  commutes' r := by
    change (algebraMap Sq Ssh) ((algebraMap S Sq) ((algebraMap R S) r)) = (algebraMap R Ssh) r
    rw [← IsScalarTower.algebraMap_apply R S Sq]
    rw [← IsScalarTower.algebraMap_apply R Sq Ssh]

/-- The canonical tensor-product comparison map `Rˢʰ ⊗[R] S → Sˢʰ`. -/
noncomputable abbrev strictHenselizationTensorMap : TensorRing →ₐ[R] Ssh := by
  letI : Algebra Rp Ssh := ((algebraMap Sq Ssh).comp (algebraMap Rp Sq)).toAlgebra
  letI : IsScalarTower Rp Sq Ssh := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R Rp Ssh := IsScalarTower.of_algebraMap_eq' <| by
    ext r
    symm
    change (algebraMap Sq Ssh)
        ((algebraMap Rp Sq) ((algebraMap R Rp) r)) = (algebraMap R Ssh) r
    rw [show (algebraMap Rp Sq) ((algebraMap R Rp) r) =
        (algebraMap S Sq) ((algebraMap R S) r) by
          simp [RingHom.algebraMap_toAlgebra, Localization.localRingHom_to_map]]
    rw [← IsScalarTower.algebraMap_apply R S Sq]
    rw [← IsScalarTower.algebraMap_apply R Sq Ssh]
  exact Algebra.TensorProduct.lift
    ((strictHenselizationComparison p q φ hφ).restrictScalars R)
    (sourceToLocalizedStrictHenselization q : S →ₐ[R] Ssh)
    (fun _ _ ↦ Commute.all _ _)

/-- The canonical prime of `Rˢʰ ⊗[R] S` cut out by the maximal ideal of `Sˢʰ`. -/
noncomputable abbrev strictHenselizationTensorPrime : Ideal TensorRing :=
  Ideal.comap (strictHenselizationTensorMap p q φ hφ).toRingHom (maximalIdeal Ssh)

local notation "tensorToSsh" =>
  strictHenselizationTensorMap p q φ hφ
local notation "tensorPrime" =>
  strictHenselizationTensorPrime p q φ hφ

/- 
Domain-style sampling:
- primary domain: strict henselization base change along `R → S`, expressed through the tensor
  product `Rˢʰ ⊗[R] S` and the comparison induced from `Rₚ → S_q`;
- sampled owner declarations of the same kind:
  `IsStrictHenselizationOf`,
  `existsUnique_algHom_between_strictHenselizations_of_residueFieldMap`,
  `Localization.localRingHom`,
  `henselizationTensorMap` / `henselizationTensorPrime` from Lemma `10.155.8`;
- best owner abstraction:
  - `source-facing`: the tensor-product prime cut out by the strict-henselization comparison and
    the resulting strict-henselization statement;
  - `core/canonical`: `IsStrictHenselizationOf`, `Localization.localRingHom`, and the strict-
    henselization comparison theorem `10.155.10`;
  - `bridge/view`: the explicit residue-field comparison `φ`, from which the comparison
    `Rˢʰ → Sˢʰ` is derived, rather than stored as primitive public algebra data;
- primitive data: the strict henselization owners on `Rₚ` and `S_q`, together with the
  compatible residue-field map `φ`;
- derived API: the comparison map `Rˢʰ → Sˢʰ`, the tensor-product map `Rˢʰ ⊗[R] S → Sˢʰ`, its
  contracted prime, and the induced localized algebra structure on `Sˢʰ`.

This file therefore treats the residue-field comparison as the source-facing compatibility input
and derives the strict-henselization comparison map from Lemma `10.155.10`, instead of accepting
an arbitrary `Rˢʰ`-algebra structure on `Sˢʰ`.
-/

local instance strictHenselizationTensorPrime_isPrime :
    Ideal.IsPrime tensorPrime :=
  Ideal.comap_isPrime _ (maximalIdeal Ssh)

noncomputable abbrev strictHenselizationTensorLocalizationToSsh :
    Localization.AtPrime tensorPrime →+* Ssh :=
  (IsLocalization.algEquiv
      (maximalIdeal Ssh).primeCompl
      (Localization.AtPrime (maximalIdeal Ssh))
      Ssh : Localization.AtPrime (maximalIdeal Ssh) →+* Ssh).comp <|
    Localization.localRingHom
      tensorPrime
      (maximalIdeal Ssh)
      (strictHenselizationTensorMap p q φ hφ).toRingHom
      rfl

/-- The canonical algebra structure on `Sˢʰ` over the localization of `Rˢʰ ⊗[R] S` at the tensor
prime cut out by `maximalIdeal Sˢʰ`, using the comparison map induced from the compatible
residue-field data `φ`. -/
noncomputable instance strictHenselizationTensorPrime_algebra :
    Algebra (Localization.AtPrime tensorPrime) Ssh :=
  RingHom.toAlgebra (strictHenselizationTensorLocalizationToSsh p q φ hφ)

omit [Algebra S Ssh] [IsScalarTower R S Ssh] in
/-- The localized tensor-product map to `Sˢʰ` agrees with the unlocalized tensor map on pure
source elements. -/
theorem strictHenselizationTensorLocalizationToSsh_algebraMap (x : TensorRing) :
    strictHenselizationTensorLocalizationToSsh p q φ hφ
        (algebraMap TensorRing (Localization.AtPrime tensorPrime) x) =
      tensorToSsh x := by
  rw [strictHenselizationTensorLocalizationToSsh, RingHom.comp_apply,
    Localization.localRingHom_to_map]
  simpa using
    (IsLocalization.algEquiv_apply
      (maximalIdeal Ssh).primeCompl
      (Localization.AtPrime (maximalIdeal Ssh))
      Ssh
      (algebraMap Ssh (Localization.AtPrime (maximalIdeal Ssh)) (tensorToSsh x)))

-- Proof sketch: the tensor-product map to `Sˢʰ` restricts on the left to the local comparison map
-- `Rˢʰ → Sˢʰ` derived from Lemma `10.155.10`. Since that map is local, the inverse image of
-- `maximalIdeal Sˢʰ` is `maximalIdeal Rˢʰ`. Unfold the tensor prime and rewrite the comap along
-- the left inclusion.
/-- The tensor-product prime lies over the maximal ideal of `Rˢʰ`. -/
theorem strictHenselizationTensorPrime_comap_includeLeft :
    Ideal.comap
        (includeLeftRingHom : Rsh →+* (Rsh ⊗[R] S))
        tensorPrime =
      maximalIdeal Rsh := sorry

-- Proof sketch: the tensor-product map to `Sˢʰ` restricts on the right to the composite
-- `S → S_q → Sˢʰ`. The maximal ideal of `Sˢʰ` therefore pulls back to the chosen prime `q` of
-- `S`. Unfold the tensor prime and rewrite the resulting comap along the right inclusion.
/-- The tensor-product prime lies over the chosen prime `q` of `S`. -/
theorem strictHenselizationTensorPrime_comap_includeRight :
    Ideal.comap
        (includeRight : S →ₐ[R] (Rsh ⊗[R] S)).toRingHom
        tensorPrime =
      q := sorry

-- Proof sketch: this is the strict-henselian analogue of Lemma `10.155.8`, now using the
-- comparison map `Rˢʰ → Sˢʰ` determined by Lemma `10.155.10` from the compatible residue-field map
-- `φ`. Replacing the henselian colimit argument by the strict-henselian one from Lemma
-- `10.155.11` identifies `Sˢʰ`, canonically viewed through the localization of its maximal ideal,
-- with the strict henselization of the localization of `Rˢʰ ⊗[R] S` at the canonical tensor prime
-- over `maximalIdeal Rˢʰ` and `q`.
/-- Lemma 10.155.12: let `Rsh` and `Ssh` be strict henselizations of `R_p` and `S_q`, and fix a
residue-field map `φ : κ(Rˢʰ) → κ(Sˢʰ)` compatible with the canonical map `κ(Rₚ) → κ(S_q)`. Then
`Sˢʰ`, canonically identified with the localization of `Sˢʰ` at its maximal ideal, is a strict
henselization of the localization of `Rˢʰ ⊗[R] S` at the canonical tensor prime cut out by the
induced strict-henselization comparison `Rˢʰ → Sˢʰ`. -/
theorem isStrictHenselizationOf_localizationAt_strictHenselizationTensorPrime :
    IsStrictHenselizationOf
      (Localization.AtPrime tensorPrime)
      Ssh := sorry

end

/-! ### Lemma_10_155_13 (from Chap10) -/
open IsLocalRing
open scoped TensorProduct

universe u

attribute [local instance] Algebra.TensorProduct.leftAlgebra Algebra.TensorProduct.rightAlgebra

noncomputable section

variable {R S : Type u}
variable {Rph Rpsh Sqh : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]
variable (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p]
local notation "Rₚ" => Localization.AtPrime p
local notation "S_q" => Localization.AtPrime q
variable [CommRing Rph] [CommRing Sqh] [CommRing Rpsh]
variable [Algebra (Localization.AtPrime p) Rph] [IsHenselizationOf (Localization.AtPrime p) Rph]
variable [Algebra (Localization.AtPrime q) Sqh]
variable [IsHenselizationOf (Localization.AtPrime q) Sqh]
variable [Algebra Rph Rpsh]
variable [IsStrictHenselizationOf Rph Rpsh]

noncomputable local instance : Algebra Rₚ S_q :=
  (Localization.localRingHom p q (algebraMap R S) (Ideal.over_def q p)).toAlgebra

local instance : IsLocalHom (algebraMap Rₚ S_q) := by
  simpa [RingHom.algebraMap_toAlgebra] using
    Localization.isLocalHom_localRingHom p q (algebraMap R S) (Ideal.over_def q p)

/-- The canonical `Rph`-algebra structure on `Sqh`, induced by the henselization comparison
`Rₚ → S_q`. -/
private noncomputable abbrev henselizationComparisonAlgebra : Algebra Rph Sqh := by
  let _ : Algebra Rₚ Sqh := Algebra.compHom Sqh (algebraMap Rₚ S_q)
  let _ : IsScalarTower Rₚ S_q Sqh := IsScalarTower.of_algebraMap_eq' rfl
  exact @henselizationMapAlgebra Rₚ Rph Sqh _ _ _ _ _ _ _ S_q _ _ _ _ _ _ _

/-- The canonical `S_q`-algebra structure on `Sqh ⊗[Rph] Rpsh`, induced from the left tensor
factor through the comparison `S_q → Sqh`. -/
private noncomputable abbrev tensorStrictHenselizationAlgebra :
    let _ : Algebra Rph Sqh := henselizationComparisonAlgebra p q
    Algebra S_q (Sqh ⊗[Rph] Rpsh) := by
  let _ : Algebra Rph Sqh := henselizationComparisonAlgebra p q
  exact Algebra.compHom (Sqh ⊗[Rph] Rpsh) (algebraMap S_q Sqh)

/-
Domain-style sampling:
- primary domain: strict henselization base change along local maps between localizations at prime
  ideals;
- sampled owner declarations of the same kind:
  `IsHenselizationOf`,
  `IsStrictHenselizationOf`,
  `henselizationMap`,
  `henselizationMapAlgebra`,
  `strictHenselization_over_henselization_isStrictHenselizationOf`,
  `exists_strictHenselization_of_henselization`,
  `isStrictHenselizationOf_localizationAt_strictHenselizationTensorPrime`;
- best owner abstraction: the source-facing statement is the chosen-`Ksep` strict-henselization
  comparison over the henselization `Sqh`; the owner `IsStrictHenselizationOf` remains the core
  abstraction, while the residue-field equivalence to the chosen common separable closure is
  source-facing bridge data that must remain visible in the main theorem;
- primitive data: the henselization owners on `Rph` and `Sqh`, the canonical induced
  henselization map `Rph → Sqh`, the strict-henselization owner of `Rpsh` over `Rph`, and the
  chosen common separable closure data;
- derived API: the file-local canonical `Rph`-algebra on `Sqh`, the resulting `S_q`-algebra on
  `Sqh ⊗[Rph] Rpsh`, and the inherited residue-field identification with `Ksep`.

Source/core/bridge triage:
- `source-facing`: the present tensor-product strict-henselization statement together with the
  chosen residue-field identification with `Ksep`;
- `core/canonical`: `IsHenselizationOf`, `IsStrictHenselizationOf`, and `henselizationMap`;
- `bridge/view`: `strictHenselization_over_henselization_isStrictHenselizationOf` from
  Remark 10.155.4, together with the chosen-`Ksep` existence theorem
  `exists_strictHenselization_of_henselization`.
-/
-- Proof sketch: use the canonical local map `Rₚ → S_q` induced by `R → S` and the assumption that
-- `κ(p) → κ(q)` is bijective. View the chosen common separable closure `Ksep` as an `S_q`
-- residue field, and suppose the chosen strict henselization `Rpsh` of `Rph` is already equipped
-- with the corresponding residue-field identification. The canonical `Rph`-algebra on `Sqh` is
-- the owner-level bridge `henselizationMapAlgebra`; base-changing `Rpsh` along `Rph → Sqh`
-- produces the strict henselization of `Sqh` built from the same `Ksep`, and hence also, via
-- Remark `10.155.4`, a strict henselization of `S_q`. This is the Lean form of the textbook
-- identity `(S_q)^sh = (S_q)^h ⊗_{(R_p)^h} (R_p)^sh` for the strict henselizations constructed
-- from a common separable closure.
section ChosenSepClosure

private lemma henselization_tensor_strictHenselization_aux
    (hκ : Function.Bijective
      (Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p)))
    {Ksep : Type u}
    [Field Ksep]
    [Algebra (ResidueField S_q) Ksep]
    [IsSepClosure (ResidueField S_q) Ksep]
    (ιR : ResidueField Rpsh ≃+* Ksep)
    (hιR :
      ιR.toRingHom.comp
          (IsLocalRing.ResidueField.map
            ((algebraMap Rph Rpsh).comp (algebraMap Rₚ Rph))) =
        (algebraMap (ResidueField S_q) Ksep).comp (ResidueField.map (algebraMap Rₚ S_q))) :
    let _ : Algebra Rph Sqh := henselizationComparisonAlgebra p q
    let _ : Algebra S_q (Sqh ⊗[Rph] Rpsh) := tensorStrictHenselizationAlgebra p q
    ∃ _ : IsStrictHenselizationOf S_q (Sqh ⊗[Rph] Rpsh),
      ∃ ιS : ResidueField (Sqh ⊗[Rph] Rpsh) ≃+* Ksep,
        ιS.toRingHom.comp
            (ResidueField.map (algebraMap S_q (Sqh ⊗[Rph] Rpsh))) =
          algebraMap (ResidueField S_q) Ksep := by
  sorry

/-- Lemma 10.155.13: assume the residue-field map `κ(p) → κ(q)` is bijective, fix a field `Ksep`
equipped with the chosen map `κ(S_q) → Ksep`, and suppose `Rpsh` is the strict henselization of
`Rph` corresponding to that same `Ksep` via the induced map `κ(Rₚ) → κ(S_q) → Ksep`. Then the
canonical tensor product `Sqh ⊗[Rph] Rpsh`, formed using the canonical comparison
`Rph → Sqh = (S_q)^h`, is a strict henselization of `S_q` whose residue field is identified with
the same chosen `Ksep`. -/
lemma henselization_tensor_strictHenselization
    (hκ : Function.Bijective
      (Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p)))
    {Ksep : Type u}
    [Field Ksep]
    [Algebra (ResidueField S_q) Ksep]
    [IsSepClosure (ResidueField S_q) Ksep]
    (ιR : ResidueField Rpsh ≃+* Ksep)
    (hιR :
      ιR.toRingHom.comp
          (IsLocalRing.ResidueField.map
            ((algebraMap Rph Rpsh).comp (algebraMap Rₚ Rph))) =
        (algebraMap (ResidueField S_q) Ksep).comp (ResidueField.map (algebraMap Rₚ S_q))) :
    let _ : Algebra Rph Sqh := henselizationComparisonAlgebra p q
    let _ : Algebra S_q (Sqh ⊗[Rph] Rpsh) := tensorStrictHenselizationAlgebra p q
    ∃ _ : IsStrictHenselizationOf S_q (Sqh ⊗[Rph] Rpsh),
      ∃ ιS : ResidueField (Sqh ⊗[Rph] Rpsh) ≃+* Ksep,
        ιS.toRingHom.comp
            (ResidueField.map (algebraMap S_q (Sqh ⊗[Rph] Rpsh))) =
          algebraMap (ResidueField S_q) Ksep := by
  exact henselization_tensor_strictHenselization_aux p q hκ ιR hιR

end ChosenSepClosure

/-- Owner-level corollary of Lemma 10.155.13, forgetting the chosen common separable closure
identification. -/
lemma henselization_tensor_strictHenselization_isStrictHenselizationOf
    (hκ : Function.Bijective
      (Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p))) :
    let _ : Algebra Rph Sqh := henselizationComparisonAlgebra p q
    let _ : Algebra S_q (Sqh ⊗[Rph] Rpsh) := tensorStrictHenselizationAlgebra p q
    IsStrictHenselizationOf S_q (Sqh ⊗[Rph] Rpsh) := by
  sorry

end
