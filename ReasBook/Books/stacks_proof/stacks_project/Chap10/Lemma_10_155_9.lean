import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_153_11
import stacks_proof.stacks_project.Chap10.Lemma_10_155_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w y

open IsLocalRing

section

variable {R : Type u} {A : Type v} {S : Type w} {Ssh : Type w} {Ksep : Type y}
variable [CommRing R] [CommRing A] [CommRing S] [CommRing Ssh] [Field Ksep]
variable [IsLocalRing R] [IsLocalRing S]
variable [Algebra R A] [Algebra R S] [Algebra S Ssh] [Algebra R Ssh]
variable [IsLocalHom (algebraMap R S)] [IsScalarTower R S Ssh]
variable [Algebra.Etale R A]
variable [IsStrictHenselizationOf S Ssh]
variable [Algebra (maximalIdeal S).ResidueField Ksep]

/- Domain-style sampling:
- primary domain: strict henselizations of local rings and residue-field-controlled lifting of
  étale points;
- sampled owner declarations of the same kind:
  `existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap`,
  `IsStrictHenselizationOf`,
  `ResidueField.map`;
- best owner abstraction:
  the present theorem is a `source-facing` strict-henselization specialization of the core
  henselian lifting owner `existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap`,
  with `IsStrictHenselizationOf S Ssh` as the owner and the chosen residue-field equivalence
  `κ(Ssh) ≃+* Ksep` only as a bridge to the auxiliary coefficient field `Ksep`;
- primitive data vs. derived API:
  primitive inputs are the strict-henselization owner on `Ssh`, the prime `q`, the contraction
  equality, the chosen residue-field identification `κ(Ssh) ≃+* Ksep`, and the two
  compatibility equations;
  the derived output is the unique `R`-algebra map `A → Ssh` inducing the chosen residue-field
  map on `q`.

Source/core/bridge triage:
- `source-facing`: the present strict-henselization lifting statement;
- `core/canonical`: `existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap` together
  with the canonical local-ring residue-field map `ResidueField.map`;
- `bridge/view`: the auxiliary field `Ksep` together with the residue-field identification
  `κ(Ssh) ≃+* Ksep`.
-/

-- Proof sketch: transport the given map `κ(q) → Ksep` across the chosen residue-field
-- identification `κ(Ssh) ≃+* Ksep` to obtain a compatible map `κ(q) → κ(Ssh)`.
-- Since a strict henselization is henselian local, apply Lemma `10.153.11` with target `Ssh`.
-- The residue-field compatibility with `Ksep` then rewrites the resulting condition exactly into
-- the desired one.
/-- Lemma 10.155.9: let `Ssh` be a strict henselization of the local ring `S`, and let `Ksep` be
a field equipped with an algebra map from `κ(S)` and identified with `κ(Ssh)` over `κ(S)`; in the
source application, `Ksep` is a chosen separable closure of `κ(S)`. If `R → A` is étale, `q` lies
over `maximalIdeal R`, and `τ : κ(q) → Ksep` is compatible with the induced map
`κ(maximalIdeal R) → κ(S) → Ksep`, then there exists a unique `R`-algebra map `f : A → Ssh`
whose inverse image of `maximalIdeal Ssh` is `q` and whose induced map on residue fields agrees
with `τ` after the chosen identification `κ(Ssh) ≃ Ksep`. -/
@[stacks 04GT]
lemma existsUnique_algHom_to_strictHenselization_of_etale_of_residueFieldMap
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = maximalIdeal R)
    (ι : (maximalIdeal Ssh).ResidueField ≃+* Ksep)
    (hι :
      ι.toRingHom.comp
          (Ideal.ResidueField.map (maximalIdeal S) (maximalIdeal Ssh) (algebraMap S Ssh)
            (IsLocalRing.maximalIdeal_comap (algebraMap S Ssh)).symm) =
        algebraMap (maximalIdeal S).ResidueField Ksep)
    (τ : q.ResidueField →+* Ksep)
    (hτ :
      τ.comp (Ideal.ResidueField.map (maximalIdeal R) q (algebraMap R A) hq.symm) =
        (algebraMap (maximalIdeal S).ResidueField Ksep).comp
          (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) (algebraMap R S)
            (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm)) :
    ∃! f : A →ₐ[R] Ssh,
      ∃ hfq : q = Ideal.comap (f : A →+* Ssh) (maximalIdeal Ssh),
        ι.toRingHom.comp (Ideal.ResidueField.map q (maximalIdeal Ssh) (f : A →+* Ssh) hfq) = τ := by
  let _ : IsLocalHom (algebraMap R Ssh) := by
    simpa [IsScalarTower.algebraMap_eq R S Ssh] using
      (show IsLocalHom ((algebraMap S Ssh).comp (algebraMap R S)) from inferInstance)
  let τSsh : q.ResidueField →+* (maximalIdeal Ssh).ResidueField :=
    ι.symm.toRingHom.comp τ
  have hqS : q.under R = (maximalIdeal S).under R := by
    rw [hq]
    simpa [Ideal.under_def] using
      (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm
  have hqSsh : q.under R = (maximalIdeal Ssh).under R := by
    rw [hq]
    simpa [Ideal.under_def] using
      (IsLocalRing.maximalIdeal_comap (algebraMap R Ssh)).symm
  have hι' :
      ι.symm.toRingHom.comp (algebraMap (maximalIdeal S).ResidueField Ksep) =
        Ideal.ResidueField.map (maximalIdeal S) (maximalIdeal Ssh) (algebraMap S Ssh)
          (IsLocalRing.maximalIdeal_comap (algebraMap S Ssh)).symm := by
    refine RingHom.ext fun x ↦ ?_
    apply ι.injective
    simpa using (congrArg (fun φ ↦ φ x) hι).symm
  have hmap :
      Ideal.ResidueField.map (q.under R) (maximalIdeal Ssh) (algebraMap R Ssh) hqSsh =
        (Ideal.ResidueField.map (maximalIdeal S) (maximalIdeal Ssh) (algebraMap S Ssh)
          (IsLocalRing.maximalIdeal_comap (algebraMap S Ssh)).symm).comp
          (Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hqS) := by
    apply Ideal.ResidueField.ringHom_ext
    ext r
    simp [IsScalarTower.algebraMap_eq R S Ssh]
  have hτS :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        (algebraMap (maximalIdeal S).ResidueField Ksep).comp
          (Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hqS) := by
    apply Ideal.ResidueField.ringHom_ext
    ext r
    have hr :=
      congrArg (fun φ ↦ φ (algebraMap R (maximalIdeal R).ResidueField r)) hτ
    simpa [hq, hqS] using hr
  have hτSsh :
      τSsh.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal Ssh) (algebraMap R Ssh) hqSsh := by
    calc
      τSsh.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl)
          = ι.symm.toRingHom.comp
              (τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl)) := by
              rfl
      _ = ι.symm.toRingHom.comp
            ((algebraMap (maximalIdeal S).ResidueField Ksep).comp
              (Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hqS)) := by
            simpa using congrArg (fun φ ↦ ι.symm.toRingHom.comp φ) hτS
      _ = (ι.symm.toRingHom.comp (algebraMap (maximalIdeal S).ResidueField Ksep)).comp
            (Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hqS) := by
            rw [RingHom.comp_assoc]
      _ = (Ideal.ResidueField.map (maximalIdeal S) (maximalIdeal Ssh) (algebraMap S Ssh)
            (IsLocalRing.maximalIdeal_comap (algebraMap S Ssh)).symm).comp
            (Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hqS) := by
            rw [hι']
      _ = Ideal.ResidueField.map (q.under R) (maximalIdeal Ssh) (algebraMap R Ssh) hqSsh := by
            rw [hmap]
  obtain ⟨f, hf, huniq⟩ :=
    existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap
      q hqSsh τSsh hτSsh
  refine ⟨f, ?_, ?_⟩
  · rcases hf with ⟨hfq, hτf⟩
    refine ⟨hfq, ?_⟩
    calc
      ι.toRingHom.comp (Ideal.ResidueField.map q (maximalIdeal Ssh) (f : A →+* Ssh) hfq)
          = ι.toRingHom.comp τSsh := by rw [hτf]
      _ = τ := by
        refine RingHom.ext fun x ↦ ?_
        simp [τSsh]
  · intro g hg
    apply huniq g
    rcases hg with ⟨hgq, hgτ⟩
    refine ⟨hgq, ?_⟩
    refine RingHom.ext fun x ↦ ?_
    apply ι.injective
    simpa [τSsh] using congrArg (fun φ ↦ φ x) hgτ

end
