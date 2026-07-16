import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_155_2

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

section

variable {R : Type u} {Rh : Type u}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]

/-- Helper for Chap10 Remark 10 155 4: maximal ideals map correctly after composing a
henselization with a strict henselization over it. -/
private theorem map_maximalIdeal_comp_henselization
    (Rsh : Type u) [CommRing Rsh] [Algebra Rh Rsh] [IsStrictHenselizationOf Rh Rsh]
    [Algebra R Rsh] [IsScalarTower R Rh Rsh] :
    Ideal.map (algebraMap R Rsh) (maximalIdeal R) = maximalIdeal Rsh := by
  -- Proof comment: rewrite the structural map as the composite `R → Rh → Rsh`, then use the
  -- maximal-ideal identities for the henselization and the strict henselization in sequence.
  calc
    Ideal.map (algebraMap R Rsh) (maximalIdeal R)
        = Ideal.map ((algebraMap Rh Rsh).comp (algebraMap R Rh)) (maximalIdeal R) := by
            rw [IsScalarTower.algebraMap_eq R Rh Rsh]
    _ = Ideal.map (algebraMap Rh Rsh)
          (Ideal.map (algebraMap R Rh) (maximalIdeal R)) := by
            rw [Ideal.map_map]
    _ = Ideal.map (algebraMap Rh Rsh) (maximalIdeal Rh) := by
            rw [IsHenselizationOf.map_maximalIdeal (R := R) (S := Rh)]
    _ = maximalIdeal Rsh := IsStrictHenselizationOf.map_maximalIdeal (R := Rh) (S := Rsh)

/-
Domain-style sampling pass for Remark 10.155.4.

Primary domain: local commutative algebra of henselizations, strict henselizations, and residue-
field comparison maps.

Sampled owner declarations:
* `IsHenselizationOf`;
* `IsHenselizationOf.residueFieldEquiv`;
* `IsStrictHenselizationOf`;
* `exists_henselization_to_strictHenselization`.

Best owner abstraction:
* source-facing owner data already live in `IsStrictHenselizationOf`;
* the chosen residue-field identification belongs to the bridge theorem
  `exists_henselization_to_strictHenselization`;
* the fact that a strict henselization over a henselization is again a strict henselization of the
  base is derived API and should not stay bundled as primitive existential data.

Primitive data vs. derived API:
* primitive data: a strict henselization of `Rh` together with the chosen residue-field
  identification with `Ksep`;
* derived API: the resulting `R`-algebra is also a strict henselization of `R`.

Source/core/bridge triage:
* `source-facing`: `exists_strictHenselization_of_henselization`;
* `core/canonical`: `IsHenselizationOf`, `IsStrictHenselizationOf`,
  `IsHenselizationOf.residueFieldEquiv`, `exists_henselization_to_strictHenselization`;
* `bridge/view`: `strictHenselization_over_henselization_isStrictHenselizationOf`.
-/

-- Proof sketch: transport the filtered-colimit-of-étale and maximal-ideal conditions from
-- `Rh → Rsh` back along the henselization map `R → Rh`, and obtain strict henselianity of `Rsh`
-- over `R` from the same underlying local ring together with the unchanged separably closed
-- residue field.
/-- A strict henselization over a henselization is again a strict henselization of the base local
ring. This is the owner-level bridge behind Remark 10.155.4. -/
theorem strictHenselization_over_henselization_isStrictHenselizationOf
    {Rsh : Type u} [CommRing Rsh] [Algebra Rh Rsh] [Algebra R Rsh] [IsScalarTower R Rh Rsh]
    [IsStrictHenselizationOf Rh Rsh] :
    IsStrictHenselizationOf R Rsh := by
  -- Proof comment: the owner fields of a strict henselization are stable under composition with
  -- the henselization map; the only non-instance field is the maximal-ideal computation above.
  refine
    { toStrictHenselianLocalRing := inferInstance
      toIsLocalHom := ?_
      isFilteredColimitOfEtale := ?_
      map_maximalIdeal := ?_ }
  · -- Proof comment: locality follows after spelling the `R`-map as `R → Rh → Rsh`.
    rw [IsScalarTower.algebraMap_eq R Rh Rsh]
    infer_instance
  · -- Proof comment: compose the ind-etale presentations for the henselization and strict map.
    have hcomp := RingHom.isFilteredColimitOfEtale_comp (algebraMap R Rh) (algebraMap Rh Rsh)
      (IsHenselizationOf.isFilteredColimitOfEtale (R := R) (S := Rh))
      (IsStrictHenselizationOf.isFilteredColimitOfEtale (R := Rh) (S := Rsh))
    rwa [← IsScalarTower.algebraMap_eq R Rh Rsh] at hcomp
  · -- Proof comment: the composite maximal-ideal identity is isolated in the helper lemma.
    exact map_maximalIdeal_comp_henselization (R := R) (Rh := Rh) Rsh

variable {Ksep : Type u}
variable [Field Ksep] [Algebra (ResidueField R) Ksep] [IsSepClosure (ResidueField R) Ksep]

/-- Helper for Chap10 Remark 10 155 4: transport the chosen `ResidueField R`-algebra structure
on `Ksep` to a `ResidueField Rh`-algebra structure through the henselization residue-field
equivalence. -/
private noncomputable abbrev transportedResidueFieldAlgebraOfHenselization :
    Algebra (ResidueField Rh) Ksep :=
  RingHom.toAlgebra ((algebraMap (ResidueField R) Ksep).comp
    (IsHenselizationOf.residueFieldEquiv (R := R) (S := Rh)).symm.toRingHom)

/-- Helper for Chap10 Remark 10 155 4: the transported residue-field algebra still makes
`Ksep` a separable closure of `ResidueField Rh`. -/
private theorem isSepClosure_transportedResidueFieldAlgebraOfHenselization :
    letI : Algebra (ResidueField Rh) Ksep :=
      transportedResidueFieldAlgebraOfHenselization (R := R) (Rh := Rh) (Ksep := Ksep)
    IsSepClosure (ResidueField Rh) Ksep := by
  -- Proof comment: separable closedness is a property of `Ksep`; separability transports across
  -- the canonical residue-field equivalence of the henselization.
  letI : Algebra (ResidueField Rh) Ksep :=
    transportedResidueFieldAlgebraOfHenselization (R := R) (Rh := Rh) (Ksep := Ksep)
  let e : ResidueField R ≃+* ResidueField Rh :=
    IsHenselizationOf.residueFieldEquiv (R := R) (S := Rh)
  have halgebraMap :
      algebraMap (ResidueField Rh) Ksep =
        (algebraMap (ResidueField R) Ksep).comp e.symm.toRingHom :=
    rfl
  have hcomp :
      (algebraMap (ResidueField Rh) Ksep).comp e.toRingHom =
        (RingEquiv.refl Ksep).toRingHom.comp (algebraMap (ResidueField R) Ksep) := by
    -- Proof comment: this records the exact square required by separability transport.
    rw [halgebraMap]
    ext x
    simp [e]
  have hsep : Algebra.IsSeparable (ResidueField Rh) Ksep :=
    Algebra.IsSeparable.of_equiv_equiv e (RingEquiv.refl Ksep) hcomp
  exact ⟨IsSepClosure.sep_closed (ResidueField R), hsep⟩

omit [IsSepClosure (ResidueField R) Ksep] in
/-- Helper for Chap10 Remark 10 155 4: residue-field compatibility over the henselization
implies compatibility over the original local ring. -/
private theorem residueField_comp_henselization_compat
    (Rsh : Type u) [CommRing Rsh] [Algebra Rh Rsh] [IsStrictHenselizationOf Rh Rsh]
    (φ : ResidueField Rsh ≃+* Ksep)
    (hφ : φ.toRingHom.comp (ResidueField.map (algebraMap Rh Rsh)) =
        (algebraMap (ResidueField R) Ksep).comp
          (IsHenselizationOf.residueFieldEquiv (R := R) (S := Rh)).symm.toRingHom) :
    φ.toRingHom.comp
        (ResidueField.map ((algebraMap Rh Rsh).comp (algebraMap R Rh))) =
      algebraMap (ResidueField R) Ksep := by
  -- Proof comment: use functoriality of residue-field maps for the composite `R → Rh → Rsh`,
  -- then cancel the henselization residue-field equivalence against its inverse.
  let e : ResidueField R ≃+* ResidueField Rh :=
    IsHenselizationOf.residueFieldEquiv (R := R) (S := Rh)
  have he : e.toRingHom = ResidueField.map (algebraMap R Rh) := rfl
  have hmap :
      ResidueField.map ((algebraMap Rh Rsh).comp (algebraMap R Rh)) =
        (ResidueField.map (algebraMap Rh Rsh)).comp
          (ResidueField.map (algebraMap R Rh)) :=
    IsLocalRing.ResidueField.map_comp (algebraMap R Rh) (algebraMap Rh Rsh)
  calc
    φ.toRingHom.comp
        (ResidueField.map ((algebraMap Rh Rsh).comp (algebraMap R Rh)))
        = φ.toRingHom.comp
            ((ResidueField.map (algebraMap Rh Rsh)).comp
              (ResidueField.map (algebraMap R Rh))) := by
            rw [hmap]
    _ = (φ.toRingHom.comp (ResidueField.map (algebraMap Rh Rsh))).comp
          (ResidueField.map (algebraMap R Rh)) := by
          ext x
          rfl
    _ = ((algebraMap (ResidueField R) Ksep).comp e.symm.toRingHom).comp e.toRingHom := by
          rw [hφ, he]
    _ = algebraMap (ResidueField R) Ksep := by
          ext x
          simp [e]

-- Proof sketch: transport the chosen separable closure `Ksep` of `ResidueField R` across the
-- canonical residue-field isomorphism of the henselization `Rh`, then apply the strict
-- henselization existence theorem to `Rh`. The resulting `Rh`-algebra is strictly henselian with
-- residue field `Ksep`; viewed as an `R`-algebra through `R → Rh`, it is still a filtered colimit
-- of étale `R`-algebras, so Lemma `10.154.7` identifies it with the strict henselization of `R`.
/-- Chap10 Remark 10 155 4: starting from a henselization `R → Rh` and a chosen separable closure
`Ksep` of `ResidueField R`, one can construct a strict henselization over `Rh`; the resulting
`Rh`-algebra has residue field identified with `Ksep` over `ResidueField R`. The companion theorem
`strictHenselization_over_henselization_isStrictHenselizationOf` records that the same `Rh`-algebra
is also a strict henselization of `R`. -/
@[stacks 0BSL]
theorem exists_strictHenselization_of_henselization :
    ∃ (Rsh : Type u) (_ : CommRing Rsh) (_ : Algebra Rh Rsh)
      (_ : IsStrictHenselizationOf Rh Rsh) (ι : ResidueField Rsh ≃+* Ksep),
      ι.toRingHom.comp
          (ResidueField.map ((algebraMap Rh Rsh).comp (algebraMap R Rh))) =
        algebraMap (ResidueField R) Ksep := by
  -- Proof comment: apply the existing strict-henselization existence theorem over the henselian
  -- base `Rh`, after transporting the chosen separable closure across the residue-field
  -- equivalence `ResidueField R ≃+* ResidueField Rh`.
  letI : Algebra (ResidueField Rh) Ksep :=
    transportedResidueFieldAlgebraOfHenselization (R := R) (Rh := Rh) (Ksep := Ksep)
  letI : IsSepClosure (ResidueField Rh) Ksep :=
    isSepClosure_transportedResidueFieldAlgebraOfHenselization
  obtain ⟨_, _, _, _, Rsh, hRshComm, hRhRshAlg, hStrict, _, _, _, ι, hι⟩ :=
    exists_henselization_to_strictHenselization Rh Ksep
  letI : CommRing Rsh := hRshComm
  letI : Algebra Rh Rsh := hRhRshAlg
  letI : IsStrictHenselizationOf Rh Rsh := hStrict
  have hιTransported :
      ι.toRingHom.comp (ResidueField.map (algebraMap Rh Rsh)) =
        (algebraMap (ResidueField R) Ksep).comp
          (IsHenselizationOf.residueFieldEquiv (R := R) (S := Rh)).symm.toRingHom := by
    -- Proof comment: unfold only the transported algebra structure used by the existence theorem.
    simpa [transportedResidueFieldAlgebraOfHenselization] using hι
  refine ⟨Rsh, inferInstance, inferInstance, hStrict, ι, ?_⟩
  -- Proof comment: rewrite compatibility over `Rh` to the requested compatibility over `R`.
  exact residueField_comp_henselization_compat Rsh ι hιTransported

end
