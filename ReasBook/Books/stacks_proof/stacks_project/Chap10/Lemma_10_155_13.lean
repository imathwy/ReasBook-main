import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_154_1
import stacks_proof.stacks_project.Chap10.Lemma_10_155_6
import stacks_proof.stacks_project.Chap10.Lemma_10_155_10
import stacks_proof.stacks_project.Chap10.Remark_10_155_4

-- Declarations for this item will be appended below by the statement pipeline.

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
- derived API: the file-local canonical `Rph`-algebra on `Sqh`, the resulting tensor product
  `Sqh ⊗[Rph] Rpsh` viewed over `Sqh`, and the inherited residue-field identification with
  `Ksep`.

Source/core/bridge triage:
- `source-facing`: the present tensor-product strict-henselization statement together with the
  chosen residue-field identification with `Ksep`;
- `core/canonical`: `IsHenselizationOf`, `IsStrictHenselizationOf`, and `henselizationMap`;
- `bridge/view`: `strictHenselization_over_henselization_isStrictHenselizationOf` from
  Remark 10.155.4, together with the chosen-`Ksep` existence theorem
  `exists_strictHenselization_of_henselization`.
-/
-- Proof sketch: the source chooses a common separable closure of the equal residue fields and
-- identifies `(S_q)^sh` with `(S_q)^h ⊗[(Rₚ)^h] (Rₚ)^sh`. In Lean the canonical owner is the
-- strict-henselization structure over the henselization `Sqh`; Remark 10.155.4 then transports
-- this back to the base local ring `S_q`.
/-- Helper for Chap10 Lemma 10 155 13: transport the bijective residue-field comparison
`ResidueField Rₚ ≃+* ResidueField S_q` across the two henselizations to obtain the canonical
comparison `ResidueField Rph ≃+* ResidueField Sqh`. -/
private noncomputable def transportedResidueFieldEquivOfBijective
    (hκ : Function.Bijective
      (Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p))) :
    ResidueField Rph ≃+* ResidueField Sqh :=
  (IsHenselizationOf.residueFieldEquiv (R := Rₚ) (S := Rph)).symm.trans
    ((RingEquiv.ofBijective
      (Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p)) hκ).trans
      (IsHenselizationOf.residueFieldEquiv (R := S_q) (S := Sqh)))

/-- Helper for Chap10 Lemma 10 155 13: the maximal-ideal residue field of a local ring agrees
with its ordinary residue field. -/
private noncomputable abbrev maximalIdealResidueFieldEquiv
    (A : Type u) [CommRing A] [IsLocalRing A] :
    (maximalIdeal A).ResidueField ≃+* ResidueField A :=
  (RingEquiv.ofBijective
    (algebraMap (ResidueField A) (maximalIdeal A).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))).symm

/-- Helper for Chap10 Lemma 10 155 13: the maximal-ideal residue-field equivalence sends the
quotient class of `a` to the usual residue class of `a`. -/
private theorem maximalIdealResidueFieldEquiv_apply_algebraMap
    (A : Type u) [CommRing A] [IsLocalRing A] (a : A) :
    maximalIdealResidueFieldEquiv A (algebraMap A (maximalIdeal A).ResidueField a) =
      residue A a := by
  -- Proof comment: compare both sides through the inverse quotient-to-residue-field equivalence.
  rw [show algebraMap A (maximalIdeal A).ResidueField a =
      algebraMap (ResidueField A) (maximalIdeal A).ResidueField (residue A a) by rfl]
  change
    maximalIdealResidueFieldEquiv A
        ((maximalIdealResidueFieldEquiv A).symm (residue A a)) =
      residue A a
  exact (maximalIdealResidueFieldEquiv A).apply_symm_apply (residue A a)

/-- Helper for Chap10 Lemma 10 155 13: quotienting a local ring by its maximal ideal gives the
usual residue field. -/
private noncomputable abbrev maximalIdealQuotientResidueFieldEquiv
    (A : Type u) [CommRing A] [IsLocalRing A] :
    (A ⧸ maximalIdeal A) ≃+* ResidueField A :=
  (RingEquiv.ofBijective
    (algebraMap (A ⧸ maximalIdeal A) (maximalIdeal A).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))).trans
    (maximalIdealResidueFieldEquiv A)

/-- Helper for Chap10 Lemma 10 155 13: the quotient by the maximal ideal is canonically the
residue field as an algebra over the original local ring. -/
private noncomputable def maximalIdealQuotientResidueFieldAlgEquiv
    (A : Type u) [CommRing A] [IsLocalRing A] :
    (A ⧸ maximalIdeal A) ≃ₐ[A] ResidueField A := by
  refine AlgEquiv.ofRingEquiv (f := maximalIdealQuotientResidueFieldEquiv A) ?_
  intro a
  -- Proof comment: both `A`-algebra structures are induced by the quotient-residue map.
  exact maximalIdealResidueFieldEquiv_apply_algebraMap A a

/-- Helper for Chap10 Lemma 10 155 13: after transporting the residue field of `Rph` to the
residue field of `Sqh`, the chosen `Ksep`-map on `ResidueField Rpsh` agrees with the canonical
`ResidueField Sqh →+* Ksep` map on residue fields. -/
private theorem transportedResidueFieldEquivToChosenSepClosure
    (Ksep : Type u) [Field Ksep] [Algebra (ResidueField S_q) Ksep]
    (hκ : Function.Bijective
      (Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p)))
    (ιR : ResidueField Rpsh ≃+* Ksep)
    (hιR :
      ιR.toRingHom.comp
          (ResidueField.map ((algebraMap Rph Rpsh).comp (algebraMap Rₚ Rph))) =
        (algebraMap (ResidueField S_q) Ksep).comp
          (RingEquiv.ofBijective
            (Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p)) hκ).toRingHom) :
    let eRp : ResidueField Rₚ ≃+* ResidueField Rph :=
      IsHenselizationOf.residueFieldEquiv (R := Rₚ) (S := Rph)
    let eSq : ResidueField S_q ≃+* ResidueField Sqh :=
      IsHenselizationOf.residueFieldEquiv (R := S_q) (S := Sqh)
    let e : ResidueField Rph ≃+* ResidueField Sqh :=
      transportedResidueFieldEquivOfBijective (p := p) (q := q) (Rph := Rph) (Sqh := Sqh) hκ
    ((algebraMap (ResidueField S_q) Ksep).comp eSq.symm.toRingHom).comp e.toRingHom =
      ιR.toRingHom.comp (ResidueField.map (algebraMap Rph Rpsh)) := by
  let eRp : ResidueField Rₚ ≃+* ResidueField Rph :=
    IsHenselizationOf.residueFieldEquiv (R := Rₚ) (S := Rph)
  let eSq : ResidueField S_q ≃+* ResidueField Sqh :=
    IsHenselizationOf.residueFieldEquiv (R := S_q) (S := Sqh)
  let eκ : ResidueField Rₚ ≃+* ResidueField S_q :=
    RingEquiv.ofBijective
      (Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p)) hκ
  let e : ResidueField Rph ≃+* ResidueField Sqh :=
    transportedResidueFieldEquivOfBijective (p := p) (q := q) (Rph := Rph) (Sqh := Sqh) hκ
  -- Proof comment: both sides are determined on the image of `ResidueField Rₚ`, where `hιR`
  -- is exactly the required compatibility.
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := eRp.surjective x
  have hy := congrFun (congrArg DFunLike.coe hιR) y
  simpa [eRp, eSq, eκ, e, transportedResidueFieldEquivOfBijective, RingHom.comp_apply] using hy

/-- Helper for Chap10 Lemma 10 155 13: the canonical maps `Sqh →+* Ksep` and `Rpsh →+* Ksep`
agree on `Rph`, so they induce a tensor-product map. -/
private theorem tensorToChosenSepClosureCompatible
    (Ksep : Type u) [Field Ksep] [Algebra (ResidueField S_q) Ksep]
    (hκ : Function.Bijective
      (Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p)))
    (ιR : ResidueField Rpsh ≃+* Ksep)
    (hιR :
      ιR.toRingHom.comp
          (ResidueField.map ((algebraMap Rph Rpsh).comp (algebraMap Rₚ Rph))) =
        (algebraMap (ResidueField S_q) Ksep).comp
          (RingEquiv.ofBijective
            (Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p)) hκ).toRingHom) :
    let _ : Algebra Rph Sqh := henselizationComparisonAlgebra p q
    (((algebraMap (ResidueField S_q) Ksep).comp
        (IsHenselizationOf.residueFieldEquiv (R := S_q) (S := Sqh)).symm.toRingHom).comp
        (residue Sqh)).comp (algebraMap Rph Sqh) =
      (ιR.toRingHom.comp (residue Rpsh)).comp (algebraMap Rph Rpsh) := by
  let _ : Algebra Rph Sqh := henselizationComparisonAlgebra p q
  let _ : Algebra Rₚ Sqh := Algebra.compHom Sqh (algebraMap Rₚ S_q)
  let _ : IsScalarTower Rₚ S_q Sqh := IsScalarTower.of_algebraMap_eq' rfl
  have hlocalSqh : IsLocalHom (algebraMap Rph Sqh) := by
    -- Proof comment: the henselization comparison map is already known to be local.
    simpa [henselizationComparisonAlgebra, RingHom.algebraMap_toAlgebra] using
      (henselizationMap_isLocalHom (R := Rₚ) (S := S_q) (Rh := Rph) (Sh := Sqh))
  let e : ResidueField Rph ≃+* ResidueField Sqh :=
    transportedResidueFieldEquivOfBijective (p := p) (q := q) (Rph := Rph) (Sqh := Sqh) hκ
  have hbase :
      e.toRingHom.comp (ResidueField.map (algebraMap Rₚ Rph)) =
        ResidueField.map (algebraMap Rₚ Sqh) := by
    -- Proof comment: the transported residue-field equivalence is defined to interpolate the
    -- residue maps `Rₚ → Rph` and `Rₚ → Sqh`.
    apply RingHom.ext
    intro x
    simp [e, transportedResidueFieldEquivOfBijective, RingHom.comp_apply,
      IsLocalRing.ResidueField.map_comp, IsScalarTower.algebraMap_eq Rₚ S_q Sqh]
  have hresSqh :
      (residue Sqh).comp (algebraMap Rph Sqh) = e.toRingHom.comp (residue Rph) := by
    -- Proof comment: the ordinary residue map of the henselization comparison is the unique map
    -- induced by the transported residue-field comparison.
    exact
      localAlgHom_residue_comp_of_base_of_surjective
        (R := Rₚ)
        (A := Rph)
        (T := Sqh)
        (IsHenselizationOf.residueField_bijective (R := Rₚ) (S := Rph)).2
        e.toRingHom
        hbase
        (IsScalarTower.toAlgHom Rₚ Rph Sqh)
        hlocalSqh
  -- Proof comment: rewrite the left factor through the transported residue-field equivalence and
  -- then use the chosen `Rpsh`-compatibility `hιR`.
  calc
    (((algebraMap (ResidueField S_q) Ksep).comp
        (IsHenselizationOf.residueFieldEquiv (R := S_q) (S := Sqh)).symm.toRingHom).comp
        (residue Sqh)).comp (algebraMap Rph Sqh)
        = (((algebraMap (ResidueField S_q) Ksep).comp
            (IsHenselizationOf.residueFieldEquiv (R := S_q) (S := Sqh)).symm.toRingHom).comp
            e.toRingHom).comp (residue Rph) := by
            rw [RingHom.comp_assoc, hresSqh]
    _ = ((ιR.toRingHom.comp (ResidueField.map (algebraMap Rph Rpsh))).comp
          (residue Rph)) := by
          rw [transportedResidueFieldEquivToChosenSepClosure
            (p := p) (q := q) (Rph := Rph) (Rpsh := Rpsh) (Sqh := Sqh)
            (Ksep := Ksep) hκ ιR hιR]
    _ = (ιR.toRingHom.comp (residue Rpsh)).comp (algebraMap Rph Rpsh) := by
          rw [← RingHom.comp_assoc, IsLocalRing.ResidueField.map_comp_residue]

/-- Helper for Chap10 Lemma 10 155 13: after base change from `Rph` to `Sqh`, the canonical map
`Sqh → Sqh ⊗[Rph] Rpsh` is still a filtered colimit of étale maps. -/
private theorem tensorStrictHenselization_isFilteredColimitOfEtale :
    let _ : Algebra Rph Sqh := henselizationComparisonAlgebra p q
    RingHom.IsFilteredColimitOfEtale (algebraMap Sqh (Sqh ⊗[Rph] Rpsh)) := by
  let _ : Algebra Rph Sqh := henselizationComparisonAlgebra p q
  -- Proof comment: this is exactly the owner-level base-change theorem applied to
  -- `Rph → Rpsh`.
  simpa using
    RingHom.filteredColimitOfEtale_baseChange
      (R := Rph) (A := Rpsh) (R' := Sqh)
      (IsStrictHenselizationOf.isFilteredColimitOfEtale (R := Rph) (S := Rpsh))

/-- Helper for Chap10 Lemma 10 155 13: quotienting the raw tensor ring by the image of
`maximalIdeal Sqh` computes the closed fiber as `ResidueField Rpsh`. -/
private noncomputable def tensorClosedFiberRingEquivResidueField
    (hκ : Function.Bijective
      (Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p))) :
    ((Sqh ⊗[Rph] Rpsh) ⧸
        Ideal.map (algebraMap Sqh (Sqh ⊗[Rph] Rpsh)) (maximalIdeal Sqh)) ≃+*
      ResidueField Rpsh := by
  let eSqh : ResidueField Rph ≃ₐ[Rph] ResidueField Sqh :=
    transportedResidueFieldAlgEquivOfBijective
      (p := p) (q := q) (Rph := Rph) (Sqh := Sqh) hκ
  let eClosedFiber :
      ((Sqh ⊗[Rph] Rpsh) ⧸
          Ideal.map (algebraMap Sqh (Sqh ⊗[Rph] Rpsh)) (maximalIdeal Sqh)) ≃+*
        (ResidueField Sqh ⊗[Rph] Rpsh) :=
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor
        (A := Sqh) (B := Sqh ⊗[Rph] Rpsh) (I := maximalIdeal Sqh)).toRingEquiv).trans <|
      (Algebra.TensorProduct.cancelBaseChange
        (R := Rph) (S := Sqh) (T := ResidueField Sqh)
        (A := ResidueField Sqh) (B := Rpsh)).toRingEquiv
  let eBaseChange :
      (ResidueField Sqh ⊗[Rph] Rpsh) ≃+*
        (ResidueField Rph ⊗[Rph] Rpsh) :=
    (Algebra.TensorProduct.congr
      eSqh.symm (AlgEquiv.refl : Rpsh ≃ₐ[Rph] Rpsh)).toRingEquiv
  let eRpshQuotient :
      (Rpsh ⧸ Ideal.map (algebraMap Rph Rpsh) (maximalIdeal Rph)) ≃+*
        (ResidueField Rph ⊗[Rph] Rpsh) :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor
      (A := Rph) (B := Rpsh) (I := maximalIdeal Rph)).toRingEquiv
  have eResidue :
      (Rpsh ⧸ Ideal.map (algebraMap Rph Rpsh) (maximalIdeal Rph)) ≃+*
        ResidueField Rpsh := by
    -- Proof comment: the strict-henselization owner already identifies the mapped maximal ideal
    -- with `maximalIdeal Rpsh`, so the quotient is the usual residue field.
    rw [IsStrictHenselizationOf.map_maximalIdeal (R := Rph) (S := Rpsh)]
    exact maximalIdealQuotientResidueFieldEquiv Rpsh
  -- Proof comment: first compute the closed fiber over `Sqh`, then transport the left residue
  -- field back to `ResidueField Rph`, and finally collapse the strict-henselization closed fiber
  -- to the ordinary residue field of `Rpsh`.
  exact eClosedFiber.trans <| eBaseChange.trans <| eRpshQuotient.symm.trans eResidue

/-- Helper for Chap10 Lemma 10 155 13: the image of `maximalIdeal Sqh` in the raw tensor ring is
already maximal because its quotient is the field `ResidueField Rpsh`. -/
private theorem tensorClosedFiber_mapMaximalIdeal_isMaximal
    (hκ : Function.Bijective
      (Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p))) :
    (Ideal.map (algebraMap Sqh (Sqh ⊗[Rph] Rpsh)) (maximalIdeal Sqh)).IsMaximal := by
  let e :=
    tensorClosedFiberRingEquivResidueField
      (p := p) (q := q) (Rph := Rph) (Rpsh := Rpsh) (Sqh := Sqh) hκ
  -- Proof comment: maximality of an ideal is equivalent to the quotient being a field.
  exact Ideal.Quotient.maximal_of_isField _ e.toMulEquiv.isField

/-- Helper for Chap10 Lemma 10 155 13: the raw tensor ring is local because the closed-fiber
ideal is maximal and already lies in the Jacobson radical of the tensor ring. -/
private theorem tensorBaseChange_isLocalRing
    (hκ : Function.Bijective
      (Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p))) :
    IsLocalRing (Sqh ⊗[Rph] Rpsh) := by
  let T := Sqh ⊗[Rph] Rpsh
  let J : Ideal T := Ideal.map (algebraMap Sqh T) (maximalIdeal Sqh)
  have hJMax : J.IsMaximal := by
    -- Proof comment: the earlier closed-fiber computation already identifies the quotient by `J`
    -- with the field `ResidueField Rpsh`.
    simpa [J, T] using
      tensorClosedFiber_mapMaximalIdeal_isMaximal
        (p := p) (q := q) (Rph := Rph) (Rpsh := Rpsh) (Sqh := Sqh) hκ
  have hJJac : J ≤ Ring.jacobson T := by
    -- Proof comment: the closed-point ideal is the image of the Jacobson radical of the local
    -- base `Sqh`, and Jacobson radicals increase under ring maps.
    have hMapJac :
        Ideal.map (algebraMap Sqh T) (Ring.jacobson Sqh) ≤ Ring.jacobson T := by
      simpa [T] using (RingHom.map_jacobson_le (f := algebraMap Sqh T))
    simpa [J, T, IsLocalRing.ringJacobson_eq_maximalIdeal] using hMapJac
  refine IsLocalRing.of_unique_max_ideal ?_
  refine ⟨J, hJMax, ?_⟩
  intro I hI
  have hJacLeI : Ring.jacobson T ≤ I := by
    -- Proof comment: every maximal ideal contains the ring Jacobson radical.
    simpa [Ideal.jacobson_eq_self_of_isMaximal (I := I)] using
      (Ideal.ringJacobson_le_jacobson (I := I) : Ring.jacobson T ≤ I.jacobson)
  -- Proof comment: once `J` is known maximal and Jacobson-radical, every maximal ideal must be
  -- equal to it.
  exact (Ideal.IsMaximal.eq_of_le hJMax hI.ne_top (hJJac.trans hJacLeI)).symm

/-- Helper for Chap10 Lemma 10 155 13: the transported residue-field equivalence
`ResidueField Rph ≃+* ResidueField Sqh` is the actual residue-field map of the canonical
henselization comparison `Rph → Sqh`. -/
private theorem transportedResidueFieldEquivOfBijective_toRingHom
    (hκ : Function.Bijective
      (Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p))) :
    let e : ResidueField Rph ≃+* ResidueField Sqh :=
      transportedResidueFieldEquivOfBijective (p := p) (q := q) (Rph := Rph) (Sqh := Sqh) hκ
    e.toRingHom = ResidueField.map (algebraMap Rph Sqh) := by
  let _ : Algebra Rₚ Sqh := Algebra.compHom Sqh (algebraMap Rₚ S_q)
  let _ : IsScalarTower Rₚ S_q Sqh := IsScalarTower.of_algebraMap_eq' rfl
  have hlocalSqh : IsLocalHom (algebraMap Rph Sqh) := by
    -- Proof comment: the henselization comparison map is already known to be local.
    simpa [henselizationComparisonAlgebra, RingHom.algebraMap_toAlgebra] using
      (henselizationMap_isLocalHom (R := Rₚ) (S := S_q) (Rh := Rph) (Sh := Sqh))
  let e : ResidueField Rph ≃+* ResidueField Sqh :=
    transportedResidueFieldEquivOfBijective (p := p) (q := q) (Rph := Rph) (Sqh := Sqh) hκ
  have hbase :
      e.toRingHom.comp (ResidueField.map (algebraMap Rₚ Rph)) =
        ResidueField.map (algebraMap Rₚ Sqh) := by
    -- Proof comment: this is the defining interpolation property of the transported
    -- residue-field equivalence.
    apply RingHom.ext
    intro x
    simp [e, transportedResidueFieldEquivOfBijective, RingHom.comp_apply,
      IsLocalRing.ResidueField.map_comp, IsScalarTower.algebraMap_eq Rₚ S_q Sqh]
  have hresSqh :
      (residue Sqh).comp (algebraMap Rph Sqh) = e.toRingHom.comp (residue Rph) := by
    -- Proof comment: a local map out of the henselization has residue-field map determined by
    -- its values on `ResidueField Rₚ`.
    exact
      localAlgHom_residue_comp_of_base_of_surjective
        (R := Rₚ)
        (A := Rph)
        (T := Sqh)
        (IsHenselizationOf.residueField_bijective (R := Rₚ) (S := Rph)).2
        e.toRingHom
        hbase
        (IsScalarTower.toAlgHom Rₚ Rph Sqh)
        hlocalSqh
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  have hy := congrFun (congrArg DFunLike.coe hresSqh) y
  simpa [RingHom.comp_apply, IsLocalRing.ResidueField.map_residue] using hy

/-- Helper for Chap10 Lemma 10 155 13: after the residue-field comparison is normalized to the
canonical map `Rph → Sqh`, it upgrades to an `Rph`-algebra equivalence. -/
private noncomputable def transportedResidueFieldAlgEquivOfBijective
    (hκ : Function.Bijective
      (Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p))) :
    ResidueField Rph ≃ₐ[Rph] ResidueField Sqh := by
  refine AlgEquiv.ofRingEquiv
    (f := transportedResidueFieldEquivOfBijective (p := p) (q := q) (Rph := Rph) (Sqh := Sqh) hκ)
    ?_
  intro x
  -- Proof comment: the underlying ring equivalence is exactly `ResidueField.map (Rph → Sqh)`.
  change
    transportedResidueFieldEquivOfBijective
        (p := p) (q := q) (Rph := Rph) (Sqh := Sqh) hκ
        (algebraMap Rph (ResidueField Rph) x) =
      algebraMap Rph (ResidueField Sqh) x
  rw [show
      (transportedResidueFieldEquivOfBijective
        (p := p) (q := q) (Rph := Rph) (Sqh := Sqh) hκ).toRingHom =
        ResidueField.map (algebraMap Rph Sqh) by
      exact transportedResidueFieldEquivOfBijective_toRingHom
        (p := p) (q := q) (Rph := Rph) (Sqh := Sqh) hκ]
  simpa using IsLocalRing.ResidueField.map_residue (algebraMap Rph Sqh) x

/-- Helper for Chap10 Lemma 10 155 13: the chosen `Ksep`-maps on `Rpsh` and on a strict
henselization over `Sqh` agree after transporting along `ResidueField.map (algebraMap Rph Sqh)`.
-/
private theorem chosenSqhStrictHenselization_residueCompat
    (Ksep : Type u) [Field Ksep] [Algebra (ResidueField S_q) Ksep]
    (hκ : Function.Bijective
      (Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p)))
    (ιR : ResidueField Rpsh ≃+* Ksep)
    (hιR :
      ιR.toRingHom.comp
          (ResidueField.map ((algebraMap Rph Rpsh).comp (algebraMap Rₚ Rph))) =
        (algebraMap (ResidueField S_q) Ksep).comp
          (RingEquiv.ofBijective
            (Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p)) hκ).toRingHom)
    {Ssh : Type u} [CommRing Ssh] [Algebra Sqh Ssh] [IsStrictHenselizationOf Sqh Ssh]
    (ιS : ResidueField Ssh ≃+* Ksep)
    (hιS :
      ιS.toRingHom.comp
          (ResidueField.map ((algebraMap Sqh Ssh).comp (algebraMap S_q Sqh))) =
        algebraMap (ResidueField S_q) Ksep) :
    let κR : ResidueField Rph →+* Ksep :=
      ιR.toRingHom.comp (ResidueField.map (algebraMap Rph Rpsh))
    let κS : ResidueField Sqh →+* Ksep :=
      ιS.toRingHom.comp (ResidueField.map (algebraMap Sqh Ssh))
    κR = κS.comp (ResidueField.map (algebraMap Rph Sqh)) := by
  let eSq : ResidueField S_q ≃+* ResidueField Sqh :=
    IsHenselizationOf.residueFieldEquiv (R := S_q) (S := Sqh)
  let κR : ResidueField Rph →+* Ksep :=
    ιR.toRingHom.comp (ResidueField.map (algebraMap Rph Rpsh))
  let κS : ResidueField Sqh →+* Ksep :=
    ιS.toRingHom.comp (ResidueField.map (algebraMap Sqh Ssh))
  have hκScomp :
      κS.comp (ResidueField.map (algebraMap S_q Sqh)) =
        algebraMap (ResidueField S_q) Ksep := by
    -- Proof comment: rewrite the chosen `Sqh`-strict compatibility through residue-field
    -- functoriality for the composite `S_q → Sqh → Ssh`.
    simpa [κS, RingHom.comp_assoc, IsLocalRing.ResidueField.map_comp] using hιS
  have hκS :
      κS = (algebraMap (ResidueField S_q) Ksep).comp eSq.symm.toRingHom := by
    -- Proof comment: the residue field of a henselization is identified by the inverse of the
    -- canonical henselization residue-field equivalence.
    apply RingHom.ext
    intro x
    obtain ⟨y, rfl⟩ := eSq.surjective x
    have hy := congrFun (congrArg DFunLike.coe hκScomp) y
    simpa [eSq, RingHom.comp_apply] using hy
  have hκR :
      κR =
        ((algebraMap (ResidueField S_q) Ksep).comp eSq.symm.toRingHom).comp
          (ResidueField.map (algebraMap Rph Sqh)) := by
    -- Proof comment: the previously isolated transport theorem already computes the `Rpsh`
    -- residue-field map through the canonical comparison `Rph → Sqh`.
    let e : ResidueField Rph ≃+* ResidueField Sqh :=
      transportedResidueFieldEquivOfBijective (p := p) (q := q) (Rph := Rph) (Sqh := Sqh) hκ
    have he :
        e.toRingHom = ResidueField.map (algebraMap Rph Sqh) :=
      transportedResidueFieldEquivOfBijective_toRingHom
        (p := p) (q := q) (Rph := Rph) (Sqh := Sqh) hκ
    simpa [κR, e, he, RingHom.comp_assoc] using
      (transportedResidueFieldEquivToChosenSepClosure
        (p := p) (q := q) (Rph := Rph) (Rpsh := Rpsh) (Sqh := Sqh)
        (Ksep := Ksep) hκ ιR hιR).symm
  calc
    κR = ((algebraMap (ResidueField S_q) Ksep).comp eSq.symm.toRingHom).comp
          (ResidueField.map (algebraMap Rph Sqh)) := hκR
    _ = κS.comp (ResidueField.map (algebraMap Rph Sqh)) := by rw [hκS]

/-- Helper for Chap10 Lemma 10 155 13: any chosen strict henselization over `Sqh` receives the
canonical comparison map from `Rpsh`, with residue-field behavior governed by the common `Ksep`.
-/
private theorem existsUnique_strictComparisonToChosenSqhStrictHenselization
    (Ksep : Type u) [Field Ksep] [Algebra (ResidueField S_q) Ksep]
    (hκ : Function.Bijective
      (Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p)))
    (ιR : ResidueField Rpsh ≃+* Ksep)
    (hιR :
      ιR.toRingHom.comp
          (ResidueField.map ((algebraMap Rph Rpsh).comp (algebraMap Rₚ Rph))) =
        (algebraMap (ResidueField S_q) Ksep).comp
          (RingEquiv.ofBijective
            (Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p)) hκ).toRingHom)
    {Ssh : Type u} [CommRing Ssh] [Algebra Sqh Ssh] [IsStrictHenselizationOf Sqh Ssh]
    (ιS : ResidueField Ssh ≃+* Ksep)
    (hιS :
      ιS.toRingHom.comp
          (ResidueField.map ((algebraMap Sqh Ssh).comp (algebraMap S_q Sqh))) =
        algebraMap (ResidueField S_q) Ksep) :
    let _ : Algebra Rph Ssh := Algebra.compHom Ssh (algebraMap Rph Sqh)
    let _ : IsScalarTower Rph Sqh Ssh := IsScalarTower.of_algebraMap_eq' rfl
    let κR : ResidueField Rph →+* Ksep :=
      ιR.toRingHom.comp (ResidueField.map (algebraMap Rph Rpsh))
    let κS : ResidueField Sqh →+* Ksep :=
      ιS.toRingHom.comp (ResidueField.map (algebraMap Sqh Ssh))
    let _ : Algebra (ResidueField Rph) Ksep := RingHom.toAlgebra κR
    let _ : Algebra (ResidueField Sqh) Ksep := RingHom.toAlgebra κS
    ∃! f : Rpsh →ₐ[Rph] Ssh,
      IsLocalHom (f : Rpsh →+* Ssh) ∧
        (ιS.toRingHom.comp (residue Ssh)).comp (f : Rpsh →+* Ssh) =
          (ιR.toRingHom.comp (residue Rpsh)) := by
  let _ : Algebra Rph Ssh := Algebra.compHom Ssh (algebraMap Rph Sqh)
  let _ : IsScalarTower Rph Sqh Ssh := IsScalarTower.of_algebraMap_eq' rfl
  let κR : ResidueField Rph →+* Ksep :=
    ιR.toRingHom.comp (ResidueField.map (algebraMap Rph Rpsh))
  let κS : ResidueField Sqh →+* Ksep :=
    ιS.toRingHom.comp (ResidueField.map (algebraMap Sqh Ssh))
  let _ : Algebra (ResidueField Rph) Ksep := RingHom.toAlgebra κR
  let _ : Algebra (ResidueField Sqh) Ksep := RingHom.toAlgebra κS
  have hbase :
      (RingHom.id Ksep).comp (algebraMap (ResidueField Rph) Ksep) =
        (algebraMap (ResidueField Sqh) Ksep).comp
          (ResidueField.map (algebraMap Rph Sqh)) := by
    -- Proof comment: both algebra structures on `Ksep` were chosen to encode the same
    -- transported residue-field comparison.
    simpa [κR, κS, RingHom.algebraMap_toAlgebra] using
      chosenSqhStrictHenselization_residueCompat
        (p := p) (q := q) (Rph := Rph) (Rpsh := Rpsh) (Sqh := Sqh)
        (Ksep := Ksep) hκ ιR hιR ιS hιS
  simpa [κR, κS, RingHom.algebraMap_toAlgebra, RingHom.id_comp] using
    (existsUnique_algHom_between_strictHenselizations_of_residueFieldMap
      (R := Rph)
      (S := Sqh)
      (Rsh := Rpsh)
      (Ssh := Ssh)
      ιR
      rfl
      ιS
      rfl
      (RingHom.id Ksep)
      hbase)

/-- Helper for Chap10 Lemma 10 155 13: once the comparison `Rpsh ≃ₐ[Rph] Ssh` is known, the raw
tensor product `Sqh ⊗[Rph] Rpsh` identifies with `Ssh` by tensoring on the right and then
collapsing the trivial right tensor factor. -/
private noncomputable def rawTensorToChosenSqhStrictHenselizationAlgEquiv
    {Ssh : Type u} [CommRing Ssh] [Algebra Sqh Ssh]
    [Algebra Rph Ssh] [IsScalarTower Rph Sqh Ssh]
    (e : Rpsh ≃ₐ[Rph] Ssh) :
    Sqh ⊗[Rph] Rpsh ≃ₐ[Sqh] Ssh :=
  -- Proof comment: tensor the right-factor equivalence with the identity on `Sqh`, then use the
  -- standard right-unit tensor equivalence over `Rph`.
  (Algebra.TensorProduct.congr (AlgEquiv.refl : Sqh ≃ₐ[Rph] Sqh) e).trans
    (Algebra.TensorProduct.rid Rph Sqh Ssh)

/-- Chap10 Lemma 10 155 13: if the residue-field map `κ(p) → κ(q)` is bijective, `Ksep` is a
chosen separable closure of the common residue field, and `Rpsh` is the strict henselization of
`Rₚ` corresponding to that same chosen separable closure, then the canonical tensor product
`Sqh ⊗[Rph] Rpsh = (S_q)^h ⊗[(Rₚ)^h] (Rₚ)^sh`, formed using the canonical comparison
`Rph → Sqh`, is the strict henselization of `S_q` corresponding to the same chosen separable
closure `Ksep`; this is the source identity
`(S_q)^sh = (S_q)^h ⊗[(Rₚ)^h] (Rₚ)^sh` in owner form together with the chosen residue-field
identification. -/
@[stacks 0C2Z]
lemma henselization_tensor_strictHenselization
    (Ksep : Type u) [Field Ksep] [Algebra (ResidueField S_q) Ksep]
    [IsSepClosure (ResidueField S_q) Ksep]
    (hκ : Function.Bijective
      (Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p)))
    (ιR : ResidueField Rpsh ≃+* Ksep)
    (hιR :
      ιR.toRingHom.comp
          (ResidueField.map ((algebraMap Rph Rpsh).comp (algebraMap Rₚ Rph))) =
        (algebraMap (ResidueField S_q) Ksep).comp
          (RingEquiv.ofBijective
            (Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p)) hκ).toRingHom) :
    let _ : Algebra Rph Sqh := henselizationComparisonAlgebra p q
    let _ : Algebra S_q (Sqh ⊗[Rph] Rpsh) := tensorStrictHenselizationAlgebra p q
    IsStrictHenselizationOf S_q (Sqh ⊗[Rph] Rpsh) ∧
      ∃ ιS : ResidueField (Sqh ⊗[Rph] Rpsh) ≃+* Ksep,
        ιS.toRingHom.comp
            (ResidueField.map (algebraMap S_q (Sqh ⊗[Rph] Rpsh))) =
          algebraMap (ResidueField S_q) Ksep := sorry

end
