import Mathlib
import StacksProject_2024.Chap10.Lemma_10_155_12
import StacksProject_2024.Chap10.Lemma_10_156_3
import StacksProject_2024.Chap10.Lemma_10_156_5

open scoped TensorProduct
open CategoryTheory MorphismProperty Limits
open Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v

namespace RingHom

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/- Domain-style sampling:
- primary domain: strict henselization comparison maps and ind-quasi-finite ring maps;
- sampled owner declarations:
  `RingHom.IsFilteredColimitOfEtale`,
  `RingHom.IsFilteredColimitOfSmooth`,
  `strictHenselizationComparison`,
  `RingHom.QuasiFinite`,
  `RingHom.toMorphismProperty`,
  `CategoryTheory.MorphismProperty.ind`;
- best owner abstraction: the filtered-colimit hypothesis should be exposed through the same
  source-facing ring-hom owner pattern as the chapter's ind-étale and ind-smooth wrappers, with
  `CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty RingHom.QuasiFinite)` kept as
  the hidden core/canonical content;
- primitive data: a ring map together with the canonical comparison maps it induces;
- derived API: the tensor-base-change map/equivalence built from those comparison maps.

Source/core/bridge triage:
- `source-facing`: the canonical map `B^sh ⊗[A^sh] C^sh → (B ⊗[A] C)^sh`;
- `core/canonical`: `strictHenselizationComparison`, `RingHom.QuasiFinite`,
  `RingHom.toMorphismProperty`, and `CategoryTheory.MorphismProperty.ind`;
- `bridge/view`: the same-universe `ULift` presentation needed only to feed the canonical owner.
-/

/-- An `R`-algebra map `f : R →+* A` is a filtered colimit of quasi-finite `R`-algebras. This
source-facing wrapper hides the same-universe `ULift` presentation of the canonical owner
`CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty RingHom.QuasiFinite)`. -/
abbrev IsFilteredColimitOfQuasiFinite (f : R →+* A) : Prop :=
  let _ : Algebra R A := f.toAlgebra
  let _ : Algebra R (ULift A) := ULift.algebra
  let _ : Algebra (ULift.{v} R) (ULift A) := ULift.algebra' R (ULift A)
  ind.{max u v, max u v, max u v + 1} (toMorphismProperty QuasiFinite)
    (CommRingCat.ofHom (algebraMap (ULift.{v} R) (ULift A)))

end

end RingHom

noncomputable section

section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C]
variable {pA : Ideal A} [pA.IsPrime]
variable {pB : Ideal B} [pB.IsPrime] [pB.LiesOver pA]
variable {pC : Ideal C} [pC.IsPrime]
variable {pD : Ideal (B ⊗[A] C)} [pD.IsPrime] [pD.LiesOver pB] [pD.LiesOver pC]
variable {Ash Bsh Csh Dsh : Type u}
variable [CommRing Ash] [CommRing Bsh] [CommRing Csh] [CommRing Dsh]
variable [Algebra (Localization.AtPrime pA) Ash]
variable [IsStrictHenselizationOf (Localization.AtPrime pA) Ash]
variable [Algebra (Localization.AtPrime pB) Bsh]
variable [IsStrictHenselizationOf (Localization.AtPrime pB) Bsh]
variable [Algebra (Localization.AtPrime pC) Csh]
variable [IsStrictHenselizationOf (Localization.AtPrime pC) Csh]
variable [Algebra (Localization.AtPrime pD) Dsh]
variable [IsStrictHenselizationOf (Localization.AtPrime pD) Dsh]

local notation "Ap" => Localization.AtPrime pA
local notation "Bp" => Localization.AtPrime pB
local notation "Cp" => Localization.AtPrime pC
local notation "Dp" => Localization.AtPrime pD

variable (pA) (pB) (pD) in
include pB in
omit [pA.IsPrime] [pB.IsPrime] [pD.IsPrime] in
private theorem pD_liesOver_pA :
    pD.LiesOver pA :=
  Ideal.LiesOver.trans pD pB pA

variable (pA) (pB) (pD) in
include pB in
omit [pA.IsPrime] [pB.IsPrime] [pD.IsPrime] in
private theorem pD_over_def_pA :
    pA = Ideal.comap (algebraMap A (B ⊗[A] C)) pD := by
  let _ : pD.LiesOver pA := Ideal.LiesOver.trans pD pB pA
  simpa [Ideal.under_def] using pD.over_def pA

private theorem pC_liesOver_pA
    (pA : Ideal A) [pA.IsPrime] (pB : Ideal B) [pB.IsPrime] [pB.LiesOver pA]
    (pC : Ideal C) [pC.IsPrime] (pD : Ideal (B ⊗[A] C)) [pD.IsPrime] [pD.LiesOver pB]
    [pD.LiesOver pC] :
    pC.LiesOver pA := by
  let _ : pD.LiesOver pA := pD_liesOver_pA pA pB pD
  exact Ideal.LiesOver.tower_bot pD pC pA

private theorem pC_over_def_pA
    (pA : Ideal A) [pA.IsPrime] (pB : Ideal B) [pB.IsPrime] [pB.LiesOver pA]
    (pC : Ideal C) [pC.IsPrime] (pD : Ideal (B ⊗[A] C)) [pD.IsPrime] [pD.LiesOver pB]
    [pD.LiesOver pC] :
    pA = Ideal.comap (algebraMap A C) pC := by
  let _ : pC.LiesOver pA := pC_liesOver_pA pA pB pC pD
  simpa [Ideal.under_def] using pC.over_def pA

noncomputable local instance : Algebra Ap Bp :=
  (Localization.localRingHom pA pB (algebraMap A B) (pB.over_def pA)).toAlgebra

private noncomputable abbrev algebraApCp
    (pA : Ideal A) [pA.IsPrime] (pB : Ideal B) [pB.IsPrime] [pB.LiesOver pA]
    (pC : Ideal C) [pC.IsPrime] (pD : Ideal (B ⊗[A] C)) [pD.IsPrime] [pD.LiesOver pB]
    [pD.LiesOver pC] :
    Algebra (Localization.AtPrime pA) (Localization.AtPrime pC) :=
  (Localization.localRingHom pA pC (algebraMap A C) (pC_over_def_pA pA pB pC pD)).toAlgebra

variable (pA) (pB) (pD) in
include pB in
private noncomputable abbrev algebraApDp :
    Algebra Ap Dp :=
  (Localization.localRingHom pA pD (algebraMap A (B ⊗[A] C))
    (pD_over_def_pA pA pB pD)).toAlgebra

private noncomputable abbrev algebraApBsh :
    Algebra Ap Bsh :=
  ((algebraMap Bp Bsh).comp (algebraMap Ap Bp)).toAlgebra

private noncomputable abbrev algebraApCsh :
    Algebra Ap Csh :=
  let _ : Algebra Ap Cp := algebraApCp pA pB pC pD
  ((algebraMap Cp Csh).comp (algebraMap Ap Cp)).toAlgebra

variable (pA) (pB) (pD) in
include pB in
private noncomputable abbrev algebraApDsh :
    let _ : Algebra Ap Dp := algebraApDp pA pB pD
    Algebra Ap Dsh :=
  let _ : Algebra Ap Dp := algebraApDp pA pB pD
  ((algebraMap Dp Dsh).comp (algebraMap Ap Dp)).toAlgebra

private noncomputable abbrev algebraBpDsh :
    Algebra Bp Dsh :=
  ((algebraMap Dp Dsh).comp (algebraMap Bp Dp)).toAlgebra

private noncomputable abbrev algebraCpDsh :
    Algebra Cp Dsh :=
  ((algebraMap Dp Dsh).comp (algebraMap Cp Dp)).toAlgebra

noncomputable local instance : Algebra Bp Dp :=
  (Localization.localRingHom pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB)).toAlgebra

noncomputable local instance : Algebra Cp Dp :=
  (Localization.localRingHom pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC)).toAlgebra

local instance : IsLocalHom (algebraMap Ap Bp) := by
  simpa [RingHom.algebraMap_toAlgebra] using
    Localization.isLocalHom_localRingHom pA pB (algebraMap A B) (pB.over_def pA)

local instance : IsLocalHom (algebraMap Bp Dp) := by
  simpa [RingHom.algebraMap_toAlgebra] using
    Localization.isLocalHom_localRingHom pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB)

local instance : IsLocalHom (algebraMap Cp Dp) := by
  simpa [RingHom.algebraMap_toAlgebra] using
    Localization.isLocalHom_localRingHom pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC)

/-- Helper for Chap10 Lemma 10 156 6: the local map from `A_p` to `C_p` is induced by
localizing `A → C` at the prime selected by `pD`. -/
private theorem localizationAtPrime_pA_pC_isLocalHom
    (pA : Ideal A) [pA.IsPrime] (pB : Ideal B) [pB.IsPrime] [pB.LiesOver pA]
    (pC : Ideal C) [pC.IsPrime] (pD : Ideal (B ⊗[A] C)) [pD.IsPrime] [pD.LiesOver pB]
    [pD.LiesOver pC] :
    let _ : Algebra (Localization.AtPrime pA) (Localization.AtPrime pC) :=
      algebraApCp pA pB pC pD
    IsLocalHom (algebraMap (Localization.AtPrime pA) (Localization.AtPrime pC)) := by
  -- The local homomorphism property is inherited from the localization map associated to
  -- `A → C` and the contraction equality supplied by the chosen tensor prime.
  let _ : Algebra (Localization.AtPrime pA) (Localization.AtPrime pC) :=
    algebraApCp pA pB pC pD
  simpa [RingHom.algebraMap_toAlgebra] using
    Localization.isLocalHom_localRingHom pA pC (algebraMap A C)
      (pC_over_def_pA pA pB pC pD)

include pB in
local instance :
    let _ : Algebra Ap Dp := algebraApDp pA pB pD
    IsLocalHom (algebraMap Ap Dp) := by
  let _ : Algebra Ap Dp := algebraApDp pA pB pD
  simpa [RingHom.algebraMap_toAlgebra] using
    Localization.isLocalHom_localRingHom pA pD (algebraMap A (B ⊗[A] C))
      (pD_over_def_pA pA pB pD)

/-- Helper for Chap10 Lemma 10 156 6: residue-field maps compose along
`A_p → B_p → D_p`. -/
private theorem residueFieldMap_comp_pA_pB_pD :
    (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB)).comp
        (Ideal.ResidueField.map pA pB (algebraMap A B) (pB.over_def pA)) =
      Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
        (pD_over_def_pA pA pB pD) := by
  -- Residue-field maps are determined by the images of elements from the source ring, where the
  -- equality is the scalar-tower identity for `A → B → B ⊗[A] C`.
  apply Ideal.ResidueField.ringHom_ext
  apply RingHom.ext
  intro x
  simpa only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap] using
    congrArg (algebraMap (B ⊗[A] C) (Ideal.ResidueField pD))
      (IsScalarTower.algebraMap_apply A B (B ⊗[A] C) x)

/-- Helper for Chap10 Lemma 10 156 6: residue-field maps compose along
`A_p → C_p → D_p`. -/
private theorem residueFieldMap_comp_pA_pC_pD :
    (Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC)).comp
        (Ideal.ResidueField.map pA pC (algebraMap A C) (pC_over_def_pA pA pB pC pD)) =
      Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
        (pD_over_def_pA pA pB pD) := by
  -- The right tensor inclusion gives the same `A`-algebra map to the tensor product, so the
  -- residue-field maps agree on the algebra generators.
  apply Ideal.ResidueField.ringHom_ext
  apply RingHom.ext
  intro x
  simpa only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap] using
    congrArg (algebraMap (B ⊗[A] C) (Ideal.ResidueField pD))
      (IsScalarTower.algebraMap_apply A C (B ⊗[A] C) x).symm

section StrictHenselizationComparisonAPI

variable {R S Rsh Ssh : Type u}
variable [CommRing R] [CommRing S] [CommRing Rsh] [CommRing Ssh]
variable [Algebra R S]
variable (p : Ideal R) [p.IsPrime]
variable (q : Ideal S) [q.IsPrime] [q.LiesOver p]
variable [Algebra (Localization.AtPrime p) Rsh]
variable [IsStrictHenselizationOf (Localization.AtPrime p) Rsh]
variable [Algebra (Localization.AtPrime q) Ssh]
variable [IsStrictHenselizationOf (Localization.AtPrime q) Ssh]
variable (φ : IsLocalRing.ResidueField Rsh →+* IsLocalRing.ResidueField Ssh)
variable (hφ :
  φ.comp (IsLocalRing.ResidueField.map (algebraMap (Localization.AtPrime p) Rsh)) =
    (IsLocalRing.ResidueField.map (algebraMap (Localization.AtPrime q) Ssh)).comp
      (IsLocalRing.ResidueField.map
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))))

/-- Helper for Chap10 Lemma 10 156 6: the chosen comparison between strict henselizations is a
local homomorphism. -/
private theorem strictHenselizationComparison_isLocalHom_here :
    let _ : Algebra (Localization.AtPrime p) Ssh :=
      ((algebraMap (Localization.AtPrime q) Ssh).comp
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))).toAlgebra
    let _ : IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q) Ssh :=
      IsScalarTower.of_algebraMap_eq' rfl
    IsLocalHom (strictHenselizationComparison p q φ hφ : Rsh →+* Ssh) := by
  -- The comparison is the chosen witness of the strict-henselization uniqueness theorem, whose
  -- witness package includes locality.
  letI : Algebra (Localization.AtPrime p) Ssh :=
    ((algebraMap (Localization.AtPrime q) Ssh).comp
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))).toAlgebra
  letI : IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q) Ssh :=
    IsScalarTower.of_algebraMap_eq' rfl
  let hexists :=
    ExistsUnique.exists <|
      existsUnique_algHom_between_strictHenselizations_of_residueFieldMap
        (RingEquiv.refl _) rfl
        (RingEquiv.refl _) rfl
        φ hφ
  let hchosen := Classical.choose_spec hexists
  rcases hchosen with ⟨hlocal, -⟩
  simpa [strictHenselizationComparison] using hlocal

/-- Helper for Chap10 Lemma 10 156 6: the chosen comparison induces the residue-field map used
to define it. -/
private theorem strictHenselizationComparison_residue_here :
    let _ : Algebra (Localization.AtPrime p) Ssh :=
      ((algebraMap (Localization.AtPrime q) Ssh).comp
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))).toAlgebra
    let _ : IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q) Ssh :=
      IsScalarTower.of_algebraMap_eq' rfl
    (IsLocalRing.residue Ssh).comp
        (strictHenselizationComparison p q φ hφ : Rsh →+* Ssh) =
      φ.comp (IsLocalRing.residue Rsh) := by
  -- The chosen witness also records the residue-field compatibility clause of the uniqueness
  -- theorem.
  letI : Algebra (Localization.AtPrime p) Ssh :=
    ((algebraMap (Localization.AtPrime q) Ssh).comp
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))).toAlgebra
  letI : IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q) Ssh :=
    IsScalarTower.of_algebraMap_eq' rfl
  let hexists :=
    ExistsUnique.exists <|
      existsUnique_algHom_between_strictHenselizations_of_residueFieldMap
        (RingEquiv.refl _) rfl
        (RingEquiv.refl _) rfl
        φ hφ
  let hchosen := Classical.choose_spec hexists
  rcases hchosen with ⟨-, hres⟩
  simpa [strictHenselizationComparison] using hres

/-- Helper for Chap10 Lemma 10 156 6: two maps out of a strict henselization agree if they are
local algebra maps and induce the residue-field map used to define the chosen comparison. -/
private theorem strictHenselizationComparison_ext_here
    (f :
      let _ : Algebra (Localization.AtPrime p) Ssh :=
        ((algebraMap (Localization.AtPrime q) Ssh).comp
          (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))).toAlgebra
      let _ : IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q) Ssh :=
        IsScalarTower.of_algebraMap_eq' rfl
      Rsh →ₐ[Localization.AtPrime p] Ssh)
    (hf :
      let _ : Algebra (Localization.AtPrime p) Ssh :=
        ((algebraMap (Localization.AtPrime q) Ssh).comp
          (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))).toAlgebra
      let _ : IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q) Ssh :=
        IsScalarTower.of_algebraMap_eq' rfl
      IsLocalHom (f : Rsh →+* Ssh))
    (hres :
      let _ : Algebra (Localization.AtPrime p) Ssh :=
        ((algebraMap (Localization.AtPrime q) Ssh).comp
          (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))).toAlgebra
      let _ : IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q) Ssh :=
        IsScalarTower.of_algebraMap_eq' rfl
      (IsLocalRing.residue Ssh).comp (f : Rsh →+* Ssh) =
        φ.comp (IsLocalRing.residue Rsh)) :
    let _ : Algebra (Localization.AtPrime p) Ssh :=
      ((algebraMap (Localization.AtPrime q) Ssh).comp
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))).toAlgebra
    let _ : IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q) Ssh :=
      IsScalarTower.of_algebraMap_eq' rfl
    (f : Rsh →+* Ssh) =
      (strictHenselizationComparison p q φ hφ : Rsh →+* Ssh) := by
  -- Reuse the same uniqueness theorem, comparing the chosen witness with the supplied local map.
  letI : Algebra (Localization.AtPrime p) Ssh :=
    ((algebraMap (Localization.AtPrime q) Ssh).comp
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))).toAlgebra
  letI : IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q) Ssh :=
    IsScalarTower.of_algebraMap_eq' rfl
  let huniq :=
    existsUnique_algHom_between_strictHenselizations_of_residueFieldMap
      (RingEquiv.refl _) rfl
      (RingEquiv.refl _) rfl
      φ hφ
  let hchosen := Classical.choose_spec (ExistsUnique.exists huniq)
  dsimp
  symm
  exact congrArg AlgHom.toRingHom <|
    ExistsUnique.unique huniq hchosen ⟨hf, by simpa using hres⟩

end StrictHenselizationComparisonAPI

/- Domain-style sampling:
- primary domain: strict henselization comparison maps attached to a common geometric point of the
  tensor product;
- sampled owner declarations:
  `strictHenselizationComparison`,
  `isStrictHenselizationOf_localizationAt_strictHenselizationTensorPrime`,
  `RingHom.QuasiFinite`,
  `CategoryTheory.MorphismProperty.ind`;
- best owner abstraction:
  - `source-facing`: the canonical map `B^sh ⊗[A^sh] C^sh → (B ⊗[A] C)^sh` attached to one common
    geometric point of `B ⊗[A] C`, presented through one common target field for the four strict
    henselization residue fields;
  - `core/canonical`: the comparison owner `strictHenselizationComparison` and the ind-quasi-
    finite owner `CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty
    RingHom.QuasiFinite)`;
  - `bridge/view`: the chosen common target field together with the residue-field
    identifications into it.
- primitive data: one common target field `Kgeo` together with compatible residue-field
  identifications from `Ash`, `Bsh`, `Csh`, and `Dsh`;
- derived API: the pairwise strict-henselization comparison maps and the tensor-base-change map.

Source/core/bridge triage:
- `source-facing`: the tensor-base-change map and its bijectivity;
- `core/canonical`: `strictHenselizationComparison`, `RingHom.QuasiFinite`,
  `RingHom.toMorphismProperty`, and `CategoryTheory.MorphismProperty.ind`;
- `bridge/view`: the chosen common target field `Kgeo`, from which the pairwise residue-field
  comparison maps are derived internally.
-/

variable {Kgeo : Type u} [Field Kgeo]
variable [Algebra (Ideal.ResidueField pD) Kgeo]

variable
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp
          (IsLocalRing.ResidueField.map (algebraMap (Localization.AtPrime pA) Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιBsh : IsLocalRing.ResidueField Bsh ≃+* Kgeo)
    (hιBsh :
      ιBsh.toRingHom.comp
          (IsLocalRing.ResidueField.map (algebraMap (Localization.AtPrime pB) Bsh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB)))
    (ιCsh : IsLocalRing.ResidueField Csh ≃+* Kgeo)
    (hιCsh :
      ιCsh.toRingHom.comp
          (IsLocalRing.ResidueField.map (algebraMap (Localization.AtPrime pC) Csh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC)))
    (ιDsh : IsLocalRing.ResidueField Dsh ≃+* Kgeo)
    (hιDsh :
      ιDsh.toRingHom.comp
          (IsLocalRing.ResidueField.map (algebraMap (Localization.AtPrime pD) Dsh)) =
        algebraMap (Ideal.ResidueField pD) Kgeo)

/-- Helper for Chap10 Lemma 10 156 6: the residue-field map determined by the chosen
identifications for `A^sh` and `B^sh` is compatible with `A_p → B_p`. -/
private theorem strictHenselizationResidueCompatibilityAB
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιBsh : IsLocalRing.ResidueField Bsh ≃+* Kgeo)
    (hιBsh :
      ιBsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Bp Bsh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB))) :
    ((ιBsh.symm.toRingHom).comp ιAsh.toRingHom).comp
        (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
      (IsLocalRing.ResidueField.map (algebraMap Bp Bsh)).comp
        (Ideal.ResidueField.map pA pB (algebraMap A B) (pB.over_def pA)) := by
  -- Compare after applying the common embedding of `ResidueField B^sh` into `Kgeo`; injectivity
  -- then reduces the claim to the residue-field tower through `pD`.
  apply RingHom.ext
  intro x
  apply ιBsh.injective
  calc
    ιBsh (((ιBsh.symm.toRingHom.comp ιAsh.toRingHom).comp
        (IsLocalRing.ResidueField.map (algebraMap Ap Ash))) x)
        = ιAsh ((IsLocalRing.ResidueField.map (algebraMap Ap Ash)) x) := by
          simp
    _ = ((algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD))) x := by
          exact congrArg (fun f : IsLocalRing.ResidueField Ap →+* Kgeo => f x) hιAsh
    _ = (((algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB))).comp
          (Ideal.ResidueField.map pA pB (algebraMap A B) (pB.over_def pA))) x := by
          exact congrArg
            (fun f : Ideal.ResidueField pA →+* Ideal.ResidueField pD =>
              ((algebraMap (Ideal.ResidueField pD) Kgeo).comp f) x)
            (residueFieldMap_comp_pA_pB_pD (pA := pA) (pB := pB) (pD := pD)).symm
    _ = ιBsh (((IsLocalRing.ResidueField.map (algebraMap Bp Bsh)).comp
          (Ideal.ResidueField.map pA pB (algebraMap A B) (pB.over_def pA))) x) := by
          exact (congrArg
            (fun f : IsLocalRing.ResidueField Bp →+* Kgeo =>
              f ((Ideal.ResidueField.map pA pB (algebraMap A B) (pB.over_def pA)) x))
            hιBsh).symm

/-- Helper for Chap10 Lemma 10 156 6: the residue-field map determined by the chosen
identifications for `A^sh` and `C^sh` is compatible with `A_p → C_p`. -/
private theorem strictHenselizationResidueCompatibilityAC
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιCsh : IsLocalRing.ResidueField Csh ≃+* Kgeo)
    (hιCsh :
      ιCsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Cp Csh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC))) :
    ((ιCsh.symm.toRingHom).comp ιAsh.toRingHom).comp
        (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
      (IsLocalRing.ResidueField.map (algebraMap Cp Csh)).comp
        (Ideal.ResidueField.map pA pC (algebraMap A C) (pC_over_def_pA pA pB pC pD)) := by
  -- The proof is the same common-target comparison as for `B`, using the tower
  -- `A_p → C_p → D_p`.
  apply RingHom.ext
  intro x
  apply ιCsh.injective
  calc
    ιCsh (((ιCsh.symm.toRingHom.comp ιAsh.toRingHom).comp
        (IsLocalRing.ResidueField.map (algebraMap Ap Ash))) x)
        = ιAsh ((IsLocalRing.ResidueField.map (algebraMap Ap Ash)) x) := by
          simp
    _ = ((algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD))) x := by
          exact congrArg (fun f : IsLocalRing.ResidueField Ap →+* Kgeo => f x) hιAsh
    _ = (((algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC))).comp
          (Ideal.ResidueField.map pA pC (algebraMap A C) (pC_over_def_pA pA pB pC pD))) x := by
          exact congrArg
            (fun f : Ideal.ResidueField pA →+* Ideal.ResidueField pD =>
              ((algebraMap (Ideal.ResidueField pD) Kgeo).comp f) x)
            (residueFieldMap_comp_pA_pC_pD (pA := pA) (pB := pB) (pC := pC)
              (pD := pD)).symm
    _ = ιCsh (((IsLocalRing.ResidueField.map (algebraMap Cp Csh)).comp
          (Ideal.ResidueField.map pA pC (algebraMap A C) (pC_over_def_pA pA pB pC pD))) x) := by
          exact (congrArg
            (fun f : IsLocalRing.ResidueField Cp →+* Kgeo =>
              f ((Ideal.ResidueField.map pA pC (algebraMap A C)
                (pC_over_def_pA pA pB pC pD)) x))
            hιCsh).symm

omit [pB.IsPrime] in
/-- Helper for Chap10 Lemma 10 156 6: the residue-field map determined by the chosen
identifications for `A^sh` and `D^sh` is compatible with `A_p → D_p`. -/
private theorem strictHenselizationResidueCompatibilityAD
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιDsh : IsLocalRing.ResidueField Dsh ≃+* Kgeo)
    (hιDsh :
      ιDsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Dp Dsh)) =
        algebraMap (Ideal.ResidueField pD) Kgeo) :
    ((ιDsh.symm.toRingHom).comp ιAsh.toRingHom).comp
        (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
      (IsLocalRing.ResidueField.map (algebraMap Dp Dsh)).comp
        (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
          (pD_over_def_pA pA pB pD)) := by
  -- Inject into the common residue field `Kgeo`; the two sides are exactly the two compatibility
  -- hypotheses for `A^sh` and `D^sh`.
  apply RingHom.ext
  intro x
  apply ιDsh.injective
  calc
    ιDsh (((ιDsh.symm.toRingHom.comp ιAsh.toRingHom).comp
        (IsLocalRing.ResidueField.map (algebraMap Ap Ash))) x)
        = ιAsh ((IsLocalRing.ResidueField.map (algebraMap Ap Ash)) x) := by
          simp
    _ = ((algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD))) x := by
          exact congrArg (fun f : IsLocalRing.ResidueField Ap →+* Kgeo => f x) hιAsh
    _ = ιDsh (((IsLocalRing.ResidueField.map (algebraMap Dp Dsh)).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD))) x) := by
          exact (congrArg
            (fun f : IsLocalRing.ResidueField Dp →+* Kgeo =>
              f ((Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
                (pD_over_def_pA pA pB pD)) x))
            hιDsh).symm

/-- Helper for Chap10 Lemma 10 156 6: the residue-field map determined by the chosen
identifications for `B^sh` and `D^sh` is compatible with `B_p → D_p`. -/
private theorem strictHenselizationResidueCompatibilityBD
    (ιBsh : IsLocalRing.ResidueField Bsh ≃+* Kgeo)
    (hιBsh :
      ιBsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Bp Bsh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB)))
    (ιDsh : IsLocalRing.ResidueField Dsh ≃+* Kgeo)
    (hιDsh :
      ιDsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Dp Dsh)) =
        algebraMap (Ideal.ResidueField pD) Kgeo) :
    ((ιDsh.symm.toRingHom).comp ιBsh.toRingHom).comp
        (IsLocalRing.ResidueField.map (algebraMap Bp Bsh)) =
      (IsLocalRing.ResidueField.map (algebraMap Dp Dsh)).comp
        (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB)) := by
  -- Apply the common target equivalence for `D^sh`; the remaining equality is the compatibility
  -- of `B^sh` with the chosen geometric point.
  apply RingHom.ext
  intro x
  apply ιDsh.injective
  calc
    ιDsh (((ιDsh.symm.toRingHom.comp ιBsh.toRingHom).comp
        (IsLocalRing.ResidueField.map (algebraMap Bp Bsh))) x)
        = ιBsh ((IsLocalRing.ResidueField.map (algebraMap Bp Bsh)) x) := by
          simp
    _ = ((algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB))) x := by
          exact congrArg (fun f : IsLocalRing.ResidueField Bp →+* Kgeo => f x) hιBsh
    _ = ιDsh (((IsLocalRing.ResidueField.map (algebraMap Dp Dsh)).comp
          (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB))) x) := by
          exact (congrArg
            (fun f : IsLocalRing.ResidueField Dp →+* Kgeo =>
              f ((Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C))
                (pD.over_def pB)) x))
            hιDsh).symm

/-- Helper for Chap10 Lemma 10 156 6: the residue-field map determined by the chosen
identifications for `C^sh` and `D^sh` is compatible with `C_p → D_p`. -/
private theorem strictHenselizationResidueCompatibilityCD
    (ιCsh : IsLocalRing.ResidueField Csh ≃+* Kgeo)
    (hιCsh :
      ιCsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Cp Csh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC)))
    (ιDsh : IsLocalRing.ResidueField Dsh ≃+* Kgeo)
    (hιDsh :
      ιDsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Dp Dsh)) =
        algebraMap (Ideal.ResidueField pD) Kgeo) :
    ((ιDsh.symm.toRingHom).comp ιCsh.toRingHom).comp
        (IsLocalRing.ResidueField.map (algebraMap Cp Csh)) =
      (IsLocalRing.ResidueField.map (algebraMap Dp Dsh)).comp
        (Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC)) := by
  -- Inject into `Kgeo` and rewrite with the compatibility hypotheses for `C^sh` and `D^sh`.
  apply RingHom.ext
  intro x
  apply ιDsh.injective
  calc
    ιDsh (((ιDsh.symm.toRingHom.comp ιCsh.toRingHom).comp
        (IsLocalRing.ResidueField.map (algebraMap Cp Csh))) x)
        = ιCsh ((IsLocalRing.ResidueField.map (algebraMap Cp Csh)) x) := by
          simp
    _ = ((algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC))) x := by
          exact congrArg (fun f : IsLocalRing.ResidueField Cp →+* Kgeo => f x) hιCsh
    _ = ιDsh (((IsLocalRing.ResidueField.map (algebraMap Dp Dsh)).comp
          (Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC))) x) := by
          exact (congrArg
            (fun f : IsLocalRing.ResidueField Dp →+* Kgeo =>
              f ((Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C))
                (pD.over_def pC)) x))
            hιDsh).symm

variable (pA) (pB) (pD) in
private noncomputable def strictHenselizationComparisonAB
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιBsh : IsLocalRing.ResidueField Bsh ≃+* Kgeo)
    (hιBsh :
      ιBsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Bp Bsh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB))) :
    Ash →+* Bsh :=
  let φAB : IsLocalRing.ResidueField Ash →+* IsLocalRing.ResidueField Bsh :=
    (ιBsh.symm.toRingHom).comp ιAsh.toRingHom
  let hφAB :
      φAB.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (IsLocalRing.ResidueField.map (algebraMap Bp Bsh)).comp
          (Ideal.ResidueField.map pA pB (algebraMap A B) (pB.over_def pA)) :=
    strictHenselizationResidueCompatibilityAB (pA := pA) (pB := pB) (pD := pD)
      ιAsh hιAsh ιBsh hιBsh
  let _ : Algebra Ap Bsh := algebraApBsh (pA := pA) (pB := pB)
  (strictHenselizationComparison pA pB φAB hφAB : Ash →ₐ[Ap] Bsh).toRingHom

variable (pA) (pB) (pC) (pD) in
private noncomputable def strictHenselizationComparisonAC
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιCsh : IsLocalRing.ResidueField Csh ≃+* Kgeo)
    (hιCsh :
      ιCsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Cp Csh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC))) :
    Ash →+* Csh :=
  let φAC : IsLocalRing.ResidueField Ash →+* IsLocalRing.ResidueField Csh :=
    (ιCsh.symm.toRingHom).comp ιAsh.toRingHom
  let hφAC :
      φAC.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (IsLocalRing.ResidueField.map (algebraMap Cp Csh)).comp
          (Ideal.ResidueField.map pA pC (algebraMap A C) (pC_over_def_pA pA pB pC pD)) :=
    strictHenselizationResidueCompatibilityAC (pA := pA) (pB := pB) (pC := pC)
      (pD := pD) ιAsh hιAsh ιCsh hιCsh
  let _ : pD.LiesOver pA := pD_liesOver_pA pA pB pD
  let _ : pC.LiesOver pA := pC_liesOver_pA pA pB pC pD
  let _ : Algebra Ap Cp := algebraApCp pA pB pC pD
  have hlocalCp : IsLocalHom (algebraMap Ap Cp) :=
    localizationAtPrime_pA_pC_isLocalHom pA pB pC pD
  let _ : IsLocalHom (algebraMap Ap Cp) := hlocalCp
  let _ : Algebra Ap Csh := ((algebraMap Cp Csh).comp (algebraMap Ap Cp)).toAlgebra
  ((show Ash →ₐ[Ap] Csh from strictHenselizationComparison pA pC φAC hφAC)).toRingHom

variable (pA) (pB) (pD) in
private noncomputable def strictHenselizationComparisonAD
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιDsh : IsLocalRing.ResidueField Dsh ≃+* Kgeo)
    (hιDsh :
      ιDsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Dp Dsh)) =
        algebraMap (Ideal.ResidueField pD) Kgeo) :
    Ash →+* Dsh :=
  let φAD : IsLocalRing.ResidueField Ash →+* IsLocalRing.ResidueField Dsh :=
    (ιDsh.symm.toRingHom).comp ιAsh.toRingHom
  let hφAD :
      φAD.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (IsLocalRing.ResidueField.map (algebraMap Dp Dsh)).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)) :=
    strictHenselizationResidueCompatibilityAD (pA := pA) (pB := pB) (pD := pD)
      ιAsh hιAsh ιDsh hιDsh
  let _ : Algebra Ap Dp := algebraApDp pA pB pD
  let _ : Algebra Ap Dsh := algebraApDsh pA pB pD
  let _ : pD.LiesOver pA := Ideal.LiesOver.trans pD pB pA
  (strictHenselizationComparison pA pD φAD hφAD : Ash →ₐ[Ap] Dsh).toRingHom

variable (pB) (pD) in
private noncomputable def strictHenselizationComparisonBD
    (ιBsh : IsLocalRing.ResidueField Bsh ≃+* Kgeo)
    (hιBsh :
      ιBsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Bp Bsh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB)))
    (ιDsh : IsLocalRing.ResidueField Dsh ≃+* Kgeo)
    (hιDsh :
      ιDsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Dp Dsh)) =
        algebraMap (Ideal.ResidueField pD) Kgeo) :
    Bsh →+* Dsh :=
  let φBD : IsLocalRing.ResidueField Bsh →+* IsLocalRing.ResidueField Dsh :=
    (ιDsh.symm.toRingHom).comp ιBsh.toRingHom
  let hφBD :
      φBD.comp (IsLocalRing.ResidueField.map (algebraMap Bp Bsh)) =
        (IsLocalRing.ResidueField.map (algebraMap Dp Dsh)).comp
          (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB)) :=
    strictHenselizationResidueCompatibilityBD (pB := pB) (pD := pD) ιBsh hιBsh ιDsh hιDsh
  let _ : Algebra Bp Dsh := algebraBpDsh
  (strictHenselizationComparison pB pD φBD hφBD : Bsh →ₐ[Bp] Dsh).toRingHom

variable (pC) (pD) in
private noncomputable def strictHenselizationComparisonCD
    (ιCsh : IsLocalRing.ResidueField Csh ≃+* Kgeo)
    (hιCsh :
      ιCsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Cp Csh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC)))
    (ιDsh : IsLocalRing.ResidueField Dsh ≃+* Kgeo)
    (hιDsh :
      ιDsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Dp Dsh)) =
        algebraMap (Ideal.ResidueField pD) Kgeo) :
    Csh →+* Dsh :=
  let φCD : IsLocalRing.ResidueField Csh →+* IsLocalRing.ResidueField Dsh :=
    (ιDsh.symm.toRingHom).comp ιCsh.toRingHom
  let hφCD :
      φCD.comp (IsLocalRing.ResidueField.map (algebraMap Cp Csh)) =
        (IsLocalRing.ResidueField.map (algebraMap Dp Dsh)).comp
          (Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC)) :=
    strictHenselizationResidueCompatibilityCD (pC := pC) (pD := pD) ιCsh hιCsh ιDsh hιDsh
  let _ : Algebra Cp Dsh := algebraCpDsh
  (strictHenselizationComparison pC pD φCD hφCD : Csh →ₐ[Cp] Dsh).toRingHom

/-- Helper for Chap10 Lemma 10 156 6: the composite comparison
`A^sh → B^sh → D^sh` is the direct comparison `A^sh → D^sh`. -/
private theorem strictHenselizationComparisonBD_comp_AB_eq_AD
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιBsh : IsLocalRing.ResidueField Bsh ≃+* Kgeo)
    (hιBsh :
      ιBsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Bp Bsh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB)))
    (ιDsh : IsLocalRing.ResidueField Dsh ≃+* Kgeo)
    (hιDsh :
      ιDsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Dp Dsh)) =
        algebraMap (Ideal.ResidueField pD) Kgeo) :
    (strictHenselizationComparisonBD pB pD ιBsh hιBsh ιDsh hιDsh).comp
        (strictHenselizationComparisonAB pA pB pD ιAsh hιAsh ιBsh hιBsh) =
      strictHenselizationComparisonAD pA pB pD ιAsh hιAsh ιDsh hιDsh := by
  -- Route correction: compare the concrete composite with the direct comparison by uniqueness
  -- over `A_p`, not by trying a broad functoriality theorem for all comparisons.
  let φAB : IsLocalRing.ResidueField Ash →+* IsLocalRing.ResidueField Bsh :=
    (ιBsh.symm.toRingHom).comp ιAsh.toRingHom
  let hφAB :
      φAB.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (IsLocalRing.ResidueField.map (algebraMap Bp Bsh)).comp
          (Ideal.ResidueField.map pA pB (algebraMap A B) (pB.over_def pA)) :=
    strictHenselizationResidueCompatibilityAB (pA := pA) (pB := pB) (pD := pD)
      ιAsh hιAsh ιBsh hιBsh
  let φBD : IsLocalRing.ResidueField Bsh →+* IsLocalRing.ResidueField Dsh :=
    (ιDsh.symm.toRingHom).comp ιBsh.toRingHom
  let hφBD :
      φBD.comp (IsLocalRing.ResidueField.map (algebraMap Bp Bsh)) =
        (IsLocalRing.ResidueField.map (algebraMap Dp Dsh)).comp
          (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB)) :=
    strictHenselizationResidueCompatibilityBD (pB := pB) (pD := pD) ιBsh hιBsh ιDsh hιDsh
  let φAD : IsLocalRing.ResidueField Ash →+* IsLocalRing.ResidueField Dsh :=
    (ιDsh.symm.toRingHom).comp ιAsh.toRingHom
  let hφAD :
      φAD.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (IsLocalRing.ResidueField.map (algebraMap Dp Dsh)).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)) :=
    strictHenselizationResidueCompatibilityAD (pA := pA) (pB := pB) (pD := pD)
      ιAsh hιAsh ιDsh hιDsh
  let _ : Algebra Ap Dp := algebraApDp pA pB pD
  let _ : Algebra Ap Bsh := algebraApBsh (pA := pA) (pB := pB)
  let _ : Algebra Bp Dsh := algebraBpDsh (pB := pB) (pD := pD)
  let _ : Algebra Ap Dsh := algebraApDsh pA pB pD
  let _ : pD.LiesOver pA := pD_liesOver_pA pA pB pD
  let fAB : Ash →ₐ[Ap] Bsh := strictHenselizationComparison pA pB φAB hφAB
  let fBD : Bsh →ₐ[Bp] Dsh := strictHenselizationComparison pB pD φBD hφBD
  let fAD : Ash →ₐ[Ap] Dsh := strictHenselizationComparison pA pD φAD hφAD
  have hApBpDsh :
      algebraMap Ap Dsh = (algebraMap Bp Dsh).comp (algebraMap Ap Bp) := by
    -- Normalize the two `A_p → D^sh` routes to the localization map `A_p → D_p` followed by
    -- the strict-henselization structure map.
    apply IsLocalization.ringHom_ext pA.primeCompl
    ext x
    simp [RingHom.algebraMap_toAlgebra, Localization.localRingHom_to_map, RingHom.comp_assoc]
  let _ : IsScalarTower Ap Bp Dsh := IsScalarTower.of_algebraMap_eq' hApBpDsh
  let _ : IsScalarTower Ap Bp Bsh := IsScalarTower.of_algebraMap_eq' rfl
  let f : Ash →ₐ[Ap] Dsh := (fBD.restrictScalars Ap).comp fAB
  have hABlocal : IsLocalHom (fAB : Ash →+* Bsh) := by
    -- The `A^sh → B^sh` comparison is local because it is the chosen strict-henselization map.
    simpa [fAB] using
      (strictHenselizationComparison_isLocalHom_here (p := pA) (q := pB) φAB hφAB)
  have hBDlocal : IsLocalHom (fBD : Bsh →+* Dsh) := by
    -- The `B^sh → D^sh` comparison is local for the same uniqueness reason.
    simpa [fBD] using
      (strictHenselizationComparison_isLocalHom_here (p := pB) (q := pD) φBD hφBD)
  let _ : IsLocalHom (fAB : Ash →+* Bsh) := hABlocal
  let _ : IsLocalHom (fBD : Bsh →+* Dsh) := hBDlocal
  have hflocal : IsLocalHom (f : Ash →+* Dsh) := by
    -- Local homomorphisms compose, so the concrete composite is an admissible uniqueness witness.
    have hcomp : IsLocalHom ((fBD : Bsh →+* Dsh).comp (fAB : Ash →+* Bsh)) := by
      infer_instance
    simpa [f] using hcomp
  have hresAB :
      (IsLocalRing.residue Bsh).comp (fAB : Ash →+* Bsh) =
        φAB.comp (IsLocalRing.residue Ash) := by
    simpa [fAB] using
      (strictHenselizationComparison_residue_here (p := pA) (q := pB) φAB hφAB)
  have hresBD :
      (IsLocalRing.residue Dsh).comp (fBD : Bsh →+* Dsh) =
        φBD.comp (IsLocalRing.residue Bsh) := by
    simpa [fBD] using
      (strictHenselizationComparison_residue_here (p := pB) (q := pD) φBD hφBD)
  have hres :
      (IsLocalRing.residue Dsh).comp (f : Ash →+* Dsh) =
        φAD.comp (IsLocalRing.residue Ash) := by
    -- The residue map of the composite is the composite of the two residue maps, and the common
    -- target identifications make `φBD ∘ φAB` definitionally the direct map `φAD`.
    calc
      (IsLocalRing.residue Dsh).comp (f : Ash →+* Dsh)
          = ((IsLocalRing.residue Dsh).comp (fBD : Bsh →+* Dsh)).comp
              (fAB : Ash →+* Bsh) := by
            change (IsLocalRing.residue Dsh).comp
                ((fBD : Bsh →+* Dsh).comp (fAB : Ash →+* Bsh)) =
              ((IsLocalRing.residue Dsh).comp (fBD : Bsh →+* Dsh)).comp
                (fAB : Ash →+* Bsh)
            rw [RingHom.comp_assoc]
      _ = (φBD.comp (IsLocalRing.residue Bsh)).comp (fAB : Ash →+* Bsh) := by
            rw [hresBD]
      _ = φBD.comp ((IsLocalRing.residue Bsh).comp (fAB : Ash →+* Bsh)) := by
            rw [RingHom.comp_assoc]
      _ = φBD.comp (φAB.comp (IsLocalRing.residue Ash)) := by
            rw [hresAB]
      _ = φAD.comp (IsLocalRing.residue Ash) := by
            ext x
            simp [φAB, φBD, φAD, RingHom.comp_assoc]
  have hcomp : (f : Ash →+* Dsh) = (fAD : Ash →+* Dsh) := by
    -- Uniqueness of the strict henselization comparison over `A_p` identifies the composite with
    -- the direct comparison.
    simpa [fAD] using
      (strictHenselizationComparison_ext_here (p := pA) (q := pD) φAD hφAD f hflocal hres)
  simpa [f, fAB, fBD, fAD, strictHenselizationComparisonAB,
    strictHenselizationComparisonBD, strictHenselizationComparisonAD] using hcomp

/-- Helper for Chap10 Lemma 10 156 6: the composite comparison
`A^sh → C^sh → D^sh` is the direct comparison `A^sh → D^sh`. -/
private theorem strictHenselizationComparisonCD_comp_AC_eq_AD
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιCsh : IsLocalRing.ResidueField Csh ≃+* Kgeo)
    (hιCsh :
      ιCsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Cp Csh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC)))
    (ιDsh : IsLocalRing.ResidueField Dsh ≃+* Kgeo)
    (hιDsh :
      ιDsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Dp Dsh)) =
        algebraMap (Ideal.ResidueField pD) Kgeo) :
    (strictHenselizationComparisonCD pC pD ιCsh hιCsh ιDsh hιDsh).comp
        (strictHenselizationComparisonAC pA pB pC pD ιAsh hιAsh ιCsh hιCsh) =
      strictHenselizationComparisonAD pA pB pD ιAsh hιAsh ιDsh hιDsh := by
  -- Route correction: this is the `C`-side analogue of the concrete uniqueness comparison above.
  let φAC : IsLocalRing.ResidueField Ash →+* IsLocalRing.ResidueField Csh :=
    (ιCsh.symm.toRingHom).comp ιAsh.toRingHom
  let hφAC :
      φAC.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (IsLocalRing.ResidueField.map (algebraMap Cp Csh)).comp
          (Ideal.ResidueField.map pA pC (algebraMap A C) (pC_over_def_pA pA pB pC pD)) :=
    strictHenselizationResidueCompatibilityAC (pA := pA) (pB := pB) (pC := pC)
      (pD := pD) ιAsh hιAsh ιCsh hιCsh
  let φCD : IsLocalRing.ResidueField Csh →+* IsLocalRing.ResidueField Dsh :=
    (ιDsh.symm.toRingHom).comp ιCsh.toRingHom
  let hφCD :
      φCD.comp (IsLocalRing.ResidueField.map (algebraMap Cp Csh)) =
        (IsLocalRing.ResidueField.map (algebraMap Dp Dsh)).comp
          (Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC)) :=
    strictHenselizationResidueCompatibilityCD (pC := pC) (pD := pD) ιCsh hιCsh ιDsh hιDsh
  let φAD : IsLocalRing.ResidueField Ash →+* IsLocalRing.ResidueField Dsh :=
    (ιDsh.symm.toRingHom).comp ιAsh.toRingHom
  let hφAD :
      φAD.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (IsLocalRing.ResidueField.map (algebraMap Dp Dsh)).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)) :=
    strictHenselizationResidueCompatibilityAD (pA := pA) (pB := pB) (pD := pD)
      ιAsh hιAsh ιDsh hιDsh
  let _ : Algebra Ap Cp := algebraApCp pA pB pC pD
  let _ : Algebra Ap Dp := algebraApDp pA pB pD
  let _ : Algebra Ap Csh := algebraApCsh (pA := pA) (pB := pB) (pC := pC) (pD := pD)
  let _ : Algebra Cp Dsh := algebraCpDsh (pC := pC) (pD := pD)
  let _ : Algebra Ap Dsh := algebraApDsh pA pB pD
  let _ : pD.LiesOver pA := pD_liesOver_pA pA pB pD
  let _ : pC.LiesOver pA := pC_liesOver_pA pA pB pC pD
  let fAC : Ash →ₐ[Ap] Csh := strictHenselizationComparison pA pC φAC hφAC
  let fCD : Csh →ₐ[Cp] Dsh := strictHenselizationComparison pC pD φCD hφCD
  let fAD : Ash →ₐ[Ap] Dsh := strictHenselizationComparison pA pD φAD hφAD
  have hApCpDsh :
      algebraMap Ap Dsh = (algebraMap Cp Dsh).comp (algebraMap Ap Cp) := by
    -- Normalize both maps from `A_p` to `D^sh` through the localization of `D`.
    apply IsLocalization.ringHom_ext pA.primeCompl
    ext x
    simp [RingHom.algebraMap_toAlgebra, Localization.localRingHom_to_map, RingHom.comp_assoc]
  let _ : IsScalarTower Ap Cp Dsh := IsScalarTower.of_algebraMap_eq' hApCpDsh
  let _ : IsScalarTower Ap Cp Csh := IsScalarTower.of_algebraMap_eq' rfl
  let f : Ash →ₐ[Ap] Dsh := (fCD.restrictScalars Ap).comp fAC
  have hAClocal : IsLocalHom (fAC : Ash →+* Csh) := by
    -- The `A^sh → C^sh` comparison is the chosen local strict-henselization comparison.
    simpa [fAC] using
      (strictHenselizationComparison_isLocalHom_here (p := pA) (q := pC) φAC hφAC)
  have hCDlocal : IsLocalHom (fCD : Csh →+* Dsh) := by
    -- The `C^sh → D^sh` comparison is local as another chosen comparison map.
    simpa [fCD] using
      (strictHenselizationComparison_isLocalHom_here (p := pC) (q := pD) φCD hφCD)
  let _ : IsLocalHom (fAC : Ash →+* Csh) := hAClocal
  let _ : IsLocalHom (fCD : Csh →+* Dsh) := hCDlocal
  have hflocal : IsLocalHom (f : Ash →+* Dsh) := by
    -- The concrete composite is local because both comparison factors are local.
    have hcomp : IsLocalHom ((fCD : Csh →+* Dsh).comp (fAC : Ash →+* Csh)) := by
      infer_instance
    simpa [f] using hcomp
  have hresAC :
      (IsLocalRing.residue Csh).comp (fAC : Ash →+* Csh) =
        φAC.comp (IsLocalRing.residue Ash) := by
    simpa [fAC] using
      (strictHenselizationComparison_residue_here (p := pA) (q := pC) φAC hφAC)
  have hresCD :
      (IsLocalRing.residue Dsh).comp (fCD : Csh →+* Dsh) =
        φCD.comp (IsLocalRing.residue Csh) := by
    simpa [fCD] using
      (strictHenselizationComparison_residue_here (p := pC) (q := pD) φCD hφCD)
  have hres :
      (IsLocalRing.residue Dsh).comp (f : Ash →+* Dsh) =
        φAD.comp (IsLocalRing.residue Ash) := by
    -- As on the `B` side, compose the two residue computations and cancel the common
    -- geometric-point identifications.
    calc
      (IsLocalRing.residue Dsh).comp (f : Ash →+* Dsh)
          = ((IsLocalRing.residue Dsh).comp (fCD : Csh →+* Dsh)).comp
              (fAC : Ash →+* Csh) := by
            change (IsLocalRing.residue Dsh).comp
                ((fCD : Csh →+* Dsh).comp (fAC : Ash →+* Csh)) =
              ((IsLocalRing.residue Dsh).comp (fCD : Csh →+* Dsh)).comp
                (fAC : Ash →+* Csh)
            rw [RingHom.comp_assoc]
      _ = (φCD.comp (IsLocalRing.residue Csh)).comp (fAC : Ash →+* Csh) := by
            rw [hresCD]
      _ = φCD.comp ((IsLocalRing.residue Csh).comp (fAC : Ash →+* Csh)) := by
            rw [RingHom.comp_assoc]
      _ = φCD.comp (φAC.comp (IsLocalRing.residue Ash)) := by
            rw [hresAC]
      _ = φAD.comp (IsLocalRing.residue Ash) := by
            ext x
            simp [φAC, φCD, φAD, RingHom.comp_assoc]
  have hcomp : (f : Ash →+* Dsh) = (fAD : Ash →+* Dsh) := by
    -- Uniqueness over `A_p` now identifies this composite with the direct comparison.
    simpa [fAD] using
      (strictHenselizationComparison_ext_here (p := pA) (q := pD) φAD hφAD f hflocal hres)
  simpa [f, fAC, fCD, fAD, strictHenselizationComparisonAC,
    strictHenselizationComparisonCD, strictHenselizationComparisonAD] using hcomp

attribute [irreducible]
  strictHenselizationComparisonAB
  strictHenselizationComparisonAC
  strictHenselizationComparisonAD
  strictHenselizationComparisonBD
  strictHenselizationComparisonCD

variable (pA) (pB) (pD) in
@[implicit_reducible] private noncomputable def algebraAshBsh
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιBsh : IsLocalRing.ResidueField Bsh ≃+* Kgeo)
    (hιBsh :
      ιBsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Bp Bsh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB))) :
    Algebra Ash Bsh :=
  RingHom.toAlgebra (strictHenselizationComparisonAB pA pB pD ιAsh hιAsh ιBsh hιBsh)

variable (pA) (pB) (pC) (pD) in
@[implicit_reducible] private noncomputable def algebraAshCsh
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιCsh : IsLocalRing.ResidueField Csh ≃+* Kgeo)
    (hιCsh :
      ιCsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Cp Csh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC))) :
    Algebra Ash Csh :=
  RingHom.toAlgebra (strictHenselizationComparisonAC pA pB pC pD ιAsh hιAsh ιCsh hιCsh)

variable (pA) (pB) (pD) in
@[implicit_reducible] private noncomputable def algebraAshDsh
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιDsh : IsLocalRing.ResidueField Dsh ≃+* Kgeo)
    (hιDsh :
      ιDsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Dp Dsh)) =
        algebraMap (Ideal.ResidueField pD) Kgeo) :
    Algebra Ash Dsh :=
  RingHom.toAlgebra (strictHenselizationComparisonAD pA pB pD ιAsh hιAsh ιDsh hιDsh)

/-- Helper for Chap10 Lemma 10 156 6: the comparison `A^sh → B^sh` is a local
homomorphism for the `A^sh`-algebra structure induced by the common geometric point. -/
private theorem strictHenselizationComparisonAB_isLocalHom
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιBsh : IsLocalRing.ResidueField Bsh ≃+* Kgeo)
    (hιBsh :
      ιBsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Bp Bsh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB))) :
    let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
    IsLocalHom (algebraMap Ash Bsh) := by
  -- Unfold the installed algebra map to the chosen strict-henselization comparison, whose
  -- locality is part of the comparison uniqueness package.
  let φAB : IsLocalRing.ResidueField Ash →+* IsLocalRing.ResidueField Bsh :=
    (ιBsh.symm.toRingHom).comp ιAsh.toRingHom
  let hφAB :
      φAB.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (IsLocalRing.ResidueField.map (algebraMap Bp Bsh)).comp
          (Ideal.ResidueField.map pA pB (algebraMap A B) (pB.over_def pA)) :=
    strictHenselizationResidueCompatibilityAB (pA := pA) (pB := pB) (pD := pD)
      ιAsh hιAsh ιBsh hιBsh
  let _ : Algebra Ap Bsh := algebraApBsh (pA := pA) (pB := pB)
  let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
  simpa [algebraAshBsh, strictHenselizationComparisonAB, φAB, hφAB,
    RingHom.algebraMap_toAlgebra] using
    (strictHenselizationComparison_isLocalHom_here (p := pA) (q := pB) φAB hφAB)

/-- Helper for Chap10 Lemma 10 156 6: the comparison `A^sh → C^sh` is a local
homomorphism for the `A^sh`-algebra structure induced by the common geometric point. -/
private theorem strictHenselizationComparisonAC_isLocalHom
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιCsh : IsLocalRing.ResidueField Csh ≃+* Kgeo)
    (hιCsh :
      ιCsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Cp Csh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC))) :
    let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
    IsLocalHom (algebraMap Ash Csh) := by
  -- The `C`-side comparison is local by the same strict-henselization uniqueness property, after
  -- installing the localized `A_p → C_p` structure selected by `pD`.
  let φAC : IsLocalRing.ResidueField Ash →+* IsLocalRing.ResidueField Csh :=
    (ιCsh.symm.toRingHom).comp ιAsh.toRingHom
  let hφAC :
      φAC.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (IsLocalRing.ResidueField.map (algebraMap Cp Csh)).comp
          (Ideal.ResidueField.map pA pC (algebraMap A C) (pC_over_def_pA pA pB pC pD)) :=
    strictHenselizationResidueCompatibilityAC (pA := pA) (pB := pB) (pC := pC)
      (pD := pD) ιAsh hιAsh ιCsh hιCsh
  let _ : pD.LiesOver pA := pD_liesOver_pA pA pB pD
  let _ : pC.LiesOver pA := pC_liesOver_pA pA pB pC pD
  let _ : Algebra Ap Cp := algebraApCp pA pB pC pD
  let hlocalCp : IsLocalHom (algebraMap Ap Cp) :=
    localizationAtPrime_pA_pC_isLocalHom pA pB pC pD
  let _ : IsLocalHom (algebraMap Ap Cp) := hlocalCp
  let _ : Algebra Ap Csh := ((algebraMap Cp Csh).comp (algebraMap Ap Cp)).toAlgebra
  let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
  simpa [algebraAshCsh, strictHenselizationComparisonAC, φAC, hφAC,
    RingHom.algebraMap_toAlgebra] using
    (strictHenselizationComparison_isLocalHom_here (p := pA) (q := pC) φAC hφAC)

/-- Helper for Chap10 Lemma 10 156 6: the residue-field map induced by
`A^sh → B^sh` is a bijection. -/
private theorem strictHenselizationComparisonAB_residue_bijective
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιBsh : IsLocalRing.ResidueField Bsh ≃+* Kgeo)
    (hιBsh :
      ιBsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Bp Bsh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB))) :
    let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
    let _ : IsLocalHom (algebraMap Ash Bsh) :=
      strictHenselizationComparisonAB_isLocalHom ιAsh hιAsh ιBsh hιBsh
    Function.Bijective (IsLocalRing.ResidueField.map (algebraMap Ash Bsh)) := by
  -- Identify the induced residue map with the residue-field equivalence coming from the common
  -- target field `Kgeo`.
  let φAB : IsLocalRing.ResidueField Ash →+* IsLocalRing.ResidueField Bsh :=
    (ιBsh.symm.toRingHom).comp ιAsh.toRingHom
  let hφAB :
      φAB.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (IsLocalRing.ResidueField.map (algebraMap Bp Bsh)).comp
          (Ideal.ResidueField.map pA pB (algebraMap A B) (pB.over_def pA)) :=
    strictHenselizationResidueCompatibilityAB (pA := pA) (pB := pB) (pD := pD)
      ιAsh hιAsh ιBsh hιBsh
  let _ : Algebra Ap Bsh := algebraApBsh (pA := pA) (pB := pB)
  let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
  let hlocal : IsLocalHom (algebraMap Ash Bsh) :=
    strictHenselizationComparisonAB_isLocalHom ιAsh hιAsh ιBsh hιBsh
  let _ : IsLocalHom (algebraMap Ash Bsh) := hlocal
  have hres :
      (IsLocalRing.residue Bsh).comp
          (strictHenselizationComparison pA pB φAB hφAB : Ash →+* Bsh) =
        φAB.comp (IsLocalRing.residue Ash) := by
    simpa using
      (strictHenselizationComparison_residue_here (p := pA) (q := pB) φAB hφAB)
  have hmap :
      IsLocalRing.ResidueField.map (algebraMap Ash Bsh) = φAB := by
    apply RingHom.ext
    intro x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    simpa [IsLocalRing.ResidueField.map_residue, algebraAshBsh,
      strictHenselizationComparisonAB, φAB, hφAB, RingHom.algebraMap_toAlgebra] using
      congrArg (fun f : Ash →+* IsLocalRing.ResidueField Bsh => f y) hres
  dsimp
  rw [hmap]
  simpa [φAB] using (ιAsh.trans ιBsh.symm).bijective

/-- Helper for Chap10 Lemma 10 156 6: the residue-field map induced by
`A^sh → C^sh` is a bijection. -/
private theorem strictHenselizationComparisonAC_residue_bijective
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιCsh : IsLocalRing.ResidueField Csh ≃+* Kgeo)
    (hιCsh :
      ιCsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Cp Csh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC))) :
    let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
    let _ : IsLocalHom (algebraMap Ash Csh) :=
      strictHenselizationComparisonAC_isLocalHom ιAsh hιAsh ιCsh hιCsh
    Function.Bijective (IsLocalRing.ResidueField.map (algebraMap Ash Csh)) := by
  -- As on the `B` side, the induced residue map is the equivalence through `Kgeo`.
  let φAC : IsLocalRing.ResidueField Ash →+* IsLocalRing.ResidueField Csh :=
    (ιCsh.symm.toRingHom).comp ιAsh.toRingHom
  let hφAC :
      φAC.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (IsLocalRing.ResidueField.map (algebraMap Cp Csh)).comp
          (Ideal.ResidueField.map pA pC (algebraMap A C) (pC_over_def_pA pA pB pC pD)) :=
    strictHenselizationResidueCompatibilityAC (pA := pA) (pB := pB) (pC := pC)
      (pD := pD) ιAsh hιAsh ιCsh hιCsh
  let _ : pD.LiesOver pA := pD_liesOver_pA pA pB pD
  let _ : pC.LiesOver pA := pC_liesOver_pA pA pB pC pD
  let _ : Algebra Ap Cp := algebraApCp pA pB pC pD
  let hlocalCp : IsLocalHom (algebraMap Ap Cp) :=
    localizationAtPrime_pA_pC_isLocalHom pA pB pC pD
  let _ : IsLocalHom (algebraMap Ap Cp) := hlocalCp
  let _ : Algebra Ap Csh := ((algebraMap Cp Csh).comp (algebraMap Ap Cp)).toAlgebra
  let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
  let hlocal : IsLocalHom (algebraMap Ash Csh) :=
    strictHenselizationComparisonAC_isLocalHom ιAsh hιAsh ιCsh hιCsh
  let _ : IsLocalHom (algebraMap Ash Csh) := hlocal
  have hres :
      (IsLocalRing.residue Csh).comp
          (strictHenselizationComparison pA pC φAC hφAC : Ash →+* Csh) =
        φAC.comp (IsLocalRing.residue Ash) := by
    simpa using
      (strictHenselizationComparison_residue_here (p := pA) (q := pC) φAC hφAC)
  have hmap :
      IsLocalRing.ResidueField.map (algebraMap Ash Csh) = φAC := by
    apply RingHom.ext
    intro x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    simpa [IsLocalRing.ResidueField.map_residue, algebraAshCsh,
      strictHenselizationComparisonAC, φAC, hφAC, RingHom.algebraMap_toAlgebra] using
      congrArg (fun f : Ash →+* IsLocalRing.ResidueField Csh => f y) hres
  dsimp
  rw [hmap]
  simpa [φAC] using (ιAsh.trans ιCsh.symm).bijective

/-- Helper for Chap10 Lemma 10 156 6: the installed `A^sh → B^sh` algebra structure induces
on residue fields the equivalence through the common geometric residue field. -/
private theorem strictHenselizationComparisonAB_residueMap_eq
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιBsh : IsLocalRing.ResidueField Bsh ≃+* Kgeo)
    (hιBsh :
      ιBsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Bp Bsh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB))) :
    let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
    let _ : IsLocalHom (algebraMap Ash Bsh) :=
      strictHenselizationComparisonAB_isLocalHom ιAsh hιAsh ιBsh hιBsh
    IsLocalRing.ResidueField.map (algebraMap Ash Bsh) =
      (ιBsh.symm.toRingHom).comp ιAsh.toRingHom := by
  -- Normalize the installed algebra map to the chosen strict-henselization comparison, then use
  -- the residue computation recorded by the comparison uniqueness theorem.
  let φAB : IsLocalRing.ResidueField Ash →+* IsLocalRing.ResidueField Bsh :=
    (ιBsh.symm.toRingHom).comp ιAsh.toRingHom
  let hφAB :
      φAB.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (IsLocalRing.ResidueField.map (algebraMap Bp Bsh)).comp
          (Ideal.ResidueField.map pA pB (algebraMap A B) (pB.over_def pA)) :=
    strictHenselizationResidueCompatibilityAB (pA := pA) (pB := pB) (pD := pD)
      ιAsh hιAsh ιBsh hιBsh
  let _ : Algebra Ap Bsh := algebraApBsh (pA := pA) (pB := pB)
  let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
  let hlocal : IsLocalHom (algebraMap Ash Bsh) :=
    strictHenselizationComparisonAB_isLocalHom ιAsh hιAsh ιBsh hιBsh
  let _ : IsLocalHom (algebraMap Ash Bsh) := hlocal
  have hres :
      (IsLocalRing.residue Bsh).comp
          (strictHenselizationComparison pA pB φAB hφAB : Ash →+* Bsh) =
        φAB.comp (IsLocalRing.residue Ash) := by
    simpa using
      (strictHenselizationComparison_residue_here (p := pA) (q := pB) φAB hφAB)
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  simpa [IsLocalRing.ResidueField.map_residue, algebraAshBsh,
    strictHenselizationComparisonAB, φAB, hφAB, RingHom.algebraMap_toAlgebra] using
    congrArg (fun f : Ash →+* IsLocalRing.ResidueField Bsh => f y) hres

/-- Helper for Chap10 Lemma 10 156 6: the installed `A^sh → C^sh` algebra structure induces
on residue fields the equivalence through the common geometric residue field. -/
private theorem strictHenselizationComparisonAC_residueMap_eq
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιCsh : IsLocalRing.ResidueField Csh ≃+* Kgeo)
    (hιCsh :
      ιCsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Cp Csh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC))) :
    let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
    let _ : IsLocalHom (algebraMap Ash Csh) :=
      strictHenselizationComparisonAC_isLocalHom ιAsh hιAsh ιCsh hιCsh
    IsLocalRing.ResidueField.map (algebraMap Ash Csh) =
      (ιCsh.symm.toRingHom).comp ιAsh.toRingHom := by
  -- The `C`-side proof is the same normalization, with the localized map `A_p → C_p` installed
  -- from the prime selected by `pD`.
  let φAC : IsLocalRing.ResidueField Ash →+* IsLocalRing.ResidueField Csh :=
    (ιCsh.symm.toRingHom).comp ιAsh.toRingHom
  let hφAC :
      φAC.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (IsLocalRing.ResidueField.map (algebraMap Cp Csh)).comp
          (Ideal.ResidueField.map pA pC (algebraMap A C) (pC_over_def_pA pA pB pC pD)) :=
    strictHenselizationResidueCompatibilityAC (pA := pA) (pB := pB) (pC := pC)
      (pD := pD) ιAsh hιAsh ιCsh hιCsh
  let _ : pD.LiesOver pA := pD_liesOver_pA pA pB pD
  let _ : pC.LiesOver pA := pC_liesOver_pA pA pB pC pD
  let _ : Algebra Ap Cp := algebraApCp pA pB pC pD
  let hlocalCp : IsLocalHom (algebraMap Ap Cp) :=
    localizationAtPrime_pA_pC_isLocalHom pA pB pC pD
  let _ : IsLocalHom (algebraMap Ap Cp) := hlocalCp
  let _ : Algebra Ap Csh := ((algebraMap Cp Csh).comp (algebraMap Ap Cp)).toAlgebra
  let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
  let hlocal : IsLocalHom (algebraMap Ash Csh) :=
    strictHenselizationComparisonAC_isLocalHom ιAsh hιAsh ιCsh hιCsh
  let _ : IsLocalHom (algebraMap Ash Csh) := hlocal
  have hres :
      (IsLocalRing.residue Csh).comp
          (strictHenselizationComparison pA pC φAC hφAC : Ash →+* Csh) =
        φAC.comp (IsLocalRing.residue Ash) := by
    simpa using
      (strictHenselizationComparison_residue_here (p := pA) (q := pC) φAC hφAC)
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  simpa [IsLocalRing.ResidueField.map_residue, algebraAshCsh,
    strictHenselizationComparisonAC, φAC, hφAC, RingHom.algebraMap_toAlgebra] using
    congrArg (fun f : Ash →+* IsLocalRing.ResidueField Csh => f y) hres

/-- Helper for Chap10 Lemma 10 156 6: a bijective residue-field map from a local homomorphism
gives a purely inseparable residue-field extension for the induced algebra structure. -/
private theorem residueFieldMap_isPurelyInseparable_of_bijective
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (hres : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R S))) :
    IsPurelyInseparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) := by
  -- Turn the bijective residue map into an algebra equivalence over the source residue field;
  -- equivalences preserve the purely inseparable identity extension.
  exact
    (AlgEquiv.ofBijective
      (Algebra.ofId (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S))
      (by simpa [RingHom.algebraMap_toAlgebra] using hres)).isPurelyInseparable

/-- Helper for Chap10 Lemma 10 156 6: in the quasi-finite branch, the comparison
`A^sh → B^sh` is integral because Lemma 10.156.3 makes the strict-henselization comparison
finite. -/
private theorem strictHenselizationComparisonAB_integral_of_quasiFiniteAt
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιBsh : IsLocalRing.ResidueField Bsh ≃+* Kgeo)
    (hιBsh :
      ιBsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Bp Bsh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB)))
    (hB : Algebra.QuasiFiniteAt A pB) :
    let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
    Algebra.IsIntegral Ash Bsh := by
  -- First name the residue-field comparison used by the installed `A^sh → B^sh` algebra
  -- structure, so the finite comparison theorem and the algebra map have the same normal form.
  let φAB : IsLocalRing.ResidueField Ash →+* IsLocalRing.ResidueField Bsh :=
    (ιBsh.symm.toRingHom).comp ιAsh.toRingHom
  let hφAB :
      φAB.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (IsLocalRing.ResidueField.map (algebraMap Bp Bsh)).comp
          (Ideal.ResidueField.map pA pB (algebraMap A B) (pB.over_def pA)) :=
    strictHenselizationResidueCompatibilityAB (pA := pA) (pB := pB) (pD := pD)
      ιAsh hιAsh ιBsh hιBsh
  let _ : Algebra Ap Bsh := algebraApBsh (pA := pA) (pB := pB)
  let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
  let _ : Algebra.QuasiFiniteAt A pB := hB
  have hfiniteComparison :
      RingHom.Finite (strictHenselizationComparison pA pB φAB hφAB : Ash →+* Bsh) := by
    -- Lemma 10.156.3 is stated exactly for this comparison map over `A_p → B_p`.
    simpa using
      (strictHenselizationComparison_finite_of_quasiFiniteAt
        (p := pA) (q := pB) φAB hφAB)
  have hfiniteAlgebraMap : RingHom.Finite (algebraMap Ash Bsh) := by
    -- The `A^sh`-algebra map is the same chosen strict-henselization comparison.
    simpa [algebraAshBsh, strictHenselizationComparisonAB, φAB, hφAB,
      RingHom.algebraMap_toAlgebra] using hfiniteComparison
  exact algebraMap_isIntegral_iff.mp (RingHom.Finite.to_isIntegral hfiniteAlgebraMap)

/-- Helper for Chap10 Lemma 10 156 6: once the comparison `A^sh → B^sh` is integral, the
source tensor product `B^sh ⊗[A^sh] C^sh` is local by Lemma 10.156.5 and the bijective residue
map on the `B` side. -/
private theorem sourceTensor_isLocalRing_of_integral_left
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιBsh : IsLocalRing.ResidueField Bsh ≃+* Kgeo)
    (hιBsh :
      ιBsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Bp Bsh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB)))
    (ιCsh : IsLocalRing.ResidueField Csh ≃+* Kgeo)
    (hιCsh :
      ιCsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Cp Csh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC)))
    (hInt :
      let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
      Algebra.IsIntegral Ash Bsh) :
    let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
    let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
    let _ : IsLocalHom (algebraMap Ash Bsh) :=
      strictHenselizationComparisonAB_isLocalHom ιAsh hιAsh ιBsh hιBsh
    let _ : IsLocalHom (algebraMap Ash Csh) :=
      strictHenselizationComparisonAC_isLocalHom ιAsh hιAsh ιCsh hιCsh
    IsLocalRing (Bsh ⊗[Ash] Csh) := by
  -- Route correction: use the proven local tensor theorem from Lemma 10.156.5 after swapping the
  -- tensor factors, because the available integrality hypothesis is on the `B^sh` factor.
  let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
  let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
  let hlocalB : IsLocalHom (algebraMap Ash Bsh) :=
    strictHenselizationComparisonAB_isLocalHom ιAsh hιAsh ιBsh hιBsh
  let hlocalC : IsLocalHom (algebraMap Ash Csh) :=
    strictHenselizationComparisonAC_isLocalHom ιAsh hιAsh ιCsh hιCsh
  let _ : IsLocalHom (algebraMap Ash Bsh) := hlocalB
  let _ : IsLocalHom (algebraMap Ash Csh) := hlocalC
  let _ : Algebra.IsIntegral Ash Bsh := hInt
  have hresB :
      Function.Bijective (IsLocalRing.ResidueField.map (algebraMap Ash Bsh)) :=
    strictHenselizationComparisonAB_residue_bijective ιAsh hιAsh ιBsh hιBsh
  have hpureB :
      IsPurelyInseparable (IsLocalRing.ResidueField Ash) (IsLocalRing.ResidueField Bsh) :=
    residueFieldMap_isPurelyInseparable_of_bijective hresB
  have hlocalSwapped : IsLocalRing (Csh ⊗[Ash] Bsh) := by
    -- Lemma 10.156.5 expects the integral algebra as the right tensor factor.
    exact
      tensorProduct_isLocalRing_of_local_of_integral_of_residueField_purelyInseparable
        (A := Ash) (B := Csh) (C := Bsh) (Or.inl hpureB)
  -- Tensor commutativity transports the local ring structure back to the source order.
  let _ : IsLocalRing (Csh ⊗[Ash] Bsh) := hlocalSwapped
  exact RingEquiv.isLocalRing (Algebra.TensorProduct.comm Ash Csh Bsh).toRingEquiv

/-- Helper for Chap10 Lemma 10 156 6: the comparison `B^sh → D^sh` commutes with the
`A^sh`-algebra structures induced by the common geometric point. -/
private theorem strictHenselizationComparisonBD_commutes_Ash
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιBsh : IsLocalRing.ResidueField Bsh ≃+* Kgeo)
    (hιBsh :
      ιBsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Bp Bsh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB)))
    (ιDsh : IsLocalRing.ResidueField Dsh ≃+* Kgeo)
    (hιDsh :
      ιDsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Dp Dsh)) =
        algebraMap (Ideal.ResidueField pD) Kgeo) :
    let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
    let _ : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
    (strictHenselizationComparisonBD pB pD ιBsh hιBsh ιDsh hιDsh).comp
        (algebraMap Ash Bsh) =
      algebraMap Ash Dsh := by
  -- Reduce Ash-linearity to the already isolated equality of comparison composites.
  let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
  let _ : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
  simpa [algebraAshBsh, algebraAshDsh, RingHom.algebraMap_toAlgebra] using
    strictHenselizationComparisonBD_comp_AB_eq_AD
      ιAsh hιAsh ιBsh hιBsh ιDsh hιDsh

/-- Helper for Chap10 Lemma 10 156 6: pointwise form of the `A^sh`-linearity of
`B^sh → D^sh`. -/
private theorem strictHenselizationComparisonBD_commutes_Ash_apply
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιBsh : IsLocalRing.ResidueField Bsh ≃+* Kgeo)
    (hιBsh :
      ιBsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Bp Bsh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB)))
    (ιDsh : IsLocalRing.ResidueField Dsh ≃+* Kgeo)
    (hιDsh :
      ιDsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Dp Dsh)) =
        algebraMap (Ideal.ResidueField pD) Kgeo)
    (r : Ash) :
    let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
    let _ : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
    strictHenselizationComparisonBD pB pD ιBsh hιBsh ιDsh hιDsh (algebraMap Ash Bsh r) =
      algebraMap Ash Dsh r := by
  -- The pointwise statement is just evaluation of the ring-hom equality above.
  let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
  let _ : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
  exact congrArg (fun f : Ash →+* Dsh => f r)
    (strictHenselizationComparisonBD_commutes_Ash ιAsh hιAsh ιBsh hιBsh ιDsh hιDsh)

/-- Helper for Chap10 Lemma 10 156 6: the comparison `C^sh → D^sh` commutes with the
`A^sh`-algebra structures induced by the common geometric point. -/
private theorem strictHenselizationComparisonCD_commutes_Ash
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιCsh : IsLocalRing.ResidueField Csh ≃+* Kgeo)
    (hιCsh :
      ιCsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Cp Csh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC)))
    (ιDsh : IsLocalRing.ResidueField Dsh ≃+* Kgeo)
    (hιDsh :
      ιDsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Dp Dsh)) =
        algebraMap (Ideal.ResidueField pD) Kgeo) :
    let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
    let _ : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
    (strictHenselizationComparisonCD pC pD ιCsh hιCsh ιDsh hιDsh).comp
        (algebraMap Ash Csh) =
      algebraMap Ash Dsh := by
  -- Reduce Ash-linearity to the already isolated equality of comparison composites.
  let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
  let _ : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
  simpa [algebraAshCsh, algebraAshDsh, RingHom.algebraMap_toAlgebra] using
    strictHenselizationComparisonCD_comp_AC_eq_AD
      ιAsh hιAsh ιCsh hιCsh ιDsh hιDsh

/-- Helper for Chap10 Lemma 10 156 6: pointwise form of the `A^sh`-linearity of
`C^sh → D^sh`. -/
private theorem strictHenselizationComparisonCD_commutes_Ash_apply
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιCsh : IsLocalRing.ResidueField Csh ≃+* Kgeo)
    (hιCsh :
      ιCsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Cp Csh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC)))
    (ιDsh : IsLocalRing.ResidueField Dsh ≃+* Kgeo)
    (hιDsh :
      ιDsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Dp Dsh)) =
        algebraMap (Ideal.ResidueField pD) Kgeo)
    (r : Ash) :
    let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
    let _ : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
    strictHenselizationComparisonCD pC pD ιCsh hιCsh ιDsh hιDsh (algebraMap Ash Csh r) =
      algebraMap Ash Dsh r := by
  -- Evaluate the ring-hom commutativity statement at the chosen scalar.
  let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
  let _ : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
  exact congrArg (fun f : Ash →+* Dsh => f r)
    (strictHenselizationComparisonCD_commutes_Ash ιAsh hιAsh ιCsh hιCsh ιDsh hιDsh)

/-- Helper for Chap10 Lemma 10 156 6: the comparison `B^sh → D^sh` as an `A^sh`-algebra
homomorphism. -/
private noncomputable def strictHenselizationComparisonBDOverAsh
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιBsh : IsLocalRing.ResidueField Bsh ≃+* Kgeo)
    (hιBsh :
      ιBsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Bp Bsh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB)))
    (ιDsh : IsLocalRing.ResidueField Dsh ≃+* Kgeo)
    (hιDsh :
      ιDsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Dp Dsh)) =
        algebraMap (Ideal.ResidueField pD) Kgeo) :
    let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
    let _ : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
    Bsh →ₐ[Ash] Dsh :=
  let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
  let _ : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
  { toRingHom := strictHenselizationComparisonBD pB pD ιBsh hιBsh ιDsh hιDsh
    commutes' := strictHenselizationComparisonBD_commutes_Ash_apply
      ιAsh hιAsh ιBsh hιBsh ιDsh hιDsh }

/-- Helper for Chap10 Lemma 10 156 6: the comparison `C^sh → D^sh` as an `A^sh`-algebra
homomorphism. -/
private noncomputable def strictHenselizationComparisonCDOverAsh
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Ap Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιCsh : IsLocalRing.ResidueField Csh ≃+* Kgeo)
    (hιCsh :
      ιCsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Cp Csh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC)))
    (ιDsh : IsLocalRing.ResidueField Dsh ≃+* Kgeo)
    (hιDsh :
      ιDsh.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap Dp Dsh)) =
        algebraMap (Ideal.ResidueField pD) Kgeo) :
    let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
    let _ : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
    Csh →ₐ[Ash] Dsh :=
  let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
  let _ : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
  { toRingHom := strictHenselizationComparisonCD pC pD ιCsh hιCsh ιDsh hιDsh
    commutes' := strictHenselizationComparisonCD_commutes_Ash_apply
      ιAsh hιAsh ιCsh hιCsh ιDsh hιDsh }

/-
The canonical map `B^sh ⊗[A^sh] C^sh → (B ⊗[A] C)^sh` attached to one common geometric point
of `B ⊗[A] C`, obtained from one common target field for the four residue fields via the canonical
owner `strictHenselizationComparison`.
-/
private noncomputable def strictHenselizationTensorBaseChangeMapCore :
    let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
    let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
    let _ : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
    Bsh ⊗[Ash] Csh →ₐ[Ash] Dsh :=
  let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
  let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
  let _ : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
  Algebra.TensorProduct.productMap
    (strictHenselizationComparisonBDOverAsh ιAsh hιAsh ιBsh hιBsh ιDsh hιDsh)
    (strictHenselizationComparisonCDOverAsh ιAsh hιAsh ιCsh hιCsh ιDsh hιDsh)

attribute [irreducible] strictHenselizationTensorBaseChangeMapCore

local notation "tensorBaseChangeMapCore" =>
  (strictHenselizationTensorBaseChangeMapCore
    ιAsh hιAsh ιBsh hιBsh ιCsh hιCsh ιDsh hιDsh)

/-- Helper for Chap10 Lemma 10 156 6: on pure tensors, the core base-change map is the product
of the two strict-henselization comparison maps to `D^sh`. -/
private theorem strictHenselizationTensorBaseChangeMapCore_tmul
    (x : Bsh) (y : Csh) :
    let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
    let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
    let _ : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
    tensorBaseChangeMapCore (x ⊗ₜ[Ash] y) =
      strictHenselizationComparisonBD pB pD ιBsh hιBsh ιDsh hιDsh x *
        strictHenselizationComparisonCD pC pD ιCsh hιCsh ιDsh hιDsh y := by
  -- Unfold the core map exactly once; future comparison proofs can rewrite pure tensor
  -- generators without reopening the `productMap` construction.
  let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
  let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
  let _ : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
  unfold strictHenselizationTensorBaseChangeMapCore
  simp [Algebra.TensorProduct.productMap_apply_tmul, strictHenselizationComparisonBDOverAsh,
    strictHenselizationComparisonCDOverAsh]

/-- Helper for Chap10 Lemma 10 156 6: the two residue maps from `B^sh` and `C^sh` to the
common geometric residue field agree on `A^sh`. -/
private theorem sourceTensorResidueToKgeo_agree :
    let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
    let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
    (ιBsh.toRingHom.comp (IsLocalRing.residue Bsh)).comp (algebraMap Ash Bsh) =
      (ιCsh.toRingHom.comp (IsLocalRing.residue Csh)).comp (algebraMap Ash Csh) := by
  -- Route correction: normalize the residue maps for the installed `Ash`-algebra structures,
  -- rather than rebuilding comparison maps with fresh proof arguments.
  let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
  let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
  let hlocalB : IsLocalHom (algebraMap Ash Bsh) :=
    strictHenselizationComparisonAB_isLocalHom ιAsh hιAsh ιBsh hιBsh
  let hlocalC : IsLocalHom (algebraMap Ash Csh) :=
    strictHenselizationComparisonAC_isLocalHom ιAsh hιAsh ιCsh hιCsh
  let _ : IsLocalHom (algebraMap Ash Bsh) := hlocalB
  let _ : IsLocalHom (algebraMap Ash Csh) := hlocalC
  have hBres :
      IsLocalRing.ResidueField.map (algebraMap Ash Bsh) =
        (ιBsh.symm.toRingHom).comp ιAsh.toRingHom :=
    strictHenselizationComparisonAB_residueMap_eq ιAsh hιAsh ιBsh hιBsh
  have hCres :
      IsLocalRing.ResidueField.map (algebraMap Ash Csh) =
        (ιCsh.symm.toRingHom).comp ιAsh.toRingHom :=
    strictHenselizationComparisonAC_residueMap_eq ιAsh hιAsh ιCsh hιCsh
  apply RingHom.ext
  intro r
  calc
    ((ιBsh.toRingHom.comp (IsLocalRing.residue Bsh)).comp (algebraMap Ash Bsh)) r
        = ιBsh.toRingHom
            (IsLocalRing.ResidueField.map (algebraMap Ash Bsh)
              (IsLocalRing.residue Ash r)) := by
          simp only [RingHom.comp_apply, IsLocalRing.ResidueField.map_residue]
    _ = ιBsh.toRingHom (((ιBsh.symm.toRingHom).comp ιAsh.toRingHom)
            (IsLocalRing.residue Ash r)) := by
          rw [hBres]
    _ = ιAsh.toRingHom (IsLocalRing.residue Ash r) := by
          simp
    _ = ιCsh.toRingHom (((ιCsh.symm.toRingHom).comp ιAsh.toRingHom)
            (IsLocalRing.residue Ash r)) := by
          simp
    _ = ιCsh.toRingHom
            (IsLocalRing.ResidueField.map (algebraMap Ash Csh)
              (IsLocalRing.residue Ash r)) := by
          rw [hCres]
    _ = ((ιCsh.toRingHom.comp (IsLocalRing.residue Csh)).comp
            (algebraMap Ash Csh)) r := by
          simp only [RingHom.comp_apply, IsLocalRing.ResidueField.map_residue]

/-- Helper for Chap10 Lemma 10 156 6: the source tensor product maps to the common geometric
residue field by multiplying the two strict-henselization residue maps. -/
private noncomputable def sourceTensorResidueToKgeo :
    let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
    let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
    let _ : Algebra Ash Kgeo :=
      RingHom.toAlgebra ((ιBsh.toRingHom.comp (IsLocalRing.residue Bsh)).comp
        (algebraMap Ash Bsh))
    Bsh ⊗[Ash] Csh →ₐ[Ash] Kgeo :=
  let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
  let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
  let fB : Bsh →+* Kgeo := ιBsh.toRingHom.comp (IsLocalRing.residue Bsh)
  let fC : Csh →+* Kgeo := ιCsh.toRingHom.comp (IsLocalRing.residue Csh)
  let _ : Algebra Ash Kgeo :=
    RingHom.toAlgebra (fB.comp (algebraMap Ash Bsh))
  let left : Bsh →ₐ[Ash] Kgeo :=
    { toRingHom := fB
      commutes' := fun _ ↦ rfl }
  let right : Csh →ₐ[Ash] Kgeo :=
    { toRingHom := fC
      commutes' := fun r ↦
        (congrFun
          (congrArg DFunLike.coe
            (sourceTensorResidueToKgeo_agree
              ιAsh hιAsh ιBsh hιBsh ιCsh hιCsh)) r).symm }
  Algebra.TensorProduct.lift
    left
    right
    (fun _ _ ↦ Commute.all _ _)

/-- Helper for Chap10 Lemma 10 156 6: the residue map from the source tensor product has the
expected value on pure tensors. -/
private theorem sourceTensorResidueToKgeo_tmul
    (x : Bsh) (y : Csh) :
    let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
    let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
    let _ : Algebra Ash Kgeo :=
      RingHom.toAlgebra ((ιBsh.toRingHom.comp (IsLocalRing.residue Bsh)).comp
        (algebraMap Ash Bsh))
    sourceTensorResidueToKgeo ιAsh hιAsh ιBsh hιBsh ιCsh hιCsh (x ⊗ₜ[Ash] y) =
      ιBsh (IsLocalRing.residue Bsh x) * ιCsh (IsLocalRing.residue Csh y) := by
  -- The definition is a tensor-product lift, so its computation rule gives the value on
  -- generators immediately.
  let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
  let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
  let _ : Algebra Ash Kgeo :=
    RingHom.toAlgebra ((ιBsh.toRingHom.comp (IsLocalRing.residue Bsh)).comp
      (algebraMap Ash Bsh))
  unfold sourceTensorResidueToKgeo
  rw [Algebra.TensorProduct.lift_tmul]
  rfl

/-- Helper for Chap10 Lemma 10 156 6: in the quasi-finite branch, the source tensor product
`B^sh ⊗[A^sh] C^sh` is local for the algebra structures determined by the common geometric
point. -/
private theorem sourceTensor_isLocalRing_of_quasiFiniteAt
    (hB : Algebra.QuasiFiniteAt A pB) :
    let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
    let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
    let _ : IsLocalHom (algebraMap Ash Bsh) :=
      strictHenselizationComparisonAB_isLocalHom ιAsh hιAsh ιBsh hιBsh
    let _ : IsLocalHom (algebraMap Ash Csh) :=
      strictHenselizationComparisonAC_isLocalHom ιAsh hιAsh ιCsh hιCsh
    IsLocalRing (Bsh ⊗[Ash] Csh) := by
  -- The quasi-finite hypothesis makes the `A^sh → B^sh` comparison integral; the existing tensor
  -- locality theorem then applies with the residue-field equivalence through `Kgeo`.
  let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
  let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
  have hInt : Algebra.IsIntegral Ash Bsh :=
    strictHenselizationComparisonAB_integral_of_quasiFiniteAt
      ιAsh hιAsh ιBsh hιBsh hB
  exact sourceTensor_isLocalRing_of_integral_left
    ιAsh hιAsh ιBsh hιBsh ιCsh hιCsh
    (by
      let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
      exact hInt)

-- Proof sketch: in the quasi-finite case, apply Lemma `10.156.3` to the strict-henselization
-- comparison maps `B^sh → (B ⊗[A] C)^sh` and `C^sh → (B ⊗[A] C)^sh`, then identify the source
-- with the strict henselization of the localized tensor product from Lemma `10.155.12`. For the
-- ind-quasi-finite cases, pass to filtered colimits through
-- `RingHom.toMorphismProperty RingHom.QuasiFinite`.
-- The source lemma also includes the integral case in the main statement, so the public owner
-- theorem here keeps that fourth alternative in the primary hypothesis rather than as a later
-- corollary.
section

/-- Lemma 10.156.6: for strict henselizations at primes determined by one common geometric point
of `B ⊗[A] C`, the canonical map
`B^sh ⊗[A^sh] C^sh → (B ⊗[A] C)^sh`
is bijective if `A → B` is quasi-finite at `pB`, or `B` is a filtered colimit of quasi-finite
`A`-algebras, or `B_(pB)` is a filtered colimit of quasi-finite `A_(pA)`-algebras, or `A → B`
is integral. -/
@[stacks 0GIP]
private theorem strictHenselizationTensorBaseChangeMap_bijectiveCore
    (hB :
      Algebra.QuasiFiniteAt A pB ∨
        (algebraMap A B).IsFilteredColimitOfQuasiFinite ∨
        RingHom.IsFilteredColimitOfQuasiFinite
          (Localization.localRingHom pA pB (algebraMap A B) (pB.over_def pA)) ∨
        Algebra.IsIntegral A B) :
    Function.Bijective tensorBaseChangeMapCore := by
  -- Route correction: the previous ad hoc common-prime route stalled before producing common
  -- strict-henselization owners. The verified prefix below records the quasi-finite branch's
  -- source-locality input; the remaining blocker is a canonical common-base owner for both this
  -- source tensor product and `D^sh`, together with the generator-level identification of the
  -- resulting uniqueness comparison with `tensorBaseChangeMapCore`.
  have hqfSourceLocal (hqf : Algebra.QuasiFiniteAt A pB) :
      let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
      let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
      let _ : IsLocalHom (algebraMap Ash Bsh) :=
        strictHenselizationComparisonAB_isLocalHom ιAsh hιAsh ιBsh hιBsh
      let _ : IsLocalHom (algebraMap Ash Csh) :=
        strictHenselizationComparisonAC_isLocalHom ιAsh hιAsh ιCsh hιCsh
      IsLocalRing (Bsh ⊗[Ash] Csh) :=
    sourceTensor_isLocalRing_of_quasiFiniteAt
      ιAsh hιAsh ιBsh hιBsh ιCsh hιCsh hqf
  -- TODO: prove the transported target-prime/common strict-henselization comparison package from
  -- Lemma 10.155.12, then consume it by strict-henselization uniqueness and tensor-generator
  -- extensionality.
  sorry

/-- The canonical map of Lemma 10.156.6 is an algebra isomorphism. -/
private noncomputable def strictHenselizationTensorBaseChangeIsoCore
    (hB :
      Algebra.QuasiFiniteAt A pB ∨
        (algebraMap A B).IsFilteredColimitOfQuasiFinite ∨
        RingHom.IsFilteredColimitOfQuasiFinite
          (Localization.localRingHom pA pB (algebraMap A B) (pB.over_def pA)) ∨
        Algebra.IsIntegral A B) :=
  letI : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
  letI : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
  letI : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
  AlgEquiv.ofBijective
    tensorBaseChangeMapCore <|
    strictHenselizationTensorBaseChangeMap_bijectiveCore
      ιAsh hιAsh ιBsh hιBsh ιCsh hιCsh ιDsh hιDsh hB

end

section

-- Proof sketch: specialize the full source-faithful disjunction from Lemma `10.156.6`.
/-- Companion specialization of Lemma 10.156.6 to the quasi-finite and filtered-colimit cases. -/
private theorem strictHenselizationTensorBaseChangeMap_bijective_of_quasiFinite_or_colimitCore
    (hB :
      Algebra.QuasiFiniteAt A pB ∨
        (algebraMap A B).IsFilteredColimitOfQuasiFinite ∨
        RingHom.IsFilteredColimitOfQuasiFinite
          (Localization.localRingHom pA pB (algebraMap A B) (pB.over_def pA))) :
    Function.Bijective tensorBaseChangeMapCore := by
  -- Embed the three-way specialization into the four-way statement by choosing the corresponding
  -- branch and leaving the integral alternative unused.
  apply strictHenselizationTensorBaseChangeMap_bijectiveCore
    ιAsh hιAsh ιBsh hιBsh ιCsh hιCsh ιDsh hιDsh
  rcases hB with hqf | hcolim | hlocalColim
  · exact Or.inl hqf
  · exact Or.inr (Or.inl hcolim)
  · exact Or.inr (Or.inr (Or.inl hlocalColim))

/-- Algebra-isomorphism form of the quasi-finite/filtered-colimit specialization. -/
private noncomputable def strictHenselizationTensorBaseChangeIso_of_quasiFinite_or_colimitCore
    (hB :
      Algebra.QuasiFiniteAt A pB ∨
        (algebraMap A B).IsFilteredColimitOfQuasiFinite ∨
        RingHom.IsFilteredColimitOfQuasiFinite
          (Localization.localRingHom pA pB (algebraMap A B) (pB.over_def pA))) :=
  letI : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
  letI : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
  letI : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
  AlgEquiv.ofBijective
    tensorBaseChangeMapCore <|
    strictHenselizationTensorBaseChangeMap_bijective_of_quasiFinite_or_colimitCore
      ιAsh hιAsh ιBsh hιBsh ιCsh hιCsh ιDsh hιDsh hB

end

section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C]
variable {pA : Ideal A} [pA.IsPrime]
variable {pB : Ideal B} [pB.IsPrime] [pB.LiesOver pA]
variable (pC : Ideal C) [pC.IsPrime]
variable (pD : Ideal (B ⊗[A] C)) [pD.IsPrime] [pD.LiesOver pB] [pD.LiesOver pC]
variable {Ash Bsh Csh Dsh : Type u}
variable [CommRing Ash] [CommRing Bsh] [CommRing Csh] [CommRing Dsh]
variable [Algebra (Localization.AtPrime pA) Ash]
variable [IsStrictHenselizationOf (Localization.AtPrime pA) Ash]
variable [Algebra (Localization.AtPrime pB) Bsh]
variable [IsStrictHenselizationOf (Localization.AtPrime pB) Bsh]
variable [Algebra (Localization.AtPrime pC) Csh]
variable [IsStrictHenselizationOf (Localization.AtPrime pC) Csh]
variable [Algebra (Localization.AtPrime pD) Dsh]
variable [IsStrictHenselizationOf (Localization.AtPrime pD) Dsh]
variable (Kgeo : Type u) [Field Kgeo]
variable [Algebra (Ideal.ResidueField pD) Kgeo]

/-
The public owner surface keeps the common geometric-point data explicit. The actual construction is
the unchanged internal core above.
-/
noncomputable def strictHenselizationTensorBaseChangeMap
    (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
    (hιAsh :
      ιAsh.toRingHom.comp
          (IsLocalRing.ResidueField.map (algebraMap (Localization.AtPrime pA) Ash)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
            (pD_over_def_pA pA pB pD)))
    (ιBsh : IsLocalRing.ResidueField Bsh ≃+* Kgeo)
    (hιBsh :
      ιBsh.toRingHom.comp
          (IsLocalRing.ResidueField.map (algebraMap (Localization.AtPrime pB) Bsh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB)))
    (ιCsh : IsLocalRing.ResidueField Csh ≃+* Kgeo)
    (hιCsh :
      ιCsh.toRingHom.comp
          (IsLocalRing.ResidueField.map (algebraMap (Localization.AtPrime pC) Csh)) =
        (algebraMap (Ideal.ResidueField pD) Kgeo).comp
          (Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC)))
    (ιDsh : IsLocalRing.ResidueField Dsh ≃+* Kgeo)
    (hιDsh :
      ιDsh.toRingHom.comp
          (IsLocalRing.ResidueField.map (algebraMap (Localization.AtPrime pD) Dsh)) =
        algebraMap (Ideal.ResidueField pD) Kgeo) :=
  let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
  let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
  let _ : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
  strictHenselizationTensorBaseChangeMapCore
    ιAsh hιAsh ιBsh hιBsh ιCsh hιCsh ιDsh hιDsh

attribute [irreducible] strictHenselizationTensorBaseChangeMap

section CommonGeometricPoint

variable (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
variable
  (hιAsh :
    ιAsh.toRingHom.comp
        (IsLocalRing.ResidueField.map (algebraMap (Localization.AtPrime pA) Ash)) =
      (algebraMap (Ideal.ResidueField pD) Kgeo).comp
        (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
          (pD_over_def_pA pA pB pD)))
variable (ιBsh : IsLocalRing.ResidueField Bsh ≃+* Kgeo)
variable
  (hιBsh :
    ιBsh.toRingHom.comp
        (IsLocalRing.ResidueField.map (algebraMap (Localization.AtPrime pB) Bsh)) =
      (algebraMap (Ideal.ResidueField pD) Kgeo).comp
        (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB)))
variable (ιCsh : IsLocalRing.ResidueField Csh ≃+* Kgeo)
variable
  (hιCsh :
    ιCsh.toRingHom.comp
        (IsLocalRing.ResidueField.map (algebraMap (Localization.AtPrime pC) Csh)) =
      (algebraMap (Ideal.ResidueField pD) Kgeo).comp
        (Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC)))
variable (ιDsh : IsLocalRing.ResidueField Dsh ≃+* Kgeo)
variable
  (hιDsh :
    ιDsh.toRingHom.comp
        (IsLocalRing.ResidueField.map (algebraMap (Localization.AtPrime pD) Dsh)) =
      algebraMap (Ideal.ResidueField pD) Kgeo)

private noncomputable abbrev tensorBaseChangeMap :=
  let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
  let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
  let _ : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
  (strictHenselizationTensorBaseChangeMap
    pC pD Kgeo ιAsh hιAsh ιBsh hιBsh ιCsh hιCsh ιDsh hιDsh :
      Bsh ⊗[Ash] Csh →ₐ[Ash] Dsh)

/-- Lemma 10.156.6: for strict henselizations at primes determined by one common geometric point
of `B ⊗[A] C`, the canonical map
`B^sh ⊗[A^sh] C^sh → (B ⊗[A] C)^sh`
is bijective if `A → B` is quasi-finite at `pB`, or `B` is a filtered colimit of quasi-finite
`A`-algebras, or `B_(pB)` is a filtered colimit of quasi-finite `A_(pA)`-algebras, or `A → B`
is integral. -/
@[stacks 0GIP]
theorem strictHenselizationTensorBaseChangeMap_bijective
    (hB :
      Algebra.QuasiFiniteAt A pB ∨
        (algebraMap A B).IsFilteredColimitOfQuasiFinite ∨
        RingHom.IsFilteredColimitOfQuasiFinite
          (Localization.localRingHom pA pB (algebraMap A B) (pB.over_def pA)) ∨
        Algebra.IsIntegral A B) :
    Function.Bijective
      (tensorBaseChangeMap pC pD Kgeo ιAsh hιAsh ιBsh hιBsh ιCsh hιCsh ιDsh hιDsh) := by
  have hB' :
      Algebra.QuasiFiniteAt A pB ∨
        (algebraMap A B).IsFilteredColimitOfQuasiFinite ∨
        RingHom.IsFilteredColimitOfQuasiFinite
          (Localization.localRingHom pA pB (algebraMap A B) (pB.over_def pA)) ∨
        Algebra.IsIntegral A B := by
    simpa [RingHom.IsFilteredColimitOfQuasiFinite] using hB
  unfold tensorBaseChangeMap
  unfold strictHenselizationTensorBaseChangeMap
  simpa [strictHenselizationTensorBaseChangeMapCore] using
    strictHenselizationTensorBaseChangeMap_bijectiveCore
      ιAsh hιAsh ιBsh hιBsh ιCsh hιCsh ιDsh hιDsh hB'

/-- The canonical map of Lemma 10.156.6 is an algebra isomorphism. -/
noncomputable def strictHenselizationTensorBaseChangeIso
    (hB :
      Algebra.QuasiFiniteAt A pB ∨
        (algebraMap A B).IsFilteredColimitOfQuasiFinite ∨
        RingHom.IsFilteredColimitOfQuasiFinite
          (Localization.localRingHom pA pB (algebraMap A B) (pB.over_def pA)) ∨
        Algebra.IsIntegral A B) :=
  letI : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
  letI : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
  letI : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
  AlgEquiv.ofBijective
    (tensorBaseChangeMap pC pD Kgeo ιAsh hιAsh ιBsh hιBsh ιCsh hιCsh ιDsh hιDsh)
    (strictHenselizationTensorBaseChangeMap_bijective
      pC pD Kgeo ιAsh hιAsh ιBsh hιBsh ιCsh hιCsh ιDsh hιDsh hB)

end CommonGeometricPoint

section CommonGeometricPoint

variable (ιAsh : IsLocalRing.ResidueField Ash ≃+* Kgeo)
variable
  (hιAsh :
    ιAsh.toRingHom.comp
        (IsLocalRing.ResidueField.map (algebraMap (Localization.AtPrime pA) Ash)) =
      (algebraMap (Ideal.ResidueField pD) Kgeo).comp
        (Ideal.ResidueField.map pA pD (algebraMap A (B ⊗[A] C))
          (pD_over_def_pA pA pB pD)))
variable (ιBsh : IsLocalRing.ResidueField Bsh ≃+* Kgeo)
variable
  (hιBsh :
    ιBsh.toRingHom.comp
        (IsLocalRing.ResidueField.map (algebraMap (Localization.AtPrime pB) Bsh)) =
      (algebraMap (Ideal.ResidueField pD) Kgeo).comp
        (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB)))
variable (ιCsh : IsLocalRing.ResidueField Csh ≃+* Kgeo)
variable
  (hιCsh :
    ιCsh.toRingHom.comp
        (IsLocalRing.ResidueField.map (algebraMap (Localization.AtPrime pC) Csh)) =
      (algebraMap (Ideal.ResidueField pD) Kgeo).comp
        (Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC)))
variable (ιDsh : IsLocalRing.ResidueField Dsh ≃+* Kgeo)
variable
  (hιDsh :
    ιDsh.toRingHom.comp
        (IsLocalRing.ResidueField.map (algebraMap (Localization.AtPrime pD) Dsh)) =
      algebraMap (Ideal.ResidueField pD) Kgeo)

private noncomputable abbrev tensorBaseChangeMap_qf :=
  let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
  let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
  let _ : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
  (strictHenselizationTensorBaseChangeMap
    pC pD Kgeo ιAsh hιAsh ιBsh hιBsh ιCsh hιCsh ιDsh hιDsh :
      Bsh ⊗[Ash] Csh →ₐ[Ash] Dsh)

/-- Companion specialization of Lemma 10.156.6 to the quasi-finite and filtered-colimit cases. -/
theorem strictHenselizationTensorBaseChangeMap_bijective_of_quasiFinite_or_colimit
    (hB :
      Algebra.QuasiFiniteAt A pB ∨
        (algebraMap A B).IsFilteredColimitOfQuasiFinite ∨
        RingHom.IsFilteredColimitOfQuasiFinite
          (Localization.localRingHom pA pB (algebraMap A B) (pB.over_def pA))) :
    Function.Bijective
      (tensorBaseChangeMap_qf pC pD Kgeo ιAsh hιAsh ιBsh hιBsh ιCsh hιCsh ιDsh hιDsh) := by
  have hB' :
      Algebra.QuasiFiniteAt A pB ∨
        (algebraMap A B).IsFilteredColimitOfQuasiFinite ∨
        RingHom.IsFilteredColimitOfQuasiFinite
          (Localization.localRingHom pA pB (algebraMap A B) (pB.over_def pA)) := by
    simpa [RingHom.IsFilteredColimitOfQuasiFinite] using hB
  unfold tensorBaseChangeMap_qf
  unfold strictHenselizationTensorBaseChangeMap
  simpa [strictHenselizationTensorBaseChangeMapCore] using
    strictHenselizationTensorBaseChangeMap_bijective_of_quasiFinite_or_colimitCore
      ιAsh hιAsh ιBsh hιBsh ιCsh hιCsh ιDsh hιDsh hB'

/-- Algebra-isomorphism form of the quasi-finite/filtered-colimit specialization. -/
noncomputable def strictHenselizationTensorBaseChangeIso_of_quasiFinite_or_colimit
    (hB :
      Algebra.QuasiFiniteAt A pB ∨
        (algebraMap A B).IsFilteredColimitOfQuasiFinite ∨
        RingHom.IsFilteredColimitOfQuasiFinite
          (Localization.localRingHom pA pB (algebraMap A B) (pB.over_def pA))) :=
  letI : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
  letI : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
  letI : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
  AlgEquiv.ofBijective
    (tensorBaseChangeMap_qf pC pD Kgeo ιAsh hιAsh ιBsh hιBsh ιCsh hιCsh ιDsh hιDsh)
    (strictHenselizationTensorBaseChangeMap_bijective_of_quasiFinite_or_colimit
      pC pD Kgeo ιAsh hιAsh ιBsh hιBsh ιCsh hιCsh ιDsh hιDsh hB)

end CommonGeometricPoint

end

end
