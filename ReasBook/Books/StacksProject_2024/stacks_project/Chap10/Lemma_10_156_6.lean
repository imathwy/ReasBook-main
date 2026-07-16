import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_155_12

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

include pB in
local instance :
    let _ : Algebra Ap Dp := algebraApDp pA pB pD
    IsLocalHom (algebraMap Ap Dp) := by
  let _ : Algebra Ap Dp := algebraApDp pA pB pD
  simpa [RingHom.algebraMap_toAlgebra] using
    Localization.isLocalHom_localRingHom pA pD (algebraMap A (B ⊗[A] C))
      (pD_over_def_pA pA pB pD)

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
          (Ideal.ResidueField.map pA pB (algebraMap A B) (pB.over_def pA)) := by
    sorry
  let _ : Algebra Ap Bsh := algebraApBsh
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
          (Ideal.ResidueField.map pA pC (algebraMap A C) (pC_over_def_pA pA pB pC pD)) := by
    sorry
  let _ : pD.LiesOver pA := pD_liesOver_pA pA pB pD
  let _ : pC.LiesOver pA := pC_liesOver_pA pA pB pC pD
  let _ : Algebra Ap Cp := algebraApCp pA pB pC pD
  have hlocalCp : IsLocalHom (algebraMap Ap Cp) := by
    simpa [RingHom.algebraMap_toAlgebra] using
      Localization.isLocalHom_localRingHom pA pC (algebraMap A C) (pC_over_def_pA pA pB pC pD)
  let _ : IsLocalHom (algebraMap Ap Cp) := hlocalCp
  let _ : Algebra Ap Csh := by
    let _ : Algebra Ap Cp := algebraApCp pA pB pC pD
    exact ((algebraMap Cp Csh).comp (algebraMap Ap Cp)).toAlgebra
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
            (pD_over_def_pA pA pB pD)) := by
    sorry
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
          (Ideal.ResidueField.map pB pD (algebraMap B (B ⊗[A] C)) (pD.over_def pB)) := by
    sorry
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
          (Ideal.ResidueField.map pC pD (algebraMap C (B ⊗[A] C)) (pD.over_def pC)) := by
    sorry
  let _ : Algebra Cp Dsh := algebraCpDsh
  (strictHenselizationComparison pC pD φCD hφCD : Csh →ₐ[Cp] Dsh).toRingHom

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

/-
The canonical map `B^sh ⊗[A^sh] C^sh → (B ⊗[A] C)^sh` attached to one common geometric point
of `B ⊗[A] C`, obtained from one common target field for the four residue fields via the canonical
owner `strictHenselizationComparison`.
-/
private noncomputable def strictHenselizationTensorBaseChangeMapCore :
    let _ : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
    let _ : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
    let _ : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
    Bsh ⊗[Ash] Csh →ₐ[Ash] Dsh := by
  letI : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
  letI : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
  letI : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
  let comparisonBD : Bsh →+* Dsh :=
    strictHenselizationComparisonBD pB pD ιBsh hιBsh ιDsh hιDsh
  let comparisonCD : Csh →+* Dsh :=
    strictHenselizationComparisonCD pC pD ιCsh hιCsh ιDsh hιDsh
  let hcompABD :
      comparisonBD.comp (algebraMap Ash Bsh) = algebraMap Ash Dsh := by
    sorry
  let hcompACD :
      comparisonCD.comp (algebraMap Ash Csh) = algebraMap Ash Dsh := by
    sorry
  let comparisonBDOverAsh : Bsh →ₐ[Ash] Dsh :=
    { toRingHom := comparisonBD
      commutes' := by
        intro r
        simpa [RingHom.algebraMap_toAlgebra] using
          congrArg (fun f ↦ f r) hcompABD }
  let comparisonCDOverAsh : Csh →ₐ[Ash] Dsh :=
    { toRingHom := comparisonCD
      commutes' := by
        intro r
        simpa [RingHom.algebraMap_toAlgebra] using
          congrArg (fun f ↦ f r) hcompACD }
  exact Algebra.TensorProduct.productMap comparisonBDOverAsh comparisonCDOverAsh

attribute [irreducible] strictHenselizationTensorBaseChangeMapCore

local notation "tensorBaseChangeMapCore" =>
  (strictHenselizationTensorBaseChangeMapCore
    ιAsh hιAsh ιBsh hιBsh ιCsh hιCsh ιDsh hιDsh)

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
private theorem strictHenselizationTensorBaseChangeMap_bijectiveCore
    (hB :
      Algebra.QuasiFiniteAt A pB ∨
        (algebraMap A B).IsFilteredColimitOfQuasiFinite ∨
        RingHom.IsFilteredColimitOfQuasiFinite
          (Localization.localRingHom pA pB (algebraMap A B) (pB.over_def pA)) ∨
        Algebra.IsIntegral A B) :
    Function.Bijective tensorBaseChangeMapCore := by
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
  sorry

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
        algebraMap (Ideal.ResidueField pD) Kgeo) := by
  letI : Algebra Ash Bsh := algebraAshBsh pA pB pD ιAsh hιAsh ιBsh hιBsh
  letI : Algebra Ash Csh := algebraAshCsh pA pB pC pD ιAsh hιAsh ιCsh hιCsh
  letI : Algebra Ash Dsh := algebraAshDsh pA pB pD ιAsh hιAsh ιDsh hιDsh
  exact strictHenselizationTensorBaseChangeMapCore
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
