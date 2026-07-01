import Mathlib
import Serre.Chap14.Corollary_14_14_4_4
import Serre.Chap14.Lemma_14_14_4_2

open scoped MonoidAlgebra

universe u v x y

section

variable {A : Type u} [CommRing A] [IsLocalRing A]

namespace Representation

section ResidueFieldLift

variable {G : Type v} [Group G]
variable {V : Type x} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]

local notation "k" => IsLocalRing.ResidueField A
noncomputable local instance residueFieldLiftResidueFieldModule : Module A k :=
  Module.compHom k (algebraMap A k)
local instance residueFieldLiftResidueFieldScalarTower : IsScalarTower A k k :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
noncomputable local instance residueFieldLiftTargetModule : Module A V :=
  Module.compHom V (algebraMap A k)
local instance residueFieldLiftTargetScalarTower : IsScalarTower A k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- A representation over the residue field lifts to a free finitely generated `A`-representation
when the chosen reduction map is the Chapter `14` owner
`LinearMap.IsResidueFieldReduction`, viewed through the source-facing Chapter `15`
representation data. This remains a bridge/view declaration rather than a second owner. -/
abbrev IsResidueFieldLift
    (ρl : Representation k G V)
    {P : Type y} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    (ρA : Representation A G P)
    (red : P →ₗ[A] V) : Prop :=
  letI : Module A[G] P := Module.compHom P ρA.asAlgebraHom.toRingHom
  letI : IsScalarTower A A[G] P :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρA.asAlgebraHom (algebraMap A A[G] a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA.asAlgebraHom.commutes a) x
  letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
  letI : IsScalarTower k k[G] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρl.asAlgebraHom.commutes a) x
  red.IsResidueFieldReduction G

/-- Helper for Exercise 15-15.5-3: under the restricted `H`-action `ρA.comp f`, the generator
`single h 1` acts as the original `G`-action evaluated at `f h`. -/
private lemma restricted_source_single_smul_eq_comp_apply
    {H : Type*} [Group H]
    {P : Type y} [AddCommGroup P] [Module A P]
    (ρA : Representation A G P) (f : H →* G) (h : H) (x : P) :
    letI : Module A[H] P := Module.compHom P (Representation.asAlgebraHom (ρA.comp f)).toRingHom
    (MonoidAlgebra.single h (1 : A)) • x = ρA (f h) x := by
  change (Representation.asAlgebraHom (ρA.comp f) (MonoidAlgebra.single h 1)) x = _
  simp [Representation.asAlgebraHom_single]

/-- Helper for Exercise 15-15.5-3: under the restricted residue-field `H`-action `ρl.comp f`,
the generator `single h 1` acts as the original `G`-action evaluated at `f h`. -/
private lemma restricted_target_single_smul_eq_comp_apply
    {H : Type*} [Group H]
    (ρl : Representation k G V) (f : H →* G) (h : H) (x : V) :
    letI : Module k[H] V := Module.compHom V (Representation.asAlgebraHom (ρl.comp f)).toRingHom
    (MonoidAlgebra.single h (1 : k)) • x = ρl (f h) x := by
  change (Representation.asAlgebraHom (ρl.comp f) (MonoidAlgebra.single h 1)) x = _
  simp [Representation.asAlgebraHom_single]

namespace LinearMap.IsResidueFieldReduction

/-- Helper for Exercise 15-15.5-3: the Chapter `14` residue-field reduction owner is preserved
when both source and target actions are restricted along `f : H →* G`. -/
theorem comp_monoidHom
    {H : Type*} [Group H]
    {ρl : Representation k G V}
    {P : Type y} [AddCommGroup P] [Module A P]
    {ρA : Representation A G P}
    {red : P →ₗ[A] V}
    (h :
      letI : Module A[G] P := Module.compHom P ρA.asAlgebraHom.toRingHom
      letI : IsScalarTower A A[G] P :=
        IsScalarTower.of_algebraMap_smul fun a x ↦ by
          change ρA.asAlgebraHom (algebraMap A A[G] a) x = a • x
          simp [Algebra.smul_def]
      letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
      letI : IsScalarTower k k[G] V :=
        IsScalarTower.of_algebraMap_smul fun a x ↦ by
          change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
          simp [Algebra.smul_def]
      red.IsResidueFieldReduction G)
    (f : H →* G) :
    letI : Module A[H] P := Module.compHom P (Representation.asAlgebraHom (ρA.comp f)).toRingHom
    letI : IsScalarTower A A[H] P :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change (Representation.asAlgebraHom (ρA.comp f)) (algebraMap A A[H] a) x = a • x
        simp [Algebra.smul_def]
    letI : Module k[H] V := Module.compHom V (Representation.asAlgebraHom (ρl.comp f)).toRingHom
    letI : IsScalarTower k k[H] V :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change (Representation.asAlgebraHom (ρl.comp f)) (algebraMap k k[H] a) x = a • x
        simp [Algebra.smul_def]
    red.IsResidueFieldReduction H := by
  letI : Module A[H] P := Module.compHom P (Representation.asAlgebraHom (ρA.comp f)).toRingHom
  letI : IsScalarTower A A[H] P :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change (Representation.asAlgebraHom (ρA.comp f)) (algebraMap A A[H] a) x = a • x
      simp [Algebra.smul_def]
  letI : Module k[H] V := Module.compHom V (Representation.asAlgebraHom (ρl.comp f)).toRingHom
  letI : IsScalarTower k k[H] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change (Representation.asAlgebraHom (ρl.comp f)) (algebraMap k k[H] a) x = a • x
      simp [Algebra.smul_def]
  letI : Module A[G] P := Module.compHom P ρA.asAlgebraHom.toRingHom
  letI : IsScalarTower A A[G] P :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρA.asAlgebraHom (algebraMap A A[G] a) x = a • x
      simp [Algebra.smul_def]
  letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
  letI : IsScalarTower k k[G] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
      simp [Algebra.smul_def]
  letI : Module A[G] V := Module.compHom V (MonoidAlgebra.mapRingHom G (algebraMap A k))
  letI : IsScalarTower A A[G] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change
        (MonoidAlgebra.mapRingHom G (algebraMap A k))
            (MonoidAlgebra.single (1 : G) a) • x =
          a • x
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) =
            algebraMap k k[G] (IsLocalRing.residue A a) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) • x
            = (IsLocalRing.residue A a) • x := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul k[G] (IsLocalRing.residue A a) x)
        _ = a • x := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul k a x)
  constructor
  · exact h.1
  ·
    refine Representation.IsIntertwiningMap.mk ?_
    intro h' x
    letI : Module A[H] V := Module.compHom V (MonoidAlgebra.mapRingHom H (algebraMap A k))
    letI : IsScalarTower A A[H] V :=
      IsScalarTower.of_algebraMap_smul fun a y ↦ by
        change
          (MonoidAlgebra.mapRingHom H (algebraMap A k))
              (MonoidAlgebra.single (1 : H) a) • y =
            a • y
        rw [MonoidAlgebra.mapRingHom_single]
        have hsingle :
            MonoidAlgebra.single (1 : H) (IsLocalRing.residue A a) =
              algebraMap k k[H] (IsLocalRing.residue A a) := by
          rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
          simp
        calc
          MonoidAlgebra.single (1 : H) (IsLocalRing.residue A a) • y
              = (IsLocalRing.residue A a) • y := by
                  simpa only [hsingle] using
                    (IsScalarTower.algebraMap_smul k[H] (IsLocalRing.residue A a) y)
          _ = a • y := by
                simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                  (IsScalarTower.algebraMap_smul k a y)
    let ρsrcH : Representation A H P := Representation.ofModule' P
    let ρtgtH : Representation A H V := Representation.ofModule' V
    have hsrc :
        ρsrcH h' x = ρA (f h') x := by
      simpa [Representation.ofModule', MonoidAlgebra.of_apply] using
        restricted_source_single_smul_eq_comp_apply (ρA := ρA) (f := f) (h := h') (x := x)
    have htgt :
        ρtgtH h' (red x) = ρl (f h') (red x) := by
      change (MonoidAlgebra.of A H h') • red x = _
      rw [MonoidAlgebra.of_apply]
      change
        (MonoidAlgebra.mapRingHom H (algebraMap A k) (MonoidAlgebra.single h' (1 : A))) • red x = _
      rw [MonoidAlgebra.mapRingHom_single]
      simpa using
        restricted_target_single_smul_eq_comp_apply (ρl := ρl) (f := f) (h := h') (x := red x)
    have hsrcG :
        (MonoidAlgebra.single (f h') (1 : A)) • x = ρA (f h') x := by
      change (Representation.asAlgebraHom ρA (MonoidAlgebra.single (f h') 1)) x = _
      simp [Representation.asAlgebraHom_single]
    have htgtG :
        (MonoidAlgebra.single (f h') (1 : k)) • red x = ρl (f h') (red x) := by
      change (Representation.asAlgebraHom ρl (MonoidAlgebra.single (f h') 1)) (red x) = _
      simp [Representation.asAlgebraHom_single]
    have hG :
        red ((MonoidAlgebra.single (f h') (1 : A)) • x) =
          (MonoidAlgebra.single (f h') (1 : k)) • red x := by
      simpa [MonoidAlgebra.of_apply] using h.map_monoidAlgebra_of (f h') x
    have hcalc : red (ρsrcH h' x) = ρtgtH h' (red x) := by
      calc
        red (ρsrcH h' x)
          = red (ρA (f h') x) := by rw [hsrc]
        _ = ρl (f h') (red x) := by
            rw [← hsrcG, hG, htgtG]
        _ = ρtgtH h' (red x) := by
            rw [← htgt]
    simpa [ρsrcH, ρtgtH] using hcalc

end LinearMap.IsResidueFieldReduction

/-- A residue-field lift remains a residue-field lift after restricting the group action along a
group homomorphism. -/
theorem isResidueFieldLift_comp
    {H : Type*} [Group H]
    {ρl : Representation k G V}
    {P : Type y} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    {ρA : Representation A G P}
    {red : P →ₗ[A] V}
    (h : IsResidueFieldLift ρl ρA red) (f : H →* G) :
    IsResidueFieldLift (ρl.comp f) (ρA.comp f) red := by
  simpa [IsResidueFieldLift] using
    LinearMap.IsResidueFieldReduction.comp_monoidHom
      (A := A) (G := G) (V := V) (ρl := ρl) (ρA := ρA) (red := red) h f

end ResidueFieldLift

end Representation

end
