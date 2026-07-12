import StacksProject_2024.Chap10.Definition_10_134_1
import StacksProject_2024.Chap10.Lemma_10_131_5
import Mathlib.Tactic.StacksAttribute

open Algebra
open Algebra.Extension
open Algebra.Generators
open CategoryTheory
open CategoryTheory.Limits
open scoped NaiveCotangent

universe u

noncomputable section

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {R S : I → Type u}
variable [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, Algebra (R i) (S i)]
variable {ρ : ∀ i j, i ≤ j → R i →+* R j}
variable {σ : ∀ i j, i ≤ j → S i →+* S j}
variable (hcomm :
  ∀ ⦃i j : I⦄ (h : i ≤ j),
    (algebraMap (R j) (S j)).comp (ρ i j h) =
      (σ i j h).comp (algebraMap (R i) (S i)))

local notation "R∞" => Ring.DirectLimit R (fun i j h ↦ ρ i j h)
local notation "S∞" => Ring.DirectLimit S (fun i j h ↦ σ i j h)

/-- Helper for Lemma 10.134.9: the induced direct-limit target ring carries its canonical
`R∞`-algebra structure. -/
private instance directLimitAlgebra : Algebra R∞ S∞ :=
  (Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).toAlgebra

/-- Helper for Lemma 10.134.9: the canonical map from a stage ring into the source direct limit. -/
private abbrev stageBaseMap (i : I) : R i →+* R∞ :=
  Ring.DirectLimit.of R (fun i j h ↦ ρ i j h) i

/-- Helper for Lemma 10.134.9: the canonical map from a stage target ring into the target direct
limit. -/
private abbrev stageTargetMap (i : I) : S i →+* S∞ :=
  Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i

/-- Helper for Lemma 10.134.9: the stage structure map to `S∞` factors through later stages. -/
private theorem stageTargetMap_comp {i j : I} (h : i ≤ j) :
    (Ring.DirectLimit.of S (fun i j h ↦ σ i j h) j).comp (σ i j h) =
      Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i := by
  ext x
  change Ring.DirectLimit.of S (fun i j h ↦ σ i j h) j (σ i j h x) =
    Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i x
  simp [Ring.DirectLimit.of_f h x]

/-- Helper for Lemma 10.134.9: the stage structure map to `R∞` factors through later stages. -/
private theorem stageBaseMap_comp {i j : I} (h : i ≤ j) :
    (Ring.DirectLimit.of R (fun i j h ↦ ρ i j h) j).comp (ρ i j h) =
      Ring.DirectLimit.of R (fun i j h ↦ ρ i j h) i := by
  -- This is the base-ring analogue of `stageTargetMap_comp`.
  ext x
  change Ring.DirectLimit.of R (fun i j h ↦ ρ i j h) j (ρ i j h x) =
    Ring.DirectLimit.of R (fun i j h ↦ ρ i j h) i x
  simp [Ring.DirectLimit.of_f h x]

/-- Helper for Lemma 10.134.9: the stage square commutes with the induced map on ring direct
limits. -/
private theorem directLimit_square
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :
    (Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).comp
        (Ring.DirectLimit.of R (fun i j h ↦ ρ i j h) i) =
      (Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i).comp (algebraMap (R i) (S i)) := by
  ext x
  simp

/-- Helper for Lemma 10.134.9: the canonical self-presentation maps compose to the direct-limit
target map. -/
private theorem selfPresentation_defaultHom_comp
    {i j : I} (h : i ≤ j) :
    let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
    let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
    let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
    let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
    let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
    let _ : Algebra (R i) S∞ :=
      ((Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ hij ↦ hcomm hij).comp
        (stageBaseMap (ρ := ρ) i)).toAlgebra
    let _ : Algebra (R j) R∞ := (stageBaseMap (ρ := ρ) j).toAlgebra
    let _ : Algebra (S j) S∞ := (stageTargetMap (σ := σ) j).toAlgebra
    let _ : Algebra (R j) S∞ :=
      ((Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ hij ↦ hcomm hij).comp
        (stageBaseMap (ρ := ρ) j)).toAlgebra
    let _ : Algebra R∞ S∞ :=
      (Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ hij ↦ hcomm hij).toAlgebra
    let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
    let _ : IsScalarTower (R i) (R j) R∞ := IsScalarTower.of_algebraMap_eq'
      (stageBaseMap_comp (ρ := ρ) h).symm
    let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R j) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R j) (S j) S∞ :=
      IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm j)
    let _ : IsScalarTower (S i) (S j) S∞ := IsScalarTower.of_algebraMap_eq'
      (stageTargetMap_comp (σ := σ) h).symm
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
    let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
    (Generators.defaultHom Pj Pinf).comp (Generators.defaultHom Pi Pj) =
      Generators.defaultHom Pi Pinf := by
  classical
  let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
  let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
  let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
  let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
  let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
  let _ : Algebra (R i) S∞ :=
    ((Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ hij ↦ hcomm hij).comp
      (stageBaseMap (ρ := ρ) i)).toAlgebra
  let _ : Algebra (R j) R∞ := (stageBaseMap (ρ := ρ) j).toAlgebra
  let _ : Algebra (S j) S∞ := (stageTargetMap (σ := σ) j).toAlgebra
  let _ : Algebra (R j) S∞ :=
    ((Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ hij ↦ hcomm hij).comp
      (stageBaseMap (ρ := ρ) j)).toAlgebra
  let _ : Algebra R∞ S∞ :=
    (Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ hij ↦ hcomm hij).toAlgebra
  let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
  let _ : IsScalarTower (R i) (R j) R∞ := IsScalarTower.of_algebraMap_eq'
    (stageBaseMap_comp (ρ := ρ) h).symm
  let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R j) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R j) (S j) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm j)
  let _ : IsScalarTower (S i) (S j) S∞ := IsScalarTower.of_algebraMap_eq'
    (stageTargetMap_comp (σ := σ) h).symm
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  -- Compare the two generator families on each stage variable `s`.
  ext s m
  have hσ :
      stageTargetMap (σ := σ) j (σ i j h s) =
        stageTargetMap (σ := σ) i s := by
    simpa using DFunLike.congr_fun (stageTargetMap_comp (σ := σ) h) s
  simp [Generators.defaultHom, Generators.Hom.comp]
  exact congrArg
    (fun x : S∞ ↦ MvPolynomial.coeff m (MvPolynomial.X x : Pinf.Ring))
    hσ

/-- Helper for Lemma 10.134.9: the induced extension maps for the canonical self-presentations
compose to the direct-limit extension map. -/
private theorem selfPresentation_defaultHom_toExtensionHom_comp
    {i j : I} (h : i ≤ j) :
    let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
    let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
    let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
    let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
    let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
    let _ : Algebra (R i) S∞ :=
      ((Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ hij ↦ hcomm hij).comp
        (stageBaseMap (ρ := ρ) i)).toAlgebra
    let _ : Algebra (R j) R∞ := (stageBaseMap (ρ := ρ) j).toAlgebra
    let _ : Algebra (S j) S∞ := (stageTargetMap (σ := σ) j).toAlgebra
    let _ : Algebra (R j) S∞ :=
      ((Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ hij ↦ hcomm hij).comp
        (stageBaseMap (ρ := ρ) j)).toAlgebra
    let _ : Algebra R∞ S∞ :=
      (Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ hij ↦ hcomm hij).toAlgebra
    let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
    let _ : IsScalarTower (R i) (R j) R∞ := IsScalarTower.of_algebraMap_eq'
      (stageBaseMap_comp (ρ := ρ) h).symm
    let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) S∞ :=
      IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
    let _ : IsScalarTower (R j) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R j) (S j) S∞ :=
      IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm j)
    let _ : IsScalarTower (S i) (S j) S∞ := IsScalarTower.of_algebraMap_eq'
      (stageTargetMap_comp (σ := σ) h).symm
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
    let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
    (Generators.defaultHom Pj Pinf).toExtensionHom.comp
        (Generators.defaultHom Pi Pj).toExtensionHom =
      (Generators.defaultHom Pi Pinf).toExtensionHom := by
  classical
  let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
  let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
  let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
  let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
  let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
  let _ : Algebra (R i) S∞ :=
    ((Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ hij ↦ hcomm hij).comp
      (stageBaseMap (ρ := ρ) i)).toAlgebra
  let _ : Algebra (R j) R∞ := (stageBaseMap (ρ := ρ) j).toAlgebra
  let _ : Algebra (S j) S∞ := (stageTargetMap (σ := σ) j).toAlgebra
  let _ : Algebra (R j) S∞ :=
    ((Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ hij ↦ hcomm hij).comp
      (stageBaseMap (ρ := ρ) j)).toAlgebra
  let _ : Algebra R∞ S∞ :=
    (Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ hij ↦ hcomm hij).toAlgebra
  let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
  let _ : IsScalarTower (R i) (R j) R∞ := IsScalarTower.of_algebraMap_eq'
    (stageBaseMap_comp (ρ := ρ) h).symm
  let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
  let _ : IsScalarTower (R j) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R j) (S j) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm j)
  let _ : IsScalarTower (S i) (S j) S∞ := IsScalarTower.of_algebraMap_eq'
    (stageTargetMap_comp (σ := σ) h).symm
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  -- Transport the generator-level composition identity through `toExtensionHom`.
  simpa [Generators.Hom.toExtensionHom_comp] using
    congrArg Generators.Hom.toExtensionHom
      (selfPresentation_defaultHom_comp (ρ := ρ) (σ := σ) hcomm h)

/-- Helper for Lemma 10.134.9: the stage-to-stage self-presentation map followed by the
stage-to-target self-presentation map is the direct stage-to-target map on extensions. -/
private theorem selfPresentation_toTarget_extensionHom_comp
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
    let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
    let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
    let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
    let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
    let _ : Algebra (R i) S∞ :=
      ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
        (stageBaseMap (ρ := ρ) i)).toAlgebra
    let _ : Algebra (R j) R∞ := (stageBaseMap (ρ := ρ) j).toAlgebra
    let _ : Algebra (S j) S∞ := (stageTargetMap (σ := σ) j).toAlgebra
    let _ : Algebra (R j) S∞ :=
      ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
        (stageBaseMap (ρ := ρ) j)).toAlgebra
    let _ : Algebra R∞ S∞ :=
      (Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).toAlgebra
    let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
    let _ : IsScalarTower (R i) (R j) R∞ := IsScalarTower.of_algebraMap_eq'
      (stageBaseMap_comp (ρ := ρ) h).symm
    let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) S∞ :=
      IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
    let _ : IsScalarTower (R j) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R j) (S j) S∞ :=
      IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm j)
    let _ : IsScalarTower (S i) (S j) S∞ := IsScalarTower.of_algebraMap_eq'
      (stageTargetMap_comp (σ := σ) h).symm
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
    let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
    let fij : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
    let fjInf : Pj.toExtension.Hom Pinf.toExtension :=
      (Generators.defaultHom Pj Pinf).toExtensionHom
    let fiInf : Pi.toExtension.Hom Pinf.toExtension :=
      (Generators.defaultHom Pi Pinf).toExtensionHom
    fjInf.comp fij = fiInf := by
  let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
  let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
  let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
  let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
  let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
  let _ : Algebra (R i) S∞ :=
    ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
      (stageBaseMap (ρ := ρ) i)).toAlgebra
  let _ : Algebra (R j) R∞ := (stageBaseMap (ρ := ρ) j).toAlgebra
  let _ : Algebra (S j) S∞ := (stageTargetMap (σ := σ) j).toAlgebra
  let _ : Algebra (R j) S∞ :=
    ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
      (stageBaseMap (ρ := ρ) j)).toAlgebra
  let _ : Algebra R∞ S∞ :=
    (Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).toAlgebra
  let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
  let _ : IsScalarTower (R i) (R j) R∞ := IsScalarTower.of_algebraMap_eq'
    (stageBaseMap_comp (ρ := ρ) h).symm
  let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
  let _ : IsScalarTower (R j) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R j) (S j) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm j)
  let _ : IsScalarTower (S i) (S j) S∞ := IsScalarTower.of_algebraMap_eq'
    (stageTargetMap_comp (σ := σ) h).symm
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  let fij : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
  let fjInf : Pj.toExtension.Hom Pinf.toExtension :=
    (Generators.defaultHom Pj Pinf).toExtensionHom
  let fiInf : Pi.toExtension.Hom Pinf.toExtension :=
    (Generators.defaultHom Pi Pinf).toExtensionHom
  -- Collapse the two presentation maps before any cotangent-space or conormal transport.
  simpa [fij, fjInf, fiInf] using
    selfPresentation_defaultHom_toExtensionHom_comp (ρ := ρ) (σ := σ) hcomm h

/-- Helper for Lemma 10.134.9: on cotangent spaces, the stage-to-stage map followed by the
stage-to-target map equals the direct stage-to-target map. -/
private theorem selfPresentation_toTarget_cotangentSpace_map_comp_apply
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j)
    (y : ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension).CotangentSpace) :
    let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
    let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
    let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
    let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
    let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
    let _ : Algebra (R i) S∞ :=
      ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
        (stageBaseMap (ρ := ρ) i)).toAlgebra
    let _ : Algebra (R j) R∞ := (stageBaseMap (ρ := ρ) j).toAlgebra
    let _ : Algebra (S j) S∞ := (stageTargetMap (σ := σ) j).toAlgebra
    let _ : Algebra (R j) S∞ :=
      ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
        (stageBaseMap (ρ := ρ) j)).toAlgebra
    let _ : Algebra R∞ S∞ :=
      (Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).toAlgebra
    let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
    let _ : IsScalarTower (R i) (R j) R∞ := IsScalarTower.of_algebraMap_eq'
      (stageBaseMap_comp (ρ := ρ) h).symm
    let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) S∞ :=
      IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
    let _ : IsScalarTower (R j) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R j) (S j) S∞ :=
      IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm j)
    let _ : IsScalarTower (S i) (S j) S∞ := IsScalarTower.of_algebraMap_eq'
      (stageTargetMap_comp (σ := σ) h).symm
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
    let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
    let fij : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
    let fjInf : Pj.toExtension.Hom Pinf.toExtension :=
      (Generators.defaultHom Pj Pinf).toExtensionHom
    let fiInf : Pi.toExtension.Hom Pinf.toExtension :=
      (Generators.defaultHom Pi Pinf).toExtensionHom
    Extension.CotangentSpace.map fjInf (Extension.CotangentSpace.map fij y) =
      Extension.CotangentSpace.map fiInf y := by
  let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
  let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
  let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
  let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
  let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
  let _ : Algebra (R i) S∞ :=
    ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
      (stageBaseMap (ρ := ρ) i)).toAlgebra
  let _ : Algebra (R j) R∞ := (stageBaseMap (ρ := ρ) j).toAlgebra
  let _ : Algebra (S j) S∞ := (stageTargetMap (σ := σ) j).toAlgebra
  let _ : Algebra (R j) S∞ :=
    ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
      (stageBaseMap (ρ := ρ) j)).toAlgebra
  let _ : Algebra R∞ S∞ :=
    (Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).toAlgebra
  let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
  let _ : IsScalarTower (R i) (R j) R∞ := IsScalarTower.of_algebraMap_eq'
    (stageBaseMap_comp (ρ := ρ) h).symm
  let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
  let _ : IsScalarTower (R j) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R j) (S j) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm j)
  let _ : IsScalarTower (S i) (S j) S∞ := IsScalarTower.of_algebraMap_eq'
    (stageTargetMap_comp (σ := σ) h).symm
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  let fij : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
  let fjInf : Pj.toExtension.Hom Pinf.toExtension :=
    (Generators.defaultHom Pj Pinf).toExtensionHom
  let fiInf : Pi.toExtension.Hom Pinf.toExtension :=
    (Generators.defaultHom Pi Pinf).toExtensionHom
  -- Rewrite the composite as the cotangent-space map of the composed extension hom.
  calc
    Extension.CotangentSpace.map fjInf (Extension.CotangentSpace.map fij y) =
      Extension.CotangentSpace.map (fjInf.comp fij) y := by
        simpa using (Extension.CotangentSpace.map_comp_apply fij fjInf y).symm
    _ = Extension.CotangentSpace.map fiInf y := by
      rw [selfPresentation_toTarget_extensionHom_comp (ρ := ρ) (σ := σ) hcomm h]

/-- Helper for Lemma 10.134.9: on cotangent terms, the stage-to-stage map followed by the
stage-to-target map equals the direct stage-to-target map. -/
private theorem selfPresentation_toTarget_cotangent_map_comp_apply
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j)
    (x : ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension).Cotangent) :
    let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
    let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
    let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
    let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
    let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
    let _ : Algebra (R i) S∞ :=
      ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
        (stageBaseMap (ρ := ρ) i)).toAlgebra
    let _ : Algebra (R j) R∞ := (stageBaseMap (ρ := ρ) j).toAlgebra
    let _ : Algebra (S j) S∞ := (stageTargetMap (σ := σ) j).toAlgebra
    let _ : Algebra (R j) S∞ :=
      ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
        (stageBaseMap (ρ := ρ) j)).toAlgebra
    let _ : Algebra R∞ S∞ :=
      (Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).toAlgebra
    let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
    let _ : IsScalarTower (R i) (R j) R∞ := IsScalarTower.of_algebraMap_eq'
      (stageBaseMap_comp (ρ := ρ) h).symm
    let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) S∞ :=
      IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
    let _ : IsScalarTower (R j) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R j) (S j) S∞ :=
      IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm j)
    let _ : IsScalarTower (S i) (S j) S∞ := IsScalarTower.of_algebraMap_eq'
      (stageTargetMap_comp (σ := σ) h).symm
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
    let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
    let fij : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
    let fjInf : Pj.toExtension.Hom Pinf.toExtension :=
      (Generators.defaultHom Pj Pinf).toExtensionHom
    let fiInf : Pi.toExtension.Hom Pinf.toExtension :=
      (Generators.defaultHom Pi Pinf).toExtensionHom
    Extension.Cotangent.map fjInf (Extension.Cotangent.map fij x) =
      Extension.Cotangent.map fiInf x := by
  let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
  let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
  let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
  let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
  let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
  let _ : Algebra (R i) S∞ :=
    ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
      (stageBaseMap (ρ := ρ) i)).toAlgebra
  let _ : Algebra (R j) R∞ := (stageBaseMap (ρ := ρ) j).toAlgebra
  let _ : Algebra (S j) S∞ := (stageTargetMap (σ := σ) j).toAlgebra
  let _ : Algebra (R j) S∞ :=
    ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
      (stageBaseMap (ρ := ρ) j)).toAlgebra
  let _ : Algebra R∞ S∞ :=
    (Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).toAlgebra
  let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
  let _ : IsScalarTower (R i) (R j) R∞ := IsScalarTower.of_algebraMap_eq'
    (stageBaseMap_comp (ρ := ρ) h).symm
  let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
  let _ : IsScalarTower (R j) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R j) (S j) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm j)
  let _ : IsScalarTower (S i) (S j) S∞ := IsScalarTower.of_algebraMap_eq'
    (stageTargetMap_comp (σ := σ) h).symm
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  let fij : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
  let fjInf : Pj.toExtension.Hom Pinf.toExtension :=
    (Generators.defaultHom Pj Pinf).toExtensionHom
  let fiInf : Pi.toExtension.Hom Pinf.toExtension :=
    (Generators.defaultHom Pi Pinf).toExtensionHom
  -- Rewrite the composite as the conormal map of the composed extension hom.
  calc
    Extension.Cotangent.map fjInf (Extension.Cotangent.map fij x) =
      Extension.Cotangent.map (fjInf.comp fij) x := by
        exact
          (DFunLike.congr_fun
            (Extension.Cotangent.map_comp
              (P := Pi.toExtension) (P' := Pj.toExtension) (P'' := Pinf.toExtension) fij fjInf)
            x).symm
    _ = Extension.Cotangent.map fiInf x := by
      rw [selfPresentation_toTarget_extensionHom_comp (ρ := ρ) (σ := σ) hcomm h]

/-- Helper for Lemma 10.134.9: on self-presentations, the default transition map sends the
canonical cotangent-space basis vector for `s` to the basis vector of its image in the later
stage. -/
private theorem selfPresentation_cotangentSpaceBasis_compatible
    {i j : I} (h : i ≤ j) (s : S i) :
    let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
    let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
    let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
    let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
    let f : Pi.Hom Pj := Generators.defaultHom Pi Pj
    Extension.CotangentSpace.map f.toExtensionHom (Pi.cotangentSpaceBasis s) =
      Pj.cotangentSpaceBasis (σ i j h s) := by
  classical
  let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
  let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
  let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
  let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  let f : Pi.Hom Pj := Generators.defaultHom Pi Pj
  change Extension.CotangentSpace.map f.toExtensionHom (Pi.cotangentSpaceBasis s) =
    Pj.cotangentSpaceBasis (σ i j h s)
  -- Rewrite the source basis vector as `1 ⊗ d[X_s]`, then evaluate the default hom on `X s`.
  have hmap :
      Extension.CotangentSpace.map f.toExtensionHom (Pi.cotangentSpaceBasis s) =
        (algebraMap (S i) (S j) (1 : S i)) ⊗ₜ[Pj.Ring]
          KaehlerDifferential.D (R j) Pj.Ring (f.toExtensionHom.toAlgHom (MvPolynomial.X s)) := by
    simpa [Pi, Generators.cotangentSpaceBasis_apply] using
      (Extension.CotangentSpace.map_tmul
        (f := f.toExtensionHom) (x := (1 : S i)) (y := (MvPolynomial.X s : Pi.Ring)))
  refine hmap.trans ?_
  rw [map_one, Pj.cotangentSpaceBasis_apply]
  erw [Generators.Hom.toAlgHom_X]
  change
    1 ⊗ₜ[Pj.Ring] KaehlerDifferential.D (R j) Pj.Ring (MvPolynomial.X ((σ i j h) s)) =
      1 ⊗ₜ[Pj.Ring] KaehlerDifferential.D (R j) Pj.Ring (MvPolynomial.X ((σ i j h) s))
  rfl

/-- Helper for Lemma 10.134.9: on self-presentations, the canonical map to the direct-limit target
sends the cotangent-space basis vector for `s` to the basis vector indexed by its image in `S∞`. -/
private theorem selfPresentation_cotangentSpaceBasis_target_compatible
    (i : I) (s : S i) :
    let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
    let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
    let _ : Algebra (R i) S∞ :=
      ((Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).comp
        (stageBaseMap (ρ := ρ) i)).toAlgebra
    let _ : Algebra R∞ S∞ :=
      (Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).toAlgebra
    let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) S∞ :=
      IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
    let f : Pi.Hom Pinf := Generators.defaultHom Pi Pinf
    Extension.CotangentSpace.map f.toExtensionHom (Pi.cotangentSpaceBasis s) =
      Pinf.cotangentSpaceBasis (stageTargetMap (σ := σ) i s) := by
  classical
  let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
  let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
  let _ : Algebra (R i) S∞ :=
    ((Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).comp
      (stageBaseMap (ρ := ρ) i)).toAlgebra
  let _ : Algebra R∞ S∞ :=
    (Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).toAlgebra
  let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  let f : Pi.Hom Pinf := Generators.defaultHom Pi Pinf
  change Extension.CotangentSpace.map f.toExtensionHom (Pi.cotangentSpaceBasis s) =
    Pinf.cotangentSpaceBasis (stageTargetMap (σ := σ) i s)
  -- Rewrite the source basis vector as `1 ⊗ d[X_s]`, then evaluate the target default hom on
  -- `X s`.
  have hmap :
      Extension.CotangentSpace.map f.toExtensionHom (Pi.cotangentSpaceBasis s) =
        (algebraMap (S i) S∞ (1 : S i)) ⊗ₜ[Pinf.Ring]
          KaehlerDifferential.D R∞ Pinf.Ring (f.toExtensionHom.toAlgHom (MvPolynomial.X s)) := by
    simpa [Pi, Generators.cotangentSpaceBasis_apply] using
      (Extension.CotangentSpace.map_tmul
        (f := f.toExtensionHom) (x := (1 : S i)) (y := (MvPolynomial.X s : Pi.Ring)))
  refine hmap.trans ?_
  rw [map_one, Pinf.cotangentSpaceBasis_apply]
  erw [Generators.Hom.toAlgHom_X]
  change
    1 ⊗ₜ[Pinf.Ring] KaehlerDifferential.D R∞ Pinf.Ring
        (MvPolynomial.X (stageTargetMap (σ := σ) i s)) =
      1 ⊗ₜ[Pinf.Ring] KaehlerDifferential.D R∞ Pinf.Ring
        (MvPolynomial.X (stageTargetMap (σ := σ) i s))
  rfl

/-- Helper for Lemma 10.134.9: the induced map on ring direct limits commutes with the stage
transition `R_i → R_j` before passing to `S∞`. -/
private theorem directLimit_square_comp_stage
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    ((Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ hij ↦ hcomm hij).comp
        (stageBaseMap (ρ := ρ) j)).comp (ρ i j h) =
      (stageTargetMap (σ := σ) i).comp (algebraMap (R i) (S i)) := by
  -- Reassociate the left-hand side to the stage-`i` base map, then use `directLimit_square`.
  rw [RingHom.comp_assoc, stageBaseMap_comp (ρ := ρ) h]
  exact directLimit_square (ρ := ρ) (σ := σ) hcomm i

/-- Helper for Lemma 10.134.9: every polynomial in the target self-presentation already comes from
some stage self-presentation. -/
private theorem selfPresentation_ring_exists_stage
    (q : let _ : Algebra R∞ S∞ := directLimitAlgebra (ρ := ρ) (σ := σ) hcomm
         (Generators.self R∞ S∞ : Generators R∞ S∞ S∞).Ring) :
    ∃ i, ∃ q_i : (Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).Ring,
      let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
      let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
      let _ : Algebra (R i) S∞ :=
        ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ h ↦ hcomm h).comp
          (stageBaseMap (ρ := ρ) i)).toAlgebra
      let _ : Algebra R∞ S∞ :=
        (Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ h ↦ hcomm h).toAlgebra
      let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
      let _ : IsScalarTower (R i) (S i) S∞ :=
        IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
      let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
      let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
      (Generators.defaultHom Pi Pinf).toAlgHom q_i = q := by
  classical
  let _ : Algebra R∞ S∞ := directLimitAlgebra (ρ := ρ) (σ := σ) hcomm
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  -- Follow the source proof: descend coefficients and variables inductively through the
  -- `MvPolynomial` constructors, then merge stages using directedness.
  induction q using MvPolynomial.induction_on with
  | C r =>
      obtain ⟨i, r_i, hr⟩ := Ring.DirectLimit.exists_of (G := R) (f := fun i j h ↦ ρ i j h) r
      let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
      let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
      let _ : Algebra (R i) S∞ :=
        ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ h ↦ hcomm h).comp
          (stageBaseMap (ρ := ρ) i)).toAlgebra
      let _ : Algebra R∞ S∞ :=
        (Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ h ↦ hcomm h).toAlgebra
      let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
      let _ : IsScalarTower (R i) (S i) S∞ :=
        IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
      let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
      refine ⟨i, MvPolynomial.C r_i, ?_⟩
      -- Constants descend by lifting the coefficient in the base-ring direct limit.
      simpa [Pi, Pinf] using congrArg (fun x : R∞ ↦ (MvPolynomial.C x : Pinf.Ring)) hr
  | add p q hp hq =>
      rcases hp with ⟨i, p_i, hp_i⟩
      rcases hq with ⟨j, q_j, hq_j⟩
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      let _ : Algebra (R i) (R k) := (ρ i k hik).toAlgebra
      let _ : Algebra (S i) (S k) := (σ i k hik).toAlgebra
      let _ : Algebra (R i) (S k) := ((algebraMap (R k) (S k)).comp (ρ i k hik)).toAlgebra
      let _ : Algebra (R j) (R k) := (ρ j k hjk).toAlgebra
      let _ : Algebra (S j) (S k) := (σ j k hjk).toAlgebra
      let _ : Algebra (R j) (S k) := ((algebraMap (R k) (S k)).comp (ρ j k hjk)).toAlgebra
      let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
      let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
      let _ : Algebra (R i) S∞ :=
        ((Ring.DirectLimit.map (fun ℓ ↦ algebraMap (R ℓ) (S ℓ)) fun _ _ h ↦ hcomm h).comp
          (stageBaseMap (ρ := ρ) i)).toAlgebra
      let _ : Algebra (R j) R∞ := (stageBaseMap (ρ := ρ) j).toAlgebra
      let _ : Algebra (S j) S∞ := (stageTargetMap (σ := σ) j).toAlgebra
      let _ : Algebra (R j) S∞ :=
        ((Ring.DirectLimit.map (fun ℓ ↦ algebraMap (R ℓ) (S ℓ)) fun _ _ h ↦ hcomm h).comp
          (stageBaseMap (ρ := ρ) j)).toAlgebra
      let _ : Algebra (R k) R∞ := (stageBaseMap (ρ := ρ) k).toAlgebra
      let _ : Algebra (S k) S∞ := (stageTargetMap (σ := σ) k).toAlgebra
      let _ : Algebra (R k) S∞ :=
        ((Ring.DirectLimit.map (fun ℓ ↦ algebraMap (R ℓ) (S ℓ)) fun _ _ h ↦ hcomm h).comp
          (stageBaseMap (ρ := ρ) k)).toAlgebra
      let _ : Algebra R∞ S∞ :=
        (Ring.DirectLimit.map (fun ℓ ↦ algebraMap (R ℓ) (S ℓ)) fun _ _ h ↦ hcomm h).toAlgebra
      let _ : IsScalarTower (R i) (R k) (S k) := IsScalarTower.of_algebraMap_eq' rfl
      let _ : IsScalarTower (R i) (S i) (S k) :=
        IsScalarTower.of_algebraMap_eq' (hcomm hik)
      let _ : IsScalarTower (R i) (R k) R∞ := IsScalarTower.of_algebraMap_eq'
        (stageBaseMap_comp (ρ := ρ) hik).symm
      let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
      let _ : IsScalarTower (R i) (S i) S∞ :=
        IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
      let _ : IsScalarTower (R j) (R k) (S k) := IsScalarTower.of_algebraMap_eq' rfl
      let _ : IsScalarTower (R j) (S j) (S k) :=
        IsScalarTower.of_algebraMap_eq' (hcomm hjk)
      let _ : IsScalarTower (R j) (R k) R∞ := IsScalarTower.of_algebraMap_eq'
        (stageBaseMap_comp (ρ := ρ) hjk).symm
      let _ : IsScalarTower (R j) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
      let _ : IsScalarTower (R j) (S j) S∞ :=
        IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm j)
      let _ : IsScalarTower (R k) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
      let _ : IsScalarTower (R k) (S k) S∞ :=
        IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm k)
      let _ : IsScalarTower (S i) (S k) S∞ := IsScalarTower.of_algebraMap_eq'
        (stageTargetMap_comp (σ := σ) hik).symm
      let _ : IsScalarTower (S j) (S k) S∞ := IsScalarTower.of_algebraMap_eq'
        (stageTargetMap_comp (σ := σ) hjk).symm
      let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
      let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
      let Pk : Generators (R k) (S k) (S k) := Generators.self (R k) (S k)
      let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
      refine ⟨k,
        (Generators.defaultHom Pi Pk).toAlgHom p_i +
          (Generators.defaultHom Pj Pk).toAlgHom q_j,
        ?_⟩
      -- After moving both summands to the common stage, the target map is additive.
      have hp_move :
          (Generators.defaultHom Pk Pinf).toAlgHom
              ((Generators.defaultHom Pi Pk).toAlgHom p_i) =
            (Generators.defaultHom Pi Pinf).toAlgHom p_i := by
        calc
          (Generators.defaultHom Pk Pinf).toAlgHom
              ((Generators.defaultHom Pi Pk).toAlgHom p_i) =
              ((Generators.defaultHom Pk Pinf).comp
                  (Generators.defaultHom Pi Pk)).toAlgHom p_i := by
                    symm
                    simpa using
                      (Generators.Hom.toAlgHom_comp_apply
                        (f := Generators.defaultHom Pi Pk)
                        (g := Generators.defaultHom Pk Pinf)
                        (x := p_i))
          _ = (Generators.defaultHom Pi Pinf).toAlgHom p_i := by
                simpa [Pi, Pk, Pinf] using
                  congrArg (fun f ↦ f.toAlgHom p_i)
                    (selfPresentation_defaultHom_comp (ρ := ρ) (σ := σ) hcomm hik)
      have hq_move :
          (Generators.defaultHom Pk Pinf).toAlgHom
              ((Generators.defaultHom Pj Pk).toAlgHom q_j) =
            (Generators.defaultHom Pj Pinf).toAlgHom q_j := by
        calc
          (Generators.defaultHom Pk Pinf).toAlgHom
              ((Generators.defaultHom Pj Pk).toAlgHom q_j) =
              ((Generators.defaultHom Pk Pinf).comp
                  (Generators.defaultHom Pj Pk)).toAlgHom q_j := by
                    symm
                    simpa using
                      (Generators.Hom.toAlgHom_comp_apply
                        (f := Generators.defaultHom Pj Pk)
                        (g := Generators.defaultHom Pk Pinf)
                        (x := q_j))
          _ = (Generators.defaultHom Pj Pinf).toAlgHom q_j := by
                simpa [Pj, Pk, Pinf] using
                  congrArg (fun f ↦ f.toAlgHom q_j)
                    (selfPresentation_defaultHom_comp (ρ := ρ) (σ := σ) hcomm hjk)
      calc
        (Generators.defaultHom Pk Pinf).toAlgHom
            ((Generators.defaultHom Pi Pk).toAlgHom p_i +
              (Generators.defaultHom Pj Pk).toAlgHom q_j) =
          (Generators.defaultHom Pk Pinf).toAlgHom
              ((Generators.defaultHom Pi Pk).toAlgHom p_i) +
            (Generators.defaultHom Pk Pinf).toAlgHom
              ((Generators.defaultHom Pj Pk).toAlgHom q_j) := by
                simp
        _ = (Generators.defaultHom Pi Pinf).toAlgHom p_i +
            (Generators.defaultHom Pj Pinf).toAlgHom q_j := by
              rw [hp_move, hq_move]
        _ = p + q := by rw [hp_i, hq_j]
  | mul_X p s hp =>
      rcases hp with ⟨i, p_i, hp_i⟩
      obtain ⟨j, s_j, hs_j⟩ := Ring.DirectLimit.exists_of (G := S) (f := fun i j h ↦ σ i j h) s
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      let _ : Algebra (R i) (R k) := (ρ i k hik).toAlgebra
      let _ : Algebra (S i) (S k) := (σ i k hik).toAlgebra
      let _ : Algebra (R i) (S k) := ((algebraMap (R k) (S k)).comp (ρ i k hik)).toAlgebra
      let _ : Algebra (R j) (R k) := (ρ j k hjk).toAlgebra
      let _ : Algebra (S j) (S k) := (σ j k hjk).toAlgebra
      let _ : Algebra (R j) (S k) := ((algebraMap (R k) (S k)).comp (ρ j k hjk)).toAlgebra
      let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
      let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
      let _ : Algebra (R i) S∞ :=
        ((Ring.DirectLimit.map (fun ℓ ↦ algebraMap (R ℓ) (S ℓ)) fun _ _ h ↦ hcomm h).comp
          (stageBaseMap (ρ := ρ) i)).toAlgebra
      let _ : Algebra (R j) R∞ := (stageBaseMap (ρ := ρ) j).toAlgebra
      let _ : Algebra (S j) S∞ := (stageTargetMap (σ := σ) j).toAlgebra
      let _ : Algebra (R j) S∞ :=
        ((Ring.DirectLimit.map (fun ℓ ↦ algebraMap (R ℓ) (S ℓ)) fun _ _ h ↦ hcomm h).comp
          (stageBaseMap (ρ := ρ) j)).toAlgebra
      let _ : Algebra (R k) R∞ := (stageBaseMap (ρ := ρ) k).toAlgebra
      let _ : Algebra (S k) S∞ := (stageTargetMap (σ := σ) k).toAlgebra
      let _ : Algebra (R k) S∞ :=
        ((Ring.DirectLimit.map (fun ℓ ↦ algebraMap (R ℓ) (S ℓ)) fun _ _ h ↦ hcomm h).comp
          (stageBaseMap (ρ := ρ) k)).toAlgebra
      let _ : Algebra R∞ S∞ :=
        (Ring.DirectLimit.map (fun ℓ ↦ algebraMap (R ℓ) (S ℓ)) fun _ _ h ↦ hcomm h).toAlgebra
      let _ : IsScalarTower (R i) (R k) (S k) := IsScalarTower.of_algebraMap_eq' rfl
      let _ : IsScalarTower (R i) (S i) (S k) :=
        IsScalarTower.of_algebraMap_eq' (hcomm hik)
      let _ : IsScalarTower (R i) (R k) R∞ := IsScalarTower.of_algebraMap_eq'
        (stageBaseMap_comp (ρ := ρ) hik).symm
      let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
      let _ : IsScalarTower (R i) (S i) S∞ :=
        IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
      let _ : IsScalarTower (R j) (R k) (S k) := IsScalarTower.of_algebraMap_eq' rfl
      let _ : IsScalarTower (R j) (S j) (S k) :=
        IsScalarTower.of_algebraMap_eq' (hcomm hjk)
      let _ : IsScalarTower (R j) (R k) R∞ := IsScalarTower.of_algebraMap_eq'
        (stageBaseMap_comp (ρ := ρ) hjk).symm
      let _ : IsScalarTower (R j) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
      let _ : IsScalarTower (R j) (S j) S∞ :=
        IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm j)
      let _ : IsScalarTower (R k) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
      let _ : IsScalarTower (R k) (S k) S∞ :=
        IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm k)
      let _ : IsScalarTower (S i) (S k) S∞ := IsScalarTower.of_algebraMap_eq'
        (stageTargetMap_comp (σ := σ) hik).symm
      let _ : IsScalarTower (S j) (S k) S∞ := IsScalarTower.of_algebraMap_eq'
        (stageTargetMap_comp (σ := σ) hjk).symm
      let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
      let Pk : Generators (R k) (S k) (S k) := Generators.self (R k) (S k)
      let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
      refine ⟨k,
        (Generators.defaultHom Pi Pk).toAlgHom p_i * MvPolynomial.X (σ j k hjk s_j),
        ?_⟩
      -- After moving the polynomial part and the variable to a common stage, multiply them.
      have hp_move :
          (Generators.defaultHom Pk Pinf).toAlgHom
              ((Generators.defaultHom Pi Pk).toAlgHom p_i) =
            (Generators.defaultHom Pi Pinf).toAlgHom p_i := by
        calc
          (Generators.defaultHom Pk Pinf).toAlgHom
              ((Generators.defaultHom Pi Pk).toAlgHom p_i) =
              ((Generators.defaultHom Pk Pinf).comp
                  (Generators.defaultHom Pi Pk)).toAlgHom p_i := by
                    symm
                    simpa using
                      (Generators.Hom.toAlgHom_comp_apply
                        (f := Generators.defaultHom Pi Pk)
                        (g := Generators.defaultHom Pk Pinf)
                        (x := p_i))
          _ = (Generators.defaultHom Pi Pinf).toAlgHom p_i := by
                simpa [Pi, Pk, Pinf] using
                  congrArg (fun f ↦ f.toAlgHom p_i)
                    (selfPresentation_defaultHom_comp (ρ := ρ) (σ := σ) hcomm hik)
      have hs_move :
          stageTargetMap (σ := σ) k (σ j k hjk s_j) = s := by
        calc
          stageTargetMap (σ := σ) k (σ j k hjk s_j) =
              stageTargetMap (σ := σ) j s_j := by
                simpa using DFunLike.congr_fun (stageTargetMap_comp (σ := σ) hjk) s_j
          _ = s := hs_j
      calc
        (Generators.defaultHom Pk Pinf).toAlgHom
            ((Generators.defaultHom Pi Pk).toAlgHom p_i * MvPolynomial.X (σ j k hjk s_j)) =
          (Generators.defaultHom Pk Pinf).toAlgHom
              ((Generators.defaultHom Pi Pk).toAlgHom p_i) *
            (Generators.defaultHom Pk Pinf).toAlgHom
              (MvPolynomial.X (σ j k hjk s_j)) := by
                simp
        _ = (Generators.defaultHom Pi Pinf).toAlgHom p_i *
            (Generators.defaultHom Pk Pinf).val (σ j k hjk s_j) := by
              rw [hp_move, Generators.Hom.toAlgHom_X]
        _ = (Generators.defaultHom Pi Pinf).toAlgHom p_i *
            MvPolynomial.X (stageTargetMap (σ := σ) k (σ j k hjk s_j)) := by
              rfl
        _ = (Generators.defaultHom Pi Pinf).toAlgHom p_i *
            MvPolynomial.X s := by
              simp [hs_move]
        _ = p * MvPolynomial.X s := by simpa [hp_i]

/-- Helper for Lemma 10.134.9: every kernel element of the target self-presentation comes from a
kernel element at some stage after moving far enough along the directed system. -/
private theorem selfPresentation_stage_eval_zero_exists
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    [DirectedSystem S fun i j h ↦ σ i j h]
    {i : I}
    (q_i : (Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).Ring)
    (hzero :
      let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
      stageTargetMap (σ := σ) i (algebraMap Pi.Ring (S i) q_i) = 0) :
    ∃ j, ∃ hij : i ≤ j,
      let _ : Algebra (R i) (R j) := (ρ i j hij).toAlgebra
      let _ : Algebra (S i) (S j) := (σ i j hij).toAlgebra
      let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j hij)).toAlgebra
      let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
      let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
      algebraMap Pj.Ring (S j) ((Generators.defaultHom Pi Pj).toAlgHom q_i) = 0 := by
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  -- Route correction: isolate the source-proof vanishing step behind the exact direct-limit API
  -- instead of unfolding the quotient relation inside the main kernel-descent theorem.
  obtain ⟨j, hij, hj⟩ := Ring.DirectLimit.of.zero_exact
    (G := S) (f' := fun i j h ↦ σ i j h) hzero
  refine ⟨j, hij, ?_⟩
  let _ : Algebra (R i) (R j) := (ρ i j hij).toAlgebra
  let _ : Algebra (S i) (S j) := (σ i j hij).toAlgebra
  let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j hij)).toAlgebra
  let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm hij)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  let fij : Pi.Hom Pj := Generators.defaultHom Pi Pj
  -- Evaluate the pushed polynomial at stage `j`; this is exactly the later-stage image from
  -- `Ring.DirectLimit.of.zero_exact`.
  have hpush :
      algebraMap Pj.Ring (S j) (fij.toAlgHom q_i) =
        algebraMap (S i) (S j) (algebraMap Pi.Ring (S i) q_i) := by
    simpa [fij] using (Generators.Hom.algebraMap_toAlgHom (f := fij) q_i)
  -- Now replace the pushed evaluation by the direct image of the stage evaluation.
  calc
    algebraMap Pj.Ring (S j) ((Generators.defaultHom Pi Pj).toAlgHom q_i) =
        algebraMap (S i) (S j) (algebraMap Pi.Ring (S i) q_i) := by
          simpa [fij] using hpush
    _ = 0 := hj

/-- Helper for Lemma 10.134.9: with coherent target transition maps, every target-kernel element
descends to a later stage kernel exactly as in the source proof `I = colim I_i`. -/
private theorem selfPresentation_ker_exists_stage_of_directed
    [DirectedSystem S fun i j h ↦ σ i j h]
    (x : let _ : Algebra R∞ S∞ := directLimitAlgebra (ρ := ρ) (σ := σ) hcomm
         ((Generators.self R∞ S∞ : Generators R∞ S∞ S∞).toExtension).ker) :
    ∃ i, ∃ x_i : ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension).ker,
      let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
      let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
      let _ : Algebra (R i) S∞ :=
        ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ h ↦ hcomm h).comp
          (stageBaseMap (ρ := ρ) i)).toAlgebra
      let _ : Algebra R∞ S∞ :=
        (Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ h ↦ hcomm h).toAlgebra
      let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
      let _ : IsScalarTower (R i) (S i) S∞ :=
        IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
      let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
      let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
      (Generators.defaultHom Pi Pinf).toAlgHom x_i.1 = x.1 := by
  classical
  let _ : Algebra R∞ S∞ := directLimitAlgebra (ρ := ρ) (σ := σ) hcomm
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  obtain ⟨i, q_i, hq_i⟩ :=
    selfPresentation_ring_exists_stage (ρ := ρ) (σ := σ) hcomm x.1
  let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
  let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
  let _ : Algebra (R i) S∞ :=
    ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ h ↦ hcomm h).comp
      (stageBaseMap (ρ := ρ) i)).toAlgebra
  let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  have himage_zero :
      algebraMap Pinf.Ring S∞ ((Generators.defaultHom Pi Pinf).toAlgHom q_i) = 0 := by
    -- The descended polynomial is exactly the chosen target kernel representative.
    rw [hq_i]
    exact x.2
  have hstage_zero :
      stageTargetMap (σ := σ) i (algebraMap Pi.Ring (S i) q_i) = 0 := by
    -- Reinterpret the target evaluation as the stage evaluation followed by `S_i → S∞`.
    simpa [Generators.defaultHom] using himage_zero
  obtain ⟨j, hij, hj_zero⟩ :=
    selfPresentation_stage_eval_zero_exists
      (ρ := ρ) (σ := σ) hcomm q_i hstage_zero
  let _ : Algebra (R i) (R j) := (ρ i j hij).toAlgebra
  let _ : Algebra (S i) (S j) := (σ i j hij).toAlgebra
  let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j hij)).toAlgebra
  let _ : Algebra (R j) R∞ := (stageBaseMap (ρ := ρ) j).toAlgebra
  let _ : Algebra (S j) S∞ := (stageTargetMap (σ := σ) j).toAlgebra
  let _ : Algebra (R j) S∞ :=
    ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ h ↦ hcomm h).comp
      (stageBaseMap (ρ := ρ) j)).toAlgebra
  let _ : Algebra R∞ S∞ :=
    (Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ h ↦ hcomm h).toAlgebra
  let _ : IsScalarTower (R i) (R j) R∞ := IsScalarTower.of_algebraMap_eq'
    (stageBaseMap_comp (ρ := ρ) hij).symm
  let _ : IsScalarTower (R j) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R j) (S j) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm j)
  let _ : IsScalarTower (S i) (S j) S∞ := IsScalarTower.of_algebraMap_eq'
    (stageTargetMap_comp (σ := σ) hij).symm
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  let x_j : Pj.toExtension.ker :=
    ⟨(Generators.defaultHom Pi Pj).toAlgHom q_i, hj_zero⟩
  refine ⟨j, x_j, ?_⟩
  -- Move the descended stage-`i` kernel representative to stage `j`, then to the target.
  calc
    (Generators.defaultHom Pj Pinf).toAlgHom x_j.1 =
        (Generators.defaultHom Pj Pinf).toAlgHom
          ((Generators.defaultHom Pi Pj).toAlgHom q_i) := rfl
    _ = ((Generators.defaultHom Pj Pinf).comp
          (Generators.defaultHom Pi Pj)).toAlgHom q_i := by
        symm
        simpa using
          (Generators.Hom.toAlgHom_comp_apply
            (f := Generators.defaultHom Pi Pj)
            (g := Generators.defaultHom Pj Pinf)
            (x := q_i))
    _ = (Generators.defaultHom Pi Pinf).toAlgHom q_i := by
        simpa [Pi, Pj, Pinf] using
          congrArg (fun f ↦ f.toAlgHom q_i)
            (selfPresentation_defaultHom_comp (ρ := ρ) (σ := σ) hcomm hij)
    _ = x.1 := hq_i

/-- Helper for Lemma 10.134.9: every kernel element of the target self-presentation comes from a
kernel element at some stage after moving far enough along the directed system. -/
private theorem selfPresentation_ker_exists_stage
    [DirectedSystem S fun i j h ↦ σ i j h]
    (x : let _ : Algebra R∞ S∞ := directLimitAlgebra (ρ := ρ) (σ := σ) hcomm
         ((Generators.self R∞ S∞ : Generators R∞ S∞ S∞).toExtension).ker) :
    ∃ i, ∃ x_i : ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension).ker,
      let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
      let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
      let _ : Algebra (R i) S∞ :=
        ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ h ↦ hcomm h).comp
          (stageBaseMap (ρ := ρ) i)).toAlgebra
      let _ : Algebra R∞ S∞ :=
        (Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ h ↦ hcomm h).toAlgebra
      let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
      let _ : IsScalarTower (R i) (S i) S∞ :=
        IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
      let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
      let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
      (Generators.defaultHom Pi Pinf).toAlgHom x_i.1 = x.1 := by
  -- Proof comment: under the actual directed-system coherence hypothesis, the raw wrapper is
  -- exactly the already proved source-faithful kernel descent.
  exact selfPresentation_ker_exists_stage_of_directed
    (ρ := ρ) (σ := σ) hcomm x

/-- Helper for Lemma 10.134.9: the canonical target owner `NL_{S∞⁄R∞}`. -/
private noncomputable abbrev targetNaiveCotangent :
    ChainComplex (ModuleCat.{u} S∞) ℕ := by
  let _ : Algebra R∞ S∞ :=
    (Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).toAlgebra
  exact NL_{S∞⁄R∞}

/-- Helper for Lemma 10.134.9: the stagewise source complex after extending scalars to `S∞`. -/
private noncomputable abbrev stageNaiveCotangentBaseChange (i : I) :
    ChainComplex (ModuleCat.{u} S∞) ℕ := by
  let C : ChainComplex (ModuleCat.{u} (S i)) ℕ :=
    Algebra.Extension.naiveCotangentChainComplex
      ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension)
  exact ((ModuleCat.extendScalars (stageTargetMap i)).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj C

/-- Helper for Lemma 10.134.9: restricting scalars along an algebra map does not change the
underlying module. -/
private noncomputable def restrictOfIso
    {B : Type u} {C : Type u} [CommRing B] [CommRing C] [Algebra B C]
    (M : Type u) [AddCommGroup M] [Module C M] [Module B M] [IsScalarTower B C M] :
    (ModuleCat.restrictScalars (algebraMap B C)).obj (ModuleCat.of C M) ≅ ModuleCat.of B M :=
  (show ↑((ModuleCat.restrictScalars (algebraMap B C)).obj (ModuleCat.of C M)) ≃ₗ[B] M from
      { __ := AddEquiv.refl _
        map_smul' := fun _ _ ↦ by simp }).toModuleIso

/-- Helper for Lemma 10.134.9: before passing to `S∞`, a transition map of stages induces the
canonical chain map on naive cotangent complexes after scalar extension to the later stage. -/
private noncomputable def stageNaiveCotangentTransitionBase
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    (((ModuleCat.extendScalars (σ i j h)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Algebra.Extension.naiveCotangentChainComplex
        ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension))) ⟶
      (Algebra.Extension.naiveCotangentChainComplex
        ((Generators.self (R j) (S j) : Generators (R j) (S j) (S j)).toExtension)) := by
  let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
  let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
  let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
  let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  let C₁ :
      ChainComplex (ModuleCat (S j)) ℕ :=
    (((ModuleCat.extendScalars (σ i j h)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension))
  let C₂ : ChainComplex (ModuleCat (S j)) ℕ :=
    Algebra.Extension.naiveCotangentChainComplex Pj.toExtension
  let f : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
  let f₀' :
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0 ⟶
        (ModuleCat.restrictScalars (σ i j h)).obj (C₂.X 0) :=
    ModuleCat.ofHom (Extension.CotangentSpace.map f) ≫
      (restrictOfIso Pj.toExtension.CotangentSpace).inv
  let f₀ : C₁.X 0 ⟶ C₂.X 0 :=
    ((ModuleCat.extendRestrictScalarsAdj (σ i j h)).homEquiv _ _).symm f₀'
  let liftf : ULift Pi.toExtension.Cotangent →ₗ[S i] ULift Pj.toExtension.Cotangent :=
    { toFun := fun x ↦ ULift.up (Extension.Cotangent.map f x.down)
      map_add' := by
        intro x y
        ext <;> simp
      map_smul' := by
        intro r x
        ext <;> simp }
  let f₁' :
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 1 ⟶
        (ModuleCat.restrictScalars (σ i j h)).obj (C₂.X 1) :=
    ModuleCat.ofHom liftf ≫
      (restrictOfIso (ULift Pj.toExtension.Cotangent)).inv
  let f₁ : C₁.X 1 ⟶ C₂.X 1 :=
    ((ModuleCat.extendRestrictScalarsAdj (σ i j h)).homEquiv _ _).symm f₁'
  refine ChainComplex.mkHom _ _ f₀ f₁ ?_ ?_
  · -- Check the square on the unit tensors that generate the extended degree-`1` module.
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    rcases x with ⟨x⟩
    -- First normalize the transported degree-`1` generator and the transported degree-`0` image.
    have hgen :
        f₁ (((1 : S j) ⊗ₜ[S i] ULift.up x)) =
          ULift.up (Extension.Cotangent.map f x) := by
      have hAdj :
          ((ModuleCat.extendRestrictScalarsAdj (σ i j h)).homEquiv _ _ f₁)
            (ULift.up x) =
          f₁ (((1 : S j) ⊗ₜ[S i] ULift.up x)) := by
        simpa using
          (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
            (f := σ i j h)
            (φ := f₁)
            (m := ULift.up x))
      have hTranspose :
          f₁ (((1 : S j) ⊗ₜ[S i] ULift.up x)) =
            f₁' (ULift.up x) := by
        simpa [f₁] using hAdj.symm
      refine Eq.trans hTranspose ?_
      change
        (restrictOfIso (ULift Pj.toExtension.Cotangent)).inv
            (liftf (ULift.up x)) =
          ULift.up (Extension.Cotangent.map f x)
      rfl
    have hzero :
        f₀ (((1 : S j) ⊗ₜ[S i] Pi.toExtension.cotangentComplex x)) =
          Pj.toExtension.cotangentComplex (Extension.Cotangent.map f x) := by
      have hAdj :
          ((ModuleCat.extendRestrictScalarsAdj (σ i j h)).homEquiv _ _ f₀)
            (Pi.toExtension.cotangentComplex x) =
          f₀ (((1 : S j) ⊗ₜ[S i] Pi.toExtension.cotangentComplex x)) := by
        simpa using
          (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
            (f := σ i j h)
            (φ := f₀)
            (m := Pi.toExtension.cotangentComplex x))
      have hTranspose :
          f₀ (((1 : S j) ⊗ₜ[S i] Pi.toExtension.cotangentComplex x)) =
            f₀' (Pi.toExtension.cotangentComplex x) := by
        simpa [f₀] using hAdj.symm
      refine Eq.trans hTranspose ?_
      change
        (restrictOfIso Pj.toExtension.CotangentSpace).inv
            ((Extension.CotangentSpace.map f) (Pi.toExtension.cotangentComplex x)) =
          Pj.toExtension.cotangentComplex (Extension.Cotangent.map f x)
      simpa using
        LinearMap.congr_fun (Extension.CotangentSpace.map_comp_cotangentComplex f) x
    -- Normalize the source differential on the canonical degree-`1` generator.
    have hsource :
        C₁.d 1 0 (((1 : S j) ⊗ₜ[S i] ULift.up x)) =
          ((1 : S j) ⊗ₜ[S i] Pi.toExtension.cotangentComplex x) := by
      rw [CategoryTheory.Functor.mapHomologicalComplex_obj_d,
        Extension.naiveCotangentChainComplex_d_1_0]
      rfl
    change
      C₂.d 1 0 (f₁ (((1 : S j) ⊗ₜ[S i] ULift.up x))) =
        f₀ (C₁.d 1 0 (((1 : S j) ⊗ₜ[S i] ULift.up x)))
    rw [hgen]
    rw [Extension.naiveCotangentChainComplex_d_1_0]
    rw [hsource]
    simpa using hzero.symm
  · intro n p
    -- Above degree `1`, both naive cotangent complexes have zero differential.
    refine ⟨0, ?_⟩
    rw [Extension.naiveCotangentChainComplex_d_succ_succ Pj.toExtension n]
    rw [CategoryTheory.Functor.mapHomologicalComplex_obj_d,
      Extension.naiveCotangentChainComplex_d_succ_succ Pi.toExtension n]
    rw [CategoryTheory.Functor.map_zero]
    simp

/-- Helper for Lemma 10.134.9: the degree-`0` component of the stage transition sends the
adjunction-unit image of `cotangentComplex x` to the expected cotangent-space map. -/
private theorem stageNaiveCotangentTransitionBase_degree_zero_after_transport
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j)
    (y : ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension).CotangentSpace) :
    let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
    let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
    let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
    let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
    let C₁ : ChainComplex (ModuleCat (S j)) ℕ :=
      (((ModuleCat.extendScalars (σ i j h)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension))
    let C₂ : ChainComplex (ModuleCat (S j)) ℕ :=
      Algebra.Extension.naiveCotangentChainComplex Pj.toExtension
    let f : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
    let f₀' :
        (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0 ⟶
          (ModuleCat.restrictScalars (σ i j h)).obj (C₂.X 0) :=
      ModuleCat.ofHom (Extension.CotangentSpace.map f) ≫
        (restrictOfIso Pj.toExtension.CotangentSpace).inv
    let f₀ : C₁.X 0 ⟶ C₂.X 0 :=
      ((ModuleCat.extendRestrictScalarsAdj (σ i j h)).homEquiv _ _).symm f₀'
    f₀ (((ModuleCat.extendRestrictScalarsAdj (σ i j h)).unit.app
        ((Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0))
      y) =
      Extension.CotangentSpace.map f y := by
  let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
  let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
  let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
  let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  let C₁ : ChainComplex (ModuleCat (S j)) ℕ :=
    (((ModuleCat.extendScalars (σ i j h)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension))
  let C₂ : ChainComplex (ModuleCat (S j)) ℕ :=
    Algebra.Extension.naiveCotangentChainComplex Pj.toExtension
  let f : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
  let f₀' :
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0 ⟶
        (ModuleCat.restrictScalars (σ i j h)).obj (C₂.X 0) :=
    ModuleCat.ofHom (Extension.CotangentSpace.map f) ≫
      (restrictOfIso Pj.toExtension.CotangentSpace).inv
  let f₀ : C₁.X 0 ⟶ C₂.X 0 :=
    ((ModuleCat.extendRestrictScalarsAdj (σ i j h)).homEquiv _ _).symm f₀'
  -- Remove the scalar-extension adjunction transport before reading off the cotangent-space map.
  change f₀ (((ModuleCat.extendRestrictScalarsAdj (σ i j h)).unit.app
      ((Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0))
    y) =
    Extension.CotangentSpace.map f y
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  have hAdj :
      ((ModuleCat.extendRestrictScalarsAdj (σ i j h)).homEquiv _ _ f₀) y =
        f₀ (((1 : S j) ⊗ₜ[S i] y)) := by
    simpa using
      (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
        (f := σ i j h)
        (φ := f₀)
        (m := y))
  have hTranspose :
      f₀ (((1 : S j) ⊗ₜ[S i] y)) = f₀' y := by
    simpa [f₀] using hAdj.symm
  refine Eq.trans hTranspose ?_
  change
    (restrictOfIso Pj.toExtension.CotangentSpace).inv
        ((Extension.CotangentSpace.map f) y) =
      Extension.CotangentSpace.map f y
  rfl

/-- Helper for Lemma 10.134.9: the degree-`0` component of the stage transition sends the
adjunction-unit image of `cotangentComplex x` to the expected cotangent-space map. -/
private theorem stageNaiveCotangentTransitionBase_degree_zero_on_cotangent
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j)
    (x : ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension).Cotangent) :
    let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
    let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
    let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
    let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
    let C₁ : ChainComplex (ModuleCat (S j)) ℕ :=
      (((ModuleCat.extendScalars (σ i j h)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension))
    let C₂ : ChainComplex (ModuleCat (S j)) ℕ :=
      Algebra.Extension.naiveCotangentChainComplex Pj.toExtension
    let f : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
    let f₀' :
        (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0 ⟶
          (ModuleCat.restrictScalars (σ i j h)).obj (C₂.X 0) :=
      ModuleCat.ofHom (Extension.CotangentSpace.map f) ≫
        (restrictOfIso Pj.toExtension.CotangentSpace).inv
    let f₀ : C₁.X 0 ⟶ C₂.X 0 :=
      ((ModuleCat.extendRestrictScalarsAdj (σ i j h)).homEquiv _ _).symm f₀'
    f₀ (((ModuleCat.extendRestrictScalarsAdj (σ i j h)).unit.app
        ((Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0))
      (Pi.toExtension.cotangentComplex x)) =
      Extension.CotangentSpace.map f (Pi.toExtension.cotangentComplex x) := by
  let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
  let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
  let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
  let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  let C₁ : ChainComplex (ModuleCat (S j)) ℕ :=
    (((ModuleCat.extendScalars (σ i j h)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension))
  let C₂ : ChainComplex (ModuleCat (S j)) ℕ :=
    Algebra.Extension.naiveCotangentChainComplex Pj.toExtension
  let f : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
  let f₀' :
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0 ⟶
        (ModuleCat.restrictScalars (σ i j h)).obj (C₂.X 0) :=
    ModuleCat.ofHom (Extension.CotangentSpace.map f) ≫
      (restrictOfIso Pj.toExtension.CotangentSpace).inv
  let f₀ : C₁.X 0 ⟶ C₂.X 0 :=
    ((ModuleCat.extendRestrictScalarsAdj (σ i j h)).homEquiv _ _).symm f₀'
  -- Re-express the goal using the local names so the adjunction formula can be applied cleanly.
  change f₀ (((ModuleCat.extendRestrictScalarsAdj (σ i j h)).unit.app
      ((Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0))
    (Pi.toExtension.cotangentComplex x)) =
    Extension.CotangentSpace.map f (Pi.toExtension.cotangentComplex x)
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  have hAdj :
      ((ModuleCat.extendRestrictScalarsAdj (σ i j h)).homEquiv _ _ f₀)
        (Pi.toExtension.cotangentComplex x) =
      f₀ (((1 : S j) ⊗ₜ[S i] Pi.toExtension.cotangentComplex x)) := by
    simpa using
      (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
        (f := σ i j h)
        (φ := f₀)
        (m := Pi.toExtension.cotangentComplex x))
  have hTranspose :
      f₀ (((1 : S j) ⊗ₜ[S i] Pi.toExtension.cotangentComplex x)) =
        f₀' (Pi.toExtension.cotangentComplex x) := by
    simpa [f₀] using hAdj.symm
  refine Eq.trans hTranspose ?_
  change
    (restrictOfIso Pj.toExtension.CotangentSpace).inv
        ((Extension.CotangentSpace.map f) (Pi.toExtension.cotangentComplex x)) =
      Extension.CotangentSpace.map f (Pi.toExtension.cotangentComplex x)
  rfl

/-- Helper for Lemma 10.134.9: the degree-`0` component of the stage transition sends the
adjunction-unit image of `cotangentComplex x` to the cotangent complex of the mapped generator. -/
private theorem stageNaiveCotangentTransitionBase_degree_zero_on_mapped_cotangent
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j)
    (x : ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension).Cotangent) :
    let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
    let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
    let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
    let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
    let C₁ : ChainComplex (ModuleCat (S j)) ℕ :=
      (((ModuleCat.extendScalars (σ i j h)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension))
    let C₂ : ChainComplex (ModuleCat (S j)) ℕ :=
      Algebra.Extension.naiveCotangentChainComplex Pj.toExtension
    let f : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
    let f₀' :
        (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0 ⟶
          (ModuleCat.restrictScalars (σ i j h)).obj (C₂.X 0) :=
      ModuleCat.ofHom (Extension.CotangentSpace.map f) ≫
        (restrictOfIso Pj.toExtension.CotangentSpace).inv
    let f₀ : C₁.X 0 ⟶ C₂.X 0 :=
      ((ModuleCat.extendRestrictScalarsAdj (σ i j h)).homEquiv _ _).symm f₀'
    f₀ (((ModuleCat.extendRestrictScalarsAdj (σ i j h)).unit.app
        ((Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0))
      (Pi.toExtension.cotangentComplex x)) =
      Pj.toExtension.cotangentComplex (Extension.Cotangent.map f x) := by
  let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
  let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
  let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
  let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  let C₁ : ChainComplex (ModuleCat (S j)) ℕ :=
    (((ModuleCat.extendScalars (σ i j h)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension))
  let C₂ : ChainComplex (ModuleCat (S j)) ℕ :=
    Algebra.Extension.naiveCotangentChainComplex Pj.toExtension
  let f : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
  let f₀' :
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0 ⟶
        (ModuleCat.restrictScalars (σ i j h)).obj (C₂.X 0) :=
    ModuleCat.ofHom (Extension.CotangentSpace.map f) ≫
      (restrictOfIso Pj.toExtension.CotangentSpace).inv
  let f₀ : C₁.X 0 ⟶ C₂.X 0 :=
    ((ModuleCat.extendRestrictScalarsAdj (σ i j h)).homEquiv _ _).symm f₀'
  -- First remove the adjunction transport, then rewrite the cotangent-space image as the target
  -- cotangent complex of the mapped generator.
  refine (stageNaiveCotangentTransitionBase_degree_zero_on_cotangent
    (ρ := ρ) (σ := σ) hcomm h x).trans ?_
  simpa using
    LinearMap.congr_fun (Extension.CotangentSpace.map_comp_cotangentComplex f) x

/-- Helper for Lemma 10.134.9: after transporting across the extend/restrict adjunction, the
degree-`1` component of the stage transition sends the canonical generator to the mapped generator
at the later stage. -/
private theorem stageNaiveCotangentBaseChangeTransition_degree_one_generator_after_transport
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j)
    (x : ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension).Cotangent) :
    let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
    let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
    let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
    let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
    let C₁ : ChainComplex (ModuleCat (S j)) ℕ :=
      (((ModuleCat.extendScalars (σ i j h)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension))
    let C₂ : ChainComplex (ModuleCat (S j)) ℕ :=
      Algebra.Extension.naiveCotangentChainComplex Pj.toExtension
    let f : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
    let liftf : ULift Pi.toExtension.Cotangent →ₗ[S i] ULift Pj.toExtension.Cotangent :=
      { toFun := fun y ↦ ULift.up (Extension.Cotangent.map f y.down)
        map_add' := by
          intro y z
          ext <;> simp
        map_smul' := by
          intro r y
          ext <;> simp }
    let f₁' :
        (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 1 ⟶
          (ModuleCat.restrictScalars (σ i j h)).obj (C₂.X 1) :=
      ModuleCat.ofHom liftf ≫
        (restrictOfIso (ULift Pj.toExtension.Cotangent)).inv
    let f₁ : C₁.X 1 ⟶ C₂.X 1 :=
      ((ModuleCat.extendRestrictScalarsAdj (σ i j h)).homEquiv _ _).symm f₁'
    f₁ (((ModuleCat.extendRestrictScalarsAdj (σ i j h)).unit.app
        ((Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 1))
      (ULift.up x)) =
      ULift.up (Extension.Cotangent.map f x) := by
  let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
  let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
  let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
  let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  let C₁ : ChainComplex (ModuleCat (S j)) ℕ :=
    (((ModuleCat.extendScalars (σ i j h)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension))
  let C₂ : ChainComplex (ModuleCat (S j)) ℕ :=
    Algebra.Extension.naiveCotangentChainComplex Pj.toExtension
  let f : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
  let liftf : ULift Pi.toExtension.Cotangent →ₗ[S i] ULift Pj.toExtension.Cotangent :=
    { toFun := fun y ↦ ULift.up (Extension.Cotangent.map f y.down)
      map_add' := by
        intro y z
        ext <;> simp
      map_smul' := by
        intro r y
        ext <;> simp }
  let f₁' :
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 1 ⟶
        (ModuleCat.restrictScalars (σ i j h)).obj (C₂.X 1) :=
    ModuleCat.ofHom liftf ≫
      (restrictOfIso (ULift Pj.toExtension.Cotangent)).inv
  let f₁ : C₁.X 1 ⟶ C₂.X 1 :=
    ((ModuleCat.extendRestrictScalarsAdj (σ i j h)).homEquiv _ _).symm f₁'
  -- First remove the adjunction transport so the underlying cotangent map is visible on the
  -- canonical generator `ULift.up x`.
  change f₁ (((ModuleCat.extendRestrictScalarsAdj (σ i j h)).unit.app
      ((Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 1))
    (ULift.up x)) =
    ULift.up (Extension.Cotangent.map f x)
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  have hAdj :
      ((ModuleCat.extendRestrictScalarsAdj (σ i j h)).homEquiv _ _ f₁)
        (ULift.up x) =
      f₁ (((1 : S j) ⊗ₜ[S i] ULift.up x)) := by
    simpa using
      (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
        (f := σ i j h)
        (φ := f₁)
        (m := ULift.up x))
  have hTranspose :
      f₁ (((1 : S j) ⊗ₜ[S i] ULift.up x)) =
        f₁' (ULift.up x) := by
    simpa [f₁] using hAdj.symm
  refine Eq.trans hTranspose ?_
  change
    (restrictOfIso (ULift Pj.toExtension.Cotangent)).inv
        (liftf (ULift.up x)) =
      ULift.up (Extension.Cotangent.map f x)
  rfl

/-- Helper for Lemma 10.134.9: extending scalars from a stage first to a later stage and then to
`S∞` gives the canonical transition morphism in the common target category. -/
private noncomputable def stageNaiveCotangentBaseChangeTransition
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) := by
  let Cᵢ : ChainComplex (ModuleCat (S i)) ℕ :=
    Algebra.Extension.naiveCotangentChainComplex
      ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension)
  let σij : S i →+* S j := σ i j h
  let σjLim : S j →+* S∞ := Ring.DirectLimit.of S (fun i j h ↦ σ i j h) j
  have hobj :
      (((ModuleCat.extendScalars (stageTargetMap i)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj Cᵢ) =
        (((ModuleCat.extendScalars (σjLim.comp σij)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj Cᵢ) := by
    simpa [Cᵢ, stageNaiveCotangentBaseChange] using
      congrArg
        (fun t ↦
          ((ModuleCat.extendScalars t).mapHomologicalComplex (ComplexShape.down ℕ)).obj Cᵢ)
        (stageTargetMap_comp (σ := σ) h).symm
  exact
    eqToHom hobj ≫
      ((NatIso.mapHomologicalComplex
          (ModuleCat.extendScalarsComp σij σjLim)
        (ComplexShape.down ℕ)).hom.app Cᵢ) ≫
      ((ModuleCat.extendScalars σjLim).mapHomologicalComplex
        (ComplexShape.down ℕ)).map
        (stageNaiveCotangentTransitionBase hcomm h)

/-- Helper for Lemma 10.134.9: in degree `0`, the `S∞`-ambient transition map sends the unit
tensor of a stage cotangent-space class to the unit tensor of its image at the later stage. -/
private theorem stageNaiveCotangentBaseChangeTransition_f_zero_unit_tensor
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j)
    (y : ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension).CotangentSpace) :
    let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
    let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
    let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
    let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
    let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
    let _ : Algebra (R i) S∞ :=
      ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
        (stageBaseMap (ρ := ρ) i)).toAlgebra
    let _ : Algebra (R j) R∞ := (stageBaseMap (ρ := ρ) j).toAlgebra
    let _ : Algebra (S j) S∞ := (stageTargetMap (σ := σ) j).toAlgebra
    let _ : Algebra (R j) S∞ :=
      ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
        (stageBaseMap (ρ := ρ) j)).toAlgebra
    let _ : Algebra R∞ S∞ :=
      (Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).toAlgebra
    let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
    let _ : IsScalarTower (R i) (R j) R∞ := IsScalarTower.of_algebraMap_eq'
      (stageBaseMap_comp (ρ := ρ) h).symm
    let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) S∞ :=
      IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
    let _ : IsScalarTower (R j) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R j) (S j) S∞ :=
      IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm j)
    let _ : IsScalarTower (S i) (S j) S∞ := IsScalarTower.of_algebraMap_eq'
      (stageTargetMap_comp (σ := σ) h).symm
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
    let fij : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
    (((stageNaiveCotangentBaseChangeTransition (ρ := ρ) (σ := σ) hcomm h).f 0).hom)
        (((1 : S∞) ⊗ₜ[S i] y)) =
      ((1 : S∞) ⊗ₜ[S j] Extension.CotangentSpace.map fij y) := by
  let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
  let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
  let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
  let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
  let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
  let _ : Algebra (R i) S∞ :=
    ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
      (stageBaseMap (ρ := ρ) i)).toAlgebra
  let _ : Algebra (R j) R∞ := (stageBaseMap (ρ := ρ) j).toAlgebra
  let _ : Algebra (S j) S∞ := (stageTargetMap (σ := σ) j).toAlgebra
  let _ : Algebra (R j) S∞ :=
    ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
      (stageBaseMap (ρ := ρ) j)).toAlgebra
  let _ : Algebra R∞ S∞ :=
    (Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).toAlgebra
  let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
  let _ : IsScalarTower (R i) (R j) R∞ := IsScalarTower.of_algebraMap_eq'
    (stageBaseMap_comp (ρ := ρ) h).symm
  let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
  let _ : IsScalarTower (R j) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R j) (S j) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm j)
  let _ : IsScalarTower (S i) (S j) S∞ := IsScalarTower.of_algebraMap_eq'
    (stageTargetMap_comp (σ := σ) h).symm
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  let Cᵢ : ChainComplex (ModuleCat (S i)) ℕ :=
    Algebra.Extension.naiveCotangentChainComplex Pi.toExtension
  let σij : S i →+* S j := σ i j h
  let σjLim : S j →+* S∞ := Ring.DirectLimit.of S (fun i j h ↦ σ i j h) j
  let fij : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
  have hobj :
      (((ModuleCat.extendScalars (stageTargetMap i)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj Cᵢ) =
        (((ModuleCat.extendScalars (σjLim.comp σij)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj Cᵢ) := by
    simpa [Cᵢ, stageNaiveCotangentBaseChange] using
      congrArg
        (fun t ↦
          ((ModuleCat.extendScalars t).mapHomologicalComplex (ComplexShape.down ℕ)).obj Cᵢ)
        (stageTargetMap_comp (σ := σ) h).symm
  have hstage :
      (((stageNaiveCotangentTransitionBase (ρ := ρ) (σ := σ) hcomm h).f 0).hom)
          (((1 : S j) ⊗ₜ[S i] y)) =
        Extension.CotangentSpace.map fij y := by
    -- Evaluate the transport-free stage transition on the canonical generator.
    simpa [ModuleCat.extendRestrictScalarsAdj_unit_app_apply] using
      stageNaiveCotangentTransitionBase_degree_zero_after_transport
        (ρ := ρ) (σ := σ) hcomm h y
  have hmain :
      ((((eqToHom hobj) ≫
          ((NatIso.mapHomologicalComplex
              (ModuleCat.extendScalarsComp σij σjLim) (ComplexShape.down ℕ)).hom.app Cᵢ) ≫
          ((ModuleCat.extendScalars σjLim).mapHomologicalComplex
            (ComplexShape.down ℕ)).map
            (stageNaiveCotangentTransitionBase (ρ := ρ) (σ := σ) hcomm h)).f 0).hom)
        (((1 : S∞) ⊗ₜ[S i] y)) =
      ((1 : S∞) ⊗ₜ[S j] Extension.CotangentSpace.map fij y) := by
    -- Route correction: first strip the front `eqToHom`, then compute the remaining
    -- transport-free composite on the unit tensor.
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.eqToHom_f]
    cases hobj
    simp only [eqToHom_refl, Category.id_comp]
    erw [ModuleCat.extendScalarsComp_hom_app_one_tmul]
    rw [Functor.mapHomologicalComplex_map_f, ModuleCat.ExtendScalars.map_tmul]
    simpa [hstage]
  simpa [stageNaiveCotangentBaseChangeTransition, Cᵢ, σij, σjLim] using hmain

/-- Helper for Lemma 10.134.9: in degree `1`, the `S∞`-ambient transition map sends the unit
tensor of a stage conormal class to the unit tensor of its image at the later stage. -/
private theorem stageNaiveCotangentBaseChangeTransition_f_one_unit_tensor
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j)
    (x : ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension).Cotangent) :
    let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
    let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
    let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
    let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
    let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
    let _ : Algebra (R i) S∞ :=
      ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
        (stageBaseMap (ρ := ρ) i)).toAlgebra
    let _ : Algebra (R j) R∞ := (stageBaseMap (ρ := ρ) j).toAlgebra
    let _ : Algebra (S j) S∞ := (stageTargetMap (σ := σ) j).toAlgebra
    let _ : Algebra (R j) S∞ :=
      ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
        (stageBaseMap (ρ := ρ) j)).toAlgebra
    let _ : Algebra R∞ S∞ :=
      (Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).toAlgebra
    let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
    let _ : IsScalarTower (R i) (R j) R∞ := IsScalarTower.of_algebraMap_eq'
      (stageBaseMap_comp (ρ := ρ) h).symm
    let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) S∞ :=
      IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
    let _ : IsScalarTower (R j) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R j) (S j) S∞ :=
      IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm j)
    let _ : IsScalarTower (S i) (S j) S∞ := IsScalarTower.of_algebraMap_eq'
      (stageTargetMap_comp (σ := σ) h).symm
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
    let fij : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
    (((stageNaiveCotangentBaseChangeTransition (ρ := ρ) (σ := σ) hcomm h).f 1).hom)
        (((1 : S∞) ⊗ₜ[S i] ULift.up x)) =
      ((1 : S∞) ⊗ₜ[S j] ULift.up (Extension.Cotangent.map fij x)) := by
  let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
  let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
  let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
  let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
  let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
  let _ : Algebra (R i) S∞ :=
    ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
      (stageBaseMap (ρ := ρ) i)).toAlgebra
  let _ : Algebra (R j) R∞ := (stageBaseMap (ρ := ρ) j).toAlgebra
  let _ : Algebra (S j) S∞ := (stageTargetMap (σ := σ) j).toAlgebra
  let _ : Algebra (R j) S∞ :=
    ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
      (stageBaseMap (ρ := ρ) j)).toAlgebra
  let _ : Algebra R∞ S∞ :=
    (Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).toAlgebra
  let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
  let _ : IsScalarTower (R i) (R j) R∞ := IsScalarTower.of_algebraMap_eq'
    (stageBaseMap_comp (ρ := ρ) h).symm
  let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
  let _ : IsScalarTower (R j) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R j) (S j) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm j)
  let _ : IsScalarTower (S i) (S j) S∞ := IsScalarTower.of_algebraMap_eq'
    (stageTargetMap_comp (σ := σ) h).symm
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  let Cᵢ : ChainComplex (ModuleCat (S i)) ℕ :=
    Algebra.Extension.naiveCotangentChainComplex Pi.toExtension
  let σij : S i →+* S j := σ i j h
  let σjLim : S j →+* S∞ := Ring.DirectLimit.of S (fun i j h ↦ σ i j h) j
  let fij : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
  have hobj :
      (((ModuleCat.extendScalars (stageTargetMap i)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj Cᵢ) =
        (((ModuleCat.extendScalars (σjLim.comp σij)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj Cᵢ) := by
    simpa [Cᵢ, stageNaiveCotangentBaseChange] using
      congrArg
        (fun t ↦
          ((ModuleCat.extendScalars t).mapHomologicalComplex (ComplexShape.down ℕ)).obj Cᵢ)
        (stageTargetMap_comp (σ := σ) h).symm
  have hstage :
      (((stageNaiveCotangentTransitionBase (ρ := ρ) (σ := σ) hcomm h).f 1).hom)
          (((1 : S j) ⊗ₜ[S i] ULift.up x)) =
        ULift.up (Extension.Cotangent.map fij x) := by
    -- Evaluate the transport-free stage transition on the canonical conormal generator.
    simpa [ModuleCat.extendRestrictScalarsAdj_unit_app_apply] using
      stageNaiveCotangentBaseChangeTransition_degree_one_generator_after_transport
        (ρ := ρ) (σ := σ) hcomm h x
  have hmain :
      ((((eqToHom hobj) ≫
          ((NatIso.mapHomologicalComplex
              (ModuleCat.extendScalarsComp σij σjLim) (ComplexShape.down ℕ)).hom.app Cᵢ) ≫
          ((ModuleCat.extendScalars σjLim).mapHomologicalComplex
            (ComplexShape.down ℕ)).map
            (stageNaiveCotangentTransitionBase (ρ := ρ) (σ := σ) hcomm h)).f 1).hom)
        (((1 : S∞) ⊗ₜ[S i] ULift.up x)) =
      ((1 : S∞) ⊗ₜ[S j] ULift.up (Extension.Cotangent.map fij x)) := by
    -- Route correction: the degree-`1` transport is normalized in the same order as degree `0`.
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.eqToHom_f]
    cases hobj
    simp only [eqToHom_refl, Category.id_comp]
    erw [ModuleCat.extendScalarsComp_hom_app_one_tmul]
    rw [Functor.mapHomologicalComplex_map_f, ModuleCat.ExtendScalars.map_tmul]
    simpa [hstage]
  simpa [stageNaiveCotangentBaseChangeTransition, Cᵢ, σij, σjLim] using hmain

/-- Helper for Lemma 10.134.9: each stage base-changed naive cotangent complex maps canonically to
the target owner `NL_{S∞⁄R∞}`. -/
private noncomputable def stageNaiveCotangentToTarget
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I) :
    @stageNaiveCotangentBaseChange I _ R S _ _ _ σ i ⟶
      @targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm := by
  let σiLim : S i →+* S∞ := Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i
  let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
  let _ : Algebra (S i) S∞ := σiLim.toAlgebra
  let _ : Algebra (R i) S∞ :=
    ((Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).comp
      (stageBaseMap (ρ := ρ) i)).toAlgebra
  let _ : Algebra R∞ S∞ :=
    (Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).toAlgebra
  let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  let C₁ : ChainComplex (ModuleCat S∞) ℕ :=
    (((ModuleCat.extendScalars σiLim).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
        (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension))
  let C₂ : ChainComplex (ModuleCat S∞) ℕ :=
    @targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm
  let f : Pi.toExtension.Hom Pinf.toExtension :=
    (Generators.defaultHom Pi Pinf).toExtensionHom
  let f₀' :
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0 ⟶
        (ModuleCat.restrictScalars σiLim).obj (C₂.X 0) :=
    ModuleCat.ofHom (Extension.CotangentSpace.map f) ≫
      (restrictOfIso Pinf.toExtension.CotangentSpace).inv
  let f₀ : C₁.X 0 ⟶ C₂.X 0 :=
    ((ModuleCat.extendRestrictScalarsAdj σiLim).homEquiv _ _).symm f₀'
  let liftf : ULift Pi.toExtension.Cotangent →ₗ[S i]
      ULift Pinf.toExtension.Cotangent :=
    { toFun := fun x ↦ ULift.up (Extension.Cotangent.map f x.down)
      map_add' := by
        intro x y
        ext <;> simp
      map_smul' := by
        intro r x
        ext <;> simp }
  let f₁' :
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 1 ⟶
        (ModuleCat.restrictScalars σiLim).obj (C₂.X 1) :=
    ModuleCat.ofHom liftf ≫
      (restrictOfIso (ULift Pinf.toExtension.Cotangent)).inv
  let f₁ : C₁.X 1 ⟶ C₂.X 1 :=
    ((ModuleCat.extendRestrictScalarsAdj σiLim).homEquiv _ _).symm f₁'
  refine ChainComplex.mkHom _ _ f₀ f₁ ?_ ?_
  · -- Check the square on the unit tensors that generate the extended degree-`1` module.
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    rcases x with ⟨x⟩
    -- First normalize the transported degree-`1` generator and the transported degree-`0` image.
    have hgen :
        f₁ (((1 : S∞) ⊗ₜ[S i] ULift.up x)) =
          ULift.up (Extension.Cotangent.map f x) := by
      have hAdj :
          ((ModuleCat.extendRestrictScalarsAdj σiLim).homEquiv _ _ f₁)
            (ULift.up x) =
          f₁ (((1 : S∞) ⊗ₜ[S i] ULift.up x)) := by
        simpa using
          (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
            (f := σiLim)
            (φ := f₁)
            (m := ULift.up x))
      have hTranspose :
          f₁ (((1 : S∞) ⊗ₜ[S i] ULift.up x)) =
            f₁' (ULift.up x) := by
        simpa [f₁] using hAdj.symm
      refine Eq.trans hTranspose ?_
      change
        (restrictOfIso (ULift Pinf.toExtension.Cotangent)).inv
            (liftf (ULift.up x)) =
          ULift.up (Extension.Cotangent.map f x)
      rfl
    have hzero :
        f₀ (((1 : S∞) ⊗ₜ[S i] Pi.toExtension.cotangentComplex x)) =
          Pinf.toExtension.cotangentComplex (Extension.Cotangent.map f x) := by
      have hAdj :
          ((ModuleCat.extendRestrictScalarsAdj σiLim).homEquiv _ _ f₀)
            (Pi.toExtension.cotangentComplex x) =
          f₀ (((1 : S∞) ⊗ₜ[S i] Pi.toExtension.cotangentComplex x)) := by
        simpa using
          (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
            (f := σiLim)
            (φ := f₀)
            (m := Pi.toExtension.cotangentComplex x))
      have hTranspose :
          f₀ (((1 : S∞) ⊗ₜ[S i] Pi.toExtension.cotangentComplex x)) =
            f₀' (Pi.toExtension.cotangentComplex x) := by
        simpa [f₀] using hAdj.symm
      refine Eq.trans hTranspose ?_
      change
        (restrictOfIso Pinf.toExtension.CotangentSpace).inv
            ((Extension.CotangentSpace.map f) (Pi.toExtension.cotangentComplex x)) =
          Pinf.toExtension.cotangentComplex (Extension.Cotangent.map f x)
      simpa using
        LinearMap.congr_fun (Extension.CotangentSpace.map_comp_cotangentComplex f) x
    -- Normalize the source differential on the canonical degree-`1` generator.
    have hsource :
        C₁.d 1 0 (((1 : S∞) ⊗ₜ[S i] ULift.up x)) =
          ((1 : S∞) ⊗ₜ[S i] Pi.toExtension.cotangentComplex x) := by
      rw [CategoryTheory.Functor.mapHomologicalComplex_obj_d,
        Extension.naiveCotangentChainComplex_d_1_0]
      rfl
    change
      C₂.d 1 0 (f₁ (((1 : S∞) ⊗ₜ[S i] ULift.up x))) =
        f₀ (C₁.d 1 0 (((1 : S∞) ⊗ₜ[S i] ULift.up x)))
    rw [hgen]
    rw [Extension.naiveCotangentChainComplex_d_1_0]
    rw [hsource]
    simpa using hzero.symm
  · intro n p
    -- The target and every stage complex are two-term, so higher squares are zero.
    refine ⟨0, ?_⟩
    let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
    rw [Extension.naiveCotangentChainComplex_d_succ_succ Pinf.toExtension n]
    rw [CategoryTheory.Functor.mapHomologicalComplex_obj_d,
      Extension.naiveCotangentChainComplex_d_succ_succ Pi.toExtension n]
    rw [CategoryTheory.Functor.map_zero]
    simp

/-- Helper for Lemma 10.134.9: the degree-`0` component of the canonical map to the target sends
the adjunction-unit image of `cotangentComplex x` to the expected cotangent-space map. -/
private theorem stageNaiveCotangentToTarget_degree_zero_after_transport
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I)
    (y : ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension).CotangentSpace) :
    let σiLim : S i →+* S∞ := Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i
    let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
    let _ : Algebra (S i) S∞ := σiLim.toAlgebra
    let _ : Algebra (R i) S∞ :=
      ((Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).comp
        (stageBaseMap (ρ := ρ) i)).toAlgebra
    let _ : Algebra R∞ S∞ :=
      (Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).toAlgebra
    let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) S∞ :=
      IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
    let C₁ : ChainComplex (ModuleCat S∞) ℕ :=
      (((ModuleCat.extendScalars σiLim).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension))
    let C₂ : ChainComplex (ModuleCat S∞) ℕ :=
      @targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm
    let f : Pi.toExtension.Hom Pinf.toExtension :=
      (Generators.defaultHom Pi Pinf).toExtensionHom
    let f₀' :
        (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0 ⟶
          (ModuleCat.restrictScalars σiLim).obj (C₂.X 0) :=
      ModuleCat.ofHom (Extension.CotangentSpace.map f) ≫
        (restrictOfIso Pinf.toExtension.CotangentSpace).inv
    let f₀ : C₁.X 0 ⟶ C₂.X 0 :=
      ((ModuleCat.extendRestrictScalarsAdj σiLim).homEquiv _ _).symm f₀'
    f₀ (((ModuleCat.extendRestrictScalarsAdj σiLim).unit.app
        ((Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0))
      y) =
      Extension.CotangentSpace.map f y := by
  let σiLim : S i →+* S∞ := Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i
  let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
  let _ : Algebra (S i) S∞ := σiLim.toAlgebra
  let _ : Algebra (R i) S∞ :=
    ((Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).comp
      (stageBaseMap (ρ := ρ) i)).toAlgebra
  let _ : Algebra R∞ S∞ :=
    (Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).toAlgebra
  let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  let C₁ : ChainComplex (ModuleCat S∞) ℕ :=
    (((ModuleCat.extendScalars σiLim).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension))
  let C₂ : ChainComplex (ModuleCat S∞) ℕ :=
    @targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm
  let f : Pi.toExtension.Hom Pinf.toExtension := (Generators.defaultHom Pi Pinf).toExtensionHom
  let f₀' :
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0 ⟶
        (ModuleCat.restrictScalars σiLim).obj (C₂.X 0) :=
    ModuleCat.ofHom (Extension.CotangentSpace.map f) ≫
      (restrictOfIso Pinf.toExtension.CotangentSpace).inv
  let f₀ : C₁.X 0 ⟶ C₂.X 0 :=
    ((ModuleCat.extendRestrictScalarsAdj σiLim).homEquiv _ _).symm f₀'
  -- Remove the scalar-extension adjunction transport before reading off the target cotangent map.
  change f₀ (((ModuleCat.extendRestrictScalarsAdj σiLim).unit.app
      ((Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0))
    y) =
    Extension.CotangentSpace.map f y
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  have hAdj :
      ((ModuleCat.extendRestrictScalarsAdj σiLim).homEquiv _ _ f₀) y =
        f₀ (((1 : S∞) ⊗ₜ[S i] y)) := by
    simpa using
      (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
        (f := σiLim)
        (φ := f₀)
        (m := y))
  have hTranspose :
      f₀ (((1 : S∞) ⊗ₜ[S i] y)) = f₀' y := by
    simpa [f₀] using hAdj.symm
  refine Eq.trans hTranspose ?_
  change
    (restrictOfIso Pinf.toExtension.CotangentSpace).inv
        ((Extension.CotangentSpace.map f) y) =
      Extension.CotangentSpace.map f y
  rfl

/-- Helper for Lemma 10.134.9: the degree-`0` component of the canonical map to the target sends
the adjunction-unit image of `cotangentComplex x` to the expected cotangent-space map. -/
private theorem stageNaiveCotangentToTarget_degree_zero_on_cotangent
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I)
    (x : ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension).Cotangent) :
    let σiLim : S i →+* S∞ := Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i
    let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
    let _ : Algebra (S i) S∞ := σiLim.toAlgebra
    let _ : Algebra (R i) S∞ :=
      ((Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).comp
        (stageBaseMap (ρ := ρ) i)).toAlgebra
    let _ : Algebra R∞ S∞ :=
      (Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).toAlgebra
    let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) S∞ :=
      IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
    let C₁ : ChainComplex (ModuleCat S∞) ℕ :=
      (((ModuleCat.extendScalars σiLim).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension))
    let C₂ : ChainComplex (ModuleCat S∞) ℕ :=
      @targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm
    let f : Pi.toExtension.Hom Pinf.toExtension :=
      (Generators.defaultHom Pi Pinf).toExtensionHom
    let f₀' :
        (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0 ⟶
          (ModuleCat.restrictScalars σiLim).obj (C₂.X 0) :=
      ModuleCat.ofHom (Extension.CotangentSpace.map f) ≫
        (restrictOfIso Pinf.toExtension.CotangentSpace).inv
    let f₀ : C₁.X 0 ⟶ C₂.X 0 :=
      ((ModuleCat.extendRestrictScalarsAdj σiLim).homEquiv _ _).symm f₀'
    f₀ (((ModuleCat.extendRestrictScalarsAdj σiLim).unit.app
        ((Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0))
      (Pi.toExtension.cotangentComplex x)) =
      Extension.CotangentSpace.map f (Pi.toExtension.cotangentComplex x) := by
  let σiLim : S i →+* S∞ := Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i
  let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
  let _ : Algebra (S i) S∞ := σiLim.toAlgebra
  let _ : Algebra (R i) S∞ :=
    ((Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).comp
      (stageBaseMap (ρ := ρ) i)).toAlgebra
  let _ : Algebra R∞ S∞ :=
    (Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).toAlgebra
  let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  let C₁ : ChainComplex (ModuleCat S∞) ℕ :=
    (((ModuleCat.extendScalars σiLim).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension))
  let C₂ : ChainComplex (ModuleCat S∞) ℕ :=
    @targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm
  let f : Pi.toExtension.Hom Pinf.toExtension := (Generators.defaultHom Pi Pinf).toExtensionHom
  let f₀' :
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0 ⟶
        (ModuleCat.restrictScalars σiLim).obj (C₂.X 0) :=
    ModuleCat.ofHom (Extension.CotangentSpace.map f) ≫
      (restrictOfIso Pinf.toExtension.CotangentSpace).inv
  let f₀ : C₁.X 0 ⟶ C₂.X 0 :=
    ((ModuleCat.extendRestrictScalarsAdj σiLim).homEquiv _ _).symm f₀'
  -- Re-express the target-side formula with local names before applying the adjunction formula.
  change f₀ (((ModuleCat.extendRestrictScalarsAdj σiLim).unit.app
      ((Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0))
    (Pi.toExtension.cotangentComplex x)) =
    Extension.CotangentSpace.map f (Pi.toExtension.cotangentComplex x)
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  have hAdj :
      ((ModuleCat.extendRestrictScalarsAdj σiLim).homEquiv _ _ f₀)
        (Pi.toExtension.cotangentComplex x) =
      f₀ (((1 : S∞) ⊗ₜ[S i] Pi.toExtension.cotangentComplex x)) := by
    simpa using
      (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
        (f := σiLim)
        (φ := f₀)
        (m := Pi.toExtension.cotangentComplex x))
  have hTranspose :
      f₀ (((1 : S∞) ⊗ₜ[S i] Pi.toExtension.cotangentComplex x)) =
        f₀' (Pi.toExtension.cotangentComplex x) := by
    simpa [f₀] using hAdj.symm
  refine Eq.trans hTranspose ?_
  change
    (restrictOfIso Pinf.toExtension.CotangentSpace).inv
        ((Extension.CotangentSpace.map f) (Pi.toExtension.cotangentComplex x)) =
      Extension.CotangentSpace.map f (Pi.toExtension.cotangentComplex x)
  rfl

/-- Helper for Lemma 10.134.9: the degree-`0` component of the canonical map to the target sends
the adjunction-unit image of `cotangentComplex x` to the target cotangent complex of the mapped
generator. -/
private theorem stageNaiveCotangentToTarget_degree_zero_on_mapped_cotangent
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I)
    (x : ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension).Cotangent) :
    let σiLim : S i →+* S∞ := Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i
    let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
    let _ : Algebra (S i) S∞ := σiLim.toAlgebra
    let _ : Algebra (R i) S∞ :=
      ((Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).comp
        (stageBaseMap (ρ := ρ) i)).toAlgebra
    let _ : Algebra R∞ S∞ :=
      (Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).toAlgebra
    let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) S∞ :=
      IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
    let C₁ : ChainComplex (ModuleCat S∞) ℕ :=
      (((ModuleCat.extendScalars σiLim).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension))
    let C₂ : ChainComplex (ModuleCat S∞) ℕ :=
      @targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm
    let f : Pi.toExtension.Hom Pinf.toExtension :=
      (Generators.defaultHom Pi Pinf).toExtensionHom
    let f₀' :
        (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0 ⟶
          (ModuleCat.restrictScalars σiLim).obj (C₂.X 0) :=
      ModuleCat.ofHom (Extension.CotangentSpace.map f) ≫
        (restrictOfIso Pinf.toExtension.CotangentSpace).inv
    let f₀ : C₁.X 0 ⟶ C₂.X 0 :=
      ((ModuleCat.extendRestrictScalarsAdj σiLim).homEquiv _ _).symm f₀'
    f₀ (((ModuleCat.extendRestrictScalarsAdj σiLim).unit.app
        ((Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0))
      (Pi.toExtension.cotangentComplex x)) =
      Pinf.toExtension.cotangentComplex (Extension.Cotangent.map f x) := by
  let σiLim : S i →+* S∞ := Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i
  let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
  let _ : Algebra (S i) S∞ := σiLim.toAlgebra
  let _ : Algebra (R i) S∞ :=
    ((Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).comp
      (stageBaseMap (ρ := ρ) i)).toAlgebra
  let _ : Algebra R∞ S∞ :=
    (Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).toAlgebra
  let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  let C₁ : ChainComplex (ModuleCat S∞) ℕ :=
    (((ModuleCat.extendScalars σiLim).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension))
  let C₂ : ChainComplex (ModuleCat S∞) ℕ :=
    @targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm
  let f : Pi.toExtension.Hom Pinf.toExtension := (Generators.defaultHom Pi Pinf).toExtensionHom
  let f₀' :
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 0 ⟶
        (ModuleCat.restrictScalars σiLim).obj (C₂.X 0) :=
    ModuleCat.ofHom (Extension.CotangentSpace.map f) ≫
      (restrictOfIso Pinf.toExtension.CotangentSpace).inv
  let f₀ : C₁.X 0 ⟶ C₂.X 0 :=
    ((ModuleCat.extendRestrictScalarsAdj σiLim).homEquiv _ _).symm f₀'
  -- The target-side degree-`0` map has the same owner-level normalization as the stage
  -- transition, now for the canonical map into the direct limit presentation.
  refine (stageNaiveCotangentToTarget_degree_zero_on_cotangent
    (ρ := ρ) (σ := σ) hcomm i x).trans ?_
  simpa using
    LinearMap.congr_fun (Extension.CotangentSpace.map_comp_cotangentComplex f) x

/-- Helper for Lemma 10.134.9: after transporting across the extend/restrict adjunction, the
degree-`1` component of the canonical map to the direct-limit target sends the canonical generator
to the mapped direct-limit generator. -/
private theorem stageNaiveCotangentToTarget_degree_one_generator_after_transport
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    (i : I)
    (x : ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension).Cotangent) :
    let σiLim : S i →+* S∞ := Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i
    let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
    let _ : Algebra (S i) S∞ := σiLim.toAlgebra
    let _ : Algebra (R i) S∞ :=
      ((Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).comp
        (stageBaseMap (ρ := ρ) i)).toAlgebra
    let _ : Algebra R∞ S∞ :=
      (Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).toAlgebra
    let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) S∞ :=
      IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
    let C₁ : ChainComplex (ModuleCat S∞) ℕ :=
      (((ModuleCat.extendScalars σiLim).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension))
    let C₂ : ChainComplex (ModuleCat S∞) ℕ :=
      @targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm
    let f : Pi.toExtension.Hom Pinf.toExtension :=
      (Generators.defaultHom Pi Pinf).toExtensionHom
    let liftf : ULift Pi.toExtension.Cotangent →ₗ[S i]
        ULift Pinf.toExtension.Cotangent :=
      { toFun := fun y ↦ ULift.up (Extension.Cotangent.map f y.down)
        map_add' := by
          intro y z
          ext <;> simp
        map_smul' := by
          intro r y
          ext <;> simp }
    let f₁' :
        (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 1 ⟶
          (ModuleCat.restrictScalars σiLim).obj (C₂.X 1) :=
      ModuleCat.ofHom liftf ≫
        (restrictOfIso (ULift Pinf.toExtension.Cotangent)).inv
    let f₁ : C₁.X 1 ⟶ C₂.X 1 :=
      ((ModuleCat.extendRestrictScalarsAdj σiLim).homEquiv _ _).symm f₁'
    f₁ (((ModuleCat.extendRestrictScalarsAdj σiLim).unit.app
        ((Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 1))
      (ULift.up x)) =
      ULift.up (Extension.Cotangent.map f x) := by
  let σiLim : S i →+* S∞ := Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i
  let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
  let _ : Algebra (S i) S∞ := σiLim.toAlgebra
  let _ : Algebra (R i) S∞ :=
    ((Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).comp
      (stageBaseMap (ρ := ρ) i)).toAlgebra
  let _ : Algebra R∞ S∞ :=
    (Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h).toAlgebra
  let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  let C₁ : ChainComplex (ModuleCat S∞) ℕ :=
    (((ModuleCat.extendScalars σiLim).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension))
  let C₂ : ChainComplex (ModuleCat S∞) ℕ :=
    @targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm
  let f : Pi.toExtension.Hom Pinf.toExtension := (Generators.defaultHom Pi Pinf).toExtensionHom
  let liftf : ULift Pi.toExtension.Cotangent →ₗ[S i]
      ULift Pinf.toExtension.Cotangent :=
    { toFun := fun y ↦ ULift.up (Extension.Cotangent.map f y.down)
      map_add' := by
        intro y z
        ext <;> simp
      map_smul' := by
        intro r y
        ext <;> simp }
  let f₁' :
      (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 1 ⟶
        (ModuleCat.restrictScalars σiLim).obj (C₂.X 1) :=
    ModuleCat.ofHom liftf ≫
      (restrictOfIso (ULift Pinf.toExtension.Cotangent)).inv
  let f₁ : C₁.X 1 ⟶ C₂.X 1 :=
    ((ModuleCat.extendRestrictScalarsAdj σiLim).homEquiv _ _).symm f₁'
  -- The target-side degree-`1` map is normalized by the same adjunction formula as the
  -- stage-to-stage map, now landing in the direct-limit presentation.
  change f₁ (((ModuleCat.extendRestrictScalarsAdj σiLim).unit.app
      ((Algebra.Extension.naiveCotangentChainComplex Pi.toExtension).X 1))
    (ULift.up x)) =
    ULift.up (Extension.Cotangent.map f x)
  rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
  have hAdj :
      ((ModuleCat.extendRestrictScalarsAdj σiLim).homEquiv _ _ f₁)
        (ULift.up x) =
      f₁ (((1 : S∞) ⊗ₜ[S i] ULift.up x)) := by
    simpa using
      (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
        (f := σiLim)
        (φ := f₁)
        (m := ULift.up x))
  have hTranspose :
      f₁ (((1 : S∞) ⊗ₜ[S i] ULift.up x)) =
        f₁' (ULift.up x) := by
    simpa [f₁] using hAdj.symm
  refine Eq.trans hTranspose ?_
  change
    (restrictOfIso (ULift Pinf.toExtension.Cotangent)).inv
        (liftf (ULift.up x)) =
      ULift.up (Extension.Cotangent.map f x)
  rfl

/-- Helper for Lemma 10.134.9: the degree-`1` differential of the explicit direct-limit source is
compatible with the stage transition maps. -/
private theorem stageNaiveCotangentBaseChangeTransition_comm_10
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j) :
    let Cᵢ := stageNaiveCotangentBaseChange (σ := σ) i
    let Cⱼ := stageNaiveCotangentBaseChange (σ := σ) j
    let τ := stageNaiveCotangentBaseChangeTransition (ρ := ρ) (σ := σ) hcomm h
    τ.f 1 ≫ Cⱼ.d 1 0 = Cᵢ.d 1 0 ≫ τ.f 0 := by
  -- Record the degree-`1 → 0` square before evaluating on direct-limit representatives.
  simpa using
    ((stageNaiveCotangentBaseChangeTransition
      (ρ := ρ) (σ := σ) hcomm h).comm 1 0)

/-- Helper for Lemma 10.134.9: the degree-`1` differential of the explicit direct-limit source is
compatible with the stage transition maps. -/
-- TODO: Replan this descent lemma after stabilizing the stage transition transport API; the only
-- missing ingredient is a reusable way to apply the degree `1 → 0` square inside the module
-- direct limit without triggering the current elaboration timeout.
private theorem naiveCotangentDirectLimitDifferential_compatible
    [DecidableEq I]
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j)
    (x : (stageNaiveCotangentBaseChange (σ := σ) i).X 1) :
    Module.DirectLimit.of S∞ I
      (fun k ↦ (@stageNaiveCotangentBaseChange I _ R S _ _ _ σ k).X 0)
      (fun _ _ hij ↦ (stageNaiveCotangentBaseChangeTransition
        (ρ := ρ) (σ := σ) hcomm hij).f 0 |>.hom) j
      (((stageNaiveCotangentBaseChange (σ := σ) j).d 1 0).hom
        (((stageNaiveCotangentBaseChangeTransition
          (ρ := ρ) (σ := σ) hcomm h).f 1).hom x)) =
    Module.DirectLimit.of S∞ I
      (fun k ↦ (@stageNaiveCotangentBaseChange I _ R S _ _ _ σ k).X 0)
      (fun _ _ hij ↦ (stageNaiveCotangentBaseChangeTransition
        (ρ := ρ) (σ := σ) hcomm hij).f 0 |>.hom) i
      (((stageNaiveCotangentBaseChange (σ := σ) i).d 1 0).hom x) := by
  -- Route correction: this compatibility is already encoded in the chain-map square for
  -- `stageNaiveCotangentBaseChangeTransition`, so the direct-limit claim follows by rewriting
  -- the stage-`j` differential through that square and then applying `Module.DirectLimit.of_f`.
  have hsq :=
    stageNaiveCotangentBaseChangeTransition_comm_10
      (ρ := ρ) (σ := σ) hcomm h
  have hsq_apply :
      (((stageNaiveCotangentBaseChange (σ := σ) j).d 1 0).hom
          ((((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm h).f 1).hom) x)) =
        (((stageNaiveCotangentBaseChangeTransition
          (ρ := ρ) (σ := σ) hcomm h).f 0).hom
          ((((stageNaiveCotangentBaseChange (σ := σ) i).d 1 0).hom) x)) := by
    -- Evaluate the degree-`1 → 0` commutative square on the stage representative `x`.
    simpa using congrArg (fun φ ↦ φ.hom x) hsq
  rw [hsq_apply]
  -- The direct-limit relation identifies a stage element with any later representative of it.
  simpa using
    (Module.DirectLimit.of_f
      (R := S∞) (ι := I)
      (G := fun k ↦ (@stageNaiveCotangentBaseChange I _ R S _ _ _ σ k).X 0)
      (f := fun _ _ hij ↦ (stageNaiveCotangentBaseChangeTransition
        (ρ := ρ) (σ := σ) hcomm hij).f 0 |>.hom)
      (i := i) (j := j) (hij := h)
      (x := (((stageNaiveCotangentBaseChange (σ := σ) i).d 1 0).hom x)))

/-- Helper for Lemma 10.134.9: after moving a degree-`0` generator from stage `i` to stage `j`,
the target map at stage `j` agrees with the direct target map from stage `i`. -/
private theorem stageNaiveCotangentToTarget_degree_zero_on_mapped_generator
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j)
    (y : ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension).CotangentSpace) :
    let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
    let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
    let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
    let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
    let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
    let _ : Algebra (R i) S∞ :=
      ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
        (stageBaseMap (ρ := ρ) i)).toAlgebra
    let _ : Algebra (R j) R∞ := (stageBaseMap (ρ := ρ) j).toAlgebra
    let _ : Algebra (S j) S∞ := (stageTargetMap (σ := σ) j).toAlgebra
    let _ : Algebra (R j) S∞ :=
      ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
        (stageBaseMap (ρ := ρ) j)).toAlgebra
    let _ : Algebra R∞ S∞ :=
      (Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).toAlgebra
    let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
    let _ : IsScalarTower (R i) (R j) R∞ := IsScalarTower.of_algebraMap_eq'
      (stageBaseMap_comp (ρ := ρ) h).symm
    let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) S∞ :=
      IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
    let _ : IsScalarTower (R j) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R j) (S j) S∞ :=
      IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm j)
    let _ : IsScalarTower (S i) (S j) S∞ := IsScalarTower.of_algebraMap_eq'
      (stageTargetMap_comp (σ := σ) h).symm
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
    let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
    let fij : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
    let fjInf : Pj.toExtension.Hom Pinf.toExtension :=
      (Generators.defaultHom Pj Pinf).toExtensionHom
    let fiInf : Pi.toExtension.Hom Pinf.toExtension :=
      (Generators.defaultHom Pi Pinf).toExtensionHom
    (((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm j).f 0).hom)
        (((1 : S∞) ⊗ₜ[S j] Extension.CotangentSpace.map fij y)) =
      Extension.CotangentSpace.map fiInf y := by
  let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
  let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
  let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
  let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
  let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
  let _ : Algebra (R i) S∞ :=
    ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
      (stageBaseMap (ρ := ρ) i)).toAlgebra
  let _ : Algebra (R j) R∞ := (stageBaseMap (ρ := ρ) j).toAlgebra
  let _ : Algebra (S j) S∞ := (stageTargetMap (σ := σ) j).toAlgebra
  let _ : Algebra (R j) S∞ :=
    ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
      (stageBaseMap (ρ := ρ) j)).toAlgebra
  let _ : Algebra R∞ S∞ :=
    (Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).toAlgebra
  let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
  let _ : IsScalarTower (R i) (R j) R∞ := IsScalarTower.of_algebraMap_eq'
    (stageBaseMap_comp (ρ := ρ) h).symm
  let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
  let _ : IsScalarTower (R j) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R j) (S j) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm j)
  let _ : IsScalarTower (S i) (S j) S∞ := IsScalarTower.of_algebraMap_eq'
    (stageTargetMap_comp (σ := σ) h).symm
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  let fij : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
  let fjInf : Pj.toExtension.Hom Pinf.toExtension :=
    (Generators.defaultHom Pj Pinf).toExtensionHom
  let fiInf : Pi.toExtension.Hom Pinf.toExtension :=
    (Generators.defaultHom Pi Pinf).toExtensionHom
  -- Evaluate the stage-`j` target map on the moved generator and collapse the composite
  -- presentation map with the already proved cotangent-space compatibility.
  calc
    (((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm j).f 0).hom)
        (((1 : S∞) ⊗ₜ[S j] Extension.CotangentSpace.map fij y)) =
      Extension.CotangentSpace.map fjInf (Extension.CotangentSpace.map fij y) := by
        simpa [fjInf] using
          stageNaiveCotangentToTarget_degree_zero_after_transport
            (ρ := ρ) (σ := σ) hcomm j (Extension.CotangentSpace.map fij y)
    _ = Extension.CotangentSpace.map fiInf y := by
        simpa [fij, fjInf, fiInf] using
          selfPresentation_toTarget_cotangentSpace_map_comp_apply
            (ρ := ρ) (σ := σ) hcomm h y

/-- Helper for Lemma 10.134.9: after moving a degree-`1` generator from stage `i` to stage `j`,
the target map at stage `j` agrees with the direct target map from stage `i`. -/
private theorem stageNaiveCotangentToTarget_degree_one_on_mapped_generator
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j)
    (x : ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension).Cotangent) :
    let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
    let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
    let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
    let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
    let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
    let _ : Algebra (R i) S∞ :=
      ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
        (stageBaseMap (ρ := ρ) i)).toAlgebra
    let _ : Algebra (R j) R∞ := (stageBaseMap (ρ := ρ) j).toAlgebra
    let _ : Algebra (S j) S∞ := (stageTargetMap (σ := σ) j).toAlgebra
    let _ : Algebra (R j) S∞ :=
      ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
        (stageBaseMap (ρ := ρ) j)).toAlgebra
    let _ : Algebra R∞ S∞ :=
      (Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).toAlgebra
    let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
    let _ : IsScalarTower (R i) (R j) R∞ := IsScalarTower.of_algebraMap_eq'
      (stageBaseMap_comp (ρ := ρ) h).symm
    let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) S∞ :=
      IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
    let _ : IsScalarTower (R j) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R j) (S j) S∞ :=
      IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm j)
    let _ : IsScalarTower (S i) (S j) S∞ := IsScalarTower.of_algebraMap_eq'
      (stageTargetMap_comp (σ := σ) h).symm
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
    let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
    let fij : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
    let fjInf : Pj.toExtension.Hom Pinf.toExtension :=
      (Generators.defaultHom Pj Pinf).toExtensionHom
    let fiInf : Pi.toExtension.Hom Pinf.toExtension :=
      (Generators.defaultHom Pi Pinf).toExtensionHom
    (((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm j).f 1).hom)
        (((1 : S∞) ⊗ₜ[S j] ULift.up (Extension.Cotangent.map fij x))) =
      ULift.up (Extension.Cotangent.map fiInf x) := by
  let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
  let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
  let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
  let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
  let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
  let _ : Algebra (R i) S∞ :=
    ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
      (stageBaseMap (ρ := ρ) i)).toAlgebra
  let _ : Algebra (R j) R∞ := (stageBaseMap (ρ := ρ) j).toAlgebra
  let _ : Algebra (S j) S∞ := (stageTargetMap (σ := σ) j).toAlgebra
  let _ : Algebra (R j) S∞ :=
    ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).comp
      (stageBaseMap (ρ := ρ) j)).toAlgebra
  let _ : Algebra R∞ S∞ :=
    (Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ hij ↦ hcomm hij).toAlgebra
  let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
  let _ : IsScalarTower (R i) (R j) R∞ := IsScalarTower.of_algebraMap_eq'
    (stageBaseMap_comp (ρ := ρ) h).symm
  let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
  let _ : IsScalarTower (R j) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R j) (S j) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm j)
  let _ : IsScalarTower (S i) (S j) S∞ := IsScalarTower.of_algebraMap_eq'
    (stageTargetMap_comp (σ := σ) h).symm
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  let fij : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
  let fjInf : Pj.toExtension.Hom Pinf.toExtension :=
    (Generators.defaultHom Pj Pinf).toExtensionHom
  let fiInf : Pi.toExtension.Hom Pinf.toExtension :=
    (Generators.defaultHom Pi Pinf).toExtensionHom
  -- Evaluate the stage-`j` target map on the moved conormal generator, then collapse the
  -- composite presentation map to the direct stage-to-target map.
  calc
    (((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm j).f 1).hom)
        (((1 : S∞) ⊗ₜ[S j] ULift.up (Extension.Cotangent.map fij x))) =
      ULift.up (Extension.Cotangent.map fjInf (Extension.Cotangent.map fij x)) := by
        simpa [fjInf] using
          stageNaiveCotangentToTarget_degree_one_generator_after_transport
            (ρ := ρ) (σ := σ) hcomm j (Extension.Cotangent.map fij x)
    _ = ULift.up (Extension.Cotangent.map fiInf x) := by
        congr 1
        simpa [fij, fjInf, fiInf] using
          selfPresentation_toTarget_cotangent_map_comp_apply
            (ρ := ρ) (σ := σ) hcomm h x

/-- Helper for Lemma 10.134.9: the degree-`0` target maps are compatible with the stage
transition maps of the explicit direct-limit source. -/
private theorem stageNaiveCotangentDegreeZeroToTarget_compatible
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j)
    (x : (stageNaiveCotangentBaseChange (σ := σ) i).X 0) :
    (((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm j).f 0).hom
        ((((stageNaiveCotangentBaseChangeTransition
          (ρ := ρ) (σ := σ) hcomm h).f 0).hom) x)) =
      (((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm i).f 0).hom) x := by
  let α :
      (stageNaiveCotangentBaseChange (σ := σ) i).X 0 ⟶
        (@targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm).X 0 :=
    (stageNaiveCotangentBaseChangeTransition (ρ := ρ) (σ := σ) hcomm h).f 0 ≫
      (stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm j).f 0
  let β :
      (stageNaiveCotangentBaseChange (σ := σ) i).X 0 ⟶
        (@targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm).X 0 :=
    (stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm i).f 0
  have hEq : α = β := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro y
    -- Route correction: after the stage-transition transport is normalized on unit tensors,
    -- compatibility is just the two source-faithful generator formulas.
    change
      (((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm j).f 0).hom)
          ((((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm h).f 0).hom)
            (((1 : S∞) ⊗ₜ[S i] y))) =
        (((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm i).f 0).hom)
          (((1 : S∞) ⊗ₜ[S i] y))
    calc
      (((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm j).f 0).hom)
          ((((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm h).f 0).hom)
            (((1 : S∞) ⊗ₜ[S i] y))) =
        (((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm j).f 0).hom)
          (((1 : S∞) ⊗ₜ[S j]
            Extension.CotangentSpace.map
              ((Generators.defaultHom
                  (Generators.self (R i) (S i))
                  (Generators.self (R j) (S j))).toExtensionHom) y)) := by
            rw [stageNaiveCotangentBaseChangeTransition_f_zero_unit_tensor
              (ρ := ρ) (σ := σ) hcomm h y]
      _ = (((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm i).f 0).hom)
            (((1 : S∞) ⊗ₜ[S i] y)) := by
            refine (stageNaiveCotangentToTarget_degree_zero_on_mapped_generator
              (ρ := ρ) (σ := σ) hcomm h y).trans ?_
            exact
              (stageNaiveCotangentToTarget_degree_zero_after_transport
                (ρ := ρ) (σ := σ) hcomm i y).symm
  simpa [α, β] using congrArg (fun φ ↦ φ x) hEq

/-- Helper for Lemma 10.134.9: the degree-`1` target maps are compatible with the stage
transition maps of the explicit direct-limit source. -/
private theorem stageNaiveCotangentDegreeOneToTarget_compatible
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i)))
    {i j : I} (h : i ≤ j)
    (x : (stageNaiveCotangentBaseChange (σ := σ) i).X 1) :
    (((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm j).f 1).hom
        ((((stageNaiveCotangentBaseChangeTransition
          (ρ := ρ) (σ := σ) hcomm h).f 1).hom) x)) =
      (((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm i).f 1).hom) x := by
  let α :
      (stageNaiveCotangentBaseChange (σ := σ) i).X 1 ⟶
        (@targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm).X 1 :=
    (stageNaiveCotangentBaseChangeTransition (ρ := ρ) (σ := σ) hcomm h).f 1 ≫
      (stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm j).f 1
  let β :
      (stageNaiveCotangentBaseChange (σ := σ) i).X 1 ⟶
        (@targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm).X 1 :=
    (stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm i).f 1
  have hEq : α = β := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    rcases x with ⟨x⟩
    -- Route correction: once the degree-`1` transition is normalized on generators, the
    -- cocone identity follows from the source-faithful generator computations on both sides.
    change
      (((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm j).f 1).hom)
          ((((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm h).f 1).hom)
            (((1 : S∞) ⊗ₜ[S i] ULift.up x))) =
        (((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm i).f 1).hom)
          (((1 : S∞) ⊗ₜ[S i] ULift.up x))
    calc
      (((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm j).f 1).hom)
          ((((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm h).f 1).hom)
            (((1 : S∞) ⊗ₜ[S i] ULift.up x))) =
        (((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm j).f 1).hom)
          (((1 : S∞) ⊗ₜ[S j]
            ULift.up (Extension.Cotangent.map
              ((Generators.defaultHom
                  (Generators.self (R i) (S i))
                  (Generators.self (R j) (S j))).toExtensionHom) x))) := by
            rw [stageNaiveCotangentBaseChangeTransition_f_one_unit_tensor
              (ρ := ρ) (σ := σ) hcomm h x]
      _ = (((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm i).f 1).hom)
            (((1 : S∞) ⊗ₜ[S i] ULift.up x)) := by
            refine (stageNaiveCotangentToTarget_degree_one_on_mapped_generator
              (ρ := ρ) (σ := σ) hcomm h x).trans ?_
            exact
              (stageNaiveCotangentToTarget_degree_one_generator_after_transport
                (ρ := ρ) (σ := σ) hcomm i x).symm
  simpa [α, β] using congrArg (fun φ ↦ φ x) hEq


/-- Helper for Lemma 10.134.9: the explicit degree-`0` direct-limit owner replacing the old
diagrammatic colimit route. -/
private noncomputable abbrev naiveCotangentDirectLimitDegreeZero :
    let _hcomm := hcomm
    ModuleCat (S∞) :=
  let _ : DecidableEq I := Classical.decEq I
  let G : I → Type u := fun i ↦ (stageNaiveCotangentBaseChange (σ := σ) i).X 0
  let μ : ∀ i j, i ≤ j → G i →ₗ[S∞] G j :=
    fun _ _ h ↦ ((stageNaiveCotangentBaseChangeTransition
      (ρ := ρ) (σ := σ) hcomm h).f 0).hom
  ModuleCat.of S∞ <| Module.DirectLimit G μ

/-- Helper for Lemma 10.134.9: the explicit degree-`1` direct-limit owner replacing the old
diagrammatic colimit route. -/
private noncomputable abbrev naiveCotangentDirectLimitDegreeOne :
    let _hcomm := hcomm
    ModuleCat (S∞) :=
  let _ : DecidableEq I := Classical.decEq I
  let G : I → Type u := fun i ↦ (stageNaiveCotangentBaseChange (σ := σ) i).X 1
  let μ : ∀ i j, i ≤ j → G i →ₗ[S∞] G j :=
    fun _ _ h ↦ ((stageNaiveCotangentBaseChangeTransition
      (ρ := ρ) (σ := σ) hcomm h).f 1).hom
  ModuleCat.of S∞ <| Module.DirectLimit G μ

/-- Helper for Lemma 10.134.9: the source differential on the explicit direct-limit model is the
descended stagewise differential `I_i / I_i² → S_i ⊗ Ω`. -/
private noncomputable def naiveCotangentDirectLimitDifferential :
    let _hcomm := hcomm
    naiveCotangentDirectLimitDegreeOne hcomm ⟶
      naiveCotangentDirectLimitDegreeZero hcomm :=
  let _ : DecidableEq I := Classical.decEq I
  let G₁ : I → Type u := fun i ↦ (stageNaiveCotangentBaseChange (σ := σ) i).X 1
  let μ₁ : ∀ i j, i ≤ j → G₁ i →ₗ[S∞] G₁ j :=
    fun _ _ h ↦ ((stageNaiveCotangentBaseChangeTransition
      (ρ := ρ) (σ := σ) hcomm h).f 1).hom
  let G₀ : I → Type u := fun i ↦ (stageNaiveCotangentBaseChange (σ := σ) i).X 0
  let μ₀ : ∀ i j, i ≤ j → G₀ i →ₗ[S∞] G₀ j :=
    fun _ _ h ↦ ((stageNaiveCotangentBaseChangeTransition
      (ρ := ρ) (σ := σ) hcomm h).f 0).hom
  let ν : ∀ i, G₁ i →ₗ[S∞] naiveCotangentDirectLimitDegreeZero hcomm :=
    fun i ↦
      (Module.DirectLimit.of S∞ I G₀ μ₀ i).comp
        (((stageNaiveCotangentBaseChange (σ := σ) i).d 1 0).hom)
  ModuleCat.ofHom <|
    Module.DirectLimit.lift S∞ I G₁ μ₁ ν fun _ _ h x ↦
      naiveCotangentDirectLimitDifferential_compatible (ρ := ρ) (σ := σ) hcomm h x

/-- Helper for Lemma 10.134.9: the descended differential evaluates on a stage representative as
the direct-limit class of the stage differential. -/
private theorem naiveCotangentDirectLimitDifferential_of_stage
    [DecidableEq I]
    (i : I) (x : (stageNaiveCotangentBaseChange (σ := σ) i).X 1) :
    (naiveCotangentDirectLimitDifferential (ρ := ρ) (σ := σ) hcomm).hom
        (Module.DirectLimit.of S∞ I
          (fun k ↦ (stageNaiveCotangentBaseChange (σ := σ) k).X 1)
          (fun _ _ hij ↦ ((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm hij).f 1).hom) i x) =
      Module.DirectLimit.of S∞ I
        (fun k ↦ (stageNaiveCotangentBaseChange (σ := σ) k).X 0)
        (fun _ _ hij ↦ ((stageNaiveCotangentBaseChangeTransition
          (ρ := ρ) (σ := σ) hcomm hij).f 0).hom) i
        (((stageNaiveCotangentBaseChange (σ := σ) i).d 1 0).hom x) := by
  -- Evaluate the direct-limit lift on the chosen stage class without unfolding the owner.
  simpa [naiveCotangentDirectLimitDifferential] using
    (Module.DirectLimit.lift_of (R := S∞) (ι := I)
      (G := fun k ↦ (stageNaiveCotangentBaseChange (σ := σ) k).X 1)
      (f := fun _ _ hij ↦ ((stageNaiveCotangentBaseChangeTransition
        (ρ := ρ) (σ := σ) hcomm hij).f 1).hom)
      (g := fun k ↦
        (Module.DirectLimit.of S∞ I
          (fun l ↦ (stageNaiveCotangentBaseChange (σ := σ) l).X 0)
          (fun _ _ hij ↦ ((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm hij).f 0).hom) k).comp
            (((stageNaiveCotangentBaseChange (σ := σ) k).d 1 0).hom))
      (Hg := fun _ _ hij y ↦
        naiveCotangentDirectLimitDifferential_compatible
          (ρ := ρ) (σ := σ) hcomm hij y)
      (i := i) (x := x))

/-- The filtered-colimit source complex built from the stagewise canonical naive cotangent
complexes `NL_{S_i⁄R_i}` after extending scalars along `S_i → S∞`. This is the source-facing
`colim NL_{S_i⁄R_i}` object of Tag `07BQ`, expressed in the common ambient category
`ChainComplex (ModuleCat S∞) ℕ`. -/
noncomputable def naiveCotangentDirectLimitModel :
    let _hcomm := hcomm
    ChainComplex (ModuleCat S∞) ℕ :=
  ChainComplex.mk'
    (naiveCotangentDirectLimitDegreeZero (ρ := ρ) (σ := σ) hcomm)
    (naiveCotangentDirectLimitDegreeOne (ρ := ρ) (σ := σ) hcomm)
    (naiveCotangentDirectLimitDifferential (ρ := ρ) (σ := σ) hcomm)
    (fun {_ _} _ ↦ ⟨ModuleCat.of S∞ PUnit, 0, zero_comp⟩)

/-- Helper for Lemma 10.134.9: the degree-`0` component of the canonical comparison from the
explicit direct-limit source to the target owner. -/
private noncomputable def naiveCotangentDirectLimitComparisonZero :
    let _hcomm := hcomm
    naiveCotangentDirectLimitDegreeZero hcomm ⟶ (targetNaiveCotangent hcomm).X 0 :=
  let _ : DecidableEq I := Classical.decEq I
  let G : I → Type u := fun i ↦ (stageNaiveCotangentBaseChange (σ := σ) i).X 0
  let μ : ∀ i j, i ≤ j → G i →ₗ[S∞] G j :=
    fun _ _ h ↦ ((stageNaiveCotangentBaseChangeTransition
      (ρ := ρ) (σ := σ) hcomm h).f 0).hom
  let ν : ∀ i, G i →ₗ[S∞] (targetNaiveCotangent hcomm).X 0 :=
    fun i ↦ ((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm i).f 0).hom
  ModuleCat.ofHom <|
    Module.DirectLimit.lift S∞ I G μ ν fun _ _ h x ↦
      stageNaiveCotangentDegreeZeroToTarget_compatible (ρ := ρ) (σ := σ) hcomm h x

/-- Helper for Lemma 10.134.9: the degree-`1` component of the canonical comparison from the
explicit direct-limit source to the target owner. -/
private noncomputable def naiveCotangentDirectLimitComparisonOne :
    let _hcomm := hcomm
    naiveCotangentDirectLimitDegreeOne hcomm ⟶ (targetNaiveCotangent hcomm).X 1 :=
  let _ : DecidableEq I := Classical.decEq I
  let G : I → Type u := fun i ↦ (stageNaiveCotangentBaseChange (σ := σ) i).X 1
  let μ : ∀ i j, i ≤ j → G i →ₗ[S∞] G j :=
    fun _ _ h ↦ ((stageNaiveCotangentBaseChangeTransition
      (ρ := ρ) (σ := σ) hcomm h).f 1).hom
  let ν : ∀ i, G i →ₗ[S∞] (targetNaiveCotangent hcomm).X 1 :=
    fun i ↦ ((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm i).f 1).hom
  ModuleCat.ofHom <|
    Module.DirectLimit.lift S∞ I G μ ν fun _ _ h x ↦
      stageNaiveCotangentDegreeOneToTarget_compatible (ρ := ρ) (σ := σ) hcomm h x

/-- Helper for Lemma 10.134.9: the degree-`0` comparison component sends a stage class to the
degree-`0` piece of the canonical stage-to-target chain map. -/
private theorem naiveCotangentDirectLimitComparisonZero_of_stage
    [DecidableEq I]
    (i : I) (x : (stageNaiveCotangentBaseChange (σ := σ) i).X 0) :
    (naiveCotangentDirectLimitComparisonZero (ρ := ρ) (σ := σ) hcomm).hom
        (Module.DirectLimit.of S∞ I
          (fun k ↦ (stageNaiveCotangentBaseChange (σ := σ) k).X 0)
          (fun _ _ hij ↦ ((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm hij).f 0).hom) i x) =
      ((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm i).f 0).hom x := by
  -- Evaluate the direct-limit lift on the chosen stage class.
  simpa [naiveCotangentDirectLimitComparisonZero] using
    (Module.DirectLimit.lift_of (R := S∞) (ι := I)
      (G := fun k ↦ (stageNaiveCotangentBaseChange (σ := σ) k).X 0)
      (f := fun _ _ hij ↦ ((stageNaiveCotangentBaseChangeTransition
        (ρ := ρ) (σ := σ) hcomm hij).f 0).hom)
      (g := fun k ↦ ((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm k).f 0).hom)
      (Hg := fun _ _ hij y ↦
        stageNaiveCotangentDegreeZeroToTarget_compatible
          (ρ := ρ) (σ := σ) hcomm hij y)
      (i := i) (x := x))

/-- Helper for Lemma 10.134.9: the degree-`1` comparison component sends a stage class to the
degree-`1` piece of the canonical stage-to-target chain map. -/
private theorem naiveCotangentDirectLimitComparisonOne_of_stage
    [DecidableEq I]
    (i : I) (x : (stageNaiveCotangentBaseChange (σ := σ) i).X 1) :
    (naiveCotangentDirectLimitComparisonOne (ρ := ρ) (σ := σ) hcomm).hom
        (Module.DirectLimit.of S∞ I
          (fun k ↦ (stageNaiveCotangentBaseChange (σ := σ) k).X 1)
          (fun _ _ hij ↦ ((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm hij).f 1).hom) i x) =
      ((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm i).f 1).hom x := by
  -- Evaluate the direct-limit lift on the chosen stage class.
  simpa [naiveCotangentDirectLimitComparisonOne] using
    (Module.DirectLimit.lift_of (R := S∞) (ι := I)
      (G := fun k ↦ (stageNaiveCotangentBaseChange (σ := σ) k).X 1)
      (f := fun _ _ hij ↦ ((stageNaiveCotangentBaseChangeTransition
        (ρ := ρ) (σ := σ) hcomm hij).f 1).hom)
      (g := fun k ↦ ((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm k).f 1).hom)
      (Hg := fun _ _ hij y ↦
        stageNaiveCotangentDegreeOneToTarget_compatible
          (ρ := ρ) (σ := σ) hcomm hij y)
      (i := i) (x := x))

/-- Helper for Lemma 10.134.9: on a single stage representative, the degree-`1 → 0` comparison
square is exactly the stage chain-map square. -/
private theorem naiveCotangentDirectLimitComparison_comm_10_on_stage
    [DecidableEq I]
    (i : I) (x : (stageNaiveCotangentBaseChange (σ := σ) i).X 1) :
    ((targetNaiveCotangent (ρ := ρ) (σ := σ) hcomm).d 1 0).hom
        (((naiveCotangentDirectLimitComparisonOne
          (ρ := ρ) (σ := σ) hcomm).hom)
          (Module.DirectLimit.of S∞ I
            (fun k ↦ (stageNaiveCotangentBaseChange (σ := σ) k).X 1)
            (fun _ _ hij ↦ ((stageNaiveCotangentBaseChangeTransition
              (ρ := ρ) (σ := σ) hcomm hij).f 1).hom) i x)) =
      ((naiveCotangentDirectLimitComparisonZero
        (ρ := ρ) (σ := σ) hcomm).hom)
        (Module.DirectLimit.of S∞ I
          (fun k ↦ (stageNaiveCotangentBaseChange (σ := σ) k).X 0)
          (fun _ _ hij ↦ ((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm hij).f 0).hom) i
          (((stageNaiveCotangentBaseChange (σ := σ) i).d 1 0).hom x)) := by
  -- Route correction: once both direct-limit maps are normalized on a stage class,
  -- the claim is exactly the stage chain-map square evaluated at `x`.
  rw [naiveCotangentDirectLimitComparisonOne_of_stage,
    naiveCotangentDirectLimitComparisonZero_of_stage]
  -- Evaluate the stage chain-map square on the chosen representative.
  simpa [ModuleCat.comp_apply] using
    congrArg (fun φ ↦ φ.hom x)
      ((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm i).comm 1 0)

/-- Helper for Lemma 10.134.9: the explicit degreewise comparison components form the `1 → 0`
square of a chain map. -/
private theorem naiveCotangentDirectLimitComparison_comm_10
    [DecidableEq I] :
    (naiveCotangentDirectLimitComparisonOne (ρ := ρ) (σ := σ) hcomm) ≫
        (targetNaiveCotangent (ρ := ρ) (σ := σ) hcomm).d 1 0 =
      (naiveCotangentDirectLimitModel (ρ := ρ) (σ := σ) hcomm).d 1 0 ≫
        (naiveCotangentDirectLimitComparisonZero (ρ := ρ) (σ := σ) hcomm) := by
  apply ModuleCat.hom_ext
  ext z
  -- Descend the stagewise chain-map square from representatives to the module direct limit.
  induction z using Module.DirectLimit.induction_on with
  | ih i x =>
      simpa [naiveCotangentDirectLimitModel, ModuleCat.comp_apply,
        naiveCotangentDirectLimitDifferential_of_stage
          (ρ := ρ) (σ := σ) hcomm i x] using
        naiveCotangentDirectLimitComparison_comm_10_on_stage
          (ρ := ρ) (σ := σ) hcomm i x

/-- Helper for Lemma 10.134.9: away from degrees `0` and `1`, the explicit comparison uses the
zero morphisms on the two-term source and target complexes. -/
private theorem naiveCotangentDirectLimitComparison_comm_succ
    (n : ℕ)
    (p :
      Σ' (f : (naiveCotangentDirectLimitModel (ρ := ρ) (σ := σ) hcomm).X n ⟶
            (targetNaiveCotangent (ρ := ρ) (σ := σ) hcomm).X n)
        (f' : (naiveCotangentDirectLimitModel (ρ := ρ) (σ := σ) hcomm).X (n + 1) ⟶
            (targetNaiveCotangent (ρ := ρ) (σ := σ) hcomm).X (n + 1)),
        f' ≫ (targetNaiveCotangent (ρ := ρ) (σ := σ) hcomm).d (n + 1) n =
          (naiveCotangentDirectLimitModel (ρ := ρ) (σ := σ) hcomm).d (n + 1) n ≫ f) :
    Σ' f'' : (naiveCotangentDirectLimitModel (ρ := ρ) (σ := σ) hcomm).X (n + 2) ⟶
          (targetNaiveCotangent (ρ := ρ) (σ := σ) hcomm).X (n + 2),
      f'' ≫ (targetNaiveCotangent (ρ := ρ) (σ := σ) hcomm).d (n + 2) (n + 1) =
        (naiveCotangentDirectLimitModel (ρ := ρ) (σ := σ) hcomm).d (n + 2) (n + 1) ≫ p.2.1 := by
  -- Both complexes are two-term, so every higher differential is zero.
  refine ⟨0, ?_⟩
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  rw [Extension.naiveCotangentChainComplex_d_succ_succ Pinf.toExtension n]
  simp [naiveCotangentDirectLimitModel, targetNaiveCotangent]

/-- The canonical comparison from the filtered-colimit source
`colim_i (S∞ ⊗[S_i] NL_{S_i⁄R_i})` to the canonical owner `NL_{S∞⁄R∞}`. -/
-- Proof comment: the comparison is assembled degreewise from the stabilized direct-limit owners,
-- with the `1 → 0` square checked on stage representatives and higher degrees forced to zero.
noncomputable def naiveCotangentDirectLimitComparison :
    let _hcomm := hcomm
    naiveCotangentDirectLimitModel hcomm ⟶
      NL(CommRingCat.ofHom
        (Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h)) :=
  let _ : DecidableEq I := Classical.decEq I
  ChainComplex.mkHom _ _
    (naiveCotangentDirectLimitComparisonZero (ρ := ρ) (σ := σ) hcomm)
    (naiveCotangentDirectLimitComparisonOne (ρ := ρ) (σ := σ) hcomm)
    (naiveCotangentDirectLimitComparison_comm_10 (ρ := ρ) (σ := σ) hcomm)
    (naiveCotangentDirectLimitComparison_comm_succ (ρ := ρ) (σ := σ) hcomm)

/-- Helper for Lemma 10.134.9: a degree-`0` stage basis element determines the corresponding class
in the explicit direct-limit source. -/
private noncomputable abbrev naiveCotangentDirectLimitDegreeZero_stageClass
    (i : I)
    (y : ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension).CotangentSpace) :
    naiveCotangentDirectLimitDegreeZero hcomm :=
  Module.DirectLimit.of S∞ I
    (fun k ↦ (stageNaiveCotangentBaseChange (σ := σ) k).X 0)
    (fun _ _ hij ↦ ((stageNaiveCotangentBaseChangeTransition
      (ρ := ρ) (σ := σ) hcomm hij).f 0).hom) i
    ((1 : S∞) ⊗ₜ[S i] y)

/-- Helper for Lemma 10.134.9: every target cotangent-space basis index in `S∞` already comes
from some stage element. -/
private theorem targetCotangentSpaceBasis_exists_stage
    (s : S∞) :
    ∃ p : Σ i, S i, stageTargetMap (σ := σ) p.1 p.2 = s := by
  obtain ⟨i, s_i, hs⟩ :=
    Ring.DirectLimit.exists_of (G := S) (f' := fun i j h ↦ σ i j h) s
  exact ⟨⟨i, s_i⟩, hs⟩

/-- Helper for Lemma 10.134.9: choose one stage representative for a target cotangent-space basis
index. -/
private noncomputable abbrev targetCotangentSpaceBasis_stage
    (s : S∞) :
    Σ i, S i :=
  Classical.choose (targetCotangentSpaceBasis_exists_stage (σ := σ) s)

/-- Helper for Lemma 10.134.9: the chosen stage representative maps to the prescribed target basis
index. -/
private theorem targetCotangentSpaceBasis_stage_spec
    (s : S∞) :
    stageTargetMap (σ := σ)
        (targetCotangentSpaceBasis_stage (σ := σ) s).1
        (targetCotangentSpaceBasis_stage (σ := σ) s).2 =
      s :=
  Classical.choose_spec (targetCotangentSpaceBasis_exists_stage (σ := σ) s)

/-- Helper for Lemma 10.134.9: two stage basis classes define the same degree-`0` direct-limit
class once their indices agree in the target direct limit. -/
private theorem degree_zero_stage_basis_class_eq_of_same_target
    [DecidableEq I]
    {i j : I} (s_i : S i) (s_j : S j)
    (hs : stageTargetMap (σ := σ) i s_i = stageTargetMap (σ := σ) j s_j) :
    naiveCotangentDirectLimitDegreeZero_stageClass (ρ := ρ) (σ := σ) hcomm i
        ((Generators.self (R i) (S i)).cotangentSpaceBasis s_i) =
      naiveCotangentDirectLimitDegreeZero_stageClass (ρ := ρ) (σ := σ) hcomm j
        ((Generators.self (R j) (S j)).cotangentSpaceBasis s_j) := by
  classical
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have hk_zero :
      stageTargetMap (σ := σ) k (σ i k hik s_i - σ j k hjk s_j) = 0 := by
    -- Move both representatives to the common stage `k`, then compare their images in `S∞`.
    calc
      stageTargetMap (σ := σ) k (σ i k hik s_i - σ j k hjk s_j) =
          stageTargetMap (σ := σ) k (σ i k hik s_i) -
            stageTargetMap (σ := σ) k (σ j k hjk s_j) := by
              simp
      _ = stageTargetMap (σ := σ) i s_i - stageTargetMap (σ := σ) j s_j := by
            rw [DFunLike.congr_fun (stageTargetMap_comp (σ := σ) hik) s_i,
              DFunLike.congr_fun (stageTargetMap_comp (σ := σ) hjk) s_j]
      _ = 0 := by rw [hs, sub_self]
  obtain ⟨ℓ, hkℓ, hℓ⟩ := Ring.DirectLimit.of.zero_exact
    (G := S) (f' := fun a b hab ↦ σ a b hab) hk_zero
  let hiℓ : i ≤ ℓ := le_trans hik hkℓ
  let hjℓ : j ≤ ℓ := le_trans hjk hkℓ
  let Pℓ : Generators (R ℓ) (S ℓ) (S ℓ) := Generators.self (R ℓ) (S ℓ)
  have hstage :
      σ i ℓ hiℓ s_i = σ j ℓ hjℓ s_j := by
    -- `Ring.DirectLimit.of.zero_exact` turns equality in the colimit into equality at a later
    -- stage, exactly as in the source proof.
    have hℓ_zero :
        σ i ℓ hiℓ s_i - σ j ℓ hjℓ s_j = 0 := by
      simpa [hiℓ, hjℓ, map_sub, map_map' σ hik hkℓ s_i, map_map' σ hjk hkℓ s_j] using hℓ
    exact sub_eq_zero.mp hℓ_zero
  have hi_move :
      naiveCotangentDirectLimitDegreeZero_stageClass (ρ := ρ) (σ := σ) hcomm i
          (Pi.cotangentSpaceBasis s_i) =
        naiveCotangentDirectLimitDegreeZero_stageClass (ρ := ρ) (σ := σ) hcomm ℓ
          (Pℓ.cotangentSpaceBasis (σ i ℓ hiℓ s_i)) := by
    -- Move the stage-`i` class to the common later stage `ℓ`.
    calc
      naiveCotangentDirectLimitDegreeZero_stageClass (ρ := ρ) (σ := σ) hcomm i
          (Pi.cotangentSpaceBasis s_i) =
        Module.DirectLimit.of S∞ I
          (fun a ↦ (stageNaiveCotangentBaseChange (σ := σ) a).X 0)
          (fun _ _ hab ↦ ((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm hab).f 0).hom) ℓ
          ((((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm hiℓ).f 0).hom)
            (((1 : S∞) ⊗ₜ[S i] Pi.cotangentSpaceBasis s_i))) := by
              simpa [naiveCotangentDirectLimitDegreeZero_stageClass, hiℓ] using
                (Module.DirectLimit.of_f
                  (R := S∞) (ι := I)
                  (G := fun a ↦ (stageNaiveCotangentBaseChange (σ := σ) a).X 0)
                  (f := fun _ _ hab ↦ ((stageNaiveCotangentBaseChangeTransition
                    (ρ := ρ) (σ := σ) hcomm hab).f 0).hom)
                  (i := i) (j := ℓ) (hij := hiℓ)
                  (x := ((1 : S∞) ⊗ₜ[S i] Pi.cotangentSpaceBasis s_i)))
      _ = Module.DirectLimit.of S∞ I
          (fun a ↦ (stageNaiveCotangentBaseChange (σ := σ) a).X 0)
          (fun _ _ hab ↦ ((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm hab).f 0).hom) ℓ
          (((1 : S∞) ⊗ₜ[S ℓ]
            Extension.CotangentSpace.map
              ((Generators.defaultHom Pi Pℓ).toExtensionHom)
              (Pi.cotangentSpaceBasis s_i))) := by
                rw [stageNaiveCotangentBaseChangeTransition_f_zero_unit_tensor
                  (ρ := ρ) (σ := σ) hcomm hiℓ (Pi.cotangentSpaceBasis s_i)]
      _ = naiveCotangentDirectLimitDegreeZero_stageClass (ρ := ρ) (σ := σ) hcomm ℓ
          (Pℓ.cotangentSpaceBasis (σ i ℓ hiℓ s_i)) := by
            congr 2
            simpa [Pi, Pℓ] using
              selfPresentation_cotangentSpaceBasis_compatible
                (ρ := ρ) (σ := σ) hcomm hiℓ s_i
  have hj_move :
      naiveCotangentDirectLimitDegreeZero_stageClass (ρ := ρ) (σ := σ) hcomm j
          (Pj.cotangentSpaceBasis s_j) =
        naiveCotangentDirectLimitDegreeZero_stageClass (ρ := ρ) (σ := σ) hcomm ℓ
          (Pℓ.cotangentSpaceBasis (σ j ℓ hjℓ s_j)) := by
    -- Repeat the same move for the stage-`j` representative.
    calc
      naiveCotangentDirectLimitDegreeZero_stageClass (ρ := ρ) (σ := σ) hcomm j
          (Pj.cotangentSpaceBasis s_j) =
        Module.DirectLimit.of S∞ I
          (fun a ↦ (stageNaiveCotangentBaseChange (σ := σ) a).X 0)
          (fun _ _ hab ↦ ((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm hab).f 0).hom) ℓ
          ((((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm hjℓ).f 0).hom)
            (((1 : S∞) ⊗ₜ[S j] Pj.cotangentSpaceBasis s_j))) := by
              simpa [naiveCotangentDirectLimitDegreeZero_stageClass, hjℓ] using
                (Module.DirectLimit.of_f
                  (R := S∞) (ι := I)
                  (G := fun a ↦ (stageNaiveCotangentBaseChange (σ := σ) a).X 0)
                  (f := fun _ _ hab ↦ ((stageNaiveCotangentBaseChangeTransition
                    (ρ := ρ) (σ := σ) hcomm hab).f 0).hom)
                  (i := j) (j := ℓ) (hij := hjℓ)
                  (x := ((1 : S∞) ⊗ₜ[S j] Pj.cotangentSpaceBasis s_j)))
      _ = Module.DirectLimit.of S∞ I
          (fun a ↦ (stageNaiveCotangentBaseChange (σ := σ) a).X 0)
          (fun _ _ hab ↦ ((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm hab).f 0).hom) ℓ
          (((1 : S∞) ⊗ₜ[S ℓ]
            Extension.CotangentSpace.map
              ((Generators.defaultHom Pj Pℓ).toExtensionHom)
              (Pj.cotangentSpaceBasis s_j))) := by
                rw [stageNaiveCotangentBaseChangeTransition_f_zero_unit_tensor
                  (ρ := ρ) (σ := σ) hcomm hjℓ (Pj.cotangentSpaceBasis s_j)]
      _ = naiveCotangentDirectLimitDegreeZero_stageClass (ρ := ρ) (σ := σ) hcomm ℓ
          (Pℓ.cotangentSpaceBasis (σ j ℓ hjℓ s_j)) := by
            congr 2
            simpa [Pj, Pℓ] using
              selfPresentation_cotangentSpaceBasis_compatible
                (ρ := ρ) (σ := σ) hcomm hjℓ s_j
  -- At stage `ℓ`, the two basis vectors coincide because their indices agree in `S ℓ`.
  calc
    naiveCotangentDirectLimitDegreeZero_stageClass (ρ := ρ) (σ := σ) hcomm i
        ((Generators.self (R i) (S i)).cotangentSpaceBasis s_i) =
      naiveCotangentDirectLimitDegreeZero_stageClass (ρ := ρ) (σ := σ) hcomm ℓ
        (Pℓ.cotangentSpaceBasis (σ i ℓ hiℓ s_i)) := hi_move
    _ = naiveCotangentDirectLimitDegreeZero_stageClass (ρ := ρ) (σ := σ) hcomm ℓ
        (Pℓ.cotangentSpaceBasis (σ j ℓ hjℓ s_j)) := by rw [hstage]
    _ = naiveCotangentDirectLimitDegreeZero_stageClass (ρ := ρ) (σ := σ) hcomm j
        ((Generators.self (R j) (S j)).cotangentSpaceBasis s_j) := hj_move.symm

/-- Helper for Lemma 10.134.9: choose a preimage in the explicit degree-`0` direct limit for each
target cotangent-space basis vector. -/
private noncomputable abbrev naiveCotangentDirectLimitComparisonZero_section :
    (targetNaiveCotangent hcomm).X 0 ⟶
      naiveCotangentDirectLimitDegreeZero hcomm :=
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  ModuleCat.ofHom <|
    Pinf.cotangentSpaceBasis.constr S∞ fun s ↦
      let p := targetCotangentSpaceBasis_stage (σ := σ) s
      naiveCotangentDirectLimitDegreeZero_stageClass (ρ := ρ) (σ := σ) hcomm p.1
        ((Generators.self (R p.1) (S p.1)).cotangentSpaceBasis p.2)

/-- Helper for Lemma 10.134.9: the degree-`0` section lands on a genuine preimage of each target
cotangent-space basis vector. -/
private theorem naiveCotangentDirectLimitComparisonZero_section_basis
    (s : S∞) :
    let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
    (naiveCotangentDirectLimitComparisonZero (ρ := ρ) (σ := σ) hcomm).hom
        ((naiveCotangentDirectLimitComparisonZero_section
          (ρ := ρ) (σ := σ) hcomm).hom (Pinf.cotangentSpaceBasis s)) =
      Pinf.cotangentSpaceBasis s := by
  classical
  let p := targetCotangentSpaceBasis_stage (σ := σ) s
  let i : I := p.1
  let s_i : S i := p.2
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  have hs :
      stageTargetMap (σ := σ) i s_i = s :=
    targetCotangentSpaceBasis_stage_spec (σ := σ) s
  -- Evaluate the degree-`0` comparison on the chosen stage class, then identify the target image
  -- with the basis vector indexed by `s`.
  rw [show (naiveCotangentDirectLimitComparisonZero_section
      (ρ := ρ) (σ := σ) hcomm).hom (Pinf.cotangentSpaceBasis s) =
      naiveCotangentDirectLimitDegreeZero_stageClass (ρ := ρ) (σ := σ) hcomm i
        (Pi.cotangentSpaceBasis s_i) by
      simp [naiveCotangentDirectLimitComparisonZero_section,
        naiveCotangentDirectLimitDegreeZero_stageClass, p, i, s_i, Pi, Pinf]]
  rw [naiveCotangentDirectLimitComparisonZero_of_stage
    (ρ := ρ) (σ := σ) hcomm i ((1 : S∞) ⊗ₜ[S i] Pi.cotangentSpaceBasis s_i)]
  calc
    (((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm i).f 0).hom)
        (((1 : S∞) ⊗ₜ[S i] Pi.cotangentSpaceBasis s_i)) =
      Extension.CotangentSpace.map
        ((Generators.defaultHom Pi Pinf).toExtensionHom)
        (Pi.cotangentSpaceBasis s_i) := by
          simpa [Pi, Pinf] using
            stageNaiveCotangentToTarget_degree_zero_after_transport
              (ρ := ρ) (σ := σ) hcomm i (Pi.cotangentSpaceBasis s_i)
    _ = Pinf.cotangentSpaceBasis (stageTargetMap (σ := σ) i s_i) := by
          simpa [Pi, Pinf] using
            selfPresentation_cotangentSpaceBasis_target_compatible
              (ρ := ρ) (σ := σ) hcomm i s_i
    _ = Pinf.cotangentSpaceBasis s := by rw [hs]

/-- Helper for Lemma 10.134.9: a stage degree-`0` basis class is fixed by applying the comparison
and then the chosen degree-`0` section. -/
private theorem stage_degree_zero_basis_class_fixed_by_section_after_comparison
    [DecidableEq I]
    (i : I) (s_i : S i) :
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    (naiveCotangentDirectLimitComparisonZero_section
      (ρ := ρ) (σ := σ) hcomm).hom
        (((naiveCotangentDirectLimitComparisonZero
          (ρ := ρ) (σ := σ) hcomm).hom)
          (naiveCotangentDirectLimitDegreeZero_stageClass
            (ρ := ρ) (σ := σ) hcomm i (Pi.cotangentSpaceBasis s_i))) =
      naiveCotangentDirectLimitDegreeZero_stageClass
        (ρ := ρ) (σ := σ) hcomm i (Pi.cotangentSpaceBasis s_i) := by
  classical
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  let s : S∞ := stageTargetMap (σ := σ) i s_i
  let p := targetCotangentSpaceBasis_stage (σ := σ) s
  have hs :
      stageTargetMap (σ := σ) p.1 p.2 = stageTargetMap (σ := σ) i s_i := by
    simpa [s, p] using targetCotangentSpaceBasis_stage_spec (σ := σ) s
  -- First identify the comparison image with the corresponding target basis vector, then use the
  -- same-target stage-class lemma to compare the chosen section with the original stage class.
  rw [naiveCotangentDirectLimitComparisonZero_of_stage
    (ρ := ρ) (σ := σ) hcomm i ((1 : S∞) ⊗ₜ[S i] Pi.cotangentSpaceBasis s_i)]
  calc
    (naiveCotangentDirectLimitComparisonZero_section
      (ρ := ρ) (σ := σ) hcomm).hom
        ((((stageNaiveCotangentToTarget
          (ρ := ρ) (σ := σ) hcomm i).f 0).hom)
          (((1 : S∞) ⊗ₜ[S i] Pi.cotangentSpaceBasis s_i))) =
      (naiveCotangentDirectLimitComparisonZero_section
        (ρ := ρ) (σ := σ) hcomm).hom (Pinf.cotangentSpaceBasis s) := by
          congr 1
          calc
            (((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm i).f 0).hom)
                (((1 : S∞) ⊗ₜ[S i] Pi.cotangentSpaceBasis s_i)) =
              Extension.CotangentSpace.map
                ((Generators.defaultHom Pi Pinf).toExtensionHom)
                (Pi.cotangentSpaceBasis s_i) := by
                  simpa [Pi, Pinf] using
                    stageNaiveCotangentToTarget_degree_zero_after_transport
                      (ρ := ρ) (σ := σ) hcomm i (Pi.cotangentSpaceBasis s_i)
            _ = Pinf.cotangentSpaceBasis (stageTargetMap (σ := σ) i s_i) := by
                  simpa [Pi, Pinf] using
                    selfPresentation_cotangentSpaceBasis_target_compatible
                      (ρ := ρ) (σ := σ) hcomm i s_i
            _ = Pinf.cotangentSpaceBasis s := by rfl
    _ = naiveCotangentDirectLimitDegreeZero_stageClass
        (ρ := ρ) (σ := σ) hcomm p.1
        ((Generators.self (R p.1) (S p.1)).cotangentSpaceBasis p.2) := by
          simp [naiveCotangentDirectLimitComparisonZero_section, p, s]
    _ = naiveCotangentDirectLimitDegreeZero_stageClass
        (ρ := ρ) (σ := σ) hcomm i (Pi.cotangentSpaceBasis s_i) := by
          exact degree_zero_stage_basis_class_eq_of_same_target
            (ρ := ρ) (σ := σ) hcomm p.2 s_i hs

/-- Helper for Lemma 10.134.9: in degree `0`, the explicit comparison is a split epimorphism, so
every target basis vector already has a source preimage coming from a stage. -/
private theorem naiveCotangentDirectLimitComparisonZero_section_comp :
    (naiveCotangentDirectLimitComparisonZero_section
      (ρ := ρ) (σ := σ) hcomm) ≫
        (naiveCotangentDirectLimitComparisonZero
          (ρ := ρ) (σ := σ) hcomm) =
      𝟙 ((targetNaiveCotangent hcomm).X 0) := by
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  apply ModuleCat.hom_ext
  apply Pinf.cotangentSpaceBasis.ext
  intro s
  -- Checking the right-inverse relation on the canonical basis is enough by freeness.
  simpa [ModuleCat.comp_apply, Pinf] using
    naiveCotangentDirectLimitComparisonZero_section_basis
      (ρ := ρ) (σ := σ) hcomm s

/-- Helper for Lemma 10.134.9: in degree `0`, the chosen section is also a left inverse on the
explicit direct-limit source. -/
private theorem naiveCotangentDirectLimitComparisonZero_comp_section
    [DecidableEq I] :
    (naiveCotangentDirectLimitComparisonZero
      (ρ := ρ) (σ := σ) hcomm) ≫
        (naiveCotangentDirectLimitComparisonZero_section
          (ρ := ρ) (σ := σ) hcomm) =
      𝟙 (naiveCotangentDirectLimitDegreeZero hcomm) := by
  let G : I → Type u := fun k ↦ (stageNaiveCotangentBaseChange (σ := σ) k).X 0
  let μ : ∀ i j, i ≤ j → G i →ₗ[S∞] G j :=
    fun _ _ hij ↦ ((stageNaiveCotangentBaseChangeTransition
      (ρ := ρ) (σ := σ) hcomm hij).f 0).hom
  let ι : ∀ i, G i →ₗ[S∞] naiveCotangentDirectLimitDegreeZero hcomm :=
    fun i ↦ Module.DirectLimit.of S∞ I G μ i
  apply ModuleCat.hom_ext
  ext z
  -- Descend the left-inverse identity from stage representatives of the source direct limit.
  induction z using Module.DirectLimit.induction_on with
  | ih i x =>
      let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
      have hstage :
          (((stageNaiveCotangentToTarget
            (ρ := ρ) (σ := σ) hcomm i).f 0) ≫
              (naiveCotangentDirectLimitComparisonZero_section
                (ρ := ρ) (σ := σ) hcomm)) =
            ModuleCat.ofHom (ι i) := by
        apply ModuleCat.ExtendScalars.hom_ext
        intro y
        -- Route correction: use the cotangent-space basis to reduce the stage claim to the
        -- already proved fixed-point statement on basis classes.
        rw [Pi.cotangentSpaceBasis.sum_repr y]
        simp only [TensorProduct.tmul_sum, map_sum, ModuleCat.comp_apply]
        refine Finset.sum_congr rfl ?_
        intro s hs
        rw [TensorProduct.tmul_smul]
        simp only [map_smul]
        calc
          (naiveCotangentDirectLimitComparisonZero_section
            (ρ := ρ) (σ := σ) hcomm).hom
              ((((stageNaiveCotangentToTarget
                (ρ := ρ) (σ := σ) hcomm i).f 0).hom)
                (((1 : S∞) ⊗ₜ[S i] Pi.cotangentSpaceBasis s))) =
            (naiveCotangentDirectLimitComparisonZero_section
              (ρ := ρ) (σ := σ) hcomm).hom
                (((naiveCotangentDirectLimitComparisonZero
                  (ρ := ρ) (σ := σ) hcomm).hom)
                  (naiveCotangentDirectLimitDegreeZero_stageClass
                    (ρ := ρ) (σ := σ) hcomm i (Pi.cotangentSpaceBasis s))) := by
                      rw [naiveCotangentDirectLimitComparisonZero_of_stage
                        (ρ := ρ) (σ := σ) hcomm i
                        (((1 : S∞) ⊗ₜ[S i] Pi.cotangentSpaceBasis s))]
          _ = naiveCotangentDirectLimitDegreeZero_stageClass
              (ρ := ρ) (σ := σ) hcomm i (Pi.cotangentSpaceBasis s) := by
                simpa [Pi] using
                  stage_degree_zero_basis_class_fixed_by_section_after_comparison
                    (ρ := ρ) (σ := σ) hcomm i s
          _ = (ι i) (((1 : S∞) ⊗ₜ[S i] Pi.cotangentSpaceBasis s)) := by
                rfl
      -- Evaluate the global direct-limit map on the chosen stage representative, then replace the
      -- resulting stage composite by the canonical inclusion.
      calc
        ((naiveCotangentDirectLimitComparisonZero
          (ρ := ρ) (σ := σ) hcomm) ≫
            (naiveCotangentDirectLimitComparisonZero_section
              (ρ := ρ) (σ := σ) hcomm)).hom
            (Module.DirectLimit.of S∞ I G μ i x) =
          ((((stageNaiveCotangentToTarget
            (ρ := ρ) (σ := σ) hcomm i).f 0) ≫
              (naiveCotangentDirectLimitComparisonZero_section
                (ρ := ρ) (σ := σ) hcomm)).hom) x := by
                  rw [ModuleCat.comp_apply,
                    naiveCotangentDirectLimitComparisonZero_of_stage
                      (ρ := ρ) (σ := σ) hcomm i x]
        _ = (ι i) x := by
              simpa [ι, ModuleCat.comp_apply] using
                congrArg (fun φ ↦ φ.hom x) hstage
        _ = (𝟙 (naiveCotangentDirectLimitDegreeZero hcomm)).hom
              (Module.DirectLimit.of S∞ I G μ i x) := by
                rfl

/-- Helper for Lemma 10.134.9: the degree-`0` comparison component is an isomorphism, with inverse
given by the explicit section built from stage representatives of target basis vectors. -/
private theorem naiveCotangentDirectLimitComparisonZero_isIso
    [DecidableEq I] :
    IsIso (naiveCotangentDirectLimitComparisonZero (ρ := ρ) (σ := σ) hcomm) := by
  -- The already proved left and right inverse identities package the degree-`0` comparison as an
  -- isomorphism without any further diagrammatic colimit API.
  refine ⟨⟨naiveCotangentDirectLimitComparisonZero_section (ρ := ρ) (σ := σ) hcomm, ?_, ?_⟩⟩
  · simpa using
      naiveCotangentDirectLimitComparisonZero_comp_section (ρ := ρ) (σ := σ) hcomm
  · simpa using
      naiveCotangentDirectLimitComparisonZero_section_comp (ρ := ρ) (σ := σ) hcomm

/-- Helper for Lemma 10.134.9: the degree-`0` comparison component is bijective as a linear map. -/
private theorem naiveCotangentDirectLimitComparisonZero_bijective
    [DecidableEq I] :
    Function.Bijective
      (naiveCotangentDirectLimitComparisonZero (ρ := ρ) (σ := σ) hcomm).hom := by
  let f := naiveCotangentDirectLimitComparisonZero (ρ := ρ) (σ := σ) hcomm
  letI : IsIso f :=
    naiveCotangentDirectLimitComparisonZero_isIso (ρ := ρ) (σ := σ) hcomm
  exact ⟨(ModuleCat.mono_iff_injective f).mp inferInstance,
    (ModuleCat.epi_iff_surjective f).mp inferInstance⟩

/-- Helper for Lemma 10.134.9: for a stage kernel generator, vanishing of its target degree-`1`
class is equivalent to square-ideal membership of its image in the target self-presentation. -/
private theorem stage_degree_one_generator_target_zero_iff_mem_square
    [DecidableEq I]
    (i : I)
    (x_i :
      ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension).ker) :
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
    (naiveCotangentDirectLimitComparisonOne (ρ := ρ) (σ := σ) hcomm).hom
        (Module.DirectLimit.of S∞ I
          (fun k ↦ (stageNaiveCotangentBaseChange (σ := σ) k).X 1)
          (fun _ _ hij ↦ ((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm hij).f 1).hom) i
          (((1 : S∞) ⊗ₜ[S i] ULift.up (Extension.Cotangent.mk x_i)))) = 0 ↔
      (Generators.defaultHom Pi Pinf).toAlgHom x_i.1 ∈ (Pinf.toExtension).ker ^ 2 := by
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  let fiInf : Pi.toExtension.Hom Pinf.toExtension := (Generators.defaultHom Pi Pinf).toExtensionHom
  -- Evaluate the direct-limit comparison on the chosen stage generator, then read target
  -- vanishing through `Cotangent.mk_eq_zero_iff`.
  rw [naiveCotangentDirectLimitComparisonOne_of_stage
    (ρ := ρ) (σ := σ) hcomm i
    (((1 : S∞) ⊗ₜ[S i] ULift.up (Extension.Cotangent.mk x_i)))]
  rw [stageNaiveCotangentToTarget_degree_one_generator_after_transport
    (ρ := ρ) (σ := σ) hcomm i (Extension.Cotangent.mk x_i)]
  change ULift.up (Extension.Cotangent.map fiInf (Extension.Cotangent.mk x_i)) = 0 ↔
    (Generators.defaultHom Pi Pinf).toAlgHom x_i.1 ∈ (Pinf.toExtension).ker ^ 2
  rw [ULift.up.injEq, Extension.Cotangent.map_mk]
  exact Extension.Cotangent.mk_eq_zero_iff

/-- Helper for Lemma 10.134.9: the target degree-`1` vanishing criterion can be rewritten as
zero of the corresponding class in the square-ideal quotient of the target self-presentation. -/
private theorem stage_degree_one_generator_target_zero_iff_square_quotient_zero
    [DecidableEq I]
    (i : I)
    (x_i :
      ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension).ker) :
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
    (naiveCotangentDirectLimitComparisonOne (ρ := ρ) (σ := σ) hcomm).hom
        (Module.DirectLimit.of S∞ I
          (fun k ↦ (stageNaiveCotangentBaseChange (σ := σ) k).X 1)
          (fun _ _ hij ↦ ((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm hij).f 1).hom) i
          (((1 : S∞) ⊗ₜ[S i] ULift.up (Extension.Cotangent.mk x_i)))) = 0 ↔
      Ideal.Quotient.mk ((Pinf.toExtension).ker ^ 2)
          ((Generators.defaultHom Pi Pinf).toAlgHom x_i.1) = 0 := by
  -- Replace square-ideal membership by the equivalent quotient-zero statement suggested by the
  -- source proof.
  simpa [Ideal.Quotient.eq_zero_iff_mem] using
    stage_degree_one_generator_target_zero_iff_mem_square
      (ρ := ρ) (σ := σ) hcomm i x_i

/-- Helper for Lemma 10.134.9: the default map between self-presentations sends kernel elements to
kernel elements at later stages. -/
private theorem selfPresentation_defaultHom_mem_ker
    {i j : I} (h : i ≤ j)
    (x :
      ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension).ker) :
    let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
    let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
    let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
    let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
    (Generators.defaultHom Pi Pj).toAlgHom x.1 ∈ (Pj.toExtension).ker := by
  let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
  let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
  let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
  let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  -- Evaluate the pushed polynomial in stage `j`; the source kernel equation stays zero.
  change algebraMap Pj.Ring (S j) ((Generators.defaultHom Pi Pj).toAlgHom x.1) = 0
  have hpush :
      algebraMap Pj.Ring (S j) ((Generators.defaultHom Pi Pj).toAlgHom x.1) =
        algebraMap (S i) (S j) (algebraMap Pi.Ring (S i) x.1) := by
    simpa using
      (Generators.Hom.algebraMap_toAlgHom (f := Generators.defaultHom Pi Pj) x.1)
  calc
    algebraMap Pj.Ring (S j) ((Generators.defaultHom Pi Pj).toAlgHom x.1) =
        algebraMap (S i) (S j) (algebraMap Pi.Ring (S i) x.1) := hpush
    _ = 0 := by rw [x.2, map_zero]

/-- Helper for Lemma 10.134.9: the square of the stage kernel maps into the square of the later
stage kernel under the default self-presentation map. -/
private theorem selfPresentation_square_ideal_le_comap
    {i j : I} (h : i ≤ j) :
    let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
    let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
    let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
    let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
    (Pi.toExtension).ker ^ 2 ≤
      Ideal.comap (Generators.defaultHom Pi Pj).toAlgHom ((Pj.toExtension).ker ^ 2) := by
  let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
  let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
  let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
  let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  have hker :
      (Pi.toExtension).ker ≤
        Ideal.comap (Generators.defaultHom Pi Pj).toAlgHom (Pj.toExtension).ker := by
    intro x hx
    exact selfPresentation_defaultHom_mem_ker (ρ := ρ) (σ := σ) hcomm h ⟨x, hx⟩
  -- Push kernel inclusion through the square to obtain the quotient transition condition.
  calc
    (Pi.toExtension).ker ^ 2 ≤
        (Ideal.comap (Generators.defaultHom Pi Pj).toAlgHom (Pj.toExtension).ker) ^ 2 := by
          exact Ideal.pow_le_pow_right hker
    _ ≤ Ideal.comap (Generators.defaultHom Pi Pj).toAlgHom ((Pj.toExtension).ker ^ 2) := by
          exact Ideal.le_comap_pow (f := (Generators.defaultHom Pi Pj).toAlgHom) (K := (Pj.toExtension).ker) 2

/-- Helper for Lemma 10.134.9: the default self-presentation maps induce transition maps on the
quotients by the squares of the stage kernels. -/
private noncomputable def selfPresentation_square_quotient_transition
    {i j : I} (h : i ≤ j) :
    let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
    let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
    let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
    let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
    Pi.Ring ⧸ (Pi.toExtension).ker ^ 2 →+* Pj.Ring ⧸ (Pj.toExtension).ker ^ 2 :=
  let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
  let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
  let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
  let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  Ideal.quotientMap ((Pj.toExtension).ker ^ 2) (Generators.defaultHom Pi Pj).toAlgHom
    (selfPresentation_square_ideal_le_comap (ρ := ρ) (σ := σ) hcomm h)

/-- Helper for Lemma 10.134.9: the directed system formed by the stage self-presentation rings. -/
private abbrev stageSelfPresentationRing (i : I) :=
  (Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).Ring

/-- Helper for Lemma 10.134.9: the transition map in the directed system of stage
self-presentation rings. -/
private noncomputable abbrev stageSelfPresentationTransition
    {i j : I} (h : i ≤ j) :
    stageSelfPresentationRing (R := R) (S := S) i →+*
      stageSelfPresentationRing (R := R) (S := S) j :=
  let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
  let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
  let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
  let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  (Generators.defaultHom Pi Pj).toAlgHom

/-- Helper for Lemma 10.134.9: the ring direct limit of the stage self-presentations. -/
private abbrev selfPresentationRingDirectLimit :=
  Ring.DirectLimit
    (fun i ↦ stageSelfPresentationRing (R := R) (S := S) i)
    (fun i j h ↦ stageSelfPresentationTransition
      (ρ := ρ) (σ := σ) hcomm h)

/-- Helper for Lemma 10.134.9: the canonical map from a stage self-presentation ring into its ring
direct limit. -/
private abbrev stageSelfPresentationOf (i : I) :
    stageSelfPresentationRing (R := R) (S := S) i →+*
      selfPresentationRingDirectLimit (ρ := ρ) (σ := σ) hcomm :=
  Ring.DirectLimit.of
    (fun i ↦ stageSelfPresentationRing (R := R) (S := S) i)
    (fun i j h ↦ stageSelfPresentationTransition
      (ρ := ρ) (σ := σ) hcomm h) i

/-- Helper for Lemma 10.134.9: constants from the base-ring system map compatibly into the direct
limit of the stage self-presentations. -/
private theorem stageSelfPresentation_coeff_compatible
    {i j : I} (h : i ≤ j) (r : R i) :
    let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
    let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
    let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
    let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
    stageSelfPresentationOf (ρ := ρ) (σ := σ) hcomm j
        (MvPolynomial.C (ρ i j h r)) =
      stageSelfPresentationOf (ρ := ρ) (σ := σ) hcomm i (MvPolynomial.C r) := by
  let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
  let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
  let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
  let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  have hC :
      (Generators.defaultHom Pi Pj).toAlgHom (MvPolynomial.C r) =
        MvPolynomial.C (ρ i j h r) := by
    -- The default map is an algebra hom, so it sends constants to constants.
    simpa [Pi, Pj] using (Generators.defaultHom Pi Pj).toAlgHom.commutes r
  calc
    stageSelfPresentationOf (ρ := ρ) (σ := σ) hcomm j
        (MvPolynomial.C (ρ i j h r)) =
      stageSelfPresentationOf (ρ := ρ) (σ := σ) hcomm j
        ((Generators.defaultHom Pi Pj).toAlgHom (MvPolynomial.C r)) := by
          rw [hC]
    _ = stageSelfPresentationOf (ρ := ρ) (σ := σ) hcomm i (MvPolynomial.C r) := by
          simpa [stageSelfPresentationTransition] using
            (Ring.DirectLimit.of_f
              (G := fun k ↦ stageSelfPresentationRing (R := R) (S := S) k)
              (f' := fun a b hab ↦ stageSelfPresentationTransition
                (ρ := ρ) (σ := σ) hcomm hab)
              h (MvPolynomial.C r))

/-- Helper for Lemma 10.134.9: variables from the target-ring system map compatibly into the ring
direct limit of the stage self-presentations. -/
private theorem stageSelfPresentation_var_compatible
    {i j : I} (h : i ≤ j) (s : S i) :
    let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
    let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
    let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
    let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
    stageSelfPresentationOf (ρ := ρ) (σ := σ) hcomm j
        (MvPolynomial.X (σ i j h s)) =
      stageSelfPresentationOf (ρ := ρ) (σ := σ) hcomm i (MvPolynomial.X s) := by
  let _ : Algebra (R i) (R j) := (ρ i j h).toAlgebra
  let _ : Algebra (S i) (S j) := (σ i j h).toAlgebra
  let _ : Algebra (R i) (S j) := ((algebraMap (R j) (S j)).comp (ρ i j h)).toAlgebra
  let _ : IsScalarTower (R i) (R j) (S j) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S j) := IsScalarTower.of_algebraMap_eq' (hcomm h)
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  have hX :
      (Generators.defaultHom Pi Pj).toAlgHom (MvPolynomial.X s) =
        MvPolynomial.X (σ i j h s) := by
    -- The default map sends the stage variable indexed by `s` to the later-stage variable of
    -- its image under `σᵢⱼ`.
    simpa [Pi, Pj] using Generators.Hom.toAlgHom_X (f := Generators.defaultHom Pi Pj) s
  calc
    stageSelfPresentationOf (ρ := ρ) (σ := σ) hcomm j
        (MvPolynomial.X (σ i j h s)) =
      stageSelfPresentationOf (ρ := ρ) (σ := σ) hcomm j
        ((Generators.defaultHom Pi Pj).toAlgHom (MvPolynomial.X s)) := by
          rw [hX]
    _ = stageSelfPresentationOf (ρ := ρ) (σ := σ) hcomm i (MvPolynomial.X s) := by
          simpa [stageSelfPresentationTransition] using
            (Ring.DirectLimit.of_f
              (G := fun k ↦ stageSelfPresentationRing (R := R) (S := S) k)
              (f' := fun a b hab ↦ stageSelfPresentationTransition
                (ρ := ρ) (σ := σ) hcomm hab)
              h (MvPolynomial.X s))

/-- Helper for Lemma 10.134.9: two stage variables define the same class in the direct limit of
self-presentation rings once their indices agree in `S∞`. -/
private theorem stageSelfPresentation_X_eq_of_same_target
    {i j : I} (s_i : S i) (s_j : S j)
    (hs : stageTargetMap (σ := σ) i s_i = stageTargetMap (σ := σ) j s_j) :
    stageSelfPresentationOf (ρ := ρ) (σ := σ) hcomm i (MvPolynomial.X s_i) =
      stageSelfPresentationOf (ρ := ρ) (σ := σ) hcomm j (MvPolynomial.X s_j) := by
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have hk_zero :
      stageTargetMap (σ := σ) k (σ i k hik s_i - σ j k hjk s_j) = 0 := by
    -- Move both representatives to a common stage and use equality in the target direct limit.
    calc
      stageTargetMap (σ := σ) k (σ i k hik s_i - σ j k hjk s_j) =
          stageTargetMap (σ := σ) k (σ i k hik s_i) -
            stageTargetMap (σ := σ) k (σ j k hjk s_j) := by
              simp
      _ = stageTargetMap (σ := σ) i s_i - stageTargetMap (σ := σ) j s_j := by
            rw [DFunLike.congr_fun (stageTargetMap_comp (σ := σ) hik) s_i,
              DFunLike.congr_fun (stageTargetMap_comp (σ := σ) hjk) s_j]
      _ = 0 := by rw [hs, sub_self]
  obtain ⟨ℓ, hkℓ, hℓ⟩ := Ring.DirectLimit.of.zero_exact
    (G := S) (f' := fun a b hab ↦ σ a b hab) hk_zero
  let hiℓ : i ≤ ℓ := le_trans hik hkℓ
  let hjℓ : j ≤ ℓ := le_trans hjk hkℓ
  have hstage :
      σ i ℓ hiℓ s_i = σ j ℓ hjℓ s_j := by
    -- `Ring.DirectLimit.of.zero_exact` turns equality in `S∞` into literal equality later on.
    have hℓ_zero :
        σ i ℓ hiℓ s_i - σ j ℓ hjℓ s_j = 0 := by
      simpa [hiℓ, hjℓ, map_sub, map_map' σ hik hkℓ s_i, map_map' σ hjk hkℓ s_j] using hℓ
    exact sub_eq_zero.mp hℓ_zero
  calc
    stageSelfPresentationOf (ρ := ρ) (σ := σ) hcomm i (MvPolynomial.X s_i) =
      stageSelfPresentationOf (ρ := ρ) (σ := σ) hcomm ℓ (MvPolynomial.X (σ i ℓ hiℓ s_i)) := by
        simpa using
          (stageSelfPresentation_var_compatible
            (ρ := ρ) (σ := σ) hcomm hiℓ s_i).symm
    _ = stageSelfPresentationOf (ρ := ρ) (σ := σ) hcomm ℓ (MvPolynomial.X (σ j ℓ hjℓ s_j)) := by
          rw [hstage]
    _ = stageSelfPresentationOf (ρ := ρ) (σ := σ) hcomm j (MvPolynomial.X s_j) := by
          simpa using
            stageSelfPresentation_var_compatible
              (ρ := ρ) (σ := σ) hcomm hjℓ s_j

/-- Helper for Lemma 10.134.9: coefficients of `R∞` lift canonically to the direct limit of the
stage self-presentation rings. -/
private noncomputable abbrev selfPresentationRingDirectLimitCoeff :
    R∞ →+* selfPresentationRingDirectLimit (ρ := ρ) (σ := σ) hcomm :=
  Ring.DirectLimit.lift
    R (fun i j h ↦ ρ i j h)
    (selfPresentationRingDirectLimit (ρ := ρ) (σ := σ) hcomm)
    (fun i ↦ (stageSelfPresentationOf (ρ := ρ) (σ := σ) hcomm i).comp MvPolynomial.C)
    (fun i j hij r ↦
      stageSelfPresentation_coeff_compatible
        (ρ := ρ) (σ := σ) hcomm hij r)

/-- Helper for Lemma 10.134.9: choose a stage representative for a target variable of the
self-presentation `R∞[S∞]`. -/
private theorem targetSelfPresentationVariable_exists_stage
    (s : S∞) :
    ∃ p : Σ i, S i, stageTargetMap (σ := σ) p.1 p.2 = s := by
  obtain ⟨i, s_i, hs⟩ :=
    Ring.DirectLimit.exists_of (G := S) (f' := fun i j h ↦ σ i j h) s
  exact ⟨⟨i, s_i⟩, hs⟩

/-- Helper for Lemma 10.134.9: a chosen stage representative of a target variable in `S∞`. -/
private noncomputable abbrev targetSelfPresentationVariable_stage
    (s : S∞) :
    Σ i, S i :=
  Classical.choose (targetSelfPresentationVariable_exists_stage (σ := σ) s)

/-- Helper for Lemma 10.134.9: the chosen variable representative maps to the prescribed target
element of `S∞`. -/
private theorem targetSelfPresentationVariable_stage_spec
    (s : S∞) :
    stageTargetMap (σ := σ)
        (targetSelfPresentationVariable_stage (σ := σ) s).1
        (targetSelfPresentationVariable_stage (σ := σ) s).2 =
      s :=
  Classical.choose_spec (targetSelfPresentationVariable_exists_stage (σ := σ) s)

/-- Helper for Lemma 10.134.9: a target variable in `S∞` maps to the corresponding class in the
direct limit of the stage self-presentation rings. -/
private noncomputable def selfPresentationRingDirectLimitVar
    (s : S∞) :
    selfPresentationRingDirectLimit (ρ := ρ) (σ := σ) hcomm :=
  let p := targetSelfPresentationVariable_stage (σ := σ) s
  stageSelfPresentationOf (ρ := ρ) (σ := σ) hcomm p.1 (MvPolynomial.X p.2)

/-- Helper for Lemma 10.134.9: when a target variable already comes from stage `i`, the chosen
class in the self-presentation ring direct limit is the expected stage variable class. -/
private theorem selfPresentationRingDirectLimitVar_of_stage
    (i : I) (s_i : S i) :
    selfPresentationRingDirectLimitVar (ρ := ρ) (σ := σ) hcomm
        (stageTargetMap (σ := σ) i s_i) =
      stageSelfPresentationOf (ρ := ρ) (σ := σ) hcomm i (MvPolynomial.X s_i) := by
  let p := targetSelfPresentationVariable_stage (σ := σ) (stageTargetMap (σ := σ) i s_i)
  have hs :
      stageTargetMap (σ := σ) p.1 p.2 = stageTargetMap (σ := σ) i s_i := by
    simpa [p] using
      targetSelfPresentationVariable_stage_spec
        (σ := σ) (stageTargetMap (σ := σ) i s_i)
  -- Compare the chosen variable representative with the original stage variable via equality in
  -- the target direct limit `S∞`.
  simpa [selfPresentationRingDirectLimitVar, p] using
    stageSelfPresentation_X_eq_of_same_target
      (ρ := ρ) (σ := σ) hcomm p.2 s_i hs

/-- Helper for Lemma 10.134.9: evaluate the target self-presentation `R∞[S∞]` in the explicit
ring direct limit of the stage self-presentations. -/
private noncomputable def selfPresentationRingFromTarget :
    let _ : Algebra R∞ S∞ := directLimitAlgebra (ρ := ρ) (σ := σ) hcomm
    (Generators.self R∞ S∞ : Generators R∞ S∞ S∞).Ring →+*
      selfPresentationRingDirectLimit (ρ := ρ) (σ := σ) hcomm :=
  let _ : Algebra R∞ S∞ := directLimitAlgebra (ρ := ρ) (σ := σ) hcomm
  MvPolynomial.eval₂Hom
    (selfPresentationRingDirectLimitCoeff (ρ := ρ) (σ := σ) hcomm)
    (selfPresentationRingDirectLimitVar (ρ := ρ) (σ := σ) hcomm)

/-- Helper for Lemma 10.134.9: the target-to-stage-direct-limit evaluation is a left inverse on
every stage self-presentation. -/
private theorem selfPresentationRingFromTarget_of_stage
    (i : I)
    (q_i :
      (Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).Ring) :
    let _ : Algebra R∞ S∞ := directLimitAlgebra (ρ := ρ) (σ := σ) hcomm
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
    selfPresentationRingFromTarget (ρ := ρ) (σ := σ) hcomm
        ((Generators.defaultHom Pi Pinf).toAlgHom q_i) =
      stageSelfPresentationOf (ρ := ρ) (σ := σ) hcomm i q_i := by
  let _ : Algebra R∞ S∞ := directLimitAlgebra (ρ := ρ) (σ := σ) hcomm
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  let f :
      Pi.Ring →+* selfPresentationRingDirectLimit (ρ := ρ) (σ := σ) hcomm :=
    (selfPresentationRingFromTarget (ρ := ρ) (σ := σ) hcomm).comp
      (Generators.defaultHom Pi Pinf).toAlgHom
  let g :
      Pi.Ring →+* selfPresentationRingDirectLimit (ρ := ρ) (σ := σ) hcomm :=
    stageSelfPresentationOf (ρ := ρ) (σ := σ) hcomm i
  have hfg : f = g := by
    -- Compare the two stage maps on constants and variables of `R_i[S_i]`.
    apply MvPolynomial.ringHom_ext
    · intro r
      change
        selfPresentationRingFromTarget (ρ := ρ) (σ := σ) hcomm
            ((Generators.defaultHom Pi Pinf).toAlgHom (MvPolynomial.C r)) =
          stageSelfPresentationOf (ρ := ρ) (σ := σ) hcomm i (MvPolynomial.C r)
      rw [show (Generators.defaultHom Pi Pinf).toAlgHom (MvPolynomial.C r) =
          MvPolynomial.C (stageBaseMap (ρ := ρ) i r) by
          simpa [Pi, Pinf] using (Generators.defaultHom Pi Pinf).toAlgHom.commutes r]
      -- The coefficient map into the stage direct limit is the defining cocone of that direct
      -- limit.
      simpa [selfPresentationRingFromTarget, selfPresentationRingDirectLimitCoeff,
        stageBaseMap] using
        (Ring.DirectLimit.lift_of
          (G := R)
          (f := fun a b hab ↦ ρ a b hab)
          (P := selfPresentationRingDirectLimit (ρ := ρ) (σ := σ) hcomm)
          (g := fun j ↦
            (stageSelfPresentationOf (ρ := ρ) (σ := σ) hcomm j).comp MvPolynomial.C)
          (Hg := fun a b hab r' ↦
            stageSelfPresentation_coeff_compatible
              (ρ := ρ) (σ := σ) hcomm hab r')
          i r)
    · intro s
      change
        selfPresentationRingFromTarget (ρ := ρ) (σ := σ) hcomm
            ((Generators.defaultHom Pi Pinf).toAlgHom (MvPolynomial.X s)) =
          stageSelfPresentationOf (ρ := ρ) (σ := σ) hcomm i (MvPolynomial.X s)
      rw [show (Generators.defaultHom Pi Pinf).toAlgHom (MvPolynomial.X s) =
          MvPolynomial.X (stageTargetMap (σ := σ) i s) by
          simpa [Pi, Pinf] using Generators.Hom.toAlgHom_X
            (f := Generators.defaultHom Pi Pinf) s]
      -- Variables are sent to the chosen stage class of their image in `S∞`.
      simpa [selfPresentationRingFromTarget] using
        selfPresentationRingDirectLimitVar_of_stage
          (ρ := ρ) (σ := σ) hcomm i s
  exact congrArg (fun h : Pi.Ring →+* _ ↦ h q_i) hfg

/-- Helper for Lemma 10.134.9: if a stage self-presentation polynomial vanishes in the target
presentation ring, then it already vanishes at some later stage. -/
private theorem selfPresentation_ring_zero_exact
    (i : I)
    (q_i :
      (Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).Ring)
    (hzero :
      let _ : Algebra R∞ S∞ := directLimitAlgebra (ρ := ρ) (σ := σ) hcomm
      let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
      let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
      (Generators.defaultHom Pi Pinf).toAlgHom q_i = 0) :
    ∃ j, ∃ hij : i ≤ j,
      stageSelfPresentationTransition (ρ := ρ) (σ := σ) hcomm hij q_i = 0 := by
  let _ : Algebra R∞ S∞ := directLimitAlgebra (ρ := ρ) (σ := σ) hcomm
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  have hzero' :
      selfPresentationRingFromTarget (ρ := ρ) (σ := σ) hcomm
          ((Generators.defaultHom Pi Pinf).toAlgHom q_i) = 0 := by
    exact congrArg
      (selfPresentationRingFromTarget (ρ := ρ) (σ := σ) hcomm) hzero
  have hdl :
      stageSelfPresentationOf (ρ := ρ) (σ := σ) hcomm i q_i = 0 := by
    simpa [Pi, Pinf] using
      (selfPresentationRingFromTarget_of_stage
        (ρ := ρ) (σ := σ) hcomm i q_i).trans hzero'
  obtain ⟨j, hij, hj⟩ := Ring.DirectLimit.of.zero_exact
    (G := fun k ↦ stageSelfPresentationRing (R := R) (S := S) k)
    (f' := fun a b hab ↦ stageSelfPresentationTransition
      (ρ := ρ) (σ := σ) hcomm hab) hdl
  refine ⟨j, hij, ?_⟩
  exact hj

/-- Helper for Lemma 10.134.9: two stage self-presentation polynomials with the same target image
become literally equal at a common later stage. -/
private theorem selfPresentation_ring_eventually_equal_of_same_target
    {i j : I}
    (q_i :
      (Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).Ring)
    (q_j :
      (Generators.self (R j) (S j) : Generators (R j) (S j) (S j)).Ring)
    (hEq :
      let _ : Algebra R∞ S∞ := directLimitAlgebra (ρ := ρ) (σ := σ) hcomm
      let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
      let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
      let _ : Algebra (R i) S∞ :=
        ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ h ↦ hcomm h).comp
          (stageBaseMap (ρ := ρ) i)).toAlgebra
      let _ : Algebra (R j) R∞ := (stageBaseMap (ρ := ρ) j).toAlgebra
      let _ : Algebra (S j) S∞ := (stageTargetMap (σ := σ) j).toAlgebra
      let _ : Algebra (R j) S∞ :=
        ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ h ↦ hcomm h).comp
          (stageBaseMap (ρ := ρ) j)).toAlgebra
      let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
      let _ : IsScalarTower (R i) (S i) S∞ :=
        IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm i)
      let _ : IsScalarTower (R j) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
      let _ : IsScalarTower (R j) (S j) S∞ :=
        IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm j)
      let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
      let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
      let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
      (Generators.defaultHom Pi Pinf).toAlgHom q_i =
        (Generators.defaultHom Pj Pinf).toAlgHom q_j) :
    ∃ k, ∃ hik : i ≤ k, ∃ hjk : j ≤ k,
      stageSelfPresentationTransition (ρ := ρ) (σ := σ) hcomm hik q_i =
        stageSelfPresentationTransition (ρ := ρ) (σ := σ) hcomm hjk q_j := by
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  let _ : Algebra R∞ S∞ := directLimitAlgebra (ρ := ρ) (σ := σ) hcomm
  let _ : Algebra (R i) (R k) := (ρ i k hik).toAlgebra
  let _ : Algebra (S i) (S k) := (σ i k hik).toAlgebra
  let _ : Algebra (R i) (S k) := ((algebraMap (R k) (S k)).comp (ρ i k hik)).toAlgebra
  let _ : Algebra (R j) (R k) := (ρ j k hjk).toAlgebra
  let _ : Algebra (S j) (S k) := (σ j k hjk).toAlgebra
  let _ : Algebra (R j) (S k) := ((algebraMap (R k) (S k)).comp (ρ j k hjk)).toAlgebra
  let _ : Algebra (R i) R∞ := (stageBaseMap (ρ := ρ) i).toAlgebra
  let _ : Algebra (S i) S∞ := (stageTargetMap (σ := σ) i).toAlgebra
  let _ : Algebra (R i) S∞ :=
    ((Ring.DirectLimit.map (fun ℓ ↦ algebraMap (R ℓ) (S ℓ)) fun _ _ h ↦ hcomm h).comp
      (stageBaseMap (ρ := ρ) i)).toAlgebra
  let _ : Algebra (R j) R∞ := (stageBaseMap (ρ := ρ) j).toAlgebra
  let _ : Algebra (S j) S∞ := (stageTargetMap (σ := σ) j).toAlgebra
  let _ : Algebra (R j) S∞ :=
    ((Ring.DirectLimit.map (fun ℓ ↦ algebraMap (R ℓ) (S ℓ)) fun _ _ h ↦ hcomm h).comp
      (stageBaseMap (ρ := ρ) j)).toAlgebra
  let _ : Algebra (R k) R∞ := (stageBaseMap (ρ := ρ) k).toAlgebra
  let _ : Algebra (S k) S∞ := (stageTargetMap (σ := σ) k).toAlgebra
  let _ : Algebra (R k) S∞ :=
    ((Ring.DirectLimit.map (fun ℓ ↦ algebraMap (R ℓ) (S ℓ)) fun _ _ h ↦ hcomm h).comp
      (stageBaseMap (ρ := ρ) k)).toAlgebra
  let _ : IsScalarTower (R i) (R k) (S k) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S k) := IsScalarTower.of_algebraMap_eq' (hcomm hik)
  let _ : IsScalarTower (R j) (R k) (S k) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R j) (S j) (S k) := IsScalarTower.of_algebraMap_eq' (hcomm hjk)
  let _ : IsScalarTower (R i) (R k) R∞ := IsScalarTower.of_algebraMap_eq'
    (stageBaseMap_comp (ρ := ρ) hik).symm
  let _ : IsScalarTower (R j) (R k) R∞ := IsScalarTower.of_algebraMap_eq'
    (stageBaseMap_comp (ρ := ρ) hjk).symm
  let _ : IsScalarTower (R i) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R j) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R k) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R k) (S k) S∞ :=
    IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm k)
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  let Pk : Generators (R k) (S k) (S k) := Generators.self (R k) (S k)
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  let qik : Pk.Ring := stageSelfPresentationTransition
    (ρ := ρ) (σ := σ) hcomm hik q_i
  let qjk : Pk.Ring := stageSelfPresentationTransition
    (ρ := ρ) (σ := σ) hcomm hjk q_j
  have hk_zero :
      (Generators.defaultHom Pk Pinf).toAlgHom (qik - qjk) = 0 := by
    -- Move both stage representatives to the common stage `k` before comparing them in the
    -- target self-presentation.
    have hleft :
        (Generators.defaultHom Pk Pinf).toAlgHom qik =
          (Generators.defaultHom Pi Pinf).toAlgHom q_i := by
      calc
        (Generators.defaultHom Pk Pinf).toAlgHom qik =
            ((Generators.defaultHom Pk Pinf).comp
              (Generators.defaultHom Pi Pk)).toAlgHom q_i := by
                symm
                simpa [qik] using
                  (Generators.Hom.toAlgHom_comp_apply
                    (f := Generators.defaultHom Pi Pk)
                    (g := Generators.defaultHom Pk Pinf)
                    (x := q_i))
        _ = (Generators.defaultHom Pi Pinf).toAlgHom q_i := by
              simpa [Pi, Pk, Pinf] using
                congrArg (fun f ↦ f.toAlgHom q_i)
                  (selfPresentation_defaultHom_comp (ρ := ρ) (σ := σ) hcomm hik)
    have hright :
        (Generators.defaultHom Pk Pinf).toAlgHom qjk =
          (Generators.defaultHom Pj Pinf).toAlgHom q_j := by
      calc
        (Generators.defaultHom Pk Pinf).toAlgHom qjk =
            ((Generators.defaultHom Pk Pinf).comp
              (Generators.defaultHom Pj Pk)).toAlgHom q_j := by
                symm
                simpa [qjk] using
                  (Generators.Hom.toAlgHom_comp_apply
                    (f := Generators.defaultHom Pj Pk)
                    (g := Generators.defaultHom Pk Pinf)
                    (x := q_j))
        _ = (Generators.defaultHom Pj Pinf).toAlgHom q_j := by
              simpa [Pj, Pk, Pinf] using
                congrArg (fun f ↦ f.toAlgHom q_j)
                  (selfPresentation_defaultHom_comp (ρ := ρ) (σ := σ) hcomm hjk)
    calc
      (Generators.defaultHom Pk Pinf).toAlgHom (qik - qjk) =
          (Generators.defaultHom Pk Pinf).toAlgHom qik -
            (Generators.defaultHom Pk Pinf).toAlgHom qjk := by
              simp
      _ = (Generators.defaultHom Pi Pinf).toAlgHom q_i -
            (Generators.defaultHom Pj Pinf).toAlgHom q_j := by
              rw [hleft, hright]
      _ = 0 := by simpa [hEq]
  obtain ⟨ℓ, hkℓ, hℓ⟩ :=
    selfPresentation_ring_zero_exact (ρ := ρ) (σ := σ) hcomm k (qik - qjk) hk_zero
  let hiℓ : i ≤ ℓ := le_trans hik hkℓ
  let hjℓ : j ≤ ℓ := le_trans hjk hkℓ
  refine ⟨ℓ, hiℓ, hjℓ, ?_⟩
  let _ : Algebra (R i) (R ℓ) := (ρ i ℓ hiℓ).toAlgebra
  let _ : Algebra (S i) (S ℓ) := (σ i ℓ hiℓ).toAlgebra
  let _ : Algebra (R i) (S ℓ) := ((algebraMap (R ℓ) (S ℓ)).comp (ρ i ℓ hiℓ)).toAlgebra
  let _ : Algebra (R j) (R ℓ) := (ρ j ℓ hjℓ).toAlgebra
  let _ : Algebra (S j) (S ℓ) := (σ j ℓ hjℓ).toAlgebra
  let _ : Algebra (R j) (S ℓ) := ((algebraMap (R ℓ) (S ℓ)).comp (ρ j ℓ hjℓ)).toAlgebra
  let _ : IsScalarTower (R i) (R ℓ) (S ℓ) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S ℓ) := IsScalarTower.of_algebraMap_eq' (hcomm hiℓ)
  let _ : IsScalarTower (R j) (R ℓ) (S ℓ) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R j) (S j) (S ℓ) := IsScalarTower.of_algebraMap_eq' (hcomm hjℓ)
  let Pℓ : Generators (R ℓ) (S ℓ) (S ℓ) := Generators.self (R ℓ) (S ℓ)
  have hleft :
      (Generators.defaultHom Pk Pℓ).toAlgHom qik =
        (Generators.defaultHom Pi Pℓ).toAlgHom q_i := by
    calc
      (Generators.defaultHom Pk Pℓ).toAlgHom qik =
          ((Generators.defaultHom Pk Pℓ).comp
            (Generators.defaultHom Pi Pk)).toAlgHom q_i := by
              symm
              simpa [qik] using
                (Generators.Hom.toAlgHom_comp_apply
                  (f := Generators.defaultHom Pi Pk)
                  (g := Generators.defaultHom Pk Pℓ)
                  (x := q_i))
      _ = (Generators.defaultHom Pi Pℓ).toAlgHom q_i := by
            simpa [Pi, Pk, Pℓ] using
              congrArg (fun f ↦ f.toAlgHom q_i)
                (selfPresentation_defaultHom_comp (ρ := ρ) (σ := σ) hcomm hiℓ)
  have hright :
      (Generators.defaultHom Pk Pℓ).toAlgHom qjk =
        (Generators.defaultHom Pj Pℓ).toAlgHom q_j := by
    calc
      (Generators.defaultHom Pk Pℓ).toAlgHom qjk =
          ((Generators.defaultHom Pk Pℓ).comp
            (Generators.defaultHom Pj Pk)).toAlgHom q_j := by
              symm
              simpa [qjk] using
                (Generators.Hom.toAlgHom_comp_apply
                  (f := Generators.defaultHom Pj Pk)
                  (g := Generators.defaultHom Pk Pℓ)
                  (x := q_j))
      _ = (Generators.defaultHom Pj Pℓ).toAlgHom q_j := by
            simpa [Pj, Pk, Pℓ] using
              congrArg (fun f ↦ f.toAlgHom q_j)
                (selfPresentation_defaultHom_comp (ρ := ρ) (σ := σ) hcomm hjℓ)
  have hℓ_eq :
      (Generators.defaultHom Pk Pℓ).toAlgHom qik =
        (Generators.defaultHom Pk Pℓ).toAlgHom qjk := by
    have hℓ_zero :
        (Generators.defaultHom Pk Pℓ).toAlgHom (qik - qjk) = 0 := hℓ
    simpa [map_sub, sub_eq_zero] using hℓ_zero
  exact hleft.symm.trans (hℓ_eq.trans hright)

/-- Helper for Lemma 10.134.9: every target square-kernel element already comes from the square of
some stage kernel. -/
private theorem selfPresentation_ker_square_exists_stage
    [DirectedSystem S fun i j h ↦ σ i j h]
    (q :
      let _ : Algebra R∞ S∞ := directLimitAlgebra (ρ := ρ) (σ := σ) hcomm
      (Generators.self R∞ S∞ : Generators R∞ S∞ S∞).Ring)
    (hq :
      let _ : Algebra R∞ S∞ := directLimitAlgebra (ρ := ρ) (σ := σ) hcomm
      q ∈ ((Generators.self R∞ S∞ : Generators R∞ S∞ S∞).toExtension).ker ^ 2) :
    ∃ j, ∃ q_j :
      (Generators.self (R j) (S j) : Generators (R j) (S j) (S j)).Ring,
      let _ : Algebra (R j) R∞ := (stageBaseMap (ρ := ρ) j).toAlgebra
      let _ : Algebra (S j) S∞ := (stageTargetMap (σ := σ) j).toAlgebra
      let _ : Algebra (R j) S∞ :=
        ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ h ↦ hcomm h).comp
          (stageBaseMap (ρ := ρ) j)).toAlgebra
      let _ : Algebra R∞ S∞ :=
        (Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ h ↦ hcomm h).toAlgebra
      let _ : IsScalarTower (R j) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
      let _ : IsScalarTower (R j) (S j) S∞ :=
        IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm j)
      let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
      let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
      q_j ∈ (Pj.toExtension).ker ^ 2 ∧
        (Generators.defaultHom Pj Pinf).toAlgHom q_j = q := by
  classical
  let _ : Algebra R∞ S∞ := directLimitAlgebra (ρ := ρ) (σ := σ) hcomm
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  let DescendsSquare : Pinf.Ring → Prop := fun p ↦
    ∃ j, ∃ q_j :
      (Generators.self (R j) (S j) : Generators (R j) (S j) (S j)).Ring,
      let _ : Algebra (R j) R∞ := (stageBaseMap (ρ := ρ) j).toAlgebra
      let _ : Algebra (S j) S∞ := (stageTargetMap (σ := σ) j).toAlgebra
      let _ : Algebra (R j) S∞ :=
        ((Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ h ↦ hcomm h).comp
          (stageBaseMap (ρ := ρ) j)).toAlgebra
      let _ : Algebra R∞ S∞ :=
        (Ring.DirectLimit.map (fun k ↦ algebraMap (R k) (S k)) fun _ _ h ↦ hcomm h).toAlgebra
      let _ : IsScalarTower (R j) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
      let _ : IsScalarTower (R j) (S j) S∞ :=
        IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm j)
      let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
      let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
      q_j ∈ (Pj.toExtension).ker ^ 2 ∧
        (Generators.defaultHom Pj Pinf).toAlgHom q_j = p
  have hspan :
      (Pinf.toExtension).ker ^ 2 =
        Ideal.span (((Pinf.toExtension).ker : Set Pinf.Ring) * ((Pinf.toExtension).ker : Set Pinf.Ring)) := by
    rw [pow_two, ← (Pinf.toExtension).ker.span_eq, ← (Pinf.toExtension).ker.span_eq,
      Ideal.span_mul_span']
  rw [hspan] at hq
  -- Prove the descent statement by span induction on generators of `I∞²`.
  have hdesc : DescendsSquare q := by
    refine Submodule.span_induction (p := fun p _ ↦ DescendsSquare p) ?_ ?_ ?_ ?_ hq
  · intro z hz
    rcases hz with ⟨a, ha, b, hb, rfl⟩
    obtain ⟨i, a_i, ha_i⟩ :=
      selfPresentation_ker_exists_stage (ρ := ρ) (σ := σ) hcomm a
    obtain ⟨j, b_j, hb_j⟩ :=
      selfPresentation_ker_exists_stage (ρ := ρ) (σ := σ) hcomm b
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    let _ : Algebra (R i) (R k) := (ρ i k hik).toAlgebra
    let _ : Algebra (S i) (S k) := (σ i k hik).toAlgebra
    let _ : Algebra (R i) (S k) := ((algebraMap (R k) (S k)).comp (ρ i k hik)).toAlgebra
    let _ : Algebra (R j) (R k) := (ρ j k hjk).toAlgebra
    let _ : Algebra (S j) (S k) := (σ j k hjk).toAlgebra
    let _ : Algebra (R j) (S k) := ((algebraMap (R k) (S k)).comp (ρ j k hjk)).toAlgebra
    let _ : IsScalarTower (R i) (R k) (S k) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) (S k) := IsScalarTower.of_algebraMap_eq' (hcomm hik)
    let _ : IsScalarTower (R j) (R k) (S k) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R j) (S j) (S k) := IsScalarTower.of_algebraMap_eq' (hcomm hjk)
    let _ : Algebra (R k) R∞ := (stageBaseMap (ρ := ρ) k).toAlgebra
    let _ : Algebra (S k) S∞ := (stageTargetMap (σ := σ) k).toAlgebra
    let _ : Algebra (R k) S∞ :=
      ((Ring.DirectLimit.map (fun ℓ ↦ algebraMap (R ℓ) (S ℓ)) fun _ _ h ↦ hcomm h).comp
        (stageBaseMap (ρ := ρ) k)).toAlgebra
    let _ : Algebra R∞ S∞ :=
      (Ring.DirectLimit.map (fun ℓ ↦ algebraMap (R ℓ) (S ℓ)) fun _ _ h ↦ hcomm h).toAlgebra
    let _ : IsScalarTower (R k) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R k) (S k) S∞ :=
      IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm k)
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
    let Pk : Generators (R k) (S k) (S k) := Generators.self (R k) (S k)
    let a_k : Pk.toExtension.ker :=
      ⟨(Generators.defaultHom Pi Pk).toAlgHom a_i.1,
        selfPresentation_defaultHom_mem_ker (ρ := ρ) (σ := σ) hcomm hik a_i⟩
    let b_k : Pk.toExtension.ker :=
      ⟨(Generators.defaultHom Pj Pk).toAlgHom b_j.1,
        selfPresentation_defaultHom_mem_ker (ρ := ρ) (σ := σ) hcomm hjk b_j⟩
    refine ⟨k, a_k.1 * b_k.1, ?_⟩
    -- Move both kernel factors to the common stage `k` and multiply there.
    constructor
    · simpa [pow_two] using Ideal.mul_mem_mul a_k.2 b_k.2
    · calc
        (Generators.defaultHom Pk Pinf).toAlgHom (a_k.1 * b_k.1) =
            (Generators.defaultHom Pk Pinf).toAlgHom a_k.1 *
              (Generators.defaultHom Pk Pinf).toAlgHom b_k.1 := by
                simp
        _ = a.1 * b.1 := by
              rw [ha_i, hb_j]
              simp [a_k, b_k, Pi, Pj, Pk, Pinf,
                selfPresentation_defaultHom_comp (ρ := ρ) (σ := σ) hcomm hik,
                selfPresentation_defaultHom_comp (ρ := ρ) (σ := σ) hcomm hjk]
  · obtain ⟨i⟩ := ‹Nonempty I›
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    refine ⟨i, 0, ?_⟩
    constructor
    · exact Ideal.zero_mem _
    · simp [Pi]
  · intro x y hx hy
    rcases hx with ⟨i, q_i, hq_i, hmap_i⟩
    rcases hy with ⟨j, q_j, hq_j, hmap_j⟩
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    let _ : Algebra (R i) (R k) := (ρ i k hik).toAlgebra
    let _ : Algebra (S i) (S k) := (σ i k hik).toAlgebra
    let _ : Algebra (R i) (S k) := ((algebraMap (R k) (S k)).comp (ρ i k hik)).toAlgebra
    let _ : Algebra (R j) (R k) := (ρ j k hjk).toAlgebra
    let _ : Algebra (S j) (S k) := (σ j k hjk).toAlgebra
    let _ : Algebra (R j) (S k) := ((algebraMap (R k) (S k)).comp (ρ j k hjk)).toAlgebra
    let _ : IsScalarTower (R i) (R k) (S k) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) (S k) := IsScalarTower.of_algebraMap_eq' (hcomm hik)
    let _ : IsScalarTower (R j) (R k) (S k) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R j) (S j) (S k) := IsScalarTower.of_algebraMap_eq' (hcomm hjk)
    let _ : Algebra (R k) R∞ := (stageBaseMap (ρ := ρ) k).toAlgebra
    let _ : Algebra (S k) S∞ := (stageTargetMap (σ := σ) k).toAlgebra
    let _ : Algebra (R k) S∞ :=
      ((Ring.DirectLimit.map (fun ℓ ↦ algebraMap (R ℓ) (S ℓ)) fun _ _ h ↦ hcomm h).comp
        (stageBaseMap (ρ := ρ) k)).toAlgebra
    let _ : Algebra R∞ S∞ :=
      (Ring.DirectLimit.map (fun ℓ ↦ algebraMap (R ℓ) (S ℓ)) fun _ _ h ↦ hcomm h).toAlgebra
    let _ : IsScalarTower (R k) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R k) (S k) S∞ :=
      IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm k)
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
    let Pk : Generators (R k) (S k) (S k) := Generators.self (R k) (S k)
    let qk_i : Pk.Ring := (Generators.defaultHom Pi Pk).toAlgHom q_i
    let qk_j : Pk.Ring := (Generators.defaultHom Pj Pk).toAlgHom q_j
    have hqk_i : qk_i ∈ (Pk.toExtension).ker ^ 2 := by
      exact (selfPresentation_square_ideal_le_comap (ρ := ρ) (σ := σ) hcomm hik) hq_i
    have hqk_j : qk_j ∈ (Pk.toExtension).ker ^ 2 := by
      exact (selfPresentation_square_ideal_le_comap (ρ := ρ) (σ := σ) hcomm hjk) hq_j
    refine ⟨k, qk_i + qk_j, ?_⟩
    constructor
    · exact Ideal.add_mem _ hqk_i hqk_j
    · calc
        (Generators.defaultHom Pk Pinf).toAlgHom (qk_i + qk_j) =
            (Generators.defaultHom Pk Pinf).toAlgHom qk_i +
              (Generators.defaultHom Pk Pinf).toAlgHom qk_j := by
                simp
        _ = x + y := by
              rw [hmap_i, hmap_j]
              simp [qk_i, qk_j, Pi, Pj, Pk, Pinf,
                selfPresentation_defaultHom_comp (ρ := ρ) (σ := σ) hcomm hik,
                selfPresentation_defaultHom_comp (ρ := ρ) (σ := σ) hcomm hjk]
  · intro c q _ hq
    rcases hq with ⟨j, q_j, hq_j, hmap_j⟩
    obtain ⟨i, c_i, hc_i⟩ :=
      selfPresentation_ring_exists_stage (ρ := ρ) (σ := σ) hcomm c
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    let _ : Algebra (R i) (R k) := (ρ i k hik).toAlgebra
    let _ : Algebra (S i) (S k) := (σ i k hik).toAlgebra
    let _ : Algebra (R i) (S k) := ((algebraMap (R k) (S k)).comp (ρ i k hik)).toAlgebra
    let _ : Algebra (R j) (R k) := (ρ j k hjk).toAlgebra
    let _ : Algebra (S j) (S k) := (σ j k hjk).toAlgebra
    let _ : Algebra (R j) (S k) := ((algebraMap (R k) (S k)).comp (ρ j k hjk)).toAlgebra
    let _ : IsScalarTower (R i) (R k) (S k) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R i) (S i) (S k) := IsScalarTower.of_algebraMap_eq' (hcomm hik)
    let _ : IsScalarTower (R j) (R k) (S k) := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R j) (S j) (S k) := IsScalarTower.of_algebraMap_eq' (hcomm hjk)
    let _ : Algebra (R k) R∞ := (stageBaseMap (ρ := ρ) k).toAlgebra
    let _ : Algebra (S k) S∞ := (stageTargetMap (σ := σ) k).toAlgebra
    let _ : Algebra (R k) S∞ :=
      ((Ring.DirectLimit.map (fun ℓ ↦ algebraMap (R ℓ) (S ℓ)) fun _ _ h ↦ hcomm h).comp
        (stageBaseMap (ρ := ρ) k)).toAlgebra
    let _ : Algebra R∞ S∞ :=
      (Ring.DirectLimit.map (fun ℓ ↦ algebraMap (R ℓ) (S ℓ)) fun _ _ h ↦ hcomm h).toAlgebra
    let _ : IsScalarTower (R k) R∞ S∞ := IsScalarTower.of_algebraMap_eq' rfl
    let _ : IsScalarTower (R k) (S k) S∞ :=
      IsScalarTower.of_algebraMap_eq' (directLimit_square (ρ := ρ) (σ := σ) hcomm k)
    let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
    let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
    let Pk : Generators (R k) (S k) (S k) := Generators.self (R k) (S k)
    let ck : Pk.Ring := (Generators.defaultHom Pi Pk).toAlgHom c_i
    let qk : Pk.Ring := (Generators.defaultHom Pj Pk).toAlgHom q_j
    have hqk : qk ∈ (Pk.toExtension).ker ^ 2 := by
      exact (selfPresentation_square_ideal_le_comap (ρ := ρ) (σ := σ) hcomm hjk) hq_j
    refine ⟨k, ck * qk, ?_⟩
    constructor
    · exact Ideal.mul_mem_left _ _ hqk
    · calc
        (Generators.defaultHom Pk Pinf).toAlgHom (ck * qk) =
            (Generators.defaultHom Pk Pinf).toAlgHom ck *
              (Generators.defaultHom Pk Pinf).toAlgHom qk := by
                simp
        _ = c * q := by
              rw [hc_i, hmap_j]
              simp [ck, qk, Pi, Pj, Pk, Pinf,
                selfPresentation_defaultHom_comp (ρ := ρ) (σ := σ) hcomm hik,
                selfPresentation_defaultHom_comp (ρ := ρ) (σ := σ) hcomm hjk,
                smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  exact hdesc

/-- Helper for Lemma 10.134.9: the degree-`1` comparison component is surjective because every
target kernel generator descends to a stage kernel generator. -/
private theorem naiveCotangentDirectLimitComparisonOne_surjective
    [DecidableEq I] :
    Function.Surjective
      (naiveCotangentDirectLimitComparisonOne (ρ := ρ) (σ := σ) hcomm).hom := by
  classical
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  intro z
  rcases Extension.Cotangent.mk_surjective z.down with ⟨x, rfl⟩
  obtain ⟨i, x_i, hx_i⟩ :=
    selfPresentation_ker_exists_stage (ρ := ρ) (σ := σ) hcomm x
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let fiInf : Pi.toExtension.Hom Pinf.toExtension := (Generators.defaultHom Pi Pinf).toExtensionHom
  refine ⟨Module.DirectLimit.of S∞ I
      (fun k ↦ (stageNaiveCotangentBaseChange (σ := σ) k).X 1)
      (fun _ _ hij ↦ ((stageNaiveCotangentBaseChangeTransition
        (ρ := ρ) (σ := σ) hcomm hij).f 1).hom) i
      (((1 : S∞) ⊗ₜ[S i] ULift.up (Extension.Cotangent.mk x_i))), ?_⟩
  -- Evaluate the comparison on the descended stage generator and identify its target image.
  rw [naiveCotangentDirectLimitComparisonOne_of_stage
    (ρ := ρ) (σ := σ) hcomm i
    (((1 : S∞) ⊗ₜ[S i] ULift.up (Extension.Cotangent.mk x_i)))]
  rw [stageNaiveCotangentToTarget_degree_one_generator_after_transport
    (ρ := ρ) (σ := σ) hcomm i (Extension.Cotangent.mk x_i)]
  change ULift.up (Extension.Cotangent.map fiInf (Extension.Cotangent.mk x_i)) =
    ULift.up (Extension.Cotangent.mk x)
  rw [ULift.up.injEq, Extension.Cotangent.map_mk]
  congr 1
  exact hx_i

/-- Helper for Lemma 10.134.9: a stage degree-`1` generator class already vanishes in the source
direct limit once its image under the target comparison vanishes. -/
private theorem stage_degree_one_generator_class_eq_zero_of_target_zero
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)]
    [DecidableEq I]
    (i : I)
    (x_i :
      ((Generators.self (R i) (S i) : Generators (R i) (S i) (S i)).toExtension).ker)
    (hzero :
      (naiveCotangentDirectLimitComparisonOne (ρ := ρ) (σ := σ) hcomm).hom
          (Module.DirectLimit.of S∞ I
            (fun k ↦ (stageNaiveCotangentBaseChange (σ := σ) k).X 1)
            (fun _ _ hij ↦ ((stageNaiveCotangentBaseChangeTransition
              (ρ := ρ) (σ := σ) hcomm hij).f 1).hom) i
            (((1 : S∞) ⊗ₜ[S i] ULift.up (Extension.Cotangent.mk x_i)))) = 0) :
    Module.DirectLimit.of S∞ I
        (fun k ↦ (stageNaiveCotangentBaseChange (σ := σ) k).X 1)
        (fun _ _ hij ↦ ((stageNaiveCotangentBaseChangeTransition
          (ρ := ρ) (σ := σ) hcomm hij).f 1).hom) i
        (((1 : S∞) ⊗ₜ[S i] ULift.up (Extension.Cotangent.mk x_i))) = 0 := by
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  have hsquare_target :
      (Generators.defaultHom Pi Pinf).toAlgHom x_i.1 ∈ (Pinf.toExtension).ker ^ 2 := by
    -- Translate target vanishing into square-ideal membership in the target self-presentation.
    simpa [Ideal.Quotient.eq_zero_iff_mem] using
      (stage_degree_one_generator_target_zero_iff_square_quotient_zero
        (ρ := ρ) (σ := σ) hcomm i x_i).mp hzero
  obtain ⟨j, q_j, hq_j_mem, hq_j_map⟩ :=
    selfPresentation_ker_square_exists_stage (ρ := ρ) (σ := σ) hcomm
      ((Generators.defaultHom Pi Pinf).toAlgHom x_i.1) hsquare_target
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  obtain ⟨k, hik, hjk, hk_eq⟩ :=
    selfPresentation_ring_eventually_equal_of_same_target
      (ρ := ρ) (σ := σ) hcomm x_i.1 q_j hq_j_map
  let _ : Algebra (R i) (R k) := (ρ i k hik).toAlgebra
  let _ : Algebra (S i) (S k) := (σ i k hik).toAlgebra
  let _ : Algebra (R i) (S k) := ((algebraMap (R k) (S k)).comp (ρ i k hik)).toAlgebra
  let _ : Algebra (R j) (R k) := (ρ j k hjk).toAlgebra
  let _ : Algebra (S j) (S k) := (σ j k hjk).toAlgebra
  let _ : Algebra (R j) (S k) := ((algebraMap (R k) (S k)).comp (ρ j k hjk)).toAlgebra
  let _ : IsScalarTower (R i) (R k) (S k) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R i) (S i) (S k) := IsScalarTower.of_algebraMap_eq' (hcomm hik)
  let _ : IsScalarTower (R j) (R k) (S k) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (R j) (S j) (S k) := IsScalarTower.of_algebraMap_eq' (hcomm hjk)
  let Pk : Generators (R k) (S k) (S k) := Generators.self (R k) (S k)
  let x_k : Pk.toExtension.ker :=
    ⟨stageSelfPresentationTransition (ρ := ρ) (σ := σ) hcomm hik x_i.1,
      selfPresentation_defaultHom_mem_ker (ρ := ρ) (σ := σ) hcomm hik x_i⟩
  have hqk_mem :
      stageSelfPresentationTransition (ρ := ρ) (σ := σ) hcomm hjk q_j ∈
        (Pk.toExtension).ker ^ 2 := by
    exact (selfPresentation_square_ideal_le_comap (ρ := ρ) (σ := σ) hcomm hjk) hq_j_mem
  have hxk_mem : x_k.1 ∈ (Pk.toExtension).ker ^ 2 := by
    simpa [x_k] using hk_eq.symm ▸ hqk_mem
  have hxk_zero : Extension.Cotangent.mk x_k = 0 := by
    exact (Extension.Cotangent.mk_eq_zero_iff x_k).mpr hxk_mem
  let G : I → Type u := fun ℓ ↦ (stageNaiveCotangentBaseChange (σ := σ) ℓ).X 1
  let μ : ∀ a b, a ≤ b → G a →ₗ[S∞] G b := fun _ _ hab ↦
    ((stageNaiveCotangentBaseChangeTransition (ρ := ρ) (σ := σ) hcomm hab).f 1).hom
  let ι : ∀ ℓ, G ℓ →ₗ[S∞] naiveCotangentDirectLimitDegreeOne hcomm :=
    fun ℓ ↦ Module.DirectLimit.of S∞ I G μ ℓ
  have hmove :
      (ι i) (((1 : S∞) ⊗ₜ[S i] ULift.up (Extension.Cotangent.mk x_i))) =
        (ι k) (((1 : S∞) ⊗ₜ[S k] ULift.up (Extension.Cotangent.mk x_k))) := by
    -- Move the generator to stage `k` and rewrite the transition on conormal generators.
    calc
      (ι i) (((1 : S∞) ⊗ₜ[S i] ULift.up (Extension.Cotangent.mk x_i))) =
        (ι k)
          ((((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm hik).f 1).hom)
            (((1 : S∞) ⊗ₜ[S i] ULift.up (Extension.Cotangent.mk x_i)))) := by
              simpa [ι, hik] using
                (Module.DirectLimit.of_f
                  (R := S∞) (ι := I)
                  (G := G) (f := μ)
                  (i := i) (j := k) (hij := hik)
                  (x := ((1 : S∞) ⊗ₜ[S i] ULift.up (Extension.Cotangent.mk x_i))))
      _ = (ι k)
          (((1 : S∞) ⊗ₜ[S k]
            ULift.up
              (Extension.Cotangent.map
                ((Generators.defaultHom Pi Pk).toExtensionHom)
                (Extension.Cotangent.mk x_i)))) := by
                rw [stageNaiveCotangentBaseChangeTransition_f_one_unit_tensor
                  (ρ := ρ) (σ := σ) hcomm hik (Extension.Cotangent.mk x_i)]
      _ = (ι k) (((1 : S∞) ⊗ₜ[S k] ULift.up (Extension.Cotangent.mk x_k))) := by
            congr 2
            rw [Extension.Cotangent.map_mk]
    -- The final rewrite is exactly the definition of the moved kernel generator `x_k`.
  calc
    (ι i) (((1 : S∞) ⊗ₜ[S i] ULift.up (Extension.Cotangent.mk x_i))) =
      (ι k) (((1 : S∞) ⊗ₜ[S k] ULift.up (Extension.Cotangent.mk x_k))) := hmove
    _ = (ι k) 0 := by rw [hxk_zero]; simp
    _ = 0 := by simp [ι]

/-- Helper for Lemma 10.134.9: every stage degree-`1` class in the explicit source direct limit
can be rewritten as a single stage generator after passing to a later stage. -/
private theorem degree_one_directLimit_class_exists_stage_generator
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)]
    [DecidableEq I]
    {i : I}
    (x : (stageNaiveCotangentBaseChange (σ := σ) i).X 1) :
    ∃ j, ∃ x_j :
      ((Generators.self (R j) (S j) : Generators (R j) (S j) (S j)).toExtension).ker,
      Module.DirectLimit.of S∞ I
          (fun k ↦ (stageNaiveCotangentBaseChange (σ := σ) k).X 1)
          (fun _ _ hij ↦ ((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm hij).f 1).hom) i x =
        Module.DirectLimit.of S∞ I
          (fun k ↦ (stageNaiveCotangentBaseChange (σ := σ) k).X 1)
          (fun _ _ hij ↦ ((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm hij).f 1).hom) j
          (((1 : S∞) ⊗ₜ[S j] ULift.up (Extension.Cotangent.mk x_j))) := by
  let G : I → Type u := fun k ↦ (stageNaiveCotangentBaseChange (σ := σ) k).X 1
  let μ : ∀ a b, a ≤ b → G a →ₗ[S∞] G b := fun _ _ hab ↦
    ((stageNaiveCotangentBaseChangeTransition (ρ := ρ) (σ := σ) hcomm hab).f 1).hom
  let ι : ∀ k, G k →ₗ[S∞] naiveCotangentDirectLimitDegreeOne hcomm :=
    fun k ↦ Module.DirectLimit.of S∞ I G μ k
  induction x using TensorProduct.induction_on with
  | zero =>
      let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
      let x_i : Pi.toExtension.ker := ⟨0, by simp⟩
      refine ⟨i, x_i, ?_⟩
      simp [ι, x_i]
  | tmul r y =>
      rcases y with ⟨y⟩
      obtain ⟨x_i, rfl⟩ := Extension.Cotangent.mk_surjective y
      obtain ⟨j, s_j, hs_j⟩ := Ring.DirectLimit.exists_of
        (G := S) (f' := fun a b hab ↦ σ a b hab) r
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      let _ : Algebra (R i) (R k) := (ρ i k hik).toAlgebra
      let _ : Algebra (S i) (S k) := (σ i k hik).toAlgebra
      let _ : Algebra (R i) (S k) := ((algebraMap (R k) (S k)).comp (ρ i k hik)).toAlgebra
      let _ : IsScalarTower (R i) (R k) (S k) := IsScalarTower.of_algebraMap_eq' rfl
      let _ : IsScalarTower (R i) (S i) (S k) := IsScalarTower.of_algebraMap_eq' (hcomm hik)
      let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
      let Pk : Generators (R k) (S k) (S k) := Generators.self (R k) (S k)
      let x_k : Pk.toExtension.ker :=
        ⟨stageSelfPresentationTransition (ρ := ρ) (σ := σ) hcomm hik x_i.1,
          selfPresentation_defaultHom_mem_ker (ρ := ρ) (σ := σ) hcomm hik x_i⟩
      let c_k : S k := σ j k hjk s_j
      obtain ⟨z_k, hz_k⟩ :=
        Extension.Cotangent.mk_surjective (c_k • Extension.Cotangent.mk x_k)
      refine ⟨k, z_k, ?_⟩
      have hmove :
          (ι i) (((1 : S∞) ⊗ₜ[S i] ULift.up (Extension.Cotangent.mk x_i))) =
            (ι k) (((1 : S∞) ⊗ₜ[S k] ULift.up (Extension.Cotangent.mk x_k))) := by
        calc
          (ι i) (((1 : S∞) ⊗ₜ[S i] ULift.up (Extension.Cotangent.mk x_i))) =
            (ι k)
              ((((stageNaiveCotangentBaseChangeTransition
                (ρ := ρ) (σ := σ) hcomm hik).f 1).hom)
                (((1 : S∞) ⊗ₜ[S i] ULift.up (Extension.Cotangent.mk x_i)))) := by
                  simpa [ι, hik] using
                    (Module.DirectLimit.of_f
                      (R := S∞) (ι := I) (G := G) (f := μ)
                      (i := i) (j := k) (hij := hik)
                      (x := ((1 : S∞) ⊗ₜ[S i] ULift.up (Extension.Cotangent.mk x_i))))
          _ = (ι k)
              (((1 : S∞) ⊗ₜ[S k]
                ULift.up
                  (Extension.Cotangent.map
                    ((Generators.defaultHom Pi Pk).toExtensionHom)
                    (Extension.Cotangent.mk x_i)))) := by
                    rw [stageNaiveCotangentBaseChangeTransition_f_one_unit_tensor
                      (ρ := ρ) (σ := σ) hcomm hik (Extension.Cotangent.mk x_i)]
          _ = (ι k) (((1 : S∞) ⊗ₜ[S k] ULift.up (Extension.Cotangent.mk x_k))) := by
                congr 2
                rw [Extension.Cotangent.map_mk]
      have hs_k :
          stageTargetMap (σ := σ) j s_j = stageTargetMap (σ := σ) k c_k := by
        simpa [c_k] using DFunLike.congr_fun (stageTargetMap_comp (σ := σ) hjk) s_j
      calc
        (ι i) (r ⊗ₜ[S i] ULift.up (Extension.Cotangent.mk x_i)) =
          (ι i)
            ((stageTargetMap (σ := σ) j s_j) ⊗ₜ[S i] ULift.up (Extension.Cotangent.mk x_i)) := by
              rw [hs_j]
        _ = (stageTargetMap (σ := σ) j s_j) •
              (ι i (((1 : S∞) ⊗ₜ[S i] ULift.up (Extension.Cotangent.mk x_i)))) := by
                simp [TensorProduct.smul_tmul', ι]
        _ = (stageTargetMap (σ := σ) j s_j) •
              (ι k (((1 : S∞) ⊗ₜ[S k] ULift.up (Extension.Cotangent.mk x_k)))) := by
                rw [hmove]
        _ = (ι k)
              ((stageTargetMap (σ := σ) j s_j) •
                (((1 : S∞) ⊗ₜ[S k] ULift.up (Extension.Cotangent.mk x_k)))) := by
                  rfl
        _ = (ι k)
              ((stageTargetMap (σ := σ) k c_k) •
                (((1 : S∞) ⊗ₜ[S k] ULift.up (Extension.Cotangent.mk x_k)))) := by
                  rw [hs_k]
        _ = (ι k)
              (((1 : S∞) ⊗ₜ[S k] ULift.up (c_k • Extension.Cotangent.mk x_k))) := by
                simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul]
        _ = (ι k) (((1 : S∞) ⊗ₜ[S k] ULift.up (Extension.Cotangent.mk z_k))) := by
              rw [hz_k]
  | add x y hx hy =>
      rcases hx with ⟨j, x_j, hxj⟩
      rcases hy with ⟨k, y_k, hyk⟩
      obtain ⟨ℓ, hjℓ, hkℓ⟩ := exists_ge_ge j k
      let _ : Algebra (R j) (R ℓ) := (ρ j ℓ hjℓ).toAlgebra
      let _ : Algebra (S j) (S ℓ) := (σ j ℓ hjℓ).toAlgebra
      let _ : Algebra (R j) (S ℓ) := ((algebraMap (R ℓ) (S ℓ)).comp (ρ j ℓ hjℓ)).toAlgebra
      let _ : Algebra (R k) (R ℓ) := (ρ k ℓ hkℓ).toAlgebra
      let _ : Algebra (S k) (S ℓ) := (σ k ℓ hkℓ).toAlgebra
      let _ : Algebra (R k) (S ℓ) := ((algebraMap (R ℓ) (S ℓ)).comp (ρ k ℓ hkℓ)).toAlgebra
      let _ : IsScalarTower (R j) (R ℓ) (S ℓ) := IsScalarTower.of_algebraMap_eq' rfl
      let _ : IsScalarTower (R j) (S j) (S ℓ) := IsScalarTower.of_algebraMap_eq' (hcomm hjℓ)
      let _ : IsScalarTower (R k) (R ℓ) (S ℓ) := IsScalarTower.of_algebraMap_eq' rfl
      let _ : IsScalarTower (R k) (S k) (S ℓ) := IsScalarTower.of_algebraMap_eq' (hcomm hkℓ)
      let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
      let Pk : Generators (R k) (S k) (S k) := Generators.self (R k) (S k)
      let Pℓ : Generators (R ℓ) (S ℓ) (S ℓ) := Generators.self (R ℓ) (S ℓ)
      let x_ℓ : Pℓ.toExtension.ker :=
        ⟨stageSelfPresentationTransition (ρ := ρ) (σ := σ) hcomm hjℓ x_j.1,
          selfPresentation_defaultHom_mem_ker (ρ := ρ) (σ := σ) hcomm hjℓ x_j⟩
      let y_ℓ : Pℓ.toExtension.ker :=
        ⟨stageSelfPresentationTransition (ρ := ρ) (σ := σ) hcomm hkℓ y_k.1,
          selfPresentation_defaultHom_mem_ker (ρ := ρ) (σ := σ) hcomm hkℓ y_k⟩
      obtain ⟨z_ℓ, hz_ℓ⟩ :=
        Extension.Cotangent.mk_surjective
          (Extension.Cotangent.mk x_ℓ + Extension.Cotangent.mk y_ℓ)
      have hxℓ :
          (ι j) (((1 : S∞) ⊗ₜ[S j] ULift.up (Extension.Cotangent.mk x_j))) =
            (ι ℓ) (((1 : S∞) ⊗ₜ[S ℓ] ULift.up (Extension.Cotangent.mk x_ℓ))) := by
        calc
          (ι j) (((1 : S∞) ⊗ₜ[S j] ULift.up (Extension.Cotangent.mk x_j))) =
            (ι ℓ)
              ((((stageNaiveCotangentBaseChangeTransition
                (ρ := ρ) (σ := σ) hcomm hjℓ).f 1).hom)
                (((1 : S∞) ⊗ₜ[S j] ULift.up (Extension.Cotangent.mk x_j)))) := by
                  simpa [ι, hjℓ] using
                    (Module.DirectLimit.of_f
                      (R := S∞) (ι := I) (G := G) (f := μ)
                      (i := j) (j := ℓ) (hij := hjℓ)
                      (x := ((1 : S∞) ⊗ₜ[S j] ULift.up (Extension.Cotangent.mk x_j))))
          _ = (ι ℓ)
              (((1 : S∞) ⊗ₜ[S ℓ]
                ULift.up
                  (Extension.Cotangent.map
                    ((Generators.defaultHom Pj Pℓ).toExtensionHom)
                    (Extension.Cotangent.mk x_j)))) := by
                    rw [stageNaiveCotangentBaseChangeTransition_f_one_unit_tensor
                      (ρ := ρ) (σ := σ) hcomm hjℓ (Extension.Cotangent.mk x_j)]
          _ = (ι ℓ) (((1 : S∞) ⊗ₜ[S ℓ] ULift.up (Extension.Cotangent.mk x_ℓ))) := by
                congr 2
                rw [Extension.Cotangent.map_mk]
      have hyℓ :
          (ι k) (((1 : S∞) ⊗ₜ[S k] ULift.up (Extension.Cotangent.mk y_k))) =
            (ι ℓ) (((1 : S∞) ⊗ₜ[S ℓ] ULift.up (Extension.Cotangent.mk y_ℓ))) := by
        calc
          (ι k) (((1 : S∞) ⊗ₜ[S k] ULift.up (Extension.Cotangent.mk y_k))) =
            (ι ℓ)
              ((((stageNaiveCotangentBaseChangeTransition
                (ρ := ρ) (σ := σ) hcomm hkℓ).f 1).hom)
                (((1 : S∞) ⊗ₜ[S k] ULift.up (Extension.Cotangent.mk y_k)))) := by
                  simpa [ι, hkℓ] using
                    (Module.DirectLimit.of_f
                      (R := S∞) (ι := I) (G := G) (f := μ)
                      (i := k) (j := ℓ) (hij := hkℓ)
                      (x := ((1 : S∞) ⊗ₜ[S k] ULift.up (Extension.Cotangent.mk y_k))))
          _ = (ι ℓ)
              (((1 : S∞) ⊗ₜ[S ℓ]
                ULift.up
                  (Extension.Cotangent.map
                    ((Generators.defaultHom Pk Pℓ).toExtensionHom)
                    (Extension.Cotangent.mk y_k)))) := by
                    rw [stageNaiveCotangentBaseChangeTransition_f_one_unit_tensor
                      (ρ := ρ) (σ := σ) hcomm hkℓ (Extension.Cotangent.mk y_k)]
          _ = (ι ℓ) (((1 : S∞) ⊗ₜ[S ℓ] ULift.up (Extension.Cotangent.mk y_ℓ))) := by
                congr 2
                rw [Extension.Cotangent.map_mk]
      refine ⟨ℓ, z_ℓ, ?_⟩
      calc
        (ι i) (x + y) = (ι i) x + (ι i) y := by rfl
        _ = (ι j) (((1 : S∞) ⊗ₜ[S j] ULift.up (Extension.Cotangent.mk x_j))) +
              (ι k) (((1 : S∞) ⊗ₜ[S k] ULift.up (Extension.Cotangent.mk y_k))) := by
                rw [hxj, hyk]
        _ = (ι ℓ) (((1 : S∞) ⊗ₜ[S ℓ] ULift.up (Extension.Cotangent.mk x_ℓ))) +
              (ι ℓ) (((1 : S∞) ⊗ₜ[S ℓ] ULift.up (Extension.Cotangent.mk y_ℓ))) := by
                rw [hxℓ, hyℓ]
        _ = (ι ℓ)
              ((((1 : S∞) ⊗ₜ[S ℓ] ULift.up (Extension.Cotangent.mk x_ℓ)) +
                ((1 : S∞) ⊗ₜ[S ℓ] ULift.up (Extension.Cotangent.mk y_ℓ)))) := by
                  rfl
        _ = (ι ℓ)
              (((1 : S∞) ⊗ₜ[S ℓ]
                ULift.up (Extension.Cotangent.mk x_ℓ + Extension.Cotangent.mk y_ℓ))) := by
                  simp [TensorProduct.tmul_add]
        _ = (ι ℓ) (((1 : S∞) ⊗ₜ[S ℓ] ULift.up (Extension.Cotangent.mk z_ℓ))) := by
              rw [hz_ℓ]

/-- Helper for Lemma 10.134.9: once the source-faithful stage-generator vanishing lemma is
available, injectivity of the degree-`1` comparison is a direct-limit induction. -/
private theorem naiveCotangentDirectLimitComparisonOne_injective
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)]
    [DecidableEq I] :
    Function.Injective
      (naiveCotangentDirectLimitComparisonOne (ρ := ρ) (σ := σ) hcomm).hom := by
  let f := (naiveCotangentDirectLimitComparisonOne (ρ := ρ) (σ := σ) hcomm).hom
  have hker :
      ∀ z : naiveCotangentDirectLimitDegreeOne hcomm, f z = 0 → z = 0 := by
    intro z
    induction z using Module.DirectLimit.induction_on with
    | ih i x =>
        intro hz
        obtain ⟨j, x_j, hxj⟩ :=
          degree_one_directLimit_class_exists_stage_generator
            (ρ := ρ) (σ := σ) hcomm x
        have hzj :
            f (Module.DirectLimit.of S∞ I
                (fun k ↦ (stageNaiveCotangentBaseChange (σ := σ) k).X 1)
                (fun _ _ hij ↦ ((stageNaiveCotangentBaseChangeTransition
                  (ρ := ρ) (σ := σ) hcomm hij).f 1).hom) j
                (((1 : S∞) ⊗ₜ[S j] ULift.up (Extension.Cotangent.mk x_j)))) = 0 := by
          simpa [hxj] using hz
        simpa [hxj] using
          stage_degree_one_generator_class_eq_zero_of_target_zero
            (ρ := ρ) (σ := σ) hcomm j x_j hzj
  intro z w hzw
  have hz_sub : f (z - w) = 0 := by
    simpa [map_sub, hzw]
  have hzero : z - w = 0 := hker (z - w) hz_sub
  exact sub_eq_zero.mp hzero

/-- Helper for Lemma 10.134.9: once degree `1` injectivity is isolated, bijectivity packages the
degree-`1` comparison component as an isomorphism. -/
private theorem naiveCotangentDirectLimitComparisonOne_isIso
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)]
    [DecidableEq I] :
    IsIso (naiveCotangentDirectLimitComparisonOne (ρ := ρ) (σ := σ) hcomm) := by
  let f := naiveCotangentDirectLimitComparisonOne (ρ := ρ) (σ := σ) hcomm
  change IsIso (ModuleCat.ofHom f.hom)
  refine ⟨(LinearEquiv.ofBijective f.hom ?_).toModuleIso⟩
  exact ⟨naiveCotangentDirectLimitComparisonOne_injective (ρ := ρ) (σ := σ) hcomm,
    naiveCotangentDirectLimitComparisonOne_surjective (ρ := ρ) (σ := σ) hcomm⟩

/-- Helper for Lemma 10.134.9: beyond degrees `0` and `1`, the explicit direct-limit model is the
zero object `ModuleCat.of S∞ PUnit`. -/
private noncomputable def naiveCotangentDirectLimitModelXIsoPUnit
    (i : ℕ) :
    (naiveCotangentDirectLimitModel (ρ := ρ) (σ := σ) hcomm).X (i + 2) ≅
      ModuleCat.of S∞ PUnit := by
  let succZero :
      ∀ {X₀ X₁ : ModuleCat S∞} (f : X₁ ⟶ X₀),
        Σ' (X₂ : ModuleCat S∞) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
    fun {_ _} _ ↦ ⟨ModuleCat.of S∞ PUnit, 0, zero_comp⟩
  -- Read the higher terms directly from the `ChainComplex.mk'` presentation of the source model.
  simpa [naiveCotangentDirectLimitModel] using
    (ChainComplex.mk'XIso
      (naiveCotangentDirectLimitDegreeZero (ρ := ρ) (σ := σ) hcomm)
      (naiveCotangentDirectLimitDegreeOne (ρ := ρ) (σ := σ) hcomm)
      (naiveCotangentDirectLimitDifferential (ρ := ρ) (σ := σ) hcomm)
      succZero i)

/-- Helper for Lemma 10.134.9: every higher component of the explicit direct-limit model is
subsingleton. -/
private theorem naiveCotangentDirectLimitModel_subsingleton_of_succ_succ
    (i : ℕ) :
    Subsingleton ((naiveCotangentDirectLimitModel (ρ := ρ) (σ := σ) hcomm).X (i + 2)) := by
  let e := naiveCotangentDirectLimitModelXIsoPUnit (ρ := ρ) (σ := σ) hcomm i
  refine ⟨fun x y ↦ ?_⟩
  have hx : e.hom.hom x = e.hom.hom y := by
    cases e.hom.hom x
    cases e.hom.hom y
    rfl
  apply_fun e.inv.hom at hx
  simpa using hx

/-- Helper for Lemma 10.134.9: beyond degrees `0` and `1`, the target naive cotangent complex is
the zero object `ModuleCat.of S∞ PUnit`. -/
private noncomputable def targetNaiveCotangentXIsoPUnit
    (i : ℕ) :
    (targetNaiveCotangent (ρ := ρ) (σ := σ) hcomm).X (i + 2) ≅
      ModuleCat.of S∞ PUnit := by
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  let succZero :
      ∀ {X₀ X₁ : ModuleCat S∞} (f : X₁ ⟶ X₀),
        Σ' (X₂ : ModuleCat S∞) (d : X₂ ⟶ X₁), d ≫ f = 0 :=
    fun {_ _} _ ↦ ⟨ModuleCat.of S∞ PUnit, 0, zero_comp⟩
  -- This is the standard two-term shape of the canonical owner `NL_{S∞⁄R∞}`.
  simpa [targetNaiveCotangent, Algebra.Extension.naiveCotangentChainComplex] using
    (ChainComplex.mk'XIso
      (ModuleCat.of S∞ Pinf.toExtension.CotangentSpace)
      (ModuleCat.of S∞ (LiftCotangent Pinf.toExtension))
      (ModuleCat.ofHom
        (Pinf.toExtension.cotangentComplex ∘ₗ (liftCotangentEquiv Pinf.toExtension).toLinearMap))
      succZero i)

/-- Helper for Lemma 10.134.9: every higher component of the target naive cotangent complex is
subsingleton. -/
private theorem targetNaiveCotangent_subsingleton_of_succ_succ
    (i : ℕ) :
    Subsingleton ((targetNaiveCotangent (ρ := ρ) (σ := σ) hcomm).X (i + 2)) := by
  let e := targetNaiveCotangentXIsoPUnit (ρ := ρ) (σ := σ) hcomm i
  refine ⟨fun x y ↦ ?_⟩
  have hx : e.hom.hom x = e.hom.hom y := by
    cases e.hom.hom x
    cases e.hom.hom y
    rfl
  apply_fun e.inv.hom at hx
  simpa using hx

-- Proof sketch: once the genuine stagewise cocone is in place, degree `0` and degree `1` are the
-- direct-limit statements for the two terms of the canonical self-presentation, while all higher
-- degrees are zero on both sides.
/-- Lemma 10.134.9: for a directed system of ring maps `R_i → S_i`, the canonical comparison from
the filtered colimit of the stagewise naive cotangent complexes `NL_{S_i⁄R_i}` to the canonical
naive cotangent complex `NL_{S∞⁄R∞}` is an isomorphism. -/
@[stacks 07BQ]
theorem naiveCotangentDirectLimitComparison_isIso
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)] :
    IsIso (naiveCotangentDirectLimitComparison hcomm) := by
  classical
  let _ : DecidableEq I := Classical.decEq I
  let f := naiveCotangentDirectLimitComparison (ρ := ρ) (σ := σ) hcomm
  suffices ∀ n : ℕ, IsIso (f.f n) by
    exact HomologicalComplex.Hom.isIso_of_components f
  intro n
  cases n with
  | zero =>
      simpa [f, naiveCotangentDirectLimitComparison] using
        naiveCotangentDirectLimitComparisonZero_isIso (ρ := ρ) (σ := σ) hcomm
  | succ n =>
      cases n with
      | zero =>
          simpa [f, naiveCotangentDirectLimitComparison] using
            naiveCotangentDirectLimitComparisonOne_isIso (ρ := ρ) (σ := σ) hcomm
      | succ n =>
          -- Away from degrees `0` and `1`, both source and target components are zero objects, so
          -- any component map between them is automatically an isomorphism.
          letI :
              Subsingleton
                ((naiveCotangentDirectLimitModel (ρ := ρ) (σ := σ) hcomm).X (n + 2)) :=
            naiveCotangentDirectLimitModel_subsingleton_of_succ_succ
              (ρ := ρ) (σ := σ) hcomm n
          letI :
              Subsingleton ((targetNaiveCotangent (ρ := ρ) (σ := σ) hcomm).X (n + 2)) :=
            targetNaiveCotangent_subsingleton_of_succ_succ
              (ρ := ρ) (σ := σ) hcomm n
          refine ⟨⟨0, ?_, ?_⟩⟩
          · ext x
            simp
          · ext x
            simp

/-- Helper for Lemma 10.134.9: if every stage self-presentation remains injective after extending
scalars to the target direct limit, then the direct-limit extension has vanishing `H¹`. -/
theorem naiveCotangentDirectLimit_subsingletonH1_of_stagewiseInjective
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)]
    (hstage :
      ∀ i : I,
        let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
        Function.Injective
          ((((ModuleCat.extendScalars
                (Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i)).mapHomologicalComplex
                (ComplexShape.down ℕ)).obj
              (Algebra.Extension.naiveCotangentChainComplex Pi.toExtension)).d 1 0).hom) :
    Subsingleton (Algebra.H1Cotangent R∞ S∞) := by
  classical
  let _ : DecidableEq I := Classical.decEq I
  let G₀ : I → Type u := fun i ↦ (stageNaiveCotangentBaseChange (σ := σ) i).X 0
  let μ₀ : ∀ i j, i ≤ j → G₀ i →ₗ[S∞] G₀ j :=
    fun _ _ hij ↦ ((stageNaiveCotangentBaseChangeTransition
      (ρ := ρ) (σ := σ) hcomm hij).f 0).hom
  let G₁ : I → Type u := fun i ↦ (stageNaiveCotangentBaseChange (σ := σ) i).X 1
  let μ₁ : ∀ i j, i ≤ j → G₁ i →ₗ[S∞] G₁ j :=
    fun _ _ hij ↦ ((stageNaiveCotangentBaseChangeTransition
      (ρ := ρ) (σ := σ) hcomm hij).f 1).hom
  have hker :
      ∀ z : naiveCotangentDirectLimitDegreeOne (ρ := ρ) (σ := σ) hcomm,
        (naiveCotangentDirectLimitDifferential (ρ := ρ) (σ := σ) hcomm).hom z = 0 →
          z = 0 := by
    intro z hz
    induction z using Module.DirectLimit.induction_on with
    | ih i x =>
        have hz' :
            Module.DirectLimit.of S∞ I G₀ μ₀ i
                (((stageNaiveCotangentBaseChange (σ := σ) i).d 1 0).hom x) = 0 := by
          simpa [G₀, μ₀,
            naiveCotangentDirectLimitDifferential_of_stage (ρ := ρ) (σ := σ) hcomm i x] using hz
        obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact hz'
        have hsq :
            (((stageNaiveCotangentBaseChange (σ := σ) j).d 1 0).hom)
                ((((stageNaiveCotangentBaseChangeTransition
                  (ρ := ρ) (σ := σ) hcomm hij).f 1).hom) x) = 0 := by
          have hcomm10 := congrArg
            (fun φ ↦ φ.hom x)
            (stageNaiveCotangentBaseChangeTransition_comm_10
              (ρ := ρ) (σ := σ) hcomm hij)
          simpa [ModuleCat.comp_apply, G₀, μ₀] using hcomm10.trans hj
        have hstagej :
            Function.Injective (((stageNaiveCotangentBaseChange (σ := σ) j).d 1 0).hom) := by
          simpa [stageNaiveCotangentBaseChange] using hstage j
        have hxj :
            (((stageNaiveCotangentBaseChangeTransition
              (ρ := ρ) (σ := σ) hcomm hij).f 1).hom) x = 0 :=
          hstagej hsq
        calc
          Module.DirectLimit.of S∞ I G₁ μ₁ i x =
              Module.DirectLimit.of S∞ I G₁ μ₁ j
                ((((stageNaiveCotangentBaseChangeTransition
                  (ρ := ρ) (σ := σ) hcomm hij).f 1).hom) x) := by
                simpa [G₁, μ₁] using
                  (Module.DirectLimit.of_f
                    (R := S∞) (ι := I) (G := G₁) (f := μ₁) (i := i) (j := j)
                    (hij := hij) (x := x))
          _ = 0 := by simpa [hxj]
  have hsource :
      Function.Injective
        ((naiveCotangentDirectLimitModel (ρ := ρ) (σ := σ) hcomm).d 1 0).hom := by
    intro z w hzw
    have hz_sub :
        ((naiveCotangentDirectLimitModel (ρ := ρ) (σ := σ) hcomm).d 1 0).hom (z - w) = 0 := by
      simpa [naiveCotangentDirectLimitModel, map_sub, hzw]
    have hzero : z - w = 0 := hker (z - w) hz_sub
    exact sub_eq_zero.mp hzero
  let f₀ := (naiveCotangentDirectLimitComparisonZero (ρ := ρ) (σ := σ) hcomm).hom
  let f₁ := (naiveCotangentDirectLimitComparisonOne (ρ := ρ) (σ := σ) hcomm).hom
  let dsrc := (naiveCotangentDirectLimitModel (ρ := ρ) (σ := σ) hcomm).d 1 0 |>.hom
  let dtrg := (targetNaiveCotangent (ρ := ρ) (σ := σ) hcomm).d 1 0 |>.hom
  have hf₀_inj : Function.Injective f₀ :=
    (naiveCotangentDirectLimitComparisonZero_bijective (ρ := ρ) (σ := σ) hcomm).1
  have hf₁_surj : Function.Surjective f₁ :=
    naiveCotangentDirectLimitComparisonOne_surjective (ρ := ρ) (σ := σ) hcomm
  have htarget :
      Function.Injective dtrg := by
    intro x y hxy
    obtain ⟨x', rfl⟩ := hf₁_surj x
    obtain ⟨y', rfl⟩ := hf₁_surj y
    have hx' :
        dtrg (f₁ x') = f₀ (dsrc x') := by
      simpa [dtrg, dsrc, f₀, f₁, ModuleCat.comp_apply] using
        congrArg (fun φ ↦ φ.hom x')
          (naiveCotangentDirectLimitComparison_comm_10
            (ρ := ρ) (σ := σ) hcomm)
    have hy' :
        dtrg (f₁ y') = f₀ (dsrc y') := by
      simpa [dtrg, dsrc, f₀, f₁, ModuleCat.comp_apply] using
        congrArg (fun φ ↦ φ.hom y')
          (naiveCotangentDirectLimitComparison_comm_10
            (ρ := ρ) (σ := σ) hcomm)
    have hsrc_eq : dsrc x' = dsrc y' := by
      apply hf₀_inj
      exact hx'.symm.trans (hxy.trans hy')
    exact hsource hsrc_eq
  let Pinf : Generators R∞ S∞ S∞ := Generators.self R∞ S∞
  letI : Subsingleton Pinf.toExtension.H1Cotangent :=
    (Algebra.Extension.subsingleton_h1Cotangent Pinf.toExtension).2 htarget
  -- Proof comment: once the target self-presentation differential is injective, the owner
  -- `H1Cotangent` vanishes via the self-presentation equivalence.
  exact Pinf.equivH1Cotangent.symm.subsingleton

end
