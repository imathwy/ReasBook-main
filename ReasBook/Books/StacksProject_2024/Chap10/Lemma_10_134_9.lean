import StacksProject_2024.Chap10.Definition_10_134_1
import StacksProject_2024.Chap10.Lemma_10_131_5

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
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  -- Evaluate the pushed polynomial at stage `j`; this is exactly the later-stage image from
  -- `Ring.DirectLimit.of.zero_exact`.
  have hpush :
      algebraMap Pj.Ring (S j) ((Generators.defaultHom Pi Pj).toAlgHom q_i) =
        algebraMap (S i) (S j) (algebraMap Pi.Ring (S i) q_i) := by
    simpa [Pi, Pj] using
      (Generators.Hom.algebraMap_toAlgHom
        (R := R i) (S := S i) (R' := R i) (S' := S j)
        (P := Pi) (P' := Pj) (f := Generators.defaultHom Pi Pj) q_i)
  rw [hpush]
  exact hj

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
      (ρ := ρ) (σ := σ) q_i hstage_zero
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
  let fiInf : Pi.toExtension.Hom Pinf.toExtension := (Generators.defaultHom Pi Pinf).toExtensionHom
  -- First rewrite the target kernel condition in terms of the descended stage polynomial.
  have himage_zero :
      algebraMap Pinf.Ring S∞ ((Generators.defaultHom Pi Pinf).toAlgHom q_i) = 0 := by
    -- The descended polynomial is exactly the chosen target kernel representative.
    rw [hq_i]
    exact x.2
  have hstage_zero :
      stageTargetMap (σ := σ) i (algebraMap Pi.Ring (S i) q_i) = 0 := by
    -- Reinterpret the target evaluation of the descended polynomial as the stage evaluation
    -- followed by the canonical map to the direct limit.
    simpa [Generators.defaultHom] using himage_zero
  -- Route correction: the source-faithful descent is now packaged in
  -- `selfPresentation_ker_exists_stage_of_directed`. The only remaining blocker in this file is
  -- that the current item context does not provide the coherence instance on `σ` needed to apply
  -- `Ring.DirectLimit.of.zero_exact`.
  -- TODO: supply `[DirectedSystem S fun i j h ↦ σ i j h]`, then invoke
  -- `selfPresentation_ker_exists_stage_of_directed`.
  sorry

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
  let σij : S i →+* S j := σ i j h
  let σjLim : S j →+* S∞ := stageTargetMap (σ := σ) j
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  let fij : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
  let Cᵢ : ChainComplex (ModuleCat (S i)) ℕ :=
    Algebra.Extension.naiveCotangentChainComplex Pi.toExtension
  have hbase :
      (((stageNaiveCotangentTransitionBase (ρ := ρ) (σ := σ) hcomm h).f 0).hom)
          (((1 : S j) ⊗ₜ[S i] y)) =
        Extension.CotangentSpace.map fij y := by
    -- First compute the stage transition on the canonical tensor generator.
    simpa [σij, Pi, Pj, fij, Cᵢ] using
      (stageNaiveCotangentTransitionBase_degree_zero_after_transport
        (ρ := ρ) (σ := σ) hcomm h y)
  -- Then unfold the outer extension to `S∞` and evaluate the associativity isomorphism on `1 ⊗ y`.
  dsimp [stageNaiveCotangentBaseChangeTransition, stageNaiveCotangentBaseChange]
  -- The remaining map is just scalar extension of the stage degree-`0` transition.
  simpa [σij, σjLim, stageTargetMap_comp (σ := σ) h,
    ModuleCat.extendScalarsComp_hom_app_one_tmul] using hbase

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
  let σij : S i →+* S j := σ i j h
  let σjLim : S j →+* S∞ := stageTargetMap (σ := σ) j
  let Pi : Generators (R i) (S i) (S i) := Generators.self (R i) (S i)
  let Pj : Generators (R j) (S j) (S j) := Generators.self (R j) (S j)
  let fij : Pi.toExtension.Hom Pj.toExtension := (Generators.defaultHom Pi Pj).toExtensionHom
  let Cᵢ : ChainComplex (ModuleCat (S i)) ℕ :=
    Algebra.Extension.naiveCotangentChainComplex Pi.toExtension
  have hbase :
      (((stageNaiveCotangentTransitionBase (ρ := ρ) (σ := σ) hcomm h).f 1).hom)
          (((1 : S j) ⊗ₜ[S i] ULift.up x)) =
        ULift.up (Extension.Cotangent.map fij x) := by
    -- First compute the stage transition on the canonical degree-`1` generator.
    simpa [σij, Pi, Pj, fij, Cᵢ] using
      (stageNaiveCotangentBaseChangeTransition_degree_one_generator_after_transport
        (ρ := ρ) (σ := σ) hcomm h x)
  -- Then unfold the outer extension to `S∞` and evaluate the associativity isomorphism on
  -- the unit tensor.
  dsimp [stageNaiveCotangentBaseChangeTransition, stageNaiveCotangentBaseChange]
  -- The remaining map is just scalar extension of the stage degree-`1` transition.
  simpa [σij, σjLim, stageTargetMap_comp (σ := σ) h,
    ModuleCat.extendScalarsComp_hom_app_one_tmul] using hbase

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
  -- Rewrite the inner element using the degree-`1 → 0` chain-map square.
  have hsquare :
      (((stageNaiveCotangentBaseChange (σ := σ) j).d 1 0).hom
          (((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm h).f 1).hom x)) =
        (((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm h).f 0).hom
          (((stageNaiveCotangentBaseChange (σ := σ) i).d 1 0).hom x)) := by
    exact
      LinearMap.congr_fun
        (ModuleCat.hom_ext_iff.mp
          (stageNaiveCotangentBaseChangeTransition_comm_10
            (ρ := ρ) (σ := σ) hcomm h))
        x
  calc
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
          (ρ := ρ) (σ := σ) hcomm hij).f 0 |>.hom) j
        ((((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm h).f 0).hom)
          (((stageNaiveCotangentBaseChange (σ := σ) i).d 1 0).hom x)) := by
            rw [hsquare]
    _ =
      Module.DirectLimit.of S∞ I
        (fun k ↦ (@stageNaiveCotangentBaseChange I _ R S _ _ _ σ k).X 0)
        (fun _ _ hij ↦ (stageNaiveCotangentBaseChangeTransition
          (ρ := ρ) (σ := σ) hcomm hij).f 0 |>.hom) i
        (((stageNaiveCotangentBaseChange (σ := σ) i).d 1 0).hom x) := by
          simpa using
            (Module.DirectLimit.of_f
              (R := S∞)
              (ι := I)
              (G := fun k ↦ (@stageNaiveCotangentBaseChange I _ R S _ _ _ σ k).X 0)
              (f := fun _ _ hij ↦
                (stageNaiveCotangentBaseChangeTransition
                  (ρ := ρ) (σ := σ) hcomm hij).f 0 |>.hom)
              (i := i)
              (j := j)
              (hij := h)
              (x := (((stageNaiveCotangentBaseChange (σ := σ) i).d 1 0).hom x)))

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
  classical
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
  let φ :
      (stageNaiveCotangentBaseChange (σ := σ) i).X 0 ⟶
        (@targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm).X 0 :=
    ((stageNaiveCotangentBaseChangeTransition (ρ := ρ) (σ := σ) hcomm h).f 0) ≫
      ((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm j).f 0)
  let ψ :
      (stageNaiveCotangentBaseChange (σ := σ) i).X 0 ⟶
        (@targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm).X 0 :=
    (stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm i).f 0
  have hφψ : φ = ψ := by
    -- Compare the two cocone morphisms on the scalar-extension generators `1 ⊗ y`.
    apply ModuleCat.ExtendScalars.hom_ext
    intro y
    change
      (((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm j).f 0).hom)
          ((((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm h).f 0).hom) (((1 : S∞) ⊗ₜ[S i] y))) =
        (((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm i).f 0).hom)
          (((1 : S∞) ⊗ₜ[S i] y)) := by
      simp [φ, ψ]
    rw [stageNaiveCotangentBaseChangeTransition_f_zero_unit_tensor
      (ρ := ρ) (σ := σ) hcomm h y]
    rw [stageNaiveCotangentToTarget_degree_zero_after_transport
      (ρ := ρ) (σ := σ) hcomm j (Extension.CotangentSpace.map fij y)]
    rw [stageNaiveCotangentToTarget_degree_zero_after_transport
      (ρ := ρ) (σ := σ) hcomm i y]
    exact selfPresentation_toTarget_cotangentSpace_map_comp_apply
      (ρ := ρ) (σ := σ) hcomm h y
  -- Apply the generator comparison to the chosen source class `x`.
  exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp hφψ) x

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
  classical
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
  let φ :
      (stageNaiveCotangentBaseChange (σ := σ) i).X 1 ⟶
        (@targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm).X 1 :=
    ((stageNaiveCotangentBaseChangeTransition (ρ := ρ) (σ := σ) hcomm h).f 1) ≫
      ((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm j).f 1)
  let ψ :
      (stageNaiveCotangentBaseChange (σ := σ) i).X 1 ⟶
        (@targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm).X 1 :=
    (stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm i).f 1
  have hφψ : φ = ψ := by
    -- Compare the two cocone morphisms on the scalar-extension generators `1 ⊗ ULift.up x`.
    apply ModuleCat.ExtendScalars.hom_ext
    intro y
    rcases y with ⟨y⟩
    change
      (((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm j).f 1).hom)
          ((((stageNaiveCotangentBaseChangeTransition
            (ρ := ρ) (σ := σ) hcomm h).f 1).hom) (((1 : S∞) ⊗ₜ[S i] ULift.up y))) =
        (((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm i).f 1).hom)
          (((1 : S∞) ⊗ₜ[S i] ULift.up y)) := by
      simp [φ, ψ]
    rw [stageNaiveCotangentBaseChangeTransition_f_one_unit_tensor
      (ρ := ρ) (σ := σ) hcomm h y]
    rw [stageNaiveCotangentToTarget_degree_one_generator_after_transport
      (ρ := ρ) (σ := σ) hcomm j (Extension.Cotangent.map fij y)]
    rw [stageNaiveCotangentToTarget_degree_one_generator_after_transport
      (ρ := ρ) (σ := σ) hcomm i y]
    exact selfPresentation_toTarget_cotangent_map_comp_apply
      (ρ := ρ) (σ := σ) hcomm h y
  -- Apply the generator comparison to the chosen source class `x`.
  exact LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp hφψ) x

/-- Helper for Lemma 10.134.9: the explicit degree-`0` direct-limit owner replacing the old
diagrammatic colimit route. -/
private noncomputable abbrev naiveCotangentDirectLimitDegreeZero :
    ModuleCat (S∞) := by
  let _ : DecidableEq I := Classical.decEq I
  let G : I → Type u := fun i ↦ (@stageNaiveCotangentBaseChange I _ R S _ _ _ σ i).X 0
  let μ : ∀ i j, i ≤ j → G i →ₗ[S∞] G j :=
    fun _ _ h ↦ (stageNaiveCotangentBaseChangeTransition (ρ := ρ) (σ := σ) hcomm h).f 0 |>.hom
  exact ModuleCat.of S∞ <| Module.DirectLimit G μ

/-- Helper for Lemma 10.134.9: the explicit degree-`1` direct-limit owner replacing the old
diagrammatic colimit route. -/
private noncomputable abbrev naiveCotangentDirectLimitDegreeOne :
    ModuleCat (S∞) := by
  let _ : DecidableEq I := Classical.decEq I
  let G : I → Type u := fun i ↦ (@stageNaiveCotangentBaseChange I _ R S _ _ _ σ i).X 1
  let μ : ∀ i j, i ≤ j → G i →ₗ[S∞] G j :=
    fun _ _ h ↦ (stageNaiveCotangentBaseChangeTransition (ρ := ρ) (σ := σ) hcomm h).f 1 |>.hom
  exact ModuleCat.of S∞ <| Module.DirectLimit G μ

/-- Helper for Lemma 10.134.9: the source differential on the explicit direct-limit model is the
descended stagewise differential `I_i / I_i² → S_i ⊗ Ω`. -/
private noncomputable def naiveCotangentDirectLimitDifferential :
    naiveCotangentDirectLimitDegreeOne hcomm ⟶
      naiveCotangentDirectLimitDegreeZero hcomm :=
  let _ : DecidableEq I := Classical.decEq I
  let G₀ : I → Type u := fun i ↦ (@stageNaiveCotangentBaseChange I _ R S _ _ _ σ i).X 0
  let G₁ : I → Type u := fun i ↦ (@stageNaiveCotangentBaseChange I _ R S _ _ _ σ i).X 1
  let μ₀ : ∀ i j, i ≤ j → G₀ i →ₗ[S∞] G₀ j :=
    fun _ _ h ↦ (stageNaiveCotangentBaseChangeTransition (ρ := ρ) (σ := σ) hcomm h).f 0 |>.hom
  let μ₁ : ∀ i j, i ≤ j → G₁ i →ₗ[S∞] G₁ j :=
    fun _ _ h ↦ (stageNaiveCotangentBaseChangeTransition (ρ := ρ) (σ := σ) hcomm h).f 1 |>.hom
  let δ : ∀ i, G₁ i →ₗ[S∞] G₀ i :=
    fun i ↦ ((stageNaiveCotangentBaseChange (σ := σ) i).d 1 0).hom
  -- Descend the stagewise differentials through the degreewise direct limits.
  ModuleCat.ofHom <|
    Module.DirectLimit.lift S∞ I G₁ μ₁
      (fun i ↦ (Module.DirectLimit.of S∞ I G₀ μ₀ i).comp (δ i))
      (fun i j h x ↦
        naiveCotangentDirectLimitDifferential_compatible
          (ρ := ρ) (σ := σ) hcomm h x)

/-- The filtered-colimit source complex built from the stagewise canonical naive cotangent
complexes `NL_{S_i⁄R_i}` after extending scalars along `S_i → S∞`. This is the source-facing
`colim NL_{S_i⁄R_i}` object of Tag `07BQ`, expressed in the common ambient category
`ChainComplex (ModuleCat S∞) ℕ`. -/
noncomputable def naiveCotangentDirectLimitModel :
    ChainComplex (ModuleCat S∞) ℕ :=
  -- Route correction: the source is built degreewise as a two-term module direct limit, so the
  -- comparison no longer depends on the old transport-heavy cocone in `ChainComplex`.
  ChainComplex.mk'
    (naiveCotangentDirectLimitDegreeZero hcomm)
    (naiveCotangentDirectLimitDegreeOne hcomm)
    (naiveCotangentDirectLimitDifferential hcomm)
    (fun {_ _} _ ↦ ⟨ModuleCat.of S∞ PUnit, 0, zero_comp⟩)

/-- The canonical comparison from the filtered-colimit source
`colim_i (S∞ ⊗[S_i] NL_{S_i⁄R_i})` to the canonical owner `NL_{S∞⁄R∞}`. -/
noncomputable def naiveCotangentDirectLimitComparison :
    naiveCotangentDirectLimitModel hcomm ⟶
      NL(CommRingCat.ofHom
        (Ring.DirectLimit.map (fun i ↦ algebraMap (R i) (S i)) fun _ _ h ↦ hcomm h)) :=
  let _ : DecidableEq I := Classical.decEq I
  let G₀ : I → Type u := fun i ↦ (@stageNaiveCotangentBaseChange I _ R S _ _ _ σ i).X 0
  let G₁ : I → Type u := fun i ↦ (@stageNaiveCotangentBaseChange I _ R S _ _ _ σ i).X 1
  let μ₀ : ∀ i j, i ≤ j → G₀ i →ₗ[S∞] G₀ j :=
    fun _ _ h ↦ (stageNaiveCotangentBaseChangeTransition (ρ := ρ) (σ := σ) hcomm h).f 0 |>.hom
  let μ₁ : ∀ i j, i ≤ j → G₁ i →ₗ[S∞] G₁ j :=
    fun _ _ h ↦ (stageNaiveCotangentBaseChangeTransition (ρ := ρ) (σ := σ) hcomm h).f 1 |>.hom
  let φ₀ :
      naiveCotangentDirectLimitDegreeZero (ρ := ρ) (σ := σ) hcomm ⟶
        (@targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm).X 0 :=
    ModuleCat.ofHom <|
      Module.DirectLimit.lift S∞ I G₀ μ₀
        (fun i ↦ ((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm i).f 0).hom)
        (fun i j h x ↦
          stageNaiveCotangentDegreeZeroToTarget_compatible
            (ρ := ρ) (σ := σ) hcomm h x)
  let φ₁ :
      naiveCotangentDirectLimitDegreeOne (ρ := ρ) (σ := σ) hcomm ⟶
        (@targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm).X 1 :=
    ModuleCat.ofHom <|
      Module.DirectLimit.lift S∞ I G₁ μ₁
        (fun i ↦ ((stageNaiveCotangentToTarget (ρ := ρ) (σ := σ) hcomm i).f 1).hom)
        (fun i j h x ↦
          stageNaiveCotangentDegreeOneToTarget_compatible
            (ρ := ρ) (σ := σ) hcomm h x)
  -- Check the remaining degree-`1 → 0` square on direct-limit representatives.
  have hcomm10 : φ₁ ≫ (@targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm).d 1 0 =
      naiveCotangentDirectLimitDifferential (ρ := ρ) (σ := σ) hcomm ≫ φ₀ := by
    apply ModuleCat.hom_ext
    apply Module.DirectLimit.hom_ext
    intro i
    ext x
    change
      (((@targetNaiveCotangent I _ R S _ _ _ ρ σ hcomm).d 1 0).hom)
          (φ₁.hom
            (Module.DirectLimit.of S∞ I G₁ μ₁ i x)) =
        φ₀.hom
          (((naiveCotangentDirectLimitDifferential (ρ := ρ) (σ := σ) hcomm).hom)
            (Module.DirectLimit.of S∞ I G₁ μ₁ i x))
    rw [Module.DirectLimit.lift_of]
    rw [Module.DirectLimit.lift_of]
    rw [naiveCotangentDirectLimitDifferential]
    simp only [Module.DirectLimit.lift_of]
    exact
      LinearMap.congr_fun
        (ModuleCat.hom_ext_iff.mp ((stageNaiveCotangentToTarget
          (ρ := ρ) (σ := σ) hcomm i).comm 1 0))
        x
  -- Build the chain map from the degreewise descended comparison components.
  refine ChainComplex.mkHom _ _ φ₀ φ₁ ?_ ?_
  · simpa using hcomm10.symm
  · intro n p
    refine ⟨0, ?_⟩
    simp

-- Route correction: the previous constant-diagram shortcut erased the stagewise source data and
-- could not justify the comparison map. The source must be the genuine diagram of base-changed
-- stage complexes, after which the remaining work is degreewise.
-- Proof sketch: once the genuine stagewise cocone is in place, degree `0` and degree `1` are the
-- direct-limit statements for the two terms of the canonical self-presentation, while all higher
-- degrees are zero on both sides.
/-- Lemma 10.134.9: for a directed system of ring maps `R_i → S_i`, the canonical comparison from
the filtered colimit of the stagewise naive cotangent complexes `NL_{S_i⁄R_i}` to the canonical
naive cotangent complex `NL_{S∞⁄R∞}` is an isomorphism. -/
theorem naiveCotangentDirectLimitComparison_isIso :
    IsIso (naiveCotangentDirectLimitComparison hcomm) := by
  -- TODO: evaluate the comparison degreewise for the genuine stage diagram, reuse the direct-limit
  -- comparison on the degree-`0` cotangent-space term, prove the conormal comparison in degree
  -- `1`, and conclude with `HomologicalComplex.Hom.isIso_of_components`.
  sorry

end
