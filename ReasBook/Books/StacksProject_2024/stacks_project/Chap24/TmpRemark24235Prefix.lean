import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.GradedObject
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategoryBasic

open CategoryTheory CochainComplex

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type (max u v))]

private abbrev constantIntegerSheaf :
    Sheaf J (Type (max u v)) :=
  (constantSheaf J (Type (max u v))).obj (ULift.{max u v} ℤ)

abbrev GradedSheafOfSets :=
  Over (constantIntegerSheaf (C := C) (J := J))

abbrev GradedSheafOfSets.toSheaf
    (𝒮 : GradedSheafOfSets (C := C) (J := J)) :
    Sheaf J (Type (max u v)) :=
  𝒮.left

abbrev GradedSheafOfSets.deg
    (𝒮 : GradedSheafOfSets (C := C) (J := J)) :
    𝒮.toSheaf ⟶ constantIntegerSheaf (C := C) (J := J) :=
  𝒮.hom

instance gradedSheafOfSetsCoeOut :
    CoeOut (GradedSheafOfSets (C := C) (J := J)) (Sheaf J (Type (max u v))) where
  coe 𝒮 := 𝒮.toSheaf

instance gradedSheafOfSetsCoeFun :
    CoeFun (GradedSheafOfSets (C := C) (J := J)) fun _ ↦ Cᵒᵖ → Type (max u v) where
  coe 𝒮 := fun U ↦ 𝒮.toSheaf.obj.obj U

@[simp] theorem GradedSheafOfSets.toSheaf_eq_left
    (𝒮 : GradedSheafOfSets (C := C) (J := J)) :
    𝒮.left = 𝒮.toSheaf :=
  rfl

@[simp] theorem GradedSheafOfSets.deg_eq_hom
    (𝒮 : GradedSheafOfSets (C := C) (J := J)) :
    𝒮.hom = 𝒮.deg :=
  rfl

abbrev GradedSheafOfSets.sectionDegree
    (𝒮 : GradedSheafOfSets (C := C) (J := J)) (U : Cᵒᵖ) (s : 𝒮 U) : ℤ :=
  (𝒮.deg.app U s).down

@[simp] theorem GradedSheafOfSets.coe_apply
    (𝒮 : GradedSheafOfSets (C := C) (J := J)) (U : Cᵒᵖ) :
    𝒮 U = 𝒮.toSheaf.obj.obj U :=
  rfl

abbrev GradedSheafOfSets.degreeFiber
    (𝒮 : GradedSheafOfSets (C := C) (J := J)) (U : Cᵒᵖ) (n : ℤ) : Type (max u v) :=
  { s : 𝒮 U // 𝒮.sectionDegree U s = n }

namespace GradedSheafOfSets

abbrev map
    (𝒮 : GradedSheafOfSets (C := C) (J := J)) {U V : Cᵒᵖ} (f : U ⟶ V) :
    𝒮 U → 𝒮 V :=
  𝒮.toSheaf.obj.map f

theorem sectionDegree_map
    (𝒮 : GradedSheafOfSets (C := C) (J := J)) {U V : Cᵒᵖ} (f : U ⟶ V) (s : 𝒮 U) :
    𝒮.sectionDegree V (𝒮.map f s) = 𝒮.sectionDegree U s := by
  simpa [GradedSheafOfSets.sectionDegree] using
    congrArg ULift.down (congrFun (𝒮.deg.naturality f) s)

abbrev degreeFiberMap
    (𝒮 : GradedSheafOfSets (C := C) (J := J)) {U V : Cᵒᵖ} (f : U ⟶ V) (n : ℤ) :
    𝒮.degreeFiber U n → 𝒮.degreeFiber V n :=
  fun s ↦
    ⟨𝒮.map f s.1, by simpa [s.2] using 𝒮.sectionDegree_map f s.1⟩

end GradedSheafOfSets

end

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J (Type (max u v))]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod(" 𝒪 ")" => ringedSiteModuleCategory J 𝒪
local notation "GMod(" 𝒪 ")" => GradedObject ℤ (Mod(𝒪))
set_option quotPrecheck false in
local postfix:max "^#" => fun ℱ ↦
  Functor.obj
    (PresheafOfModules.sheafification (𝟙 (ringSheaf J 𝒪).obj))
    ℱ

abbrev gradedSetFreeSectionModule
    (𝒮 : GradedSheafOfSets (C := C) (J := J)) (U : Cᵒᵖ) (n : ℤ) :
    ModuleCat ((ringSheaf J 𝒪).obj.obj U) :=
  ModuleCat.of ((ringSheaf J 𝒪).obj.obj U)
    (𝒮.degreeFiber U n →₀ (ringSheaf J 𝒪).obj.obj U)

abbrev GradedObject.toZeroDifferentialCochainComplex
    (G : GMod(𝒪)) :
    CochainComplex (Mod(𝒪)) ℤ :=
  of
    (fun n ↦ G n)
    (fun _ ↦ 0)
    (fun _ ↦ by simp)

@[simp] theorem GradedObject.toZeroDifferentialCochainComplex_X
    (G : GMod(𝒪)) (n : ℤ) :
    (GradedObject.toZeroDifferentialCochainComplex G).X n = G n :=
  rfl

end

end SheafOfModules.RingedSite
