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

/-- The constant sheaf of integers on the site `(\mathcal C, J)`. -/
private abbrev constantIntegerSheaf :
    Sheaf J (Type (max u v)) :=
  (constantSheaf J (Type (max u v))).obj (ULift.{max u v} ℤ)

/-- Remark 24.23.5 (1): a sheaf of graded sets on `\mathcal C` is a sheaf of sets endowed with a
degree map, recorded here as a morphism to the constant integer sheaf. -/
abbrev GradedSheafOfSets :=
  Over (constantIntegerSheaf (C := C) (J := J))

/-- The underlying sheaf of sets of a graded sheaf of sets. -/
abbrev GradedSheafOfSets.toSheaf
    (𝒮 : GradedSheafOfSets (C := C) (J := J)) :
    Sheaf J (Type (max u v)) :=
  𝒮.left

/-- The sectionwise grading map of a graded sheaf of sets. -/
abbrev GradedSheafOfSets.deg
    (𝒮 : GradedSheafOfSets (C := C) (J := J)) :
    𝒮.toSheaf ⟶ constantIntegerSheaf (C := C) (J := J) :=
  𝒮.hom

/-- A graded sheaf of sets is canonically viewed as its underlying sheaf of sets. -/
instance gradedSheafOfSetsCoeOut :
    CoeOut (GradedSheafOfSets (C := C) (J := J)) (Sheaf J (Type (max u v))) where
  coe 𝒮 := 𝒮.toSheaf

/-- A graded sheaf of sets can be evaluated on an object of the site. -/
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

/-- The degree of a local section of a graded sheaf of sets. -/
abbrev GradedSheafOfSets.sectionDegree
    (𝒮 : GradedSheafOfSets (C := C) (J := J)) (U : Cᵒᵖ) (s : 𝒮 U) : ℤ :=
  ULift.down ((𝒮.deg.hom.app U) s)

/-- Coercion of a graded sheaf of sets recovers its sections over `U`. -/
@[simp] theorem GradedSheafOfSets.coe_apply
    (𝒮 : GradedSheafOfSets (C := C) (J := J)) (U : Cᵒᵖ) :
    𝒮 U = 𝒮.toSheaf.obj.obj U :=
  rfl

/-- The degree-`n` local sections of a graded sheaf of sets over `U`. -/
abbrev GradedSheafOfSets.degreeFiber
    (𝒮 : GradedSheafOfSets (C := C) (J := J)) (U : Cᵒᵖ) (n : ℤ) : Type (max u v) :=
  { s : 𝒮 U // 𝒮.sectionDegree U s = n }

namespace GradedSheafOfSets

/-- Restriction of local sections in a graded sheaf of sets. -/
abbrev map
    (𝒮 : GradedSheafOfSets (C := C) (J := J)) {U V : Cᵒᵖ} (f : U ⟶ V) :
    𝒮 U → 𝒮 V :=
  𝒮.toSheaf.obj.map f

/-- Restriction preserves the degree of local sections. -/
theorem sectionDegree_map
    (𝒮 : GradedSheafOfSets (C := C) (J := J)) {U V : Cᵒᵖ} (f : U ⟶ V) (s : 𝒮 U) :
    𝒮.sectionDegree V (𝒮.map f s) = 𝒮.sectionDegree U s := by
  simpa [GradedSheafOfSets.sectionDegree] using
    congrArg ULift.down (ConcreteCategory.congr_hom (𝒮.deg.hom.naturality f) s)

/-- Restriction preserves the degree-`n` fiber of a graded sheaf of sets. -/
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

/-- The free `\mathcal O(U)`-module on the degree-`n` sections of `\mathcal S(U)`. This is the
sectionwise module appearing in the source formula for the `n`th graded part of
`\mathcal O[\mathcal S]`. -/
abbrev gradedSetFreeSectionModule
    (𝒮 : GradedSheafOfSets (C := C) (J := J)) (U : Cᵒᵖ) (n : ℤ) :
    ModuleCat ((ringSheaf J 𝒪).obj.obj U) :=
  ModuleCat.of ((ringSheaf J 𝒪).obj.obj U)
    (𝒮.degreeFiber U n →₀ (ringSheaf J 𝒪).obj.obj U)

/-
Source/core/bridge triage for Remark 24.23.5:
- `source-facing`: the graded pieces of `\mathcal O[\mathcal S]`;
- `core/canonical`: `CochainComplex.of`;
- `bridge/view`: the zero-differential complex attached to a graded `\mathcal O`-module.

No earlier Chapter 24 owner turns an arbitrary `ℤ`-graded object in `Mod(𝒪)` into the
corresponding zero-differential cochain complex, so the public bridge here stays a thin
abbreviation over the canonical constructor `CochainComplex.of`.
-/
#check CochainComplex.of

/-- The canonical zero-differential cochain-complex bridge attached to a graded
`\mathcal O`-module. -/
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

@[simp] theorem GradedObject.toZeroDifferentialCochainComplex_d
    (G : GMod(𝒪)) (n : ℤ) :
    (GradedObject.toZeroDifferentialCochainComplex G).d n (n + 1) = 0 := by
  simpa only [GradedObject.toZeroDifferentialCochainComplex] using
    (CochainComplex.of_d
      (fun i ↦ G i)
      (fun i ↦ (0 : G i ⟶ G (i + 1)))
      (fun _ ↦ by simp)
      n)

/-- Remark 24.23.5 (2): for a graded sheaf of sets `\mathcal S` on a ringed site
`(\mathcal C, \mathcal O)`, `\mathcal O[\mathcal S]` is a graded `\mathcal O`-module whose
`n`th graded part is the sheafification `(presheafPiece n)^#` of the presheaf
`U ↦ ⨁_{s ∈ \mathcal S(U),\ \deg(s)=n} s \cdot \mathcal O(U)`. The same data also carries a
canonical zero-differential cochain-complex lift via the companion bridge
`FreeGradedModuleOn.toZeroDifferentialCochainComplex`. -/
structure FreeGradedModuleOn
    (𝒮 : GradedSheafOfSets (C := C) (J := J)) where
  /-- The underlying graded sheaf of `\mathcal O`-modules. -/
  toGradedModule : GMod(𝒪)
  /-- The presheaf of `\mathcal O`-modules whose sheafification gives the `n`th graded piece. -/
  presheafPiece : ℤ → PresheafOfModules (ringSheaf J 𝒪).obj
  /-- Objectwise, the `n`th presheaf piece is the free `\mathcal O(U)`-module on the degree-`n`
  local sections of `\mathcal S(U)`. -/
  presheafPieceObjIso :
    ∀ n : ℤ, ∀ U : Cᵒᵖ,
      (presheafPiece n).obj U ≅ gradedSetFreeSectionModule 𝒮 U n
  /-- The `n`th graded piece is the sheafification of the corresponding presheaf piece, using the
  canonical Chapter 18 notation `^#`. -/
  pieceIso :
    ∀ n : ℤ,
      toGradedModule n ≅ (presheafPiece n)^#

/-- A free graded module on a graded sheaf of sets can be used through its underlying graded
`\mathcal O`-module. -/
instance freeGradedModuleOnCoeOut
    (𝒮 : GradedSheafOfSets (C := C) (J := J)) :
    CoeOut (FreeGradedModuleOn (C := C) (J := J) (𝒪 := 𝒪) 𝒮) (GMod(𝒪)) where
  coe M := M.toGradedModule

/-- A free graded module on a graded sheaf of sets can be evaluated at each integer degree. -/
instance freeGradedModuleOnCoeFun
    (𝒮 : GradedSheafOfSets (C := C) (J := J)) :
    CoeFun (FreeGradedModuleOn (C := C) (J := J) (𝒪 := 𝒪) 𝒮) fun _ ↦ ℤ → Mod(𝒪) where
  coe M := M.toGradedModule

/-- Coercion of a free graded module on `\mathcal S` recovers its degree-`n` graded piece. -/
@[simp] theorem FreeGradedModuleOn.coe_apply
    {𝒮 : GradedSheafOfSets (C := C) (J := J)}
    (M : FreeGradedModuleOn (C := C) (J := J) (𝒪 := 𝒪) 𝒮) (n : ℤ) :
    M n = M.toGradedModule n :=
  rfl

namespace FreeGradedModuleOn

/-- The canonical zero-differential cochain-complex bridge attached to a free graded
`\mathcal O`-module on `\mathcal S`. -/
abbrev toZeroDifferentialCochainComplex
    {𝒮 : GradedSheafOfSets (C := C) (J := J)}
    (M : FreeGradedModuleOn (C := C) (J := J) (𝒪 := 𝒪) 𝒮) :
    CochainComplex (Mod(𝒪)) ℤ :=
  GradedObject.toZeroDifferentialCochainComplex M.toGradedModule

@[simp] theorem toZeroDifferentialCochainComplex_X
    {𝒮 : GradedSheafOfSets (C := C) (J := J)}
    (M : FreeGradedModuleOn (C := C) (J := J) (𝒪 := 𝒪) 𝒮) (n : ℤ) :
    M.toZeroDifferentialCochainComplex.X n = M n := by
  simp [toZeroDifferentialCochainComplex]

@[simp] theorem toZeroDifferentialCochainComplex_d
    {𝒮 : GradedSheafOfSets (C := C) (J := J)}
    (M : FreeGradedModuleOn (C := C) (J := J) (𝒪 := 𝒪) 𝒮) (n : ℤ) :
    M.toZeroDifferentialCochainComplex.d n (n + 1) = 0 := by
  simpa [toZeroDifferentialCochainComplex] using
    GradedObject.toZeroDifferentialCochainComplex_d M.toGradedModule n

end FreeGradedModuleOn

end

end SheafOfModules.RingedSite
