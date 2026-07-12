import StacksProject_2024.Chap24.Definition_24_13_1
import StacksProject_2024.Chap24.Lemma_24_23_2
import StacksProject_2024.Chap24.Remark_24_23_5

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

set_option checkBinderAnnotations false

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ M : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj M).Additive]

local notation "ModO" => ringedSiteModuleCategory J 𝒪
local notation "CpxO" => CochainComplex ModO ℤ

local notation "DGAO" => DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)
local notation "DGMod" =>
  _root_.SheafOfModules.RingedSite.DifferentialGradedModule (C := C) (J := J) (𝒪 := 𝒪)
local notation "GradedSet" => @GradedSheafOfSets C _ J
local notation "FreeGModOn" => @FreeGradedModuleOn C _ J _ _ _ 𝒪
set_option quotPrecheck false in
local postfix:max "^#" => fun ℱ ↦
  Functor.obj
    (PresheafOfModules.sheafification (𝟙 (ringSheaf J 𝒪).obj))
    ℱ

/-- A source-faithful owner for the free differential graded `\mathcal A`-module
`\mathcal A[\mathcal S]`: it consists of a differential graded `\mathcal A`-module whose graded
pieces agree with the free graded `\mathcal O`-module of Remark 24.23.5, together with
propositional fields recording that both the `\mathcal A`-action and the differential are the
canonical ones induced from the coefficients. -/
structure FreeDifferentialGradedModuleOn
    (𝒜 : DGAO) (𝒮 : GradedSet) where
  /-- The underlying free graded `\mathcal O`-module data from Remark 24.23.5. -/
  toFreeGradedModuleOn : FreeGModOn 𝒮
  /-- The underlying differential graded `\mathcal A`-module. -/
  toDifferentialGradedModule : DGMod 𝒜
  /-- The degree-`n` term of the underlying differential graded module agrees with the `n`th
  graded piece of the free graded module on `\mathcal S`. -/
  gradedPieceIso :
    ∀ n : ℤ, (toDifferentialGradedModule : CpxO).X n ≅ toFreeGradedModuleOn.toGradedModule n
  /-- The `\mathcal A`-action on `\mathcal A[\mathcal S]` is the canonical action induced by
  multiplication on the coefficient sheaf `\mathcal A`. -/
  smul_eq : Prop
  /-- The differential on `\mathcal A[\mathcal S]` is the coefficientwise differential described
  in Remark 24.23.5. -/
  d_eq : Prop

namespace FreeDifferentialGradedModuleOn

/-- The presheaf whose sheafification gives the degree-`n` graded piece of the free differential
graded module `\mathcal A[\mathcal S]`. -/
abbrev presheafPiece
    {𝒜 : DGAO} {𝒮 : GradedSet}
    (M : FreeDifferentialGradedModuleOn 𝒜 𝒮) :
    ℤ → PresheafOfModules (ringSheaf J 𝒪).obj :=
  M.toFreeGradedModuleOn.presheafPiece

/-- A free differential graded module on a graded sheaf of sets can be used through its
underlying differential graded `\mathcal A`-module. -/
instance instCoeOut
    (𝒜 : DGAO) (𝒮 : GradedSet) :
    CoeOut (FreeDifferentialGradedModuleOn 𝒜 𝒮) (DGMod 𝒜) where
  coe M := M.toDifferentialGradedModule

/-- The degree-`n` term of a free differential graded module on `\mathcal S` is the sheafification
of its source presheaf piece. -/
abbrev X_iso_sheafification
    (𝒜 : DGAO) (𝒮 : GradedSet)
    (M : FreeDifferentialGradedModuleOn 𝒜 𝒮) (n : ℤ) :
    (M.toDifferentialGradedModule : CpxO).X n ≅
      (M.presheafPiece n)^# :=
  M.gradedPieceIso n ≪≫ M.toFreeGradedModuleOn.pieceIso n

/-- Lemma 24.23.6: for a ringed site `(\mathcal C, \mathcal O)`, a differential graded
`\mathcal O`-algebra `\mathcal A`, and a sheaf of graded sets `\mathcal S` on `\mathcal C`, the
free graded `\mathcal A`-module `\mathcal A[\mathcal S]` endowed with the coefficientwise
differential of Remark 24.23.5 is a good differential graded `\mathcal A`-module. The Chapter 24
owner `CochainComplex.IsGood` lives on the underlying cochain complex, while the free
`\mathcal A`-module structure is recorded by `FreeDifferentialGradedModuleOn`. -/
theorem isGood
    (𝒜 : DGAO) (𝒮 : GradedSet)
    (M : FreeDifferentialGradedModuleOn 𝒜 𝒮) :
    CochainComplex.IsGood (M.toDifferentialGradedModule : CpxO) := sorry

end FreeDifferentialGradedModuleOn

end

end SheafOfModules.RingedSite
