import StacksProject_2024.Chap24.Definition_24_13_1
import StacksProject_2024.Chap24.Lemma_24_23_2

-- Declarations for this item will be appended below by the statement pipeline.

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

-- Semantic search note: `lean_leansearch` recalled the canonical `QuasiIso` /
-- `HomologicalComplex.quasiIso` owner, so the source's quasi-isomorphism condition is stated on
-- the underlying cochain map of the differential graded module homomorphism.

/-- Lemma 24.23.7: for a ringed site `(\mathcal C, \mathcal O)`, a sheaf of
differential graded algebras `\mathcal A`, and a differential graded `\mathcal A`-module
`\mathcal M`, there is a homomorphism `\mathcal P \to \mathcal M` of differential graded
`\mathcal A`-modules whose underlying cochain map is a quasi-isomorphism and whose source
`\mathcal P` is good. -/
@[stacks 0FSH]
theorem existsGoodQuasiIsoResolution
    (𝒜 : DGAO) (ℳ : DGMod 𝒜) :
    ∃ (P : DGMod 𝒜) (π : P ⟶ ℳ),
      QuasiIso π.toCochainMap ∧ CochainComplex.IsGood (P.toComplex : CpxO) := sorry

end

end SheafOfModules.RingedSite
