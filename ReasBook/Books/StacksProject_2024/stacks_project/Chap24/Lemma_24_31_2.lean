import StacksProject_2024.Chap24.Definition_24_12_1
import StacksProject_2024.Chap24.Lemma_24_31_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

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

local notation "CpxO" => CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ
local notation "DGAO" => @SheafOfModules.RingedSite.DifferentialGradedAlgebra C _ J _ 𝒪 _

-- Semantic search note: `lean_leansearch` recalled the canonical `QuasiIso` owner for
-- cochain maps; local Chapter 24 precedent supplies `DifferentialGradedAlgebra.Hom` and
-- `CochainComplex.IsGood`, which packages graded flatness, K-flatness, and pullback stability.

/-- Lemma 24.31.2: for a ringed site `(\mathcal C, \mathcal O)` and a differential graded
`\mathcal O`-algebra `\mathcal B`, there is a quasi-isomorphism of differential graded
`\mathcal O`-algebras `\mathcal A \to \mathcal B` such that the underlying complex of
`\mathcal A` is graded flat and K-flat, and remains so after pullback by any morphism of
ringed topoi. In the local Chapter 24 API this final package is `CochainComplex.IsGood`. -/
@[stacks 0FU2]
theorem existsGoodQuasiIsoAlgebraResolution
    (𝒝 : DGAO) :
    ∃ (𝒜 : DGAO) (φ : DifferentialGradedAlgebra.Hom 𝒜 𝒝),
      QuasiIso φ.hom ∧ CochainComplex.IsGood (𝒜.toComplex : CpxO) := sorry

end

end SheafOfModules.RingedSite
