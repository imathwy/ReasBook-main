import StacksProject_2024.stacks_project.Chap24.Lemma_24_23_3
import StacksProject_2024.stacks_project.Chap24.Lemma_24_23_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape

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

local notation "CpxO" => CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ
local notation "DGAO" => @SheafOfModules.RingedSite.DifferentialGradedAlgebra C _ J _ 𝒪 _

-- Semantic search note: `lean_leansearch` surfaced only general sheaf-of-modules colimit
-- infrastructure, so the statement uses the local Chapter 24 owner `CochainComplex.IsGood`,
-- which packages graded flatness, K-flatness, and stability under site-presented pullback.

/-- Lemma 24.31.1: in the inductive resolution situation, if the differential graded
`\mathcal O`-algebra `\mathcal A` is identified with the sequential colimit
`\operatorname{colim}_i \mathcal A_i` of the staged differential graded algebras and each stage
has the good-complex property supplied by the free-stage filtration argument, then
`\mathcal A` is good. Equivalently, after any morphism of ringed topoi, the pullback of
`\mathcal A` is flat as a graded module and K-flat as a complex of modules. -/
@[stacks 0FU1]
theorem resolutionColimitAlgebra_isGood
    (𝒜 : DGAO)
    (Astage : ℕ → DGAO)
    (ι : ∀ i, (Astage i).toComplex ⟶ (Astage (i + 1)).toComplex)
    [HasColimit (Functor.ofSequence ι)]
    (_colimitComparison : 𝒜.toComplex ≅ colimit (Functor.ofSequence ι))
    (_hstage : ∀ i, CochainComplex.IsGood (Astage i).toComplex) :
    CochainComplex.IsGood 𝒜.toComplex := sorry

end

end SheafOfModules.RingedSite
