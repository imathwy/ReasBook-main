import StacksProject_2024.Chap24.Definition_24_13_1
import StacksProject_2024.Chap24.Lemma_24_23_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
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

-- Semantic search note: `lean_leansearch` identified `HomologicalComplex.cyclesMap` as the
-- canonical map on kernels of differentials, so the source condition
-- `Ker(d_P) -> Ker(d_M)` is stated as epimorphy of this map in every degree.

/-- A morphism of differential graded modules whose source is good and which is surjective
both degreewise and on cycles in every degree. -/
structure GoodSurjectionCyclesSurjective
    {𝒜 : DGAO} {ℳ P : DGMod 𝒜} (π : P ⟶ ℳ) : Prop where
  degreeEpi : ∀ n : ℤ, Epi (π.toCochainMap.f n)
  cyclesEpi : ∀ n : ℤ, Epi (HomologicalComplex.cyclesMap π.toCochainMap n)
  sourceGood : CochainComplex.IsGood (P.toComplex : CpxO)

/-- Lemma 24.23.4: for a ringed site `(\mathcal C, \mathcal O)`, a sheaf of differential graded
algebras `\mathcal A`, and a differential graded `\mathcal A`-module `\mathcal M`, there is a
homomorphism `\mathcal P \to \mathcal M` of differential graded `\mathcal A`-modules that is
surjective in every degree, induces surjections on the kernels of the differentials in every
degree, and has good source. -/
@[stacks 0FSE]
theorem existsGoodSurjectionCyclesSurjective
    (𝒜 : DGAO) (ℳ : DGMod 𝒜) :
    ∃ (P : DGMod 𝒜) (π : P ⟶ ℳ), GoodSurjectionCyclesSurjective π := sorry

end

end SheafOfModules.RingedSite
