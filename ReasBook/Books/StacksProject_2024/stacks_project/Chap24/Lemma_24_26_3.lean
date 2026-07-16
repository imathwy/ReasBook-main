import Mathlib
import StacksProject_2024.stacks_project.Chap04.Definition_4_27_20
import StacksProject_2024.stacks_project.Chap24.Lemma_24_25_12

open CategoryTheory
open ComplexShape

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
local notation "DGAO" => DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)
local notation "DGModA" =>
  _root_.SheafOfModules.RingedSite.DifferentialGradedModule.moduleCategory
    (C := C) (J := J) (𝒪 := 𝒪)
local notation "Qis" => HomotopyCategory.quasiIso (DGModA 𝒜) (up ℤ)

namespace DifferentialGradedAlgebra

-- Semantic search note: `lean_leansearch` returned `HomotopyCategory.quasiIso` and
-- `HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W`; the source-facing specialization below
-- keeps the textbook `Qis` owner while aligning it with the canonical triangulated-localization
-- API.

/-- Lemma 24.26.3 (1): let `(\mathcal C, \mathcal O)` be a ringed site and let
`(\mathcal A, d)` be a sheaf of differential graded algebras on it. The subclass `\mathrm{Qis}`
of arrows of `K(\textit{Mod}(\mathcal A, d))` consisting of quasi-isomorphisms is a saturated
multiplicative system. -/
theorem quasiIso_isSaturatedMultiplicativeSystem :
    CategoryTheory.MorphismProperty.IsSaturatedMultiplicativeSystem Qis := sorry

/-- Lemma 24.26.3 (2): let `(\mathcal C, \mathcal O)` be a ringed site and let
`(\mathcal A, d)` be a sheaf of differential graded algebras on it. The quasi-isomorphism class
`\mathrm{Qis}` in `K(\textit{Mod}(\mathcal A, d))` is compatible with the triangulated structure
on the homotopy category. -/
theorem quasiIso_isCompatibleWithTriangulation :
    CategoryTheory.MorphismProperty.IsCompatibleWithTriangulation Qis := sorry

end
end DifferentialGradedAlgebra
end SheafOfModules.RingedSite
