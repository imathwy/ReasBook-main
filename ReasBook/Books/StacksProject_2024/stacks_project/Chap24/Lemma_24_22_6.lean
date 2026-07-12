import Mathlib
import StacksProject_2024.Chap24.Lemma_24_13_2

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

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
variable [HasFiniteBiproducts (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]

local notation "DGAO" => DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)

-- Semantic search note: `lean_leansearch` recalled `CategoryTheory.IsGrothendieckAbelian` and
-- `CategoryTheory.IsGrothendieckAbelian.mk`; the source-facing owner/API here was then fixed
-- against the local graded-module Grothendieck instance in `Lemma_24_11_1`, the DG-module
-- abelian/AB5 infrastructure in `Lemma_24_13_2`, and the cone generator setup from
-- `Remark_24_22_5`.

namespace DifferentialGradedModule

/-- Lemma 24.22.6: let `(\mathcal C, \mathcal O)` be a ringed site. Let `(\mathcal A, \mathrm d)`
be a differential graded `\mathcal O`-algebra. The category `\textit{Mod}(\mathcal A, \mathrm d)`
is a Grothendieck abelian category. -/
instance moduleCategoryIsGrothendieckAbelian (𝒜 : DGAO) :
    IsGrothendieckAbelian.{max u v} (moduleCategory 𝒜) := sorry

end DifferentialGradedModule

end

end SheafOfModules.RingedSite
