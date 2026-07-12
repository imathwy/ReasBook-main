import Mathlib
import StacksProject_2024.Chap24.Lemma_24_13_2

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

local notation "DGAO" => DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)

-- Semantic search note: `tool_search` did not expose a `lean_leansearch` tool in this runner, so
-- the owner/API choice below was checked against the local differential graded forgetful functor
-- from `Lemma_24_13_2`, together with the repo's standard `IsRightAdjoint` / `leftAdjoint` /
-- `Adjunction.ofIsRightAdjoint` pattern used in files such as `Remark_18_41_2` and
-- `Lemma_24_29_4`.

namespace DifferentialGradedModule

/-- Lemma 24.24.1: let `(\mathcal C, \mathcal O)` be a ringed site and let `\mathcal A` be a
sheaf of differential graded algebras on it. The forgetful functor
`F : \textit{Mod}(\mathcal A, \mathrm d) \to \textit{Mod}(\mathcal A)` has a left adjoint,
formalized canonically by the assertion that `forgetToGraded 𝒜` is a right adjoint. The induced
left adjoint is then `Functor.leftAdjoint (forgetToGraded 𝒜)`. -/
instance forgetToGradedIsRightAdjoint (𝒜 : DGAO) :
    (forgetToGraded 𝒜).IsRightAdjoint := sorry

end DifferentialGradedModule

end

end SheafOfModules.RingedSite
