import Mathlib
import StacksProject_2024.Chap24.Lemma_24_13_2

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

namespace DifferentialGradedModule

local notation "DGAO" => _root_.SheafOfModules.RingedSite.DifferentialGradedAlgebra
  (C := C) (J := J) (𝒪 := 𝒪)

-- Semantic search note: `lean_leansearch` returned the canonical homotopy-category owner
-- `HomotopyCategory`; the chapter-local specialization here is `HomotopyCategory (moduleCategory
-- 𝒜) (up ℤ)`, and the source's direct sums/products are the standard `HasCoproducts` and
-- `HasProducts` structures on that category.

/-- Lemma 24.21.3 (1): for a ringed site `(\mathcal C, \mathcal O)` and a sheaf of differential
graded algebras `\mathcal A` on it, the homotopy category `K(\textit{Mod}(\mathcal A, d))`
has direct sums, formalized as arbitrary coproducts. -/
instance homotopyCategoryHasCoproducts (𝒜 : DGAO) :
    HasCoproducts (HomotopyCategory (moduleCategory 𝒜) (up ℤ)) := sorry

/-- Lemma 24.21.3 (2): for a ringed site `(\mathcal C, \mathcal O)` and a sheaf of differential
graded algebras `\mathcal A` on it, the homotopy category `K(\textit{Mod}(\mathcal A, d))`
has products. -/
instance homotopyCategoryHasProducts (𝒜 : DGAO) :
    HasProducts (HomotopyCategory (moduleCategory 𝒜) (up ℤ)) := sorry

end DifferentialGradedModule

end

end SheafOfModules.RingedSite
