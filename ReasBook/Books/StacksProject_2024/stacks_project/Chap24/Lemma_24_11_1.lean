import Mathlib
import StacksProject_2024.stacks_project.Chap18.Lemma_18_19_2
import StacksProject_2024.stacks_project.Chap19.Definition_19_10_1
import StacksProject_2024.stacks_project.Chap24.Lemma_24_4_2

open CategoryTheory
open CategoryTheory.Limits
open scoped SheafOfModules.RingedSite.GradedModuleSheaf

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

-- Semantic search note: `lean_leansearch` located `CategoryTheory.HasSeparator`,
-- `CategoryTheory.HasSeparator.mk`, and `CategoryTheory.IsGrothendieckAbelian.hasSeparator`; the
-- source-facing owner here remains `Mod(𝒜)` from `Lemma 24.4.2`, with a separator
-- statement as the companion bridge to Definition `19.10.1`.

/-- The category of graded `\mathcal A`-modules on a ringed site is abelian. -/
instance gradedModuleSheaf_abelian (𝒜 : GradedAlgebraSheaf 𝒪) :
    Abelian (Mod(𝒜)) := sorry

end

section

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- A separator for the category of graded `\mathcal A`-modules on the ringed site
`(\mathcal C, \mathcal O)`. -/
lemma gradedModuleSheaf_hasSeparator (𝒜 : GradedAlgebraSheaf 𝒪) :
    HasSeparator (Mod(𝒜)) := sorry

/-- Lemma 24.11.1: let `(\mathcal C, \mathcal O)` be a ringed site and let `\mathcal A` be a
graded `\mathcal O`-algebra. The category `\textit{Mod}(\mathcal A)` of graded
`\mathcal A`-modules is a Grothendieck abelian category. -/
instance gradedModuleSheaf_isGrothendieckAbelian (𝒜 : GradedAlgebraSheaf 𝒪) :
    IsGrothendieckAbelian.{max u v} (Mod(𝒜)) := sorry

end

end SheafOfModules.RingedSite
