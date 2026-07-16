import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap24.Definition_24_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

local notation "DGAO" => @DifferentialGradedAlgebra C _ J _ 𝒪 _
local notation "DGModA" => @DifferentialGradedModule.moduleCategory C _ J _ 𝒪 _
namespace DifferentialGradedAlgebra

variable (𝒜 : DGAO)

/- Domain-style sampling for Definition 24.21.2:
- primary domain: the homotopy category of differential graded `\mathcal A`-modules on a ringed
  site;
- sampled canonical declarations:
  `DifferentialGradedModule.moduleCategory`,
  `HomotopyCategory`,
  `CategoryTheory.Quotient`,
  `HomotopyCategory.quotient`;
- source-facing owner: for a fixed sheaf of differential graded algebras `(\mathcal A, d)`, the
  textbook category `K(\textit{Mod}(\mathcal A, d))` is the chapter-local specialization
  `HomotopyCategory (DGModA 𝒜) (up ℤ)`;
- core/canonical owner: this homotopy category is the canonical quotient of cochain complexes in
  `DGModA 𝒜` by the homotopy relation on morphisms;
- bridge/view: the quotient presentation
  `CategoryTheory.Quotient (homotopic (DGModA 𝒜) (up ℤ))`, the quotient functor
  `HomotopyCategory.quotient (DGModA 𝒜) (up ℤ)`, and the standard comparison API
  `HomotopyCategory.eq_of_homotopy` / `HomotopyCategory.homotopyOfEq`.
-/

/- Definition 24.21.2: for a sheaf of differential graded algebras `(\mathcal A, d)` on a ringed
site, the homotopy category `K(\textit{Mod}(\mathcal A, d))` is the standard homotopy category of
the chapter-local differential graded module category `\textit{Mod}(\mathcal A, d)`. -/
recall HomotopyCategory

/- Companion check: this source-facing homotopy category is canonically the quotient of cochain
complexes of differential graded `\mathcal A`-modules by the homotopy relation on morphisms. -/
recall CategoryTheory.Quotient

/- Companion check: the quotient functor sending a cochain complex of differential graded
`\mathcal A`-modules to its homotopy-category class is `HomotopyCategory.quotient`. -/
recall HomotopyCategory.quotient

/- Companion check: a homotopy of morphisms of cochain complexes gives equality of their classes
in `K(\textit{Mod}(\mathcal A, d))`. -/
recall HomotopyCategory.eq_of_homotopy

/- Companion check: equality of morphisms in `K(\textit{Mod}(\mathcal A, d))` comes from a
homotopy between cochain-level representatives. -/
recall HomotopyCategory.homotopyOfEq

end DifferentialGradedAlgebra

end

end SheafOfModules.RingedSite
