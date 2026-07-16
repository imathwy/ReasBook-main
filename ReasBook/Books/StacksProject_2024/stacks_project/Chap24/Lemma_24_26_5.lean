import Mathlib
import StacksProject_2024.stacks_project.Chap13.Lemma_13_6_10
import StacksProject_2024.stacks_project.Chap24.Definition_24_26_4
import StacksProject_2024.stacks_project.Chap24.Lemma_24_26_2

open CategoryTheory
open ComplexShape

noncomputable section

universe u v

namespace RingedSite
namespace DifferentialGradedAlgebra

section

variable {X : RingedSite.{u, v}} (𝒜 : DifferentialGradedAlgebra X)

local notation "Ac" =>
  (HomotopyCategory.subcategoryAcyclic 𝒜.moduleCat :
    ObjectProperty (HomotopyCategory 𝒜.moduleCat (up ℤ)))

-- Semantic search note: `lean_leansearch` recalled the canonical derived-category localization
-- owners and the local project analogue `subcategoryAcyclic_kernel_Qh`; the source-faithful
-- Chapter 24 owner is the explicit localization functor `Qh 𝒜`, whose kernel should recover the
-- acyclic subcategory `Ac`.

/-- Lemma 24.26.5: in Definition 24.26.4, the kernel of the localization functor
`Q : K(\textit{Mod}(\mathcal A, d)) \to D(\mathcal A, d)` is the category `\mathrm{Ac}` of
Lemma 24.26.2. -/
theorem subcategoryAcyclic_kernel_Qh :
    Functor.kernel (Qh 𝒜) = Ac := sorry

end

end DifferentialGradedAlgebra
end RingedSite
