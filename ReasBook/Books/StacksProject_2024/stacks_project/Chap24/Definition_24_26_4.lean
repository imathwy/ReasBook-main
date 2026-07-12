import Mathlib
import StacksProject_2024.Chap24.Lemma_24_26_3

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

-- Semantic search note: `lean_leansearch` returned the canonical localization owners
-- `MorphismProperty.Localization` and `HasDerivedCategory`; the source-faithful owner here is the
-- explicit localization of `K(\mathrm{Mod}(\mathcal A, d))` at the Chapter 24 quasi-isomorphisms
-- from `Lemma_24_26_3`.

/-- Definition 24.26.4: let `(\mathcal C, \mathcal O)` be a ringed site, let `(\mathcal A, d)` be
a sheaf of differential graded algebras on it, and let `\mathrm{Qis}` be the class of
quasi-isomorphisms in `K(\textit{Mod}(\mathcal A, d))`. The derived category
`D(\mathcal A, d)` is the localization `\mathrm{Qis}^{-1}K(\textit{Mod}(\mathcal A, d))`. -/
abbrev derivedCategory :=
  MorphismProperty.Localization Qis

/-- Unfolding `derivedCategory` identifies it with the canonical localization of the homotopy
category of differential graded `\mathcal A`-modules at quasi-isomorphisms. -/
theorem derivedCategory_def :
    derivedCategory 𝒜 = MorphismProperty.Localization Qis := sorry

/-- The canonical localization functor from the homotopy category of differential graded
`\mathcal A`-modules to the derived category. -/
abbrev Qh :
    HomotopyCategory (DGModA 𝒜) (up ℤ) ⥤ derivedCategory 𝒜 :=
  MorphismProperty.Q Qis

/-- The source-facing localization functor `Qh` exhibits the derived category of
`(\mathcal A, d)` as the localization of `K(\textit{Mod}(\mathcal A, d))` at quasi-isomorphisms.
-/
theorem Qh_isLocalization :
    (Qh 𝒜).IsLocalization Qis := sorry

end
end DifferentialGradedAlgebra
end SheafOfModules.RingedSite
