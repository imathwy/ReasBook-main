import Mathlib
import StacksProject_2024.Chap13.Lemma_13_6_3
import StacksProject_2024.Chap24.Definition_24_21_2
import StacksProject_2024.Chap24.Lemma_24_25_12

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

namespace DifferentialGradedAlgebra

-- Semantic search note: `lean_leansearch` returned the canonical owner
-- `HomotopyCategory.subcategoryAcyclic`; the specialization here was then verified against the
-- Chapter 24 homotopy-category recall `Definition_24_21_2.lean` and the generic acyclic-owner
-- recall `Chap13/Lemma_13_11_2.lean`.

/- Lemma 24.26.2
Recall: with the Chapter 24 identification
`K(\mathrm{Mod}(\mathcal A, d)) = HomotopyCategory (Mod(\mathcal A, d)) (up ℤ)`, the full
subcategory `\mathrm{Ac}` of acyclic differential graded `\mathcal A`-modules is the canonical
object property `HomotopyCategory.subcategoryAcyclic 𝒜.moduleCat`. The source assertions that
`\mathrm{Ac}` is strictly full, saturated, and triangulated are exactly the standard owner
instances below. -/
#check
  (show ObjectProperty.IsClosedUnderIsomorphisms
      (HomotopyCategory.subcategoryAcyclic (DGModA 𝒜) :
        ObjectProperty (HomotopyCategory (DGModA 𝒜) (up ℤ))) from
    inferInstance)

#check
  (show ObjectProperty.IsStableUnderRetracts
      (HomotopyCategory.subcategoryAcyclic (DGModA 𝒜) :
        ObjectProperty (HomotopyCategory (DGModA 𝒜) (up ℤ))) from by
    dsimp [HomotopyCategory.subcategoryAcyclic]
    infer_instance)

#check
  (show ObjectProperty.IsTriangulated
      (HomotopyCategory.subcategoryAcyclic (DGModA 𝒜) :
        ObjectProperty (HomotopyCategory (DGModA 𝒜) (up ℤ))) from
    inferInstance)

end

end DifferentialGradedAlgebra
end SheafOfModules.RingedSite
