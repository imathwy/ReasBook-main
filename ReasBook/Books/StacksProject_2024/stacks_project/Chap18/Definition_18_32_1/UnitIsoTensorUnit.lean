import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import StacksProject_2024.Chap17.SheafOfModulesTensorUnit
import StacksProject_2024.Chap18.Definition_18_23_1

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

local notation "Mod" => ringedSiteModuleCategory J 𝒪

/-- Helper for Definition 18.32.1: the canonical comparison isomorphism from the structure sheaf
module to the ambient tensor unit on a ringed site. -/
noncomputable def unitIsoTensorUnit :
    (unitModule J 𝒪 : Mod) ≅ (𝟙_ Mod) :=
  (asIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf J 𝒪).obj)).counit.app (unitModule J 𝒪))).symm ≪≫
    eqToIso (SheafOfModules.tensorUnit_eq_sheafification_unit_model (R := ringSheaf J 𝒪))

end SheafOfModules.RingedSite
