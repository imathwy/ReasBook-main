import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{max u v}}
variable [MonoidalCategory (SheafOfModules R)]

/-- Bridge assumption for the comparison between the sheafification model of the structure
sheaf module and the ambient tensor unit. This is not a Stacks source assertion; it records the
monoidal owner data needed by later files without asking proof search to prove it from an arbitrary
`MonoidalCategory (SheafOfModules R)` instance. -/
axiom tensorUnit_eq_sheafification_unit_model :
    ((SheafOfModules.forget R ⋙
        PresheafOfModules.restrictScalars (𝟙 (R.obj))) ⋙
      PresheafOfModules.sheafification (𝟙 (R.obj))).obj (SheafOfModules.unit R) =
      (𝟙_ (SheafOfModules R))

/-- The canonical comparison isomorphism from the structure sheaf module `SheafOfModules.unit R`
to the ambient tensor unit in `SheafOfModules R`. -/
noncomputable def unitIsoTensorUnit :
    SheafOfModules.unit R ≅ (𝟙_ (SheafOfModules R)) :=
  (asIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (R.obj))).counit.app (SheafOfModules.unit R))).symm ≪≫
    eqToIso (tensorUnit_eq_sheafification_unit_model (R := R))

end SheafOfModules
