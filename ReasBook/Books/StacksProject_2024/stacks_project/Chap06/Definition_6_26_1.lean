import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import StacksProject_2024.stacks_project.Chap06.OpensMapFinal
import StacksProject_2024.stacks_project.Chap06.RingedSpaceModuleCore

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry

namespace RingedSpace

abbrev PresheafModules (X : RingedSpace.{u}) :=
  PresheafOfModules.{u} (ringCatSheaf X).obj

end RingedSpace

namespace RingedSpace.Hom

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

noncomputable abbrev inverseImageStructureSheafHomComm :
    (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj Y.sheaf ⟶ X.sheaf :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      f.hom.base).homEquiv _ _).symm (commRingSheafPushforwardMap f)

noncomputable abbrev pushforward (f : X ⟶ Y) :
    RingedSpace.Modules X ⥤ RingedSpace.Modules Y :=
  SheafOfModules.pushforward (toRingCatSheafHom f)

theorem pushforward_def :
    pushforward f = SheafOfModules.pushforward (toRingCatSheafHom f) := by
  rfl

noncomputable abbrev pullback (f : X ⟶ Y) :
    RingedSpace.Modules Y ⥤ RingedSpace.Modules X :=
  SheafOfModules.pullback (toRingCatSheafHom f)

noncomputable abbrev pullbackPushforwardAdjunction (f : X ⟶ Y) :
    pullback f ⊣ pushforward f :=
  SheafOfModules.pullbackPushforwardAdjunction (toRingCatSheafHom f)

section

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts
  preservesBinaryBiproducts_of_preservesBinaryProducts

instance pullback_isLeftAdjoint (f : X ⟶ Y) :
    (pullback f).IsLeftAdjoint := by
  infer_instance

instance pushforward_isRightAdjoint (f : X ⟶ Y) :
    (pushforward f).IsRightAdjoint := by
  infer_instance

instance pushforward_preservesFiniteLimits (f : X ⟶ Y) :
    PreservesFiniteLimits (pushforward f) := by infer_instance

instance pullback_preservesFiniteColimits (f : X ⟶ Y) :
    PreservesFiniteColimits (pullback f) := by infer_instance

instance pushforward_additive (f : X ⟶ Y) :
    (pushforward f).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

instance pullback_additive (f : X ⟶ Y) :
    (pullback f).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

end

instance pullbackObjUnitToUnit_isIso (f : X ⟶ Y) :
    IsIso (SheafOfModules.pullbackObjUnitToUnit (toRingCatSheafHom f)) := by
  letI : Functor.Final (Opens.map f.hom.base) :=
    TopologicalSpace.Opens.map_final f.hom.base
  infer_instance

end RingedSpace.Hom

namespace RingedSpace.Hom

scoped notation:max f:max " _*" => pushforward f
scoped notation:max f:max "^*" => pullback f

end RingedSpace.Hom

end AlgebraicGeometry
