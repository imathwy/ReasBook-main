import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.Topology.Sheaves.Functors

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace RingedSpace

abbrev ringCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

abbrev Modules (X : RingedSpace.{u}) :=
  SheafOfModules.{u} (ringCatSheaf X)

private abbrev asCommModulePresheaf {X : RingedSpace.{u}} (ℱ : Modules X) :
    PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat.{u}) :=
  ℱ.val

private instance instModuleStalkVal {X : RingedSpace.{u}} (ℱ : Modules X) (x : X) :
    Module (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk ℱ.val.presheaf x) := by
  change Module (X.presheaf.stalk x)
    ↑(TopCat.Presheaf.stalk (asCommModulePresheaf ℱ).presheaf x)
  infer_instance

noncomputable abbrev stalkModuleCat {X : RingedSpace.{u}} (ℱ : Modules X) (x : X) :
    ModuleCat (X.presheaf.stalk x) :=
  ModuleCat.of (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk ℱ.val.presheaf x)

instance modules_abelian (X : RingedSpace.{u}) :
    Abelian (Modules X) :=
  inferInstanceAs (Abelian (SheafOfModules.{u} (ringCatSheaf X)))

end RingedSpace

namespace RingedSpace.Hom

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

noncomputable abbrev commRingSheafPushforwardMap :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf :=
  ⟨f.hom.c⟩

noncomputable abbrev toRingCatSheafHom :
    RingedSpace.ringCatSheaf Y ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj
        (RingedSpace.ringCatSheaf X) :=
  (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).map (commRingSheafPushforwardMap f)

end RingedSpace.Hom

end AlgebraicGeometry
