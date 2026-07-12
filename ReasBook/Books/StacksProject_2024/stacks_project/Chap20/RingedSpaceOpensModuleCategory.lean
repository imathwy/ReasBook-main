import StacksProject_2024.Chap17.Definition_17_17_1
import StacksProject_2024.Chap18.RingedSiteModuleCategory
import StacksProject_2024.Chap20.RingedSpaceModuleHasDerivedCategory
import StacksProject_2024.Chap21.Lemma_21_19_1_core

open AlgebraicGeometry
open CategoryTheory
open SheafOfModules.RingedSite
open scoped RingedSite.Hom RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The commutative ringed site of opens of a ringed space, equipped with its structure sheaf. -/
abbrev opensRingedSite (X : RingedSpace.{u}) :=
  RingedSite.ofCommRingSheaf (Opens.grothendieckTopology X) X.sheaf

/-- The morphism of opens ringed sites induced by a morphism of ringed spaces. -/
abbrev opensRingedSiteHom {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    opensRingedSite X ⟶ opensRingedSite Y where
  base := TopologicalSpace.Opens.map f.hom.base
  isMorphismOfSites := by infer_instance
  structureSheafMap := RingedSpace.Hom.toRingCatSheafHom f

/-- The opens-site pullback induced by `f` inherits additivity from the usual pullback
`f^*` on sheaves of modules. -/
instance opensRingedSiteHom_pullback_additive {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(f^*).Additive] :
    (SheafOfModules.pullback (opensRingedSiteHom f).structureSheafMap).Additive := by
  change (f^*).Additive
  infer_instance

/-- The opens-site pushforward induced by `f` inherits additivity from the usual pushforward
`f _*` on sheaves of modules. -/
instance opensRingedSiteHom_modulePushforward_additive {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSite.Hom.modulePushforward (opensRingedSiteHom f)).Additive := by
  change (f _*).Additive
  infer_instance

/-- The opens-site module category of a ringed space inherits the monoidal structure on
`RingedSpace.Modules X`. -/
instance instMonoidalCategoryRingedSiteModuleCategory
    (X : RingedSpace) [MonoidalCategory (RingedSpace.Modules X)] :
    MonoidalCategory
      (ringedSiteModuleCategory (Opens.grothendieckTopology X) X.sheaf) := by
  change MonoidalCategory (RingedSpace.Modules X)
  infer_instance

/-- The opens-site module category of a ringed space inherits the preadditive monoidal structure on
`RingedSpace.Modules X`. -/
instance instMonoidalPreadditiveRingedSiteModuleCategory
    (X : RingedSpace)
    [MonoidalCategory (RingedSpace.Modules X)]
    [MonoidalPreadditive (RingedSpace.Modules X)] :
    MonoidalPreadditive
      (ringedSiteModuleCategory (Opens.grothendieckTopology X) X.sheaf) := by
  change MonoidalPreadditive (RingedSpace.Modules X)
  infer_instance

/-- The opens-site module category of a ringed space inherits projective resolutions from
`RingedSpace.Modules X`. -/
instance instHasProjectiveResolutionsRingedSiteModuleCategory
    (X : RingedSpace) [HasProjectiveResolutions (RingedSpace.Modules X)] :
    HasProjectiveResolutions
      (ringedSiteModuleCategory (Opens.grothendieckTopology X) X.sheaf) := by
  change HasProjectiveResolutions (RingedSpace.Modules X)
  infer_instance

end AlgebraicGeometry.RingedSpace
