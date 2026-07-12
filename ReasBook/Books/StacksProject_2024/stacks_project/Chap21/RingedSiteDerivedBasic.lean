import Mathlib.Algebra.Homology.DerivedCategory.Basic
import StacksProject_2024.Chap18.RingedSiteModuleCategoryBasic
import StacksProject_2024.Chap21.Lemma_21_19_1_core

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- The unbounded derived category `D(𝒪)` of sheaves of `𝒪`-modules on the ringed site `(C, J)`.
-/
abbrev RingedSiteDerived (J : GrothendieckTopology C) (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  DerivedCategory (ringedSiteModuleCategory J 𝒪)

/-- The monoidal structure on `RingedSiteDerived J 𝒪` restricts to the synonymous owner
`ModuleDerived (RingedSite.ofCommRingSheaf J 𝒪)`. -/
instance ringedSiteModuleDerivedMonoidal
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [MonoidalCategory (RingedSiteDerived J 𝒪)] :
    MonoidalCategory (_root_.RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J 𝒪)) := by
  change MonoidalCategory (RingedSiteDerived J 𝒪)
  infer_instance

/-- The braided structure on `RingedSiteDerived J 𝒪` restricts to the synonymous owner
`ModuleDerived (RingedSite.ofCommRingSheaf J 𝒪)`. -/
instance ringedSiteModuleDerivedBraided
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [MonoidalCategory (RingedSiteDerived J 𝒪)]
    [BraidedCategory (RingedSiteDerived J 𝒪)] :
    BraidedCategory (_root_.RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J 𝒪)) := by
  change BraidedCategory (RingedSiteDerived J 𝒪)
  infer_instance

/-- The closed structure on `RingedSiteDerived J 𝒪` restricts to the synonymous owner
`ModuleDerived (RingedSite.ofCommRingSheaf J 𝒪)`. -/
instance ringedSiteModuleDerivedClosed
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    [MonoidalCategory (RingedSiteDerived J 𝒪)]
    [MonoidalClosed (RingedSiteDerived J 𝒪)] :
    MonoidalClosed (_root_.RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J 𝒪)) := by
  change MonoidalClosed (RingedSiteDerived J 𝒪)
  infer_instance

end

end SheafOfModules.RingedSite

namespace RingedSite.Hom

section

variable (X : _root_.RingedSite.{u, v}) (U : X)
variable [HasBinaryProducts X.carrier]
variable [PreservesFiniteLimits (localizedRestriction X U)]
variable [PreservesFiniteColimits (localizedRestriction X U)]

/-- The exact functor on derived categories induced by restriction to the localized ringed site
`(X/U, 𝒪_U)`. -/
abbrev localizedRestrictionDerived :
    ModuleDerived X ⥤ ModuleDerived (X.localization U) :=
  CategoryTheory.Functor.mapDerivedCategory (localizedRestriction X U)

namespace RingedSiteDerived

/- Lean surface notation for the localized derived inverse-image functor `j_U^{-1}`. -/
scoped notation:max "j[" U:max "]⁻¹" =>
  RingedSite.Hom.localizedRestrictionDerived _ U

end RingedSiteDerived

end

end RingedSite.Hom
