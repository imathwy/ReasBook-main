import Mathlib
import StacksProject_2024.Chap13.Definition_13_15_3
import StacksProject_2024.Chap18.Definition_18_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace RingedSite.Hom

/-- The class of quasi-isomorphisms on cochain complexes of `\mathcal O_X`-modules. -/
abbrev ModuleQis (X : RingedSite.{u, v}) :=
  HomotopyCategory.quasiIso (SheafOfModules X.structureSheaf) (up ℤ)

/-- The direct-image functor on `\mathcal O`-modules attached to a morphism of ringed sites. -/
abbrev modulePushforward {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y) :
    SheafOfModules X.structureSheaf ⥤ SheafOfModules Y.structureSheaf :=
  SheafOfModules.pushforward f.structureSheafMap

/-- The global-sections functor on `\mathcal O_X`-modules for a ringed-site presentation `X`. -/
abbrev moduleGlobalSectionsFunctor (X : RingedSite.{u, v})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{max u v}] :
    SheafOfModules X.structureSheaf ⥤ AddCommGrpCat.{max u v} :=
  SheafOfModules.toSheaf X.structureSheaf ⋙
    CategoryTheory.Sheaf.Γ X.siteTopology AddCommGrpCat.{max u v}

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
variable [HasWeakSheafify Y.siteTopology AddCommGrpCat.{max u v}]
variable [HasGlobalSectionsFunctor Y.siteTopology AddCommGrpCat.{max u v}]
variable [Functor.Additive (modulePushforward f)]
variable [Functor.Additive (moduleGlobalSectionsFunctor Y)]
variable [Functor.HasRightDerivedFunctor
  (mapHomotopyCategoryToDerived (moduleGlobalSectionsFunctor Y))
  (ModuleQis Y)]

-- Proof sketch: by Lemma `21.14.1`, the pushforward of an injective `\mathcal O_X`-module is
-- totally acyclic on `Y`. Lemma `21.14.3` identifies total acyclicity with right acyclicity for
-- global sections, so every injective is sent by `f_*` to a `Γ(Y,-)`-acyclic object. This is
-- exactly the hypothesis needed to apply Derived Categories, Lemma `13.22.1` and deduce the
-- comparison `RΓ(Y, Rf_* \mathcal F) ≅ RΓ(X, \mathcal F)`.
/-- Remark 21.14.4: for a morphism of ringed topoi, formalized here by a morphism of ringed sites
`f`, the pushforward of any injective `\mathcal O_\mathcal C`-module sheaf is right acyclic for
global sections on the target. Consequently the Leray-type comparison
`RΓ(\mathcal D, Rf_* \mathcal F) = RΓ(\mathcal C, \mathcal F)` is available by Derived
Categories, Lemma `13.22.1`. -/
theorem modulePushforward_injective_isRightAcyclicForGlobalSections
    (ℐ : SheafOfModules X.structureSheaf) (hℐ : Injective ℐ) :
    IsRightAcyclicForAdditiveFunctor (moduleGlobalSectionsFunctor Y)
      ((modulePushforward f).obj ℐ) := sorry

end

end RingedSite.Hom
