import StacksProject_2024.stacks_project.Chap13.Lemma_13_14_16
import StacksProject_2024.stacks_project.Chap13.Lemma_13_20_2
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap20.Global_sections_module_owners_core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Functor
open AlgebraicGeometry
open scoped AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization

namespace AlgebraicGeometry.RingedSpace

variable {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

local notation "ModX" => RingedSpace.Modules X
local notation "ModY" => RingedSpace.Modules Y
local notation "ModZ" => RingedSpace.Modules Z
local notation "QX" => boundedBelowHomotopyQuasiIso ModX
local notation "QY" => boundedBelowHomotopyQuasiIso ModY
local notation "DModZ" => D⁺(ModZ)
local notation "pushforwardPlus" =>
  (mapBoundedBelowHomotopyCategory (f _*) : K⁺(ModX) ⥤ K⁺(ModY))
local notation "derivedPushforwardPlus" =>
  (mapBoundedBelowHomotopyCategoryToDerivedBelow (g _*) : K⁺(ModY) ⥤ DModZ)

/- Domain-style sampling for Lemma 20.13.7:
- primary domain: bounded-below Grothendieck comparison morphisms for compositions of module
  pushforwards on ringed spaces;
- sampled owner declarations:
  `SheafOfModules.pushforwardComp`,
  `Functor.rightDerivedCompComparison`,
  `Functor.rightDerivedNatTrans`;
- best owner abstraction: the canonical bounded-below comparison morphism
  `Functor.rightDerivedCompComparison`; `SheafOfModules.pushforwardComp`,
  `Functor.rightDerivedNatTrans`, and the bounded-below `Functor.totalRightDerived`
  specializations are the internal `bridge/view` mechanisms relating the composite pushforward to
  the iterated derived pushforwards;
- primitive data: the two composable pushforward functors, the canonical underived comparison
  `f _*`, `g _*`, and the bounded-below right-derived-functor structure canonically attached to
  these owners and their composite;
- derived API: the owner-level isomorphism statement for the ringed-space specialization of that
  canonical comparison morphism.
-/
variable [(f _*).Additive]
variable [(g _*).Additive]

-- Proof sketch: the ordinary pushforwards compose, so the canonical comparison morphism from
-- `R(g ∘ f)_* ⟶ Rg_* ∘ Rf_*` is the source-facing owner. The remaining proof is the bounded-below
-- acyclicity argument: by Lemma `20.11.10`, `f_*` sends injectives to sheaves whose higher
-- cohomology on opens vanishes for `g`, and Lemma `20.7.3` identifies the higher direct images of
-- `g_*` with those cohomology sheaves.
/-- Lemma 20.13.7: for composable morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z`, the
canonical bounded-below Grothendieck comparison morphism from the derived functor of the
composite underived pushforward to the composite of the bounded-below derived direct images is an
isomorphism. In owner form, this is exactly the bounded-below specialization of
`Functor.rightDerivedCompComparison` for module pushforward on ringed spaces. -/
@[stacks 01F5]
instance modulePushforwardDerivedPlusCompComparison_isIso :
    IsIso (rightDerivedCompComparison QX QY pushforwardPlus derivedPushforwardPlus) := by
  sorry

end AlgebraicGeometry.RingedSpace
