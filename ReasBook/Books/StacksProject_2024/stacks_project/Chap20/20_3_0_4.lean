import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap13.Definition_13_11_3
import StacksProject_2024.stacks_project.Chap13.Situation_13_15_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_11_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

attribute [local instance] CategoryTheory.mapBoundedBelowHomotopyToDerivedBelow_isLocalization

variable {X Y : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "ModY" => RingedSpace.Modules Y
local notation "DModX" => D⁺(ModX)
local notation "DModY" => D⁺(ModY)
local notation "QX" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(ModX) ⥤ DModX)

/- Domain-style sampling for 20.3.0.4:
- primary domain: bounded-below derived direct image for sheaves of modules on ringed spaces;
- sampled owner API:
  `RingedSpace.Modules`,
  `RingedSpace.Hom.pushforward`,
  `boundedBelowDerivedCategory`,
  `mapBoundedBelowHomotopyCategoryToDerivedBelow`,
  `mapBoundedBelowHomotopyCategoryToDerivedBelow_hasRightDerivedFunctor`,
  `mapBoundedBelowHomotopyToDerivedBelow`,
  `Functor.totalRightDerived`,
  `Qis⁺`;
- best owner abstraction: the ringed-space bounded-below derived direct image
  `((mapBoundedBelowHomotopyCategoryToDerivedBelow (RingedSpace.Hom.pushforward f)).totalRightDerived
      QX (Qis⁺(ModX)) :
    D⁺(ModX) ⥤ D⁺(ModY))`,
  namely the specialization of the generic owner `Functor.totalRightDerived` to the bounded-below
  homotopy-to-derived lift of the Chapter 6 owner
  `RingedSpace.Hom.pushforward f : ModX ⥤ ModY`;
- primitive data: the owner category `RingedSpace.Modules` and the additive module-pushforward
  functor `RingedSpace.Hom.pushforward f : ModX ⥤ ModY`;
- derived API: the source-facing bounded-below derived direct-image functor
  `modulePushforwardDerivedPlus f : D⁺(ModX) ⥤ D⁺(ModY)`, together with the object notation
  `Rf_[f] K` and the cohomology-sheaf notation `H^q(Rf_[f] K)`.

Source/core/bridge triage:
- `source-facing`: the bounded-below derived direct-image functor `Rf_*`, its object notation
  `Rf_[f] K`, and its cohomology sheaves `H^q(Rf_[f] K)`;
- `core/canonical`: `Functor.totalRightDerived`;
- `bridge/view`: the ringed-space specialization of `Functor.totalRightDerived` to the bounded-
  below homotopy lift of `RingedSpace.Hom.pushforward f`.

This item therefore keeps the source-facing bridge owner `modulePushforwardDerivedPlus f` together
with the notation `Rf_[f] K` and `H^q(Rf_[f] K)` on top of the specialized canonical owner. -/

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.RingedSpace.Hom

variable {X Y : RingedSpace.{u}}

local notation "ModX" => RingedSpace.Modules X
local notation "ModY" => RingedSpace.Modules Y
local notation "DModX" => D⁺(ModX)
local notation "DModY" => D⁺(ModY)
local notation "QX" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(ModX) ⥤ DModX)

/-- The bounded-below derived direct-image functor on `𝒪_X`-modules. -/
abbrev modulePushforwardDerivedPlus
    (f : X ⟶ Y)
    [Functor.HasRightDerivedFunctor
      (mapBoundedBelowHomotopyCategoryToDerivedBelow (pushforward f))
      (boundedBelowHomotopyQuasiIso ModX)] :
    DModX ⥤ DModY :=
  Functor.totalRightDerived
    (mapBoundedBelowHomotopyCategoryToDerivedBelow (pushforward f))
    QX
    (boundedBelowHomotopyQuasiIso ModX)

/- Textbook surface notation for the bounded-below derived direct-image object `Rf_[f] K` and its
cohomology sheaves `H^q(Rf_[f] K)`. The notation expands through the source-facing bridge owner
`modulePushforwardDerivedPlus`, while the cohomology notation inserts the canonical inclusion
`D⁺(ModY) ⥤ D(ModY)` before applying the Chapter `13` owner `H^q`. -/
scoped syntax:100 "Rf_[" term "] " term:max : term
scoped macro_rules
  | `(Rf_[ $f ] $K) =>
      `(((modulePushforwardDerivedPlus $f).obj $K))

scoped notation3:max "H^" q:max "(" "Rf_[" f "] " K ")" =>
  ((H^q).obj ((Rf_[f] K).toDerived))

end AlgebraicGeometry.RingedSpace.Hom
