import StacksProject_2024.Chap20.RingedSpaceOpensModuleCategory
import StacksProject_2024.Chap21.Definition_21_46_1_Core

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open TopologicalSpace
open AlgebraicGeometry
noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

/- Domain-style sampling for Definition 20.48.1 (core):
- primary domain: tor-amplitude and finite tor dimension in `D(𝒪_X)`;
- sampled owner declarations:
  `SheafOfModules.RingedSite.HasTorAmplitudeIn`,
  `SheafOfModules.RingedSite.HasFiniteTorDimension`,
  `SheafOfModules.RingedSite.ModuleHasTorDimensionLE`,
  `opensRingedSite`;
- best owner abstraction: the Chapter 20 source-facing predicates are the opens-ringed-space
  specialization of the canonical Chapter 21 core owners on ringed sites.

Source/core/bridge triage:
- `source-facing`: the Chapter 20 tor-dimension predicates on a ringed space;
- `core/canonical`: the Chapter 21 core owners on `opensRingedSite X`;
- `bridge/view`: the opens-ringed-space specialization below. -/

variable {X : RingedSpace.{u}}

variable [CategoryWithHomology (Modules X)]
variable [MonoidalCategory (DerivedCategory (Modules X))]

local notation "ModX" => Modules X
local notation "DMod" => DerivedCategory ModX
local notation "SiteModX" => RingedSite.Hom.ModuleCat (opensRingedSite X)
local notation "SiteDModX" => RingedSite.Hom.ModuleDerived (opensRingedSite X)
local notation "single0" => DerivedCategory.singleFunctor ModX (0 : ℤ)

local instance opensRingedSite_monoidalCategoryStruct :
    MonoidalCategoryStruct SiteDModX := by
  change MonoidalCategoryStruct DMod
  exact (inferInstance : MonoidalCategory DMod).toMonoidalCategoryStruct

/-- Definition 20.48.1 (1): an object `E` of `D(𝒪_X)` has tor-amplitude in `[a, b]`. This is the
opens-ringed-space specialization of the Chapter 21 core owner on a ringed site. -/
abbrev HasTorAmplitudeIn (E : DMod) (a b : ℤ) : Prop :=
  (SheafOfModules.RingedSite.HasTorAmplitudeIn : SiteDModX → ℤ → ℤ → Prop) E a b

/-- Unfolding `HasTorAmplitudeIn` gives the defining homology-vanishing condition for derived
tensor products with degree-zero module sheaves. -/
theorem hasTorAmplitudeIn_iff (E : DMod) (a b : ℤ) :
    HasTorAmplitudeIn E a b ↔
      ∀ (ℱ : ModX) (i : ℤ), i ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor ModX i).obj (E ⊗ (single0).obj ℱ)) :=
  Iff.rfl

/-- Definition 20.48.1 (2): an object of `D(𝒪_X)` has finite tor dimension if it has
tor-amplitude in some finite interval. This is the corresponding opens-ringed-space
specialization of the Chapter 21 core owner. -/
abbrev HasFiniteTorDimension (E : DMod) : Prop :=
  (SheafOfModules.RingedSite.HasFiniteTorDimension : SiteDModX → Prop) E

/-- Unfolding `HasFiniteTorDimension` gives the existence of a finite tor-amplitude interval. -/
theorem hasFiniteTorDimension_iff (E : DMod) :
    HasFiniteTorDimension E ↔ ∃ a b : ℤ, HasTorAmplitudeIn E a b :=
  Iff.rfl

/-- Tor-amplitude in a fixed finite interval implies finite tor dimension. -/
theorem HasTorAmplitudeIn.hasFiniteTorDimension
    {E : DMod} {a b : ℤ}
    (hE : HasTorAmplitudeIn E a b) :
    HasFiniteTorDimension E :=
  SheafOfModules.RingedSite.HasTorAmplitudeIn.hasFiniteTorDimension hE

/-- Definition 20.48.1 (4): an `𝒪_X`-module `ℱ` has tor dimension at most `d` if its degree-zero
derived object `ℱ[0]` has tor-amplitude in `[-d, 0]`. This is the opens-ringed-space
specialization of the Chapter 21 core owner. -/
abbrev ModuleHasTorDimensionLE (ℱ : ModX) (d : ℕ) : Prop :=
  (SheafOfModules.RingedSite.ModuleHasTorDimensionLE : SiteModX → ℕ → Prop) ℱ d

/-- Unfolding `ModuleHasTorDimensionLE` gives the tor-amplitude condition for the degree-zero
derived object `ℱ[0]`. -/
theorem moduleHasTorDimensionLE_iff (ℱ : ModX) (d : ℕ) :
    ModuleHasTorDimensionLE ℱ d ↔
      HasTorAmplitudeIn ((single0).obj ℱ) (-(d : ℤ)) 0 :=
  Iff.rfl

end

end AlgebraicGeometry.RingedSpace
