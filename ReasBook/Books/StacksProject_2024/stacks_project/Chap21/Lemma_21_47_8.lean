import Mathlib.CategoryTheory.ObjectProperty.Retract
import StacksProject_2024.stacks_project.Chap21.Definition_21_47_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.ObjectProperty.IsStableUnderRetracts

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

open RingedSite.Hom
open _root_.RingedSite.Hom.ModuleDerived

section

variable {X : RingedSite.{u, v}}
variable [HasBinaryProducts X.carrier]
variable [∀ U : X, (localizedRestriction X U).Additive]
variable [CategoryWithHomology (ModuleCat X)]
variable [∀ U : X, PreservesFiniteLimits (localizedRestriction X U)]
variable [∀ U : X, PreservesFiniteColimits (localizedRestriction X U)]
variable [∀ U : X, CategoryWithHomology (ModuleCat (X.localization U))]

local notation "DMod" => ModuleDerived X
local notation "PerfectObj" => (IsPerfect : ObjectProperty DMod)

/- Domain-style sampling for Lemma 21.47.8:
- primary domain: perfect objects in `D(𝒪_X)` as a retract-stable object property;
- sampled owner declarations:
  `RingedSite.Hom.ModuleDerived.IsPerfect`,
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_left`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_right`;
- best owner abstraction: the `core/canonical` owner is
  `PerfectObj := (RingedSite.Hom.ModuleDerived.IsPerfect : ObjectProperty DMod)`;
- primitive vs. derived:
  primitive data are the owner predicate `K.IsPerfect` from Definition `21.47.1`;
  derived API is retract stability and the left/right direct-summand consequences.

Source/core/bridge triage:
- `source-facing`: the direct-summand statement of Lemma `21.47.8`;
- `core/canonical`: `ObjectProperty.IsStableUnderRetracts PerfectObj`;
- `bridge/view`: `of_biprod_left`, `of_biprod_right`, and the conjunction package below.
-/

-- Proof sketch: choose a perfect representative of `L`, transport the retract data `K ⟶ L ⟶ K`
-- to the representative level, and split the bounded finite-free complex degreewise to obtain a
-- perfect representative of `K`.
/-- Perfect objects of `D(𝒪_X)` are stable under retracts/direct summands. -/
instance isPerfect_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts PerfectObj where
  of_retract {K L} h hL := by
    sorry

-- Proof sketch: once perfectness is exposed as the retract-stable owner `PerfectObj`, the
-- textbook statement is exactly the conjunction of the generic left and right biproduct lemmas.
omit [∀ U : X, (localizedRestriction X U).Additive]
  [CategoryWithHomology (ModuleCat X)]
  [∀ U : X, PreservesFiniteLimits (localizedRestriction X U)]
  [∀ U : X, PreservesFiniteColimits (localizedRestriction X U)] in
/-- Lemma 21.47.8: if a binary biproduct `K ⊞ L` is perfect, then both summands are perfect. -/
@[stacks 08GA]
theorem isPerfect_summands_of_biprod
    (K L : DMod) [HasBinaryBiproduct K L] (hKL : (K ⊞ L).IsPerfect) :
    K.IsPerfect ∧ L.IsPerfect :=
  ⟨of_biprod_left PerfectObj hKL, of_biprod_right PerfectObj hKL⟩

omit [∀ U : X, (localizedRestriction X U).Additive]
  [CategoryWithHomology (ModuleCat X)]
  [∀ U : X, PreservesFiniteLimits (localizedRestriction X U)]
  [∀ U : X, PreservesFiniteColimits (localizedRestriction X U)] in
/-- The left-projection companion to `isPerfect_summands_of_biprod`. -/
theorem isPerfect_left_of_biprod
    (K L : DMod) [HasBinaryBiproduct K L] (hKL : (K ⊞ L).IsPerfect) :
    K.IsPerfect :=
  (isPerfect_summands_of_biprod K L hKL).1

omit [∀ U : X, (localizedRestriction X U).Additive]
  [CategoryWithHomology (ModuleCat X)]
  [∀ U : X, PreservesFiniteLimits (localizedRestriction X U)]
  [∀ U : X, PreservesFiniteColimits (localizedRestriction X U)] in
/-- The right-projection companion to `isPerfect_summands_of_biprod`. -/
theorem isPerfect_right_of_biprod
    (K L : DMod) [HasBinaryBiproduct K L] (hKL : (K ⊞ L).IsPerfect) :
    L.IsPerfect :=
  (isPerfect_summands_of_biprod K L hKL).2

end

end SheafOfModules.RingedSite
