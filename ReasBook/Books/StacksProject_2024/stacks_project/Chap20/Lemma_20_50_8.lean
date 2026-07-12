import Mathlib.Tactic.Recall
import StacksProject_2024.Chap20.Definition_20_49_1
import StacksProject_2024.Chap20.OpensInstances
import StacksProject_2024.Chap20.RingedSpaceOpensModuleCategory
import StacksProject_2024.Chap20.«20_42_0_1»
import StacksProject_2024.Chap21.Lemma_21_19_1_core
import StacksProject_2024.Chap21.Lemma_21_48_7

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable [HasBinaryProducts (opensRingedSite X).carrier]
variable [CategoryWithHomology (RingedSite.Hom.ModuleCat (opensRingedSite X))]
variable [∀ U : (opensRingedSite X).carrier,
  (RingedSite.Hom.localizedRestriction (opensRingedSite X) U).Additive]
variable [∀ U : (opensRingedSite X).carrier,
  PreservesFiniteLimits (RingedSite.Hom.localizedRestriction (opensRingedSite X) U)]
variable [∀ U : (opensRingedSite X).carrier,
  PreservesFiniteColimits (RingedSite.Hom.localizedRestriction (opensRingedSite X) U)]
variable [∀ U : (opensRingedSite X).carrier,
  CategoryWithHomology (RingedSite.Hom.ModuleCat ((opensRingedSite X).localization U))]
variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]

local notation "DMod" => RingedSpaceDerived X

/- Domain-style sampling for Lemma 20.50.8:
- primary domain: rigid duality in the braided monoidal derived category `D(𝒪_X)`;
- sampled owner declarations:
  `CategoryTheory.ExactPairing`,
  `CategoryTheory.BraidedCategory.exactPairing_swap`,
  `CategoryTheory.rightDualIso`,
  `SheafOfModules.RingedSite.exactPairing_isPerfect`;
- best owner abstraction:
  `source-facing`: the Chapter 20 right-dual-implies-perfect statement for `D(𝒪_X)`;
  `core/canonical`: the left-dual owner theorem
    `SheafOfModules.RingedSite.exactPairing_isPerfect` on the opens ringed site of `X`, together
    with the perfectness owner `DerivedCategory.IsPerfect`;
  `bridge/view`: the braided swap `BraidedCategory.exactPairing_swap`, which converts the
    source-facing right-dual datum into the corresponding left-dual form when needed, together
    with the uniqueness isomorphism `rightDualIso`.

Primitive data are only an object of `D(𝒪_X)` together with a right-dual exact pairing.
Perfectness is the source-facing conclusion in Chapter 20, while the swap and uniqueness maps are
derived API. This file should therefore keep the right-dual theorem itself as a thin braided
bridge to the canonical left-dual owner theorem, rather than restating stronger ambient structure
on the public theorem surface.
-/

/- The comparison of two right duals is already canonically owned by `rightDualIso`. -/
recall rightDualIso

-- Proof sketch: swap the chosen right-dual pairing into a left-dual pairing by the braiding, then
-- apply the canonical opens-ringed-site owner theorem
-- `SheafOfModules.RingedSite.exactPairing_isPerfect`.
omit [∀ U : (opensRingedSite X).carrier,
  CategoryWithHomology (RingedSite.Hom.ModuleCat ((opensRingedSite X).localization U))] in
/-- Lemma 20.50.8: if an object `M` of `D(𝒪_X)` has a chosen right dual in the monoidal
category `D(𝒪_X)`, then `M` is perfect. -/
@[stacks 0FPD]
theorem exactPairing_isPerfect
    {M N : DMod} (hpair : ExactPairing M N) :
    DerivedCategory.IsPerfect M := by
  letI : ExactPairing M N := hpair
  letI : ExactPairing N M := BraidedCategory.exactPairing_swap M N
  simpa using
    (RingedSite.exactPairing_isPerfect (inferInstance : ExactPairing N M) :
      DerivedCategory.IsPerfect M)

end

end AlgebraicGeometry.RingedSpace
