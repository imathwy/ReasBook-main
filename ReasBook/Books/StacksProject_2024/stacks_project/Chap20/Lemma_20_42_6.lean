import Mathlib.Tactic.Recall
import StacksProject_2024.Chap20.«20_42_0_1»
import StacksProject_2024.Chap21.Lemma_21_35_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open SheafOfModules.RingedSite
open scoped CartesianClosed

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

local notation "DModX" => RingedSpaceDerived X

/- Domain-style sampling for Lemma 20.42.6:
- primary domain: tensor/internal-Hom comparison in the closed monoidal derived category
  `RingedSpaceDerived X` of module sheaves on a ringed space;
- sampled owner declarations:
  `SheafOfModules.RingedSite.RingedSiteDerived`,
  `SheafOfModules.RingedSite.ringedSiteDerivedTensorInternalHomComparison`,
  `SheafOfModules.RingedSite.ringedSiteDerivedTensorInternalHomComparison_uncurry`,
  `SheafOfModules.RingedSite.ringedSiteDerivedTensorInternalHomComparison_natural`;
- best owner abstraction:
  `SheafOfModules.RingedSite.ringedSiteDerivedTensorInternalHomComparison`, since
  `RingedSpaceDerived X` is the opens-site specialization of the same
  ringed-site derived category;
- primitive data:
  the three objects `K`, `L`, `M : DModX`;
- derived API:
  the canonical comparison morphism itself, its uncurried description, and its functoriality.

Source/core/bridge triage:
- `source-facing`: Lemma 20.42.6 for a ringed space `(X, 𝒪_X)`;
- `core/canonical`: `SheafOfModules.RingedSite.ringedSiteDerivedTensorInternalHomComparison`;
- `bridge/view`: direct reuse of the owner naturality theorem in the opens-site specialization
  attached to `X`, with no extra ringed-space wrapper API.

This file should therefore stay at the `bridge/view` layer: both the main comparison morphism and
its naturality are recalled directly from the ringed-site owner, without introducing a parallel
ringed-space theorem vocabulary. -/

/- Lemma 20.42.6: for a ringed space `(X, 𝒪_X)` and objects `K`, `L`, `M` of
`D(𝒪_X) = RingedSpaceDerived X`, the canonical morphism
`K ⊗ (M ⟹ L) ⟶ M ⟹ (K ⊗ L)` is the opens-site specialization of the canonical
ringed-site comparison morphism. -/
recall ringedSiteDerivedTensorInternalHomComparison

/- Specialized check for Lemma 20.42.6 on `D(𝒪_X)`. -/
#check
  (ringedSiteDerivedTensorInternalHomComparison :
    ∀ K L M : DModX, K ⊗ (M ⟹ L) ⟶ M ⟹ (K ⊗ L))

/- Companion recall: uncurrying the comparison recovers the braiding/evaluation composite already
recorded by the ringed-site owner theorem. -/
recall ringedSiteDerivedTensorInternalHomComparison_uncurry

/- Naturality is already the owner theorem
`ringedSiteDerivedTensorInternalHomComparison_natural` on the opens-site specialization
`RingedSpaceDerived X`. -/
recall ringedSiteDerivedTensorInternalHomComparison_natural

end

end AlgebraicGeometry.RingedSpace
