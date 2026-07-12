import StacksProject_2024.Chap20.RingedSpaceOpensModuleCategory
import StacksProject_2024.Chap21.Lemma_21_35_3
import Mathlib.Tactic.Recall

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.42.3:
- primary domain: restriction of derived internal Hom to an open subspace of a ringed space;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.opensRingedSite`,
  `RingedSite.Hom.localizedRestrictionDerived`,
  `RingedSite.Hom.localizedRestriction_derivedInternalHomComparison`,
  `RingedSite.Hom.localizedRestriction_derivedInternalHomComparison_isIso`;
- best owner abstraction:
  `source-facing`: the open-restriction comparison isomorphism
    `Rℋom(K, L)|_U ⟶ Rℋom(K|_U, L|_U)` for a ringed space `X`;
  `core/canonical`: the Chapter 21 owner theorem
    `RingedSite.Hom.localizedRestriction_derivedInternalHomComparison_isIso`;
  `bridge/view`: the opens-ringed-site specialization through `opensRingedSite X`.
- primitive data: the ringed space `X`, the open subset `U`, and objects `K L : D(𝒪_X)`.

This file should therefore pin only the Chapter 21 owner, with the Chapter 20 ringed-space
specialization obtained by applying it to the commutative ringed site of opens of `X`. -/

/- Lemma 20.42.3 is the ringed-space specialization of the Chapter 21 owner
`RingedSite.Hom.localizedRestriction_derivedInternalHomComparison_isIso`. -/
recall RingedSite.Hom.localizedRestriction_derivedInternalHomComparison_isIso

section

variable {X : RingedSpace.{u}} (U : TopologicalSpace.Opens X.carrier)
variable [HasBinaryProducts (opensRingedSite X).carrier]
variable [MonoidalCategory (RingedSite.Hom.ModuleDerived (opensRingedSite X))]
variable [BraidedCategory (RingedSite.Hom.ModuleDerived (opensRingedSite X))]
variable [MonoidalClosed (RingedSite.Hom.ModuleDerived (opensRingedSite X))]
variable [MonoidalCategory (RingedSite.Hom.ModuleDerived ((opensRingedSite X).localization U))]
variable [BraidedCategory (RingedSite.Hom.ModuleDerived ((opensRingedSite X).localization U))]
variable [MonoidalClosed (RingedSite.Hom.ModuleDerived ((opensRingedSite X).localization U))]
variable [PreservesFiniteLimits (RingedSite.Hom.localizedRestriction (opensRingedSite X) U)]
variable [PreservesFiniteColimits (RingedSite.Hom.localizedRestriction (opensRingedSite X) U)]
variable [Functor.Monoidal (RingedSite.Hom.localizedRestrictionDerived (opensRingedSite X) U)]

local notation "DModX" => RingedSite.Hom.ModuleDerived (opensRingedSite X)

/- Specialized check for Lemma 20.42.3 on the opens ringed site of `X`. -/
#check
  (RingedSite.Hom.localizedRestriction_derivedInternalHomComparison_isIso
    (opensRingedSite X) U :
      ∀ K L : DModX,
        IsIso
          (RingedSite.Hom.localizedRestriction_derivedInternalHomComparison
            (opensRingedSite X) U K L))

end

end AlgebraicGeometry.RingedSpace
