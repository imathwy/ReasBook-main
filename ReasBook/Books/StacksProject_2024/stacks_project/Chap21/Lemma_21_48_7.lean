import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap21.Definition_21_47_1

open CategoryTheory
open CategoryTheory.Limits
open RingedSite.Hom
open RingedSite.Hom.ModuleDerived

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

open _root_.RingedSite.DerivedCategory

variable {X : RingedSite.{u, v}}

local notation "DMod" => ModuleDerived X

variable [HasBinaryProducts X.carrier]
variable [∀ U : X, (localizedRestriction X U).Additive]
variable [∀ U : X, PreservesFiniteLimits (localizedRestriction X U)]
variable [∀ U : X, PreservesFiniteColimits (localizedRestriction X U)]
variable [CategoryWithHomology (ModuleCat X)]
variable [∀ U : X, CategoryWithHomology (ModuleCat (X.localization U))]

/- Domain-style sampling for Lemma 21.48.7:
- primary domain: left duality and perfectness in the monoidal derived category `D(𝒪)` of
  a ringed site;
- sampled owner declarations:
  `CategoryTheory.ExactPairing`,
  `RingedSite.DerivedCategory.IsPerfect`,
  `leftDualIso`;
- best owner abstraction:
  `source-facing`: the converse statement below, expressed on the intrinsic bundled ringed site
    `X`;
  `core/canonical`: an arbitrary exact pairing `ExactPairing N M` together with the perfectness
    owner `IsPerfect M`;
  `bridge/view`: the uniqueness isomorphism `leftDualIso` comparing any two chosen left duality
    data; this file should reuse that owner directly rather than introduce a second local
    comparison wrapper.

Primitive data are only the object `M` together with an arbitrary exact pairing `ExactPairing N M`.
Perfectness is the source-facing conclusion. Comparisons between chosen duality data are derived
API, so this file should keep the converse theorem on the bundled owner `X` and reuse
`leftDualIso` directly rather than package a parallel local comparison isomorphism.
-/

/-- Lemma 21.48.7 (1): if `M` has a left dual in the monoidal category `D(𝒪)` of a
ringed site, then `M` is perfect. -/
@[stacks 0FPV]
theorem exactPairing_isPerfect
    [MonoidalCategory DMod]
    {M N : DMod} (hpair : ExactPairing N M) :
    M.IsPerfect := by
  sorry

omit [HasBinaryProducts X.carrier]
  [∀ U : X, (localizedRestriction X U).Additive]
  [∀ U : X, PreservesFiniteLimits (localizedRestriction X U)]
  [∀ U : X, PreservesFiniteColimits (localizedRestriction X U)]
  [CategoryWithHomology (ModuleCat X)]
  [∀ U : X, CategoryWithHomology (ModuleCat (X.localization U))] in
/- Bridge/view for Lemma `21.48.7`: uniqueness of left duals is already owned by the canonical
comparison `leftDualIso`, so this file should not introduce a second wrapper around that owner
declaration. -/
recall leftDualIso

end

end SheafOfModules.RingedSite
