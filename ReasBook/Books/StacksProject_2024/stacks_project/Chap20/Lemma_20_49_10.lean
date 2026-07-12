import StacksProject_2024.Chap20.Lemma_20_33_6
import StacksProject_2024.Chap20.Definition_20_49_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} (U : Opens X.carrier)
variable [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
  (forget₂ CommRingCat RingCat.{u})]

local notation "DMod[" U "]" => moduleDerivedOnOpen X U
local notation "DExt[" U "]" => moduleExtensionByZeroFromOpenDerived X U
local notation "DPush[" U "]" => modulePushforwardFromOpenDerived U

/- Domain-style sampling for Lemma 20.49.10:
- primary domain: perfect derived `O_X`-modules on a ringed space and their behavior
  under open pushforward when the cohomology is supported on a closed subset of the open;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `moduleDerivedOnOpen`,
  `modulePushforwardFromOpenDerived U`,
  `moduleSupportedOn`,
  `isIso_extensionByZeroDerivedToPushforwardFromOpen_of_cohomologySupported`;
- best owner abstraction:
  `source-facing`: the perfectness statement for `Rj_* E` under the support hypothesis;
  `core/canonical`: the Chapter 20 owners `DerivedCategory.IsPerfect`,
    `moduleDerivedOnOpen X U`, `modulePushforwardFromOpenDerived U`,
    `derivedCategoryCohomologyInProperty`, `moduleSupportedOn`;
  `bridge/view`: the support comparison morphism
    from `j_! E` to `Rj_* E`, expressed in Lemma `20.33.6` as the adjoint transpose of the
    inverse unit of `j_! ⊣ j^{-1}`, and its `IsIso` theorem
    `isIso_extensionByZeroDerivedToPushforwardFromOpen_of_cohomologySupported`.

Primitive data are only the open subset `U`, the closed subset `T ⊆ X` contained in `U`, and the
derived object `E` on the open subspace. The support hypothesis itself is already canonically
expressed by `derivedCategoryCohomologyInProperty` specialized to the Chapter 17 support owner
`moduleSupportedOn` on the restricted ringed space `X.restrict U.isOpenEmbedding`, so this file
should reuse that owner directly rather than introducing another local support wrapper; the
open-subspace derived category should likewise be referenced through the Chapter 20 owner
`moduleDerivedOnOpen X U` instead of repeating its defining type expression.
-/
-- Proof sketch: first specialize Lemma `20.33.6 (2)` from a closed subset of `X` to the
-- source-facing formulation by a subset `T ⊆ U` with closed image in `X`, obtaining the canonical
-- comparison `j_! E ≅ Rj_* E`. Then `j_! E` is perfect by extension-by-zero stability, so
-- perfectness of `Rj_* E` follows from invariance under isomorphism.
/-- Companion to Lemma 20.49.10: extension by zero along an open immersion preserves perfect
objects. This is the bridge from a perfect object on the open subspace to the ambient perfect
object used in the pushforward statement. -/
theorem moduleExtensionByZeroFromOpenDerived_isPerfect
    (E : DMod[U]) (hE_perfect : DerivedCategory.IsPerfect E) :
    DerivedCategory.IsPerfect ((DExt[U]).obj E) := by
  sorry

/-- Companion bridge to Lemma 20.49.10: if the cohomology sheaves of `E` are supported on a
subset `T ⊆ U` whose image in `X` is closed, then the canonical comparison `j_! E ≅ Rj_* E`
from Lemma `20.33.6 (2)` applies directly to this source-facing closed-image formulation. -/
theorem isIsomorphic_extensionByZeroDerived_pushforwardFromOpen_of_cohomologySupported_image
    (T : Set U) (hT_closed : IsClosed (Subtype.val '' T))
    (E : DMod[U])
    (hE_support :
      derivedCategoryCohomologyInProperty
        (moduleSupportedOn (X.restrict U.isOpenEmbedding) T) E) :
    IsIsomorphic ((DExt[U]).obj E) ((DPush[U]).obj E) := by
  sorry

/-- Lemma 20.49.10: let `j : U ↪ X` be an open subspace of a ringed space and let `E` be a
perfect object of `D(O_U)`. If the cohomology sheaves of `E` are supported on a subset
`T ⊆ U` whose image in `X` is closed, then `Rj_* E` is a perfect object of
`D(O_X)`. -/
@[stacks 08DP]
theorem modulePushforwardFromOpenDerived_isPerfect_of_cohomologySupported
    (T : Set U) (hT_closed : IsClosed (Subtype.val '' T))
    (E : DMod[U])
    (hE_perfect : DerivedCategory.IsPerfect E)
    (hE_support :
      derivedCategoryCohomologyInProperty
        (moduleSupportedOn (X.restrict U.isOpenEmbedding) T) E) :
    DerivedCategory.IsPerfect ((DPush[U]).obj E) := by
  sorry

end

end AlgebraicGeometry.RingedSpace
