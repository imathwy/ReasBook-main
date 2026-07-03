import Mathlib
import StacksProject_2024.Chap20.Definition_20_48_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped RingedSpaceDerivedTensor

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

/-
Domain-style sampling for Lemma 20.48.7:
- primary domain: tor-amplitude in `D(\mathcal O_X)` under the derived tensor product;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.derivedTensorProduct`,
  `AlgebraicGeometry.RingedSpace.HasTorAmplitudeIn`,
  `CategoryTheory.HasTorAmplitudeIn` from Chapter 15;
- best owner abstraction: the ambient owners are the source-facing tor-amplitude predicate
  `HasTorAmplitudeIn` and the derived tensor-product owner `derivedTensorProduct`; this file should
  state only the closure property for those owners, not introduce a parallel tensor or
  tor-amplitude wrapper.

Source/core/bridge triage:
- `source-facing`: the tor-amplitude bound for `K ⊗^L L` on a ringed space;
- `core/canonical`: `HasTorAmplitudeIn` together with `derivedTensorProduct`;
- `bridge/view`: this lemma, which records the closure of the source-facing predicate under the
  canonical tensor owner.

Primitive vs derived:
- primitive data: the objects `K`, `L` and their tor-amplitude bounds;
- derived API: the induced tor-amplitude bound for `K ⊗^L L`.

No extra local wrapper is needed here, so the file keeps only the theorem surface.
-/

variable {X : RingedSpace.{u}}

local notation "ModX" => (RingedSpace.Modules X)
local notation "DMod" => DerivedCategory ModX

variable [CategoryWithHomology ModX]
variable [HasCountableCoproducts ModX]
variable [MonoidalCategory ModX]
variable [MonoidalPreadditive ModX]
variable [HasColimits ModX]
variable [(curriedTensor ModX).Additive]
variable [∀ ℱ : ModX, ((curriedTensor ModX).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex ModX ℤ), CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor ModX)]

variable {a b c d : ℤ}

-- Proof sketch: test the defining tor-amplitude condition against an arbitrary module sheaf
-- placed in degree `0`, rewrite the resulting triple derived tensor product by associativity, and
-- apply the Tor spectral sequence to combine the ranges `[a, b]` and `[c, d]` into
-- `[a + c, b + d]`.
/-- Lemma 20.48.7: if `K` has tor-amplitude in `[a, b]` and `L` has tor-amplitude in `[c, d]`,
then `K \otimes_{\mathcal O_X}^{\mathbf L} L` has tor-amplitude in `[a + c, b + d]`. -/
theorem hasTorAmplitudeIn_derivedTensorProduct
    (K L : DMod)
    (hK : HasTorAmplitudeIn K a b)
    (hL : HasTorAmplitudeIn L c d) :
    HasTorAmplitudeIn (K ⊗^L L) (a + c) (b + d) := sorry

end

end AlgebraicGeometry.RingedSpace
