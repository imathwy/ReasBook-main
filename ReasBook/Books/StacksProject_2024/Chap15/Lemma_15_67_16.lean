import Mathlib
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Lemma_15_67_17

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable {ι : Type*} [Finite ι]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling:
- primary domain: tor-amplitude descent in derived categories under localization-away base change;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `derivedTensorWithAlgebra`,
  `hasTorAmplitudeIn_of_faithfullyFlat_baseChange`;
- source/core/bridge triage:
  `source-facing`: local descent of tor-amplitude from a finite principal-open cover;
  `core/canonical`: `HasTorAmplitudeIn` on `DerivedCategory (ModuleCat R)`;
  `bridge/view`: the localization-away base changes `K ⊗[R]^L[Localization.Away (f i)]`.

Primitive data here is the derived object `K` together with its tor-amplitude after canonical
base change to each `Localization.Away (f i)`, indexed by an arbitrary finite type `ι`. The old
coordinate model `Fin r` carried no mathematical structure used by the statement, so the theorem
below uses the chapter's canonical finite-family surface directly. Its proof route should factor
through the chapter owner `hasTorAmplitudeIn_of_faithfullyFlat_baseChange`, rather than reaching
back to the lower-level derived scalar-extension construction file.
-/

-- Proof sketch: pass from the family `f` to the canonical faithfully flat map from `R` to the
-- finite product of the principal localizations `∏ i, Localization.Away (f i)` attached to the
-- unit-ideal hypothesis. The localized tor-amplitude assumptions give tor-amplitude after this
-- single faithfully flat base change, and Lemma `15.67.17` then descends `HasTorAmplitudeIn`
-- back to `K`.
/-- Lemma 15.67.16: if a finite family `f : ι → R` generates the unit ideal and each
localization of `K` away from `f i` has tor-amplitude in `[a, b]`, then `K` has tor-amplitude in
`[a, b]`. -/
theorem hasTorAmplitudeIn_of_localizationAway_unitIdeal
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤)
    (K : DMod) (a b : ℤ)
    (hloc : ∀ i,
      HasTorAmplitudeIn (K ⊗[R]^L[Localization.Away (f i)]) a b) :
    HasTorAmplitudeIn K a b := sorry

end

end CategoryTheory
