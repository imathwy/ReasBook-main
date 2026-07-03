import Mathlib
import StacksProject_2024.Chap15.Definition_15_67_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "Ext" => ModuleCat.extendScalars (algebraMap A B)
local notation "single₀" =>
  (ModuleCat.single0Functor : ModuleCat A ⥤ DerivedCategory (ModuleCat A))

/- Domain-style sampling for Lemma 15.67.14:
- primary domain: tor-amplitude and module tor dimension under flat scalar extension in derived
  categories of module categories;
- sampled owner declarations:
  `ModuleHasTorDimensionLE`,
  `HasTorAmplitudeIn`,
  `hasTorAmplitudeIn_derivedTensorWithAlgebra`,
  `ModuleCat.extendScalars`,
  `ModuleCat.single0Functor`;
- best owner abstraction: the core/canonical owner is the chapter tor-amplitude predicate
  `HasTorAmplitudeIn` on degree-zero derived objects, with `hasTorAmplitudeIn_derivedTensorWithAlgebra`
  as the upstream base-change owner theorem; the module statement here is only the degree-zero
  `bridge/view` consequence for ordinary scalar extension;
- primitive vs. derived:
  primitive data are the ring map `A → B`, the flatness hypothesis, and the module `M` viewed via
  `ModuleHasTorDimensionLE M d`, equivalently via the chapter owner
  `single₀`;
  the conclusion for `((Ext).obj M)` is derived API obtained
  by applying the owner theorem to the degree-zero derived object and then comparing with ordinary
  scalar extension in degree `0`.

Source/core/bridge triage:
- `source-facing`: preservation of module tor dimension under flat extension of scalars;
- `core/canonical`: `HasTorAmplitudeIn` and `hasTorAmplitudeIn_derivedTensorWithAlgebra`;
- `bridge/view`: `ModuleHasTorDimensionLE` for ordinary modules. -/

-- Proof sketch: rewrite `ModuleHasTorDimensionLE M d` as tor-amplitude in `[-d, 0]` for the
-- degree-zero owner object of `M`, apply `hasTorAmplitudeIn_derivedTensorWithAlgebra`, and then
-- use flatness of `A → B` to identify derived base change with ordinary scalar extension on
-- degree-zero modules.
/-- Lemma 15.67.14: for a flat ring map `A → B`, if an `A`-module `M` has tor dimension at most
`d`, then its scalar extension `M ⊗_A B` has tor dimension at most `d` as a `B`-module. -/
theorem moduleHasTorDimensionLE_extendScalars
    (hflat : (algebraMap A B).Flat) (M : ModuleCat A) (d : ℕ)
    (hM : ModuleHasTorDimensionLE M d) :
    ModuleHasTorDimensionLE ((Ext).obj M) d := by
  sorry

end

end CategoryTheory
