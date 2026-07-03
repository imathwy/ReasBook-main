import Mathlib
import StacksProject_2024.Chap15.Definition_15_67_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
variable {a b : ℤ}

local notation "DModB" => DerivedCategory (ModuleCat B)

/- Domain-style sampling:
- primary domain: tor-amplitude in derived categories of module categories under flat restriction
  of scalars;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `hasTorAmplitudeIn_restrictScalars_derivedTensorProduct`,
  `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`,
  `derivedTensorProduct`;
- best owner abstraction: the public statement should stay on the tor-amplitude owner
  `HasTorAmplitudeIn`, with restriction of scalars expressed directly by the canonical derived
  functor `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`;
- primitive vs. derived:
  primitive data are the ring map `A → B`, the flatness hypothesis, the derived `B`-object `K`,
  and its tor-amplitude interval `[a, b]`;
  derived API is just the restricted object
  `((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)`.

Source/core/bridge triage:
- `source-facing`: flat restriction of scalars preserves the tor-amplitude interval of a derived
  `B`-complex;
- `core/canonical`: `HasTorAmplitudeIn` and exact `Functor.mapDerivedCategory` for
  `ModuleCat.restrictScalars`;
- `bridge/view`: the degree-zero `B`-module `B[0]` used in the proof sketch to reduce to
  Lemma `15.67.10`.

The old file introduced a private alias for the derived restriction functor. That alias carried no
mathematics beyond the canonical owner operation, so the theorem surface below uses the canonical
expression directly, with this lemma understood as the flat `B[0]` specialization of
`hasTorAmplitudeIn_restrictScalars_derivedTensorProduct`.
-/

-- Proof sketch: apply `hasTorAmplitudeIn_restrictScalars_derivedTensorProduct` with
-- `L := (ModuleCat.single0Functor : ModuleCat B ⥤ DModB).obj (ModuleCat.of B B)`. The degree-zero
-- `B`-module is flat over `A`, so after restriction to `A` it has tor-amplitude in `[0, 0]`;
-- then identify `K ⊗_B^L B[0]` with `K`.
/-- Lemma 15.67.11: if `K^•` has tor-amplitude in `[a, b]` over `B` and `B` is flat over `A`,
then `K^•`, viewed as a complex of `A`-modules by restriction of scalars, has tor-amplitude in
`[a, b]`. -/
theorem hasTorAmplitudeIn_restrictScalars_of_flat
    (K : DModB) (hK : HasTorAmplitudeIn K a b) :
    HasTorAmplitudeIn
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K) a b :=
  sorry

end

end CategoryTheory
