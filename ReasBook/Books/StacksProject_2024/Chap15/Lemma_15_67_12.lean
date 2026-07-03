import Mathlib
import StacksProject_2024.Chap15.Lemma_15_67_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {a b : ℤ} {d : ℕ}

local notation "DModB" => DerivedCategory (ModuleCat B)

/- Domain-style sampling for Lemma 15.67.12:
- primary domain: tor-amplitude in derived categories under restriction of scalars;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `ModuleHasTorDimensionLE`,
  `hasTorAmplitudeIn_restrictScalars_derivedTensorProduct`,
  `ModuleCat.single0Functor`,
  `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`;
- best owner abstraction: the source-facing statement remains a tor-amplitude bound after
  restriction of scalars, while the canonical owner layer is `HasTorAmplitudeIn` together with the
  exact derived restriction functor itself; this file is the source-facing specialization of
  `hasTorAmplitudeIn_restrictScalars_derivedTensorProduct` obtained by testing against the
  canonical degree-zero object `B[0]`, not a new local wrapper around restriction of scalars;
- primitive data: the derived `B`-complex `K` and the module-level tor-dimension hypothesis on
  `B` over `A`;
- derived API: the restricted derived object
  `((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)`.

Source/core/bridge triage:
- `source-facing`: `hasTorAmplitudeIn_restrictScalars_of_moduleHasTorDimensionLE`;
- `core/canonical`: `HasTorAmplitudeIn`, `ModuleHasTorDimensionLE`, and exact
  `Functor.mapDerivedCategory` for restriction of scalars;
- `bridge/view`: the canonical degree-zero embedding `ModuleCat.single0Functor` for `B[0]`,
  together with viewing a derived `B`-complex as a derived `A`-complex by restriction. -/

-- Proof sketch: view the degree-zero object `B[0]` in `D(B)`; the hypothesis
-- `ModuleHasTorDimensionLE (ModuleCat.of A B) d` says that, after restriction to `A`, it has
-- tor-amplitude in `[-d, 0]`. Apply Lemma `15.67.10` to `K` and `B[0]`, and then identify
-- `K ⊗_B^L B[0]` with `K` to obtain the interval `[a - d, b]` over `A`.
/-- Lemma 15.67.12: if `B` has tor dimension at most `d` as an `A`-module and `K^•` has
tor-amplitude in `[a, b]` over `B`, then `K^•`, viewed as a complex of `A`-modules by
restriction of scalars, has tor-amplitude in `[a - d, b]`. -/
theorem hasTorAmplitudeIn_restrictScalars_of_moduleHasTorDimensionLE
    (K : DModB)
    (hB : ModuleHasTorDimensionLE (ModuleCat.of A B) d)
    (hK : HasTorAmplitudeIn K a b) :
    HasTorAmplitudeIn
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)
      (a - (d : ℤ)) b := sorry

end

end CategoryTheory
