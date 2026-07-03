import Mathlib
import stacks_project.Chap15.Definition_15_75_1

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)

/- Domain-style sampling for Lemma 15.75.8:
- primary domain: perfect objects in derived categories under restriction of scalars along the
  algebra map `A → B`;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `ModuleCat.IsPerfect`,
  `isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`,
  `isPseudoCoherent_iff_restrictScalars`,
  `hasTorAmplitudeIn_restrictScalars_of_moduleHasTorDimensionLE`;
- best owner abstraction: this theorem is a `source-facing` restriction-of-scalars bridge for
  perfectness, while the actual restriction construction is owned canonically by the exact derived
  functor `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`; the assumption that
  `B` is perfect as an `A`-module is kept as the source-faithful hypothesis rather than being
  replaced by the later ring-map owner `RingHom.IsPerfectRingMap`, which lives at a different
  layer;
- primitive vs. derived:
  primitive data are the derived `B`-complex `K`, the perfectness hypothesis on the `A`-module
  `B`, and the perfectness hypothesis on `K`;
  derived API is the perfectness statement for the restricted object
  `((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)`;
- source/core/bridge triage:
  `source-facing`: `isPerfect_restrictScalars_of_module_isPerfect`;
  `core/canonical`: `K.IsPerfect`, `(ModuleCat.of A B).IsPerfect`, and the functor
    `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`;
  `bridge/view`: the restriction-of-scalars image
    `((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K)`.
-/

-- Proof sketch: apply Lemma `15.75.2` to the perfect `A`-module `B` and to the perfect
-- `B`-complex `K` to obtain pseudo-coherence and finite tor dimension. Use
-- `isPseudoCoherent_iff_restrictScalars` for the pseudo-coherent part and
-- `hasTorAmplitudeIn_restrictScalars_of_moduleHasTorDimensionLE` for a finite tor-amplitude
-- interval after restriction of scalars. Then reassemble perfection with Lemma `15.75.2`.
/-- Lemma 15.75.8: if `A → B` is a ring map, `B` is perfect as an `A`-module, and `K^•` is
perfect over `B`, then `K^•` is perfect over `A` after restriction of scalars. -/
theorem isPerfect_restrictScalars_of_module_isPerfect
    (K : DModB) (hB : (ModuleCat.of A B).IsPerfect) (hK : K.IsPerfect) :
    (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K : DModA)).IsPerfect :=
      sorry

end

end CategoryTheory
