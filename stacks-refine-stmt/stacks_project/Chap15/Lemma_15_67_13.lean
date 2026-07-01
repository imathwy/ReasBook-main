import Mathlib
import stacks_project.Chap15.Definition_15_67_1
import stacks_project.Chap15.«15_60_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)

/- Domain-style sampling for Lemma 15.67.13:
- primary domain: tor-amplitude in derived categories under derived scalar extension;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `derivedTensorWithAlgebra`,
  `DerivedTensorWithAlgebra` notation `⊗[A]^L[B]`,
  `ModuleCat.extendScalars`;
- best owner abstraction: this theorem is `source-facing`, while the core/canonical owners are the
  tor-amplitude predicate `HasTorAmplitudeIn` and the derived scalar-extension owner
  `derivedTensorWithAlgebra (algebraMap A B)`;
- primitive vs. derived:
  primitive data are the derived `A`-complex `K` and its tor-amplitude interval `[a, b]`;
  the base-changed object `K ⊗[A]^L[B]` is derived API through the canonical owner notation, so
  this file should depend directly on the owner file `15_60_1_1` rather than the later
  change-of-rings bridge in `Lemma_15_60_1`;
- source/core/bridge triage:
  `source-facing`: preservation of tor-amplitude under base change along `A → B`;
  `core/canonical`: `HasTorAmplitudeIn` and `derivedTensorWithAlgebra`;
  `bridge/view`: the notation `K ⊗[A]^L[B]` for the owner applied to `K`. -/

-- Proof sketch: choose a flat representative of `K` concentrated in degrees `[a, b]` using
-- Lemma `15.67.3`; after tensoring termwise with `B`, the resulting complex is still concentrated
-- in `[a, b]`, and its terms are flat over `B` by flat base change. This new flat representative
-- computes `K ⊗_A^L B`, so Lemma `15.67.3` gives the claimed tor-amplitude interval over `B`.
/-- Lemma 15.67.13: if an object `K^•` of `D(A)` has tor-amplitude in `[a, b]`, then its derived
base change `K^• \otimes_A^{\mathbf L} B` has tor-amplitude in `[a, b]` as an object of
`D(B)`. -/
theorem hasTorAmplitudeIn_derivedTensorWithAlgebra
    (K : DModA) (a b : ℤ) (hK : HasTorAmplitudeIn K a b) :
    HasTorAmplitudeIn (K ⊗[A]^L[B]) a b := sorry

end

end CategoryTheory
