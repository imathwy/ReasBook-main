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

variable {R' R : Type u} [CommRing R'] [CommRing R] [Algebra R' R]

local notation "DModRPrime" => DerivedCategory (ModuleCat R')

/- Domain-style sampling for Lemma 15.67.20:
- primary domain: tor-amplitude in derived categories under derived scalar extension across a
  nilpotent thickening;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `derivedTensorWithAlgebra`,
  `DerivedTensorWithAlgebra` notation `⊗[R']^L[R]`,
  `hasTorAmplitudeIn_derivedTensorWithAlgebra`;
- best owner abstraction: the source-facing statement is an equivalence on the chapter owner
  predicate `HasTorAmplitudeIn` before and after applying the canonical base-change owner
  `derivedTensorWithAlgebra (algebraMap R' R)`;
- primitive vs. derived:
  primitive data are the nilpotent thickening hypotheses on `R' → R`, the derived object
  `K' : D(R')`, and the interval bounds `a, b`;
  the base-changed object `K' ⊗[R']^L[R]` is derived API through the existing scalar-extension
  owner, so this file should depend directly on the owner file `15_60_1_1` rather than on the
  later change-of-rings bridge in `Lemma_15_60_1`;
- source/core/bridge triage:
  `source-facing`: tor-amplitude is equivalent before and after base change along a surjective map
    with nilpotent kernel;
  `core/canonical`: `HasTorAmplitudeIn` and `derivedTensorWithAlgebra`;
  `bridge/view`: the notation `K' ⊗[R']^L[R]` for applying the owner functor to `K'`. -/

-- Proof sketch: the forward implication is Lemma `15.67.13`, since tor-amplitude is preserved by
-- derived base change. For the converse, induct on the nilpotence exponent of
-- `RingHom.ker (algebraMap R' R)` and use the distinguished triangle attached to
-- `0 → I M' → M' → M' / I M' → 0` for an arbitrary `R'`-module `M'`, reducing first to the case
-- where the kernel acts trivially so that `M'` descends to an `R`-module.
/-- Lemma 15.67.20: for a surjective ring map `R' → R` with nilpotent kernel, an object
`K'` of `D(R')` has tor-amplitude in `[a, b]` if and only if its derived base change
`K' \otimes_{R'}^{\mathbf L} R` has tor-amplitude in `[a, b]` in `D(R)`. -/
theorem hasTorAmplitudeIn_derivedTensorWithAlgebra_iff_of_surjective_of_nilpotent_ker
    (hsurj : Function.Surjective (algebraMap R' R))
    (hker : IsNilpotent (RingHom.ker (algebraMap R' R)))
    (K' : DModRPrime) (a b : ℤ) :
    HasTorAmplitudeIn (K' ⊗[R']^L[R]) a b ↔
      HasTorAmplitudeIn K' a b := sorry

end

end CategoryTheory
