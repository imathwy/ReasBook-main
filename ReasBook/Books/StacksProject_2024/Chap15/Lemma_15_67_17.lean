import Mathlib
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Lemma_15_60_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R R' : Type u} [CommRing R] [CommRing R']

local notation "DModR" => DerivedCategory (ModuleCat R)

/- Domain-style sampling:
- primary domain: tor-amplitude descent for objects of `D(R)` under faithfully flat derived base
  change;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `derivedTensorWithAlgebra`,
  `(ModuleCat.restrictScalars (algebraMap R R')).mapDerivedCategory`;
- source/core/bridge triage:
  `source-facing`: faithful-flat descent of tor-amplitude for a derived `R`-complex along an
    explicit ring map `f : R →+* R'`;
  `core/canonical`: the chapter owner `HasTorAmplitudeIn` on `DerivedCategory (ModuleCat R)`;
  `bridge/view`: the passage from the explicit owner object `((derivedTensorWithAlgebra f).obj K)`
    to the standard derived base-change notation `K ⊗[R]^L[R']` after passing to `f.toAlgebra`.

The old file encoded the same mathematics by quantifying over exactness of tensor complexes for a
chosen cochain representative. That representative-level formulation is derived API: the primitive
data is just the ring map `f`, the derived object `K`, and its tor-amplitude after faithfully
flat base change along `f`. The canonical owner-level statement below therefore replaces the
duplicate complex-level wrapper.
-/

-- Proof sketch: to verify `HasTorAmplitudeIn K a b`, fix an `R`-module `M` and a degree
-- `i ∉ [a, b]`. After tensoring the homology object `H_i(K ⊗_R^L M[0])` with `R'`, use the
-- standard derived base-change/associativity comparison to identify it with the degree-`i`
-- homology of `(K ⊗_R^L R') ⊗_{R'}^L ((R' ⊗_R M)[0])`, which vanishes by `hK`. Since `R'` is
-- faithfully flat over `R`, tensoring with `R'` reflects zero modules, so the original homology
-- object already vanishes.
/-- Lemma 15.67.17: if the derived base change of a derived `R`-complex `K` along a faithfully
flat ring map `R → R'` has tor-amplitude in `[a, b]`, then `K` already has tor-amplitude in
`[a, b]`. -/
theorem hasTorAmplitudeIn_of_faithfullyFlat_baseChange
    (f : R →+* R') (K : DModR) (a b : ℤ)
    (hff : f.FaithfullyFlat)
    (hK : HasTorAmplitudeIn ((derivedTensorWithAlgebra f).obj K) a b) :
    HasTorAmplitudeIn K a b := sorry

end

end CategoryTheory
