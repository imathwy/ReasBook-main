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

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.67.18:
- primary domain: relative tor-amplitude in derived categories under faithfully flat base change
  of the ambient algebra;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `derivedTensorWithAlgebra`,
  `(ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory`,
  `(ModuleCat.restrictScalars (algebraMap R B)).mapDerivedCategory`;
- best owner abstraction: the source-facing statement is an `iff` about the canonical owner
  `HasTorAmplitudeIn` after applying the two exact derived restriction functors, so the theorem
  should speak directly in that owner language instead of rebuilding a local wrapper around the
  restricted complexes;
- primitive vs. derived:
  primitive data are the scalar tower `R → A → B`, the faithfully flat hypothesis on `A → B`, and
  the derived `A`-complex `K`;
  the restricted objects
  `((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K)` and
  `((ModuleCat.restrictScalars (algebraMap R B)).mapDerivedCategory.obj (K ⊗[A]^L[B]))` are
  derived API obtained by viewing the same source-facing complex over `R` before and after base
  change.

Source/core/bridge triage:
- `source-facing`: faithful-flat invariance of tor-amplitude over the base ring `R`;
- `core/canonical`: `HasTorAmplitudeIn` on derived module categories;
- `bridge/view`: the exact derived restriction objects
  `((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K)` and
  `((ModuleCat.restrictScalars (algebraMap R B)).mapDerivedCategory.obj (K ⊗[A]^L[B]))`,
  together with the derived base-change object `K ⊗[A]^L[B]`. -/

-- Proof sketch: the forward implication is tor-amplitude preservation under derived base change,
-- applied after viewing `K` as an object of `D(R)`. For the reverse implication, apply faithful
-- flat descent for tor-amplitude to the restricted `R`-linear complex after base change along
-- `A → B`, using the compatibility between restriction of scalars and derived tensor base change.
/-- Lemma 15.67.18: for ring maps `R → A → B` with `A → B` faithfully flat, an object `K` of
`D(A)` has tor-amplitude in `[a, b]` over `R` if and only if its derived base change
`K \otimes_A^{\mathbf L} B`, regarded as an object of `D(R)`, has tor-amplitude in `[a, b]`
over `R`. -/
theorem hasTorAmplitudeIn_restrictScalars_iff_of_faithfullyFlat_baseChange
    (K : DModA) (a b : ℤ)
    (hff : RingHom.FaithfullyFlat (algebraMap A B)) :
    HasTorAmplitudeIn
        (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory).obj K) a b ↔
      HasTorAmplitudeIn
        (((ModuleCat.restrictScalars (algebraMap R B)).mapDerivedCategory).obj (K ⊗[A]^L[B]))
        a b := sorry

end

end CategoryTheory
