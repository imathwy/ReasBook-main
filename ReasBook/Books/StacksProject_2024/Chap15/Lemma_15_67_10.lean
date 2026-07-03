import Mathlib
import StacksProject_2024.Chap15.Definition_15_67_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {a b c d : ℤ}

local notation "DModB" => DerivedCategory (ModuleCat B)

/- Domain-style sampling for Lemma 15.67.10:
- primary domain: derived change of rings and tor-amplitude in derived categories of modules;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `derivedTensorProduct`,
  `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`,
  `derivedTensorProduct_associator`;
- best owner abstraction: this lemma is a `source-facing` change-of-rings bridge whose statement
  should stay on the tor-amplitude owner `HasTorAmplitudeIn`; the tensor product and restriction
  steps are already canonically owned by `derivedTensorProduct`, its associativity isomorphism
  `derivedTensorProduct_associator`, and the exact functor
  `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`, so no parallel wrapper API
  is introduced here;
- primitive data: the objects `K, L : D(B)` and the tor-amplitude hypotheses on `K` over `B`
  and on the restricted object
  `((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L` over `A`;
- derived API: the tor-amplitude bound for the restricted tensor product object
  `((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj (K ⊗[B]^L L)`.

Source/core/bridge triage:
- `source-facing`: the Stacks-project tor-amplitude bound after tensoring over `B` and then
  restricting to `A`;
- `core/canonical`: `HasTorAmplitudeIn`, `derivedTensorProduct`, and exact
  `Functor.mapDerivedCategory` for restriction of scalars;
- `bridge/view`: restriction of scalars applied via the exact derived functor
  `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`. -/

-- Proof sketch: choose a flat representative of `K` over `B` supported in `[a, b]` using
-- Lemma `15.67.3`, test the restricted derived tensor product against an arbitrary degree-zero
-- `A`-module, rewrite the resulting iterated derived tensor product with the canonical
-- associativity isomorphism `derivedTensorProduct_associator`, and use the tor-amplitude bound on
-- `L` over `A` together with the double-complex spectral sequence to bound the resulting
-- cohomology degrees by `[a + c, b + d]`.
/-- Lemma 15.67.10: if `K^•` has tor-amplitude in `[a, b]` over `B` and `L^•`, viewed as a
complex of `A`-modules by restriction of scalars, has tor-amplitude in `[c, d]`, then
`K^• \otimes_B^{\mathbf L} L^•`, viewed as a complex of `A`-modules, has tor-amplitude in
`[a + c, b + d]`. -/
theorem hasTorAmplitudeIn_restrictScalars_derivedTensorProduct
    (K L : DModB)
    (hK : HasTorAmplitudeIn K a b)
    (hL :
      HasTorAmplitudeIn
        (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L) c d) :
    HasTorAmplitudeIn
      (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj
        (K ⊗[B]^L L))
      (a + c) (b + d) := sorry

end

end CategoryTheory
