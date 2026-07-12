import Mathlib
import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap15.Lemma_15_59_14

noncomputable section

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.MonoidalCategory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for Lemma 15.75.11:
- primary domain: closure of perfect objects in derived module categories under the monoidal tensor
  on `D(R)` and its source-facing derived-tensor presentation;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `derivedCategory_tensorObj_iso_derivedTensorProduct`,
  the owner tensor object `K ⊗ L`,
  `derivedTensorWithAlgebra_isPerfect` as the base-change analogue;
- best owner abstraction: the `core/canonical` owner is the monoidal tensor object `K ⊗ L`,
  while the textbook notation `K ⊗[R]^L L` is a `bridge/view` through
  `derivedCategory_tensorObj_iso_derivedTensorProduct`;
- primitive vs. derived:
  primitive data are the perfect objects `K` and `L`;
  closure under tensor is derived API and should use the owner tensor `K ⊗ L`; the source-facing
  notation `K ⊗[R]^L L` is derived from that owner via the canonical comparison isomorphism;
- source/core/bridge triage:
  `source-facing`: perfect objects are stable under the textbook derived tensor product;
  `core/canonical`: `DerivedCategory.IsPerfect` and the monoidal tensor `K ⊗ L`;
  `bridge/view`: `derivedCategory_tensorObj_iso_derivedTensorProduct` identifying `K ⊗ L` with
    `K ⊗[R]^L L`. -/

-- Proof sketch: by Lemma `15.75.2`, it suffices to show that the derived tensor product of two
-- perfect objects is pseudo-coherent and has finite tor dimension. Pseudo-coherence follows from
-- Lemma `15.65.16 (2)`, while finite tor dimension is obtained by choosing tor-amplitude
-- intervals for `K` and `L` from Lemma `15.75.2` and applying Lemma `15.67.10` with `A = B = R`.
/-- Core owner form of Lemma 15.75.11: the monoidal tensor of two perfect objects of `D(R)` is
again perfect. -/
theorem tensor_isPerfect_of_isPerfect
    (K L : DMod)
    (hK : K.IsPerfect)
    (hL : L.IsPerfect) :
    (K ⊗ L).IsPerfect := sorry

/-- Lemma 15.75.11: if `K` and `L` are perfect objects of `D(R)`, then their derived tensor
product `K \otimes_R^{\mathbf L} L` is again a perfect object. -/
@[stacks 0GM0]
theorem isPerfect_derivedTensorProduct
    (K L : DMod)
    (hK : K.IsPerfect)
    (hL : L.IsPerfect) :
    (K ⊗[R]^L L).IsPerfect := by
  let P : ObjectProperty DMod := DerivedCategory.IsPerfect
  exact
    P.prop_of_iso
      (derivedCategory_tensorObj_iso_derivedTensorProduct K L)
      (tensor_isPerfect_of_isPerfect K L hK hL)

end

end CategoryTheory
