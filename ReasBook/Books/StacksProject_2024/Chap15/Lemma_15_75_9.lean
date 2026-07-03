import Mathlib
import StacksProject_2024.Chap15.«15_60_1_1»
import StacksProject_2024.Chap15.Definition_15_75_1

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.75.9:
- primary domain: preservation of perfect objects in derived categories under derived scalar
  extension;
- sampled owner declarations:
  `K.IsPerfect`,
  `derivedTensorWithAlgebra`,
  `derivedTensorWithAlgebra_isPseudoCoherent`,
  `hasTorAmplitudeIn_derivedTensorWithAlgebra`;
- best owner abstraction: the theorem is source-facing, while the core/canonical owners are
  `K.IsPerfect` and the derived base-change object `K ⊗[A]^L[B]`;
- primitive vs. derived:
  primitive data are the perfect object `K` and the algebra map `A → B`;
  the preservation statement is derived API over those existing owners, so the public surface
  should use the owner notation rather than a raw functor application term;
- source/core/bridge triage:
  `source-facing`: perfectness is preserved by derived base change;
  `core/canonical`: `K.IsPerfect` and `derivedTensorWithAlgebra`;
  `bridge/view`: the notation `K ⊗[A]^L[B]` for the owner applied to `K`. -/

-- Proof sketch: combine Lemma `15.75.2`, which characterizes perfect objects as the
-- pseudo-coherent objects of finite tor dimension, with Lemma `15.65.12` for preservation of
-- pseudo-coherence under derived scalar extension and Lemma `15.67.13` for preservation of tor
-- amplitude, hence of finite tor dimension.
/-- Lemma 15.75.9: if `K^•` is a perfect complex of `A`-modules, then its derived base change
`K^• \otimes_A^{\mathbf L} B` is a perfect complex of `B`-modules. -/
theorem derivedTensorWithAlgebra_isPerfect
    (K : DModA) (hK : K.IsPerfect) :
    (K ⊗[A]^L[B]).IsPerfect := sorry

end

end CategoryTheory
