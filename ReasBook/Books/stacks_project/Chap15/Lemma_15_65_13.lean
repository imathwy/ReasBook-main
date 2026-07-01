import Mathlib
import stacks_project.Chap15.Lemma_15_65_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open scoped DerivedTensorWithAlgebra

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "Ext" => ModuleCat.extendScalars (algebraMap A B)

/- Domain-style sampling for Lemma 15.65.13:
- primary domain: pseudo-coherent modules under flat scalar extension, viewed through their
  degree-zero images in the derived category;
- sampled owner declarations:
  `ModuleCat.single0Functor`,
  `DerivedCategory.IsMPseudoCoherent`,
  `derivedTensorWithAlgebra_isMPseudoCoherent`,
  `derivedTensorWithAlgebra_isPseudoCoherent`;
- best owner abstraction: the core/canonical owner is derived scalar extension
  `derivedTensorWithAlgebra A B : D(A) ⥤ D(B)`, while the module-level theorems below are flat
  `bridge/view` consequences obtained only after identifying `M[0] ⊗[A]^L B` with ordinary scalar
  extension of `M` in degree `0`;
- primitive vs. derived:
  primitive data are the ring map `A → B`, the flatness hypothesis, and the module `M` viewed as
  `(ModuleCat.single0Functor : ModuleCat A ⥤ DerivedCategory (ModuleCat A)).obj M : D(A)`;
  the ordinary module pseudo-coherence conclusions are derived API obtained from the owner
  theorems in Lemma `15.65.12` plus the flat degree-zero comparison;
- layer: `bridge/view`. The public statement should therefore be a flat bridge from the derived
  owner theorem, not an arbitrary ordinary base-change theorem. -/

-- Proof sketch: `M.IsMPseudoCoherent m` is definitionally `m`-pseudo-coherence of the degree-zero
-- owner object `(ModuleCat.single0Functor.obj M)`. Apply
-- `derivedTensorWithAlgebra_isMPseudoCoherent`, then use flatness of `A → B` to identify the
-- derived base change of that degree-zero object with the degree-zero object of `Ext.obj M`.
/-- Lemma 15.65.13: for a flat ring map `A → B`, if an `A`-module `M` is `m`-pseudo-coherent,
then its scalar extension `M \otimes_A B` is `m`-pseudo-coherent as a `B`-module. -/
theorem isMPseudoCoherent_extendScalars
    (hflat : (algebraMap A B).Flat) (M : ModuleCat A) (m : ℤ)
    (hM : M.IsMPseudoCoherent m) :
    ((Ext).obj M).IsMPseudoCoherent m := sorry

-- Proof sketch: apply the previous theorem for every `m : ℤ`, or equivalently specialize
-- `derivedTensorWithAlgebra_isPseudoCoherent` and use the same flat degree-zero identification.
/-- For a flat ring map `A → B`, ordinary scalar extension preserves pseudo-coherent modules. -/
theorem isPseudoCoherent_extendScalars
    (hflat : (algebraMap A B).Flat) (M : ModuleCat A)
    (hM : M.IsPseudoCoherent) :
    ((Ext).obj M).IsPseudoCoherent := sorry

end

end CategoryTheory
