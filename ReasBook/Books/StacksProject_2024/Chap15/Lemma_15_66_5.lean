import Mathlib
import Mathlib.Algebra.Category.ModuleCat.AB
import StacksProject_2024.Chap13.Situation_13_15_1
import StacksProject_2024.Chap15.Definition_15_59_13
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap19.Lemma_19_13_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local instance (A : Type u) :
    HasProductsOfShape A (DerivedCategory (ModuleCat.{u} R)) :=
  derivedCategory_hasProductsOfShape

-- Domain-style sampling for pseudo-coherence via tensor-product/product comparison:
-- - primary domain: source-facing product-comparison maps for the functor
--   `Q ↦ Q[0] ⊗_R^L K`;
-- - inspected declarations:
--   * `ModuleCat.single0Functor`
--   * `CategoryTheory.derivedTensorProduct`
--   * `Limits.piComparison`
--   * constant-family specializations of `piComparison` already used elsewhere in Chapter 15;
-- - best owner abstraction:
--   in this module-category specialization, the canonical construction is the comparison morphism
--   `piComparison` for `ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj`; the
--   constant-family and free-family maps in the source are specializations of this owner.
--
-- Source/core/bridge triage:
-- - `source-facing`: the three product-comparison conditions and the TFAE statements phrased in
--   terms of those maps;
-- - `core/canonical`: `piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj)`;
-- - `bridge/view`: the constant-family and `R^A` specializations of that `piComparison`.
--
-- Primitive data is the composite functor `ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj`;
-- the comparison maps and their homology conditions are derived API.

-- Proof sketch: represent `K` by a bounded-above termwise finite free complex, compute derived
-- tensor products by ordinary tensor products with that complex, and use Algebra,
-- Proposition `10.89.3` together with the description of products in `D(R)` to identify the
-- three product-preservation conditions.
/-- Commutative-ring specialization of Stacks Lemma 15.66.5 (1): for a bounded-above derived
`R`-complex `K`, the following are equivalent: `K` is pseudo-coherent; for every family of
`R`-modules the canonical product comparison for `Q ↦ Q[0] ⊗_R^{\mathbf L} K` is an isomorphism;
the same holds for constant families; and the same holds for free families `R^A`. -/
theorem boundedAbove_isPseudoCoherent_tfae_derivedTensorProduct_preservesProducts
    (K : D⁻((ModuleCat.{u} R))) :
    List.TFAE [
      K.obj.IsPseudoCoherent,
      ∀ {A : Type u} (Q : A → ModuleCat.{u} R),
        IsIso (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj) Q),
      ∀ (Q : ModuleCat.{u} R) (A : Type u),
        IsIso (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj) fun _ : A ↦ Q),
      ∀ A : Type u,
        IsIso (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj)
          fun _ : A ↦ ModuleCat.of R R)
    ] := sorry

-- Proof sketch: the forward implications are obtained from the pseudo-coherent finite free model
-- as above. For the converse, apply the free-family criterion to the top nonvanishing cohomology
-- module, deduce finiteness from Algebra, Proposition `10.89.2`, kill that cohomology by a finite
-- free complex, and conclude by induction using Lemmas `15.65.2` and `15.65.5`.
/-- Commutative-ring specialization of Stacks Lemma 15.66.5 (2): given `m ∈ ℤ` and a bounded-
above derived `R`-complex `K`, the following are equivalent: `K` is `m`-pseudo-coherent; for
every family of `R`-modules the canonical product comparison for `Q ↦ Q[0] ⊗_R^{\mathbf L} K`
induces cohomology isomorphisms in degrees `> m` and an epimorphism in degree `m`; the same
holds for constant families; and the same holds for free families `R^A`. -/
theorem boundedAbove_isMPseudoCoherent_tfae_derivedTensorProduct_preservesProductsUpTo
    (K : D⁻((ModuleCat.{u} R))) (m : ℤ) :
    List.TFAE [
      K.obj.IsMPseudoCoherent m,
      ∀ {A : Type u} (Q : A → ModuleCat.{u} R),
        (∀ i : ℤ, m < i →
          IsIso ((H^i).map
            (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj) Q))) ∧
          Epi ((H^m).map
            (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj) Q)),
      ∀ (Q : ModuleCat.{u} R) (A : Type u),
        (∀ i : ℤ, m < i →
          IsIso ((H^i).map
            (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj)
              fun _ : A ↦ Q))) ∧
          Epi ((H^m).map
            (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj)
              fun _ : A ↦ Q)),
      ∀ A : Type u,
        (∀ i : ℤ, m < i →
          IsIso ((H^i).map
            (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj)
              fun _ : A ↦ ModuleCat.of R R))) ∧
          Epi ((H^m).map
            (piComparison (ModuleCat.single0Functor ⋙ derivedTensorProduct K.obj)
              fun _ : A ↦ ModuleCat.of R R))
    ] := sorry

end

end CategoryTheory
