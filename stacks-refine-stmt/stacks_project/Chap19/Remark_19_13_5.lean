import Mathlib
import stacks_project.Chap19.Lemma_19_13_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory

noncomputable section

universe w v u

namespace CategoryTheory

attribute [local instance] HasDerivedCategory.standard

/- Domain-style sampling for Remark 19.13.5:
- primary domain: direct-sum/product comparison for shifted countable families in derived
  categories of Grothendieck abelian categories with exact countable products;
- sampled owner declarations:
  `CountableAB4Star`,
  `derivedCategory_hasCoproductsOfShape`,
  `derivedCategory_hasProductsOfShape`,
  `DerivedCategory.singleFunctor`;
- best owner abstraction: the canonical comparison morphism from the coproduct to the product of
  the shifted `ℤ`-family in `DerivedCategory A`, with ambient existence supplied by
  `derivedCategory_hasCoproductsOfShape` and `derivedCategory_hasProductsOfShape`;
- primitive data: a family `M : ℤ → A`;
- derived API: the comparison morphism
  `derivedCategory_shiftedFamilyCoproductToProduct` and the source-facing theorem that this direct
  sum is also the corresponding product.

Source/core/bridge triage:
- `source-facing`: `derivedCategory_shiftedModules_coproductToProduct_isIso`;
- `core/canonical`: `CountableAB4Star A` together with the Chapter 19 ambient owners
  `derivedCategory_hasCoproductsOfShape` and `derivedCategory_hasProductsOfShape`;
- `bridge/view`: `derivedCategory_shiftedFamily_coproductToProduct_isIso`, which expresses the
  same comparison for any Grothendieck abelian category with exact countable products. -/

section

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]

local instance derivedCategory_hasCoproducts : HasCoproducts.{w} (DerivedCategory A) := fun _ ↦
  CategoryTheory.derivedCategory_hasCoproductsOfShape

local instance derivedCategory_hasProducts : HasProducts.{w} (DerivedCategory A) := fun _ ↦
  CategoryTheory.derivedCategory_hasProductsOfShape

/-- The canonical map from the coproduct of the shifted family `M n[-n]` to its product in
`D(A)`. -/
noncomputable def derivedCategory_shiftedFamilyCoproductToProduct
    (M : ℤ → A) :
    (∐ fun n ↦ (singleFunctor A n).obj (M n)) ⟶
      ∏ᶜ fun n ↦ (singleFunctor A n).obj (M n) :=
  Pi.lift fun n ↦ Sigma.π (fun m ↦ (singleFunctor A m).obj (M m)) n

-- Proof sketch: `A` is Grothendieck abelian, so Chapter 19 gives the ambient coproduct and
-- product in `D(A)`. The extra `CountableAB4Star` hypothesis is the exact-product owner needed
-- for the source argument that the countable direct sum of the shifted family already satisfies
-- the universal property of the product.
/-- If `A` is Grothendieck abelian with exact countable products, then the canonical map
`⨁ M_n[-n] ⟶ ∏ M_n[-n]` is an isomorphism in `D(A)`. -/
theorem derivedCategory_shiftedFamily_coproductToProduct_isIso
    [CountableAB4Star A] (M : ℤ → A) :
    IsIso (derivedCategory_shiftedFamilyCoproductToProduct M) := by
  sorry

end

section

variable (R : Type u) [Ring R]

/-- Remark 19.13.5: for a family of `R`-modules `M n`, the canonical map
`⨁ M_n[-n] ⟶ ∏ M_n[-n]` is an isomorphism in `D(R)`. -/
theorem derivedCategory_shiftedModules_coproductToProduct_isIso
    (M : ℤ → ModuleCat.{u} R) :
    IsIso (derivedCategory_shiftedFamilyCoproductToProduct M) := by
  exact derivedCategory_shiftedFamily_coproductToProduct_isIso M

end

end CategoryTheory
