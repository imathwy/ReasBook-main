import Mathlib
import stacks_project.Chap13.Lemma_13_31_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

attribute [local instance] HasDerivedCategory.standard

/-
Domain-style sampling for Lemma 19.13.4:
- primary domain: products and coproducts in derived categories of Grothendieck abelian
  categories;
- inspected owner declarations:
  * `CategoryTheory.Limits.isColimitOfHasCoproductOfPreservesColimit`
  * `CategoryTheory.Limits.isLimitOfHasProductOfPreservesLimit`
  * `CategoryTheory.derivedCategory_Q_preserves_countableCoproduct`
  * `CategoryTheory.derivedCategory_Q_preserves_product_of_kInjective`
- best owner abstraction:
  * coproduct side: `PreservesColimit (Discrete.functor K) DerivedCategory.Q`;
  * ambient existence side: `HasCoproductsOfShape J (DerivedCategory C)` and
    `HasProductsOfShape J (DerivedCategory C)`;
  * product side: the preservation owner
    `PreservesLimit (Discrete.functor I) DerivedCategory.Q`, with the fan witness recovered by
    `isLimitOfHasProductOfPreservesLimit`.
- primitive data:
  * a family of complexes `K` or `I`;
  * K-injectivity on the product side.
- derived API:
  * the `IsColimit` witness in `DerivedCategory C`;
  * the `PreservesLimit` witness for termwise products of K-injective complexes, and the induced
    `IsLimit` witness in `DerivedCategory C`;
  * the induced shape-wise coproduct and product structures on `DerivedCategory C`.

Source/core/bridge triage:
- source-facing:
  `derivedCategory_coproduct_isColimit_of_termwise_directSums` and
  `derivedCategory_product_isLimit_of_termwise_products_of_kInjective`;
- core/canonical:
  `PreservesColimit (Discrete.functor K) DerivedCategory.Q`,
  `PreservesLimit (Discrete.functor I) DerivedCategory.Q`,
  `HasCoproductsOfShape J (DerivedCategory C)`, and
  `HasProductsOfShape J (DerivedCategory C)`;
- bridge/view:
  `derivedCategory_has_directSums_and_products`, which packages the two ambient owner instances
  into the source wording of the Stacks item.
-/

/-- Exact coproducts in a Grothendieck abelian category make the localization functor to the
derived category preserve termwise coproducts of cochain complexes. -/
theorem derivedCategory_Q_preserves_coproduct {J : Type w}
    (K : J → CochainComplex C ℤ) :
    PreservesColimit (Discrete.functor K) DerivedCategory.Q := by
  sorry

-- Proof sketch: take the categorical coproduct `∐ K` in `CochainComplex C ℤ`, which is computed
-- degreewise because limits and colimits in complexes are created by the evaluation functors. For
-- a K-injective target complex, morphisms from `∐ K` in the derived category are identified with
-- the product of the morphism groups from each `K j`, so the image of this termwise coproduct
-- under `DerivedCategory.Q` satisfies the universal property of a coproduct in `D(C)`.
/-- The image in the derived category of the termwise direct sum of a family of complexes is a
coproduct of the corresponding family of derived-category objects. -/
noncomputable def derivedCategory_coproduct_isColimit_of_termwise_directSums {J : Type w}
    (K : J → CochainComplex C ℤ) :
    IsColimit
      (Cofan.mk
        (DerivedCategory.Q.obj (∐ K))
        (fun j ↦ DerivedCategory.Q.map (Sigma.ι K j))) := by
  letI := derivedCategory_Q_preserves_coproduct K
  exact Limits.isColimitOfHasCoproductOfPreservesColimit DerivedCategory.Q K

-- Proof sketch: form the categorical product `∏ᶜ I` of a family of K-injective complexes, which
-- is computed degreewise in the category of complexes. Lemma 13.31.5 identifies morphisms in the
-- derived category into each `I j` with homotopy classes of maps into the chosen K-injective
-- representative, so the termwise product retains the universal property of a product after
-- applying `DerivedCategory.Q`.
/-- The image in the derived category of the termwise product of a family of K-injective complexes
is a product of the corresponding family of derived-category objects. -/
noncomputable def derivedCategory_product_isLimit_of_termwise_products_of_kInjective {J : Type w}
    (I : J → CochainComplex C ℤ) [∀ j, (I j).IsKInjective] :
    IsLimit
      (Fan.mk
        (DerivedCategory.Q.obj (∏ᶜ I))
        (fun j ↦ DerivedCategory.Q.map (Pi.π I j))) := by
  letI := derivedCategory_Q_preserves_product_of_kInjective I
  exact isLimitOfHasProductOfPreservesLimit DerivedCategory.Q I

-- Proof sketch: the Grothendieck hypothesis gives arbitrary coproducts and products in `C`, hence
-- termwise coproducts and products of cochain complexes. Coproducts descend directly to the
-- derived category because morphisms from a coproduct into a K-injective complex are computed
-- termwise, while products are computed by first replacing each object with a K-injective
-- representative and then applying the corresponding hom-computation for termwise products.
/-- A Grothendieck abelian category has arbitrary coproducts in its derived category. -/
theorem derivedCategory_hasCoproductsOfShape {J : Type w} :
    HasCoproductsOfShape J (DerivedCategory C) := by
  sorry

/-- A Grothendieck abelian category has arbitrary products in its derived category. -/
theorem derivedCategory_hasProductsOfShape {J : Type w} :
    HasProductsOfShape J (DerivedCategory C) := by
  sorry

/-- Lemma 19.13.4: if `C` is a Grothendieck abelian category, then `D(C)` has direct sums and
products. -/
theorem derivedCategory_has_directSums_and_products {J : Type w} :
    HasCoproductsOfShape J (DerivedCategory C) ∧ HasProductsOfShape J (DerivedCategory C) :=
  ⟨derivedCategory_hasCoproductsOfShape, derivedCategory_hasProductsOfShape⟩

end

end CategoryTheory
