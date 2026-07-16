import Mathlib
import StacksProject_2024.stacks_project.Chap13.Lemma_13_16_4
import StacksProject_2024.stacks_project.Chap13.Lemma_13_33_5
import StacksProject_2024.stacks_project.Chap13.Lemma_13_34_2
import StacksProject_2024.stacks_project.Chap19.Lemma_19_13_4

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
  `DerivedCategory.singleFunctor`;
- best owner abstraction: the canonical comparison morphism from the coproduct to the product of
  the shifted `ℤ`-family in `DerivedCategory A`;
- primitive data: a family `M : ℤ → A`;
- derived API: the comparison morphism
  `derivedCategory_shiftedFamilyCoproductToProduct` and the source-facing theorem that this direct
  sum is also the corresponding product.

Source/core/bridge triage:
- `source-facing`: `derivedCategory_shiftedModules_coproductToProduct_isIso`;
- `core/canonical`: `CountableAB4Star A` together with local product/coproduct owners for the
  shifted family;
- `bridge/view`: `derivedCategory_shiftedFamily_coproductToProduct_isIso`, which expresses the
  same comparison for any Grothendieck abelian category with exact countable products. -/

section

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]

/-- Helper for Remark 19.13.5: the shifted family needs a local coproduct owner so the canonical
comparison morphism typechecks without importing the broken Chapter 13 wrapper. -/
private noncomputable instance shiftedFamilyHasCoproduct
    (M : ℤ → A) :
    HasCoproduct (fun n ↦ (DerivedCategory.singleFunctor A n).obj (M n)) := by
  -- Proof comment: recover countable coproducts in `A` from the Grothendieck hypotheses, then use
  -- the Chapter 13 countable-coproduct owner in the derived category.
  let _ : HasCountableCoproducts A := hasCountableCoproducts_of_sequentialColimits (𝒜 := A)
  let _ : CountableAB4 A := CountableAB4.of_countableAB5 A
  let _ : HasCoproductsOfShape ℤ (DerivedCategory A) :=
    derivedCategory_hasCoproductsOfShape_of_exactCountableCoproducts (𝒜 := A) ℤ
  infer_instance

/-- Helper for Remark 19.13.5: the shifted family needs a local product owner so the canonical
comparison morphism typechecks without importing the broken Chapter 19 functorial-resolution
wrapper. -/
private noncomputable instance shiftedFamilyHasProduct
    (M : ℤ → A) :
    HasProduct (fun n ↦ (DerivedCategory.singleFunctor A n).obj (M n)) := by
  -- Proof comment: reuse the earlier ambient product owner for derived categories of
  -- Grothendieck abelian categories.
  let _ : HasProductsOfShape ℤ (DerivedCategory A) :=
    derivedCategory_hasProductsOfShape (C := A) (J := ℤ)
  infer_instance

/-- The canonical map from the coproduct of the shifted family `M n[-n]` to its product in
`D(A)`. -/
noncomputable def derivedCategory_shiftedFamilyCoproductToProduct
    (M : ℤ → A) :
    (∐ fun n ↦ (DerivedCategory.singleFunctor A n).obj (M n)) ⟶
      ∏ᶜ fun n ↦ (DerivedCategory.singleFunctor A n).obj (M n) :=
  Pi.lift fun n ↦ Sigma.π (fun m ↦ (DerivedCategory.singleFunctor A m).obj (M m)) n

/-- Helper for Remark 19.13.5: the canonical comparison map has the expected `n`-th product
component. -/
lemma shiftedFamilyCoproductToProduct_comp_π
    (M : ℤ → A) (n : ℤ) :
    derivedCategory_shiftedFamilyCoproductToProduct M ≫
        Pi.π (fun m ↦ (DerivedCategory.singleFunctor A m).obj (M m)) n =
      Sigma.π (fun m ↦ (DerivedCategory.singleFunctor A m).obj (M m)) n := by
  -- Proof comment: unfold the comparison morphism and use the defining projection formula for
  -- `Pi.lift`.
  rw [derivedCategory_shiftedFamilyCoproductToProduct, Pi.lift_π]

/-- Helper for Remark 19.13.5: on the `n`-th summand and `n`-th product factor, the canonical
comparison map acts by the identity. -/
lemma shiftedFamilyCoproductToProduct_ι_comp_π_self
    (M : ℤ → A) (n : ℤ) :
    Sigma.ι (fun m ↦ (DerivedCategory.singleFunctor A m).obj (M m)) n ≫
        derivedCategory_shiftedFamilyCoproductToProduct M ≫
        Pi.π (fun m ↦ (DerivedCategory.singleFunctor A m).obj (M m)) n =
      𝟙 ((DerivedCategory.singleFunctor A n).obj (M n)) := by
  -- Proof comment: rewrite the target projection of the comparison map and then use the standard
  -- diagonal formula for the biproduct-style map `Sigma.π`.
  rw [Category.assoc, shiftedFamilyCoproductToProduct_comp_π]
  simpa using Limits.Sigma.ι_π (f := fun m ↦ (DerivedCategory.singleFunctor A m).obj (M m)) n

/-- Helper for Remark 19.13.5: after applying `H^n`, the diagonal summand-factor composite of the
canonical comparison map is still the identity on the shifted `n`-th term. -/
lemma shiftedFamilyCoproductToProduct_homology_ι_comp_π_self
    (M : ℤ → A) (n : ℤ) :
    (DerivedCategory.homologyFunctor A n).map
        (Sigma.ι (fun m ↦ (DerivedCategory.singleFunctor A m).obj (M m)) n) ≫
      (DerivedCategory.homologyFunctor A n).map
        (derivedCategory_shiftedFamilyCoproductToProduct M) ≫
      (DerivedCategory.homologyFunctor A n).map
        (Pi.π (fun m ↦ (DerivedCategory.singleFunctor A m).obj (M m)) n) =
    𝟙 ((DerivedCategory.homologyFunctor A n).obj
      ((DerivedCategory.singleFunctor A n).obj (M n))) := by
  -- Proof comment: apply the `n`-th homology functor to the already-established diagonal
  -- identity in the derived category and expand the functorial composition.
  simpa [Functor.map_comp, Category.assoc] using
    congrArg
      ((DerivedCategory.homologyFunctor A n).map)
      (shiftedFamilyCoproductToProduct_ι_comp_π_self (A := A) M n)

/-- Helper for Remark 19.13.5: under the standard identification
`H^n(M n[-n]) ≅ M n`, the diagonal homology component of the canonical comparison is the identity
on `M n`. -/
lemma shiftedFamilyCoproductToProduct_homology_ι_comp_π_self_on_module
    (M : ℤ → A) (n : ℤ) :
    (DerivedCategory.homologyFunctor A n).map
        (Sigma.ι (fun m ↦ (DerivedCategory.singleFunctor A m).obj (M m)) n) ≫
      (DerivedCategory.homologyFunctor A n).map
        (derivedCategory_shiftedFamilyCoproductToProduct M) ≫
      (DerivedCategory.homologyFunctor A n).map
        (Pi.π (fun m ↦ (DerivedCategory.singleFunctor A m).obj (M m)) n) ≫
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso A n).app (M n)).hom =
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso A n).app (M n)).hom := by
  -- Proof comment: the previous lemma identifies the threefold composite on homology with the
  -- identity, after which the target comparison to `M n` is unchanged.
  rw [shiftedFamilyCoproductToProduct_homology_ι_comp_π_self]
  simp

-- Proof sketch: once the local shifted-family coproduct and product owners are rebuilt, the
-- existing homology-conjugation route can be replayed verbatim to identify every homology map
-- with the identity on the diagonal object `M p`.
/-- If `A` is Grothendieck abelian with exact countable products, then the canonical map
`⨁ M_n[-n] ⟶ ∏ M_n[-n]` is an isomorphism in `D(A)`. -/
theorem derivedCategory_shiftedFamily_coproductToProduct_isIso
    [CountableAB4Star A] (M : ℤ → A) :
    IsIso (derivedCategory_shiftedFamilyCoproductToProduct M) := by
  -- Route correction: the ambient coproduct/product owners now typecheck again, so the remaining
  -- work is the source-proof homology comparison showing that each `H^p` of the comparison map is
  -- the identity on the unique surviving diagonal term `M p`.
  -- TODO: compare both sides with the concrete degree-`p` representative `M p` using the
  -- countable coproduct owner from Chapter 13 and a product model built from K-injective
  -- representatives of the shifted singles, then apply
  -- `derivedCategory_isIso_iff_homology_map_isIso`.
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
