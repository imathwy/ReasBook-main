import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_19_13_1 (from Chap19) -/
open CategoryTheory.Limits
open Opposite

universe v u

namespace CategoryTheory

/- Domain-style sampling for Lemma 19.13.1:
- primary domain: representability of `Type`-valued presheaves via adjointness in category theory;
- sampled owner declarations:
  `Functor.IsRepresentable`,
  `Functor.IsRightAdjoint`,
  `isRightAdjoint_of_preservesLimits_of_isCoseparating`,
  `Functor.representable_preservesLimits`;
- best owner abstraction: `F.IsRightAdjoint` for `F : Aᵒᵖ ⥤ Type v`;
- primitive data: the presheaf `F`;
- derived API: representability and preservation of limits.

Source/core/bridge triage:
- `source-facing`: the Stacks statement that a presheaf is representable iff it commutes with
  colimits, equivalently preserves limits;
- `core/canonical`: `F.IsRightAdjoint`;
- `bridge/view`: the two thin theorems below passing between `F.IsRightAdjoint`,
  `F.IsRepresentable`, and `PreservesLimits F`.

The previous file stored the source statement directly as a standalone theorem with no connection
to the owner abstraction. The refined file keeps the source-facing theorem, but factors the proof
through the canonical adjointness owner already used upstream in Chapter 4 and mathlib.
-/

section

variable {A : Type u} [Category.{v} A]

/-- A `Type`-valued presheaf on `A` that is a right adjoint is representable. -/
theorem isRepresentable_of_isRightAdjoint (F : Aᵒᵖ ⥤ Type v) [F.IsRightAdjoint] :
    F.IsRepresentable := by
  let adj : F.leftAdjoint ⊣ F := Adjunction.ofIsRightAdjoint F
  refine ⟨(F.leftAdjoint.obj PUnit).unop, ⟨?_⟩⟩
  refine
    { homEquiv := fun {X} ↦
        { toFun := fun f ↦ Equiv.punitArrowEquiv _ ((adj.homEquiv PUnit (op X)) f.op)
          invFun := fun x ↦
            ((adj.homEquiv PUnit (op X)).symm ((Equiv.punitArrowEquiv _).symm x)).unop
          left_inv := ?_
          right_inv := ?_ }
      homEquiv_comp := ?_ }
  · intro f
    simp
  · intro x
    simp
  · intro X X' f g
    exact congrFun (adj.homEquiv_naturality_right g.op f.op) PUnit.unit

end

section

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]

/-- A `Type`-valued presheaf on the opposite of a Grothendieck abelian category that preserves
limits is a right adjoint. -/
theorem isRightAdjoint_of_preservesLimits (F : Aᵒᵖ ⥤ Type v) [PreservesLimits F] :
    F.IsRightAdjoint :=
  isRightAdjoint_of_preservesLimits_of_isCoseparating (isCoseparator_coseparator (Aᵒᵖ)) F

/-- Lemma 19.13.1: a set-valued functor on the opposite of a Grothendieck abelian category is
representable if and only if it commutes with colimits in `A`, equivalently if it preserves
limits as a functor `Aᵒᵖ ⥤ Type v`. -/
theorem isRepresentable_iff_preservesLimits (F : Aᵒᵖ ⥤ Type v) :
    F.IsRepresentable ↔ PreservesLimits F := by
  constructor
  · intro
    infer_instance
  · intro
    let _ : F.IsRightAdjoint := isRightAdjoint_of_preservesLimits F
    exact isRepresentable_of_isRightAdjoint F

end

end CategoryTheory

/-! ### Lemma_19_13_2 (from Chap19) -/
open CategoryTheory.Limits

universe w v u

namespace CategoryTheory

variable (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]

/- Domain-style sampling for Lemma 19.13.2:
- primary domain: existence of products and limits in Grothendieck abelian categories;
- sampled owner declarations:
  `HasProducts`,
  `hasProductsOfShape_of_hasProducts`,
  `AB4Star`,
  `IsGrothendieckAbelian.hasLimits`;
- best owner abstraction: the source-facing owner for the lemma is `HasProducts A`, while the
  stronger core justification is the instance `IsGrothendieckAbelian.hasLimits`;
- primitive data: an abelian category equipped with `IsGrothendieckAbelian`;
- derived API: `HasProductsOfShape J A` for each indexing type `J`, and more generally all small
  limits in `A`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma that a Grothendieck abelian category has `AB3*`, i.e.
  the canonical product structure `HasProducts A`;
- `core/canonical`: the stronger owner instance `IsGrothendieckAbelian.hasLimits`;
- `bridge/view`: the standard specialization `hasProductsOfShape_of_hasProducts` from global
  products to products of a fixed shape.

This item adds no new theorem: the faithful refinement is to recall the canonical source-facing
owner `HasProducts` and use `IsGrothendieckAbelian.hasLimits` only as justification, rather than
shifting the public statement to the stronger all-limits instance. -/

/- Lemma 19.13.2: a Grothendieck abelian category has `AB3*`, i.e. it has products; this is
the canonical structure `HasProducts A`, justified upstream by the stronger instance
`IsGrothendieckAbelian.hasLimits`. -/
recall HasProducts

end CategoryTheory

/-! ### Remark_19_13_3 (from Chap19) -/
open CategoryTheory.Localization
open CategoryTheory.DerivedCategory
open CategoryTheory.Limits

universe w v u

namespace CategoryTheory

/- Domain-style sampling for Remark 19.13.3:
- primary domain: derived categories of Grothendieck abelian categories, localized at
  quasi-isomorphisms;
- sampled owner declarations:
  `Localization.HasSmallLocalizedHom`,
  `DerivedCategory.Qh`,
  `hasSmallLocalizedHom_of_quasiIso_to_isKInjective`,
  `CochainComplex.exists_functorial_kInjective_resolution`;
- best owner abstraction: smallness is controlled by the localization functor `DerivedCategory.Qh`,
  while the Grothendieck-specific K-injective resolution statement is already owned by Chapter 19;
- primitive data: the Grothendieck-abelian hypothesis on `A`;
- derived API: the homotopy-category presentation of small morphism types in `D(A)`.

Source/core/bridge triage:
- `source-facing`: `derived_hom_small_of_isGrothendieckAbelian`;
- `core/canonical`: `HasSmallLocalizedHom`, `DerivedCategory.Q`, `DerivedCategory.Qh`, and the
  Chapter 13 bridge theorem `hasSmallLocalizedHom_of_quasiIso_to_isKInjective`;
- `bridge/view`: the theorem below transports Chapter 13 smallness from complexes to the
  homotopy-category localization through `quotientCompQhIso`. -/

/- Reuse the Chapter 19 Grothendieck-abelian K-injective resolution theorem directly rather than
restating it with a local wrapper. -/
#check CochainComplex.exists_functorial_kInjective_resolution

section

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]

/-- Remark 19.13.3: in a Grothendieck abelian category, the localization of the homotopy category
at quasi-isomorphisms has `w`-small Hom-types, so morphisms in the derived category are sets. -/
theorem derived_hom_small_of_isGrothendieckAbelian
    (K L : HomotopyCategory A (ComplexShape.up ℤ)) :
    HasSmallLocalizedHom.{w} (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) K L := by
  letI : HasDerivedCategory.{max u v} A := HasDerivedCategory.standard A
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective L
  rw [Localization.hasSmallLocalizedHom_iff
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) DerivedCategory.Qh]
  letI : HasSmallLocalizedHom.{w}
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) K L :=
    by
      obtain ⟨J, -, hKinj⟩ := CochainComplex.exists_functorial_kInjective_resolution A
      let _ : (J.toFunctor.obj L).IsKInjective := hKinj L
      exact _root_.hasSmallLocalizedHom_of_quasiIso_to_isKInjective K
        (J.ι.app L) (J.quasiIso_app L)
  let h :=
    Localization.small_of_hasSmallLocalizedHom
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) DerivedCategory.Q K L
  exact (small_congr
    (Iso.homCongr ((DerivedCategory.quotientCompQhIso A).app K)
      ((DerivedCategory.quotientCompQhIso A).app L))).2 h

end

end CategoryTheory

/-! ### Lemma_19_13_4 (from Chap19) -/
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

/-! ### Remark_19_13_5 (from Chap19) -/
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

/-! ### Lemma_19_13_6 (from Chap19) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe w u₁ u₂ v₁ v₂

namespace CategoryTheory

section

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Abelian A]
  [Category.{v₂} B] [Abelian B]

/-- The standard chosen derived categories used for this item. -/
local instance additiveFunctorDerivedSource_hasDerivedCategory :
    HasDerivedCategory.{max u₁ v₁} A :=
  HasDerivedCategory.standard A

/-- The standard chosen derived categories used for this item. -/
local instance additiveFunctorDerivedTarget_hasDerivedCategory :
    HasDerivedCategory.{max u₂ v₂} B :=
  HasDerivedCategory.standard B

-- Proof sketch: choose the functorial K-injective resolution on `A` provided by the
-- Grothendieck hypothesis, and use that every K-injective complex computes the right derived
-- functor of `F.mapHomologicalComplex (ComplexShape.up ℤ)` after localization to `D(B)`.
/-- The cochain-level functor induced by an additive functor out of a Grothendieck abelian
category admits a total right derived functor. -/
theorem mapHomologicalComplexQ_hasRightDerivedFunctor
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A] :
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) := sorry

attribute [local instance] mapHomologicalComplexQ_hasRightDerivedFunctor

/-- The total right derived functor `RF : D(A) ⥤ D(B)` attached to an additive functor
`F : A ⥤ B`. -/
noncomputable abbrev additiveFunctorTotalRightDerived
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A] :
    DerivedCategory A ⥤ DerivedCategory B :=
  (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).totalRightDerived
    DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))

-- Proof sketch: choose a Milnor triangle for `K` built from a product of K-injective complexes
-- representing the stages of `Ksys`. The right derived functor is computed on those
-- K-injective representatives by applying `F`, and the hypothesis that `F` preserves countable
-- products identifies the image of the Milnor difference map with the Milnor difference map of
-- the stagewise image system. Exact countable products in `B` then identify the termwise product
-- complexes with products in `D(B)`, so the image triangle exhibits `RF(K)` as the derived limit
-- of `(RF(K_n))`.
/-- Lemma 19.13.6: let `F : A ⥤ B` be an additive functor of abelian categories. Assume `A` is a
Grothendieck abelian category, `B` has exact countable products, and `F` commutes with countable
products. Then the total right derived functor `RF : D(A) ⥤ D(B)` carries a derived limit of a
sequential inverse system in `D(A)` to a derived limit of the stagewise image system in `D(B)`. -/
theorem additiveFunctor_totalRightDerived_preservesDerivedLimit
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A]
    [HasCountableProducts B] [CountableAB4Star B]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    {Ksys : ℕᵒᵖ ⥤ DerivedCategory A} {K : DerivedCategory A}
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit
      (Ksys ⋙ additiveFunctorTotalRightDerived F)
      ((additiveFunctorTotalRightDerived F).obj K) := sorry

end

end CategoryTheory

/-! ### Lemma_19_13_7 (from Chap19) -/
open CategoryTheory
open CategoryTheory.Limits
open FilteredObject
open FilteredComplex

noncomputable section

universe w v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Lemma 19.13.7:
- primary domain: filtered cochain complexes in a Grothendieck abelian category and their
  K-injective replacements;
- sampled owner declarations:
  `FilteredComplex`,
  `FilteredComplex.underlying`,
  `FilteredComplex.stage`,
  `FilteredComplex.stageMapOfLE`,
  `FilteredObject.quotientFunctor`;
- best owner abstraction: the canonical filtered-complex owner `FilteredComplex 𝒜`, together with
  the stage, quotient, and subquotient bridge constructions obtained from the filtered-object
  functors lifted along `mapHomologicalComplex`;
- primitive data: a filtered-complex morphism `j : K ⟶ J`;
- derived API retained here: quotient and subquotient complexes and the induced comparison maps;
- source/core/bridge triage:
  `source-facing`: `exists_filteredComplex_kInjectiveReplacement`;
  `core/canonical`: `FilteredComplex 𝒜`, `underlying`, `stage`, `stageMapOfLE`, and
  `quotientFunctor`;
  `bridge/view`: `FilteredComplex.quotient`, `FilteredComplex.quotientMap`,
    `FilteredComplex.underlyingToQuotient`, `FilteredComplex.subquotient`, and
    `FilteredComplex.subquotientMap`. -/

-- Proof sketch: apply Theorem 19.12.6 functorially to the underlying complex and to each stage
-- complex `F^p K^•`, then correct the comparison maps by acyclic K-injective summands so that the
-- stagewise maps become termwise monomorphisms inside one filtered target complex. Products of
-- injectives remain injective in a Grothendieck abelian category, and the standard two-out-of-three
-- arguments for K-injective complexes and long exact cohomology sequences give the quotient and
-- subquotient quasi-isomorphisms and K-injectivity statements.
/-- Lemma 19.13.7: every filtered complex in a Grothendieck abelian category admits a morphism to
a filtered complex whose terms, stage complexes, quotient complexes, and filtration-subquotient
complexes are injective and K-injective in the appropriate sense, and such that the induced maps
on the underlying complex, every stage, every quotient, and every filtration subquotient are
quasi-isomorphisms. -/
theorem exists_filteredComplex_kInjectiveReplacement
    [IsGrothendieckAbelian.{w} 𝒜]
    (K : FilteredComplex 𝒜) :
    ∃ (J : FilteredComplex 𝒜) (j : K ⟶ J),
      (∀ n : ℤ, Injective (J.underlying.X n)) ∧
        (∀ p n : ℤ, Injective ((J.stage p).X n)) ∧
        (∀ p n : ℤ, Injective ((J.quotient p).X n)) ∧
        (∀ {p p' : ℤ} (hpp' : p ≤ p') (n : ℤ),
          Injective ((J.subquotient hpp').X n)) ∧
        J.underlying.IsKInjective ∧
        (∀ p : ℤ, (J.stage p).IsKInjective) ∧
        (∀ p : ℤ, (J.quotient p).IsKInjective) ∧
        (∀ {p p' : ℤ} (hpp' : p ≤ p'), (J.subquotient hpp').IsKInjective) ∧
        QuasiIso ((FilteredObject.forget.mapHomologicalComplex (ComplexShape.up ℤ)).map j) ∧
        (∀ p : ℤ, QuasiIso (((stageFunctor p).mapHomologicalComplex (ComplexShape.up ℤ)).map j)) ∧
        (∀ p : ℤ, QuasiIso (FilteredComplex.quotientMap j p)) ∧
        (∀ {p p' : ℤ} (hpp' : p ≤ p'), QuasiIso (FilteredComplex.subquotientMap j hpp')) := sorry

end CategoryTheory

/-! ### Remark_19_13_8 (from Chap19) -/
open CategoryTheory
open CategoryTheory.Limits
open FilteredComplex

noncomputable section

universe t w v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [LocallySmall 𝒜] [WellPowered 𝒜]
  [HasWidePullbacks 𝒜] [HasCoproducts 𝒜] [InitialMonoClass 𝒜] [IsGrothendieckAbelian.{w} 𝒜]
  [HasDerivedCategory.{t} 𝒜]

/-
Domain-style sampling for Remark 19.13.8:
- primary domain: filtered cochain complexes and their associated cohomological spectral sequences
  in an abelian category, together with derived-category `Ext`;
- sampled owner declarations:
  `FilteredComplex.underlying`,
  `FilteredComplex.stage`,
  `FilteredComplex.gradedPiece`,
  `CategoryTheory.IsAssociatedToFilteredComplex`,
  `FilteredComplex.convergesToCohomology`;
- best owner abstraction: the Chapter 12 owner `FilteredComplex 𝒜` together with the associated
  spectral-sequence owner predicate `IsAssociatedToFilteredComplex` and the convergence owner
  `FilteredComplex.convergesToCohomology`;
- primitive data: a filtered complex `K : FilteredComplex 𝒜`, a derived object `M`, and an
  auxiliary filtered `Hom` complex together with its associated spectral sequence;
- derived API: the induced `Ext` maps and the eventual vanishing/stability hypotheses on stagewise
  `Ext`;
- source/core/bridge triage:
  `source-facing`: `EventualDerivedExtVanishesAbove`, `EventualDerivedExtStabilizesBelow`, and
    `filteredComplexExtSpectralSequence_exists`;
  `core/canonical`: `FilteredComplex 𝒜`, `IsAssociatedToFilteredComplex`, and
  `FilteredComplex.convergesToCohomology`;
  `bridge/view`: the explicit auxiliary filtered `Hom` complex appearing in
    `filteredComplexExtSpectralSequence_exists`, together with `derivedExtGroup` and
    `derivedExtGroupMap`. -/

local notation "FilteredComplex" => CategoryTheory.FilteredComplex 𝒜
local notation "AbFilteredComplex" => CategoryTheory.FilteredComplex AddCommGrpCat
local notation "D" => DerivedCategory 𝒜

/-- The derived `Ext` group `Ext^n(M, X)`, written as morphisms `M ⟶ X[n]` in the derived
category. -/
abbrev derivedExtGroup (M X : D) (n : ℤ) : AddCommGrpCat :=
  AddCommGrpCat.of (M ⟶ X⟦n⟧)

-- Proof sketch: composition in the shifted derived category is additive in the source morphism,
-- so postcomposition with the shifted map `f⟦n⟧'` defines an additive homomorphism.
/-- Postcomposition with a morphism in the shifted derived category is additive on derived
`Ext` groups. -/
theorem derivedExtGroupMap_add
    (M : D) {X Y : D} (f : X ⟶ Y) (n : ℤ)
    (α β : M ⟶ X⟦n⟧) :
    (α + β) ≫ (shiftFunctor (DerivedCategory 𝒜) n).map f =
      α ≫ (shiftFunctor (DerivedCategory 𝒜) n).map f +
        β ≫ (shiftFunctor (DerivedCategory 𝒜) n).map f := sorry

/-- The map on derived `Ext` groups induced by a morphism `X ⟶ Y` in the second variable. -/
def derivedExtGroupMap
    (M : D) {X Y : D} (f : X ⟶ Y) (n : ℤ) :
    derivedExtGroup M X n ⟶ derivedExtGroup M Y n :=
  AddCommGrpCat.ofHom <|
    AddMonoidHom.mk'
      (fun α ↦ α ≫ (shiftFunctor (DerivedCategory 𝒜) n).map f)
      (derivedExtGroupMap_add M f n)

/-- For every total degree, the groups `Ext^n(M, F^p K)` vanish for all sufficiently large
filtration indices `p`. -/
def EventualDerivedExtVanishesAbove (M : D) (K : FilteredComplex) : Prop :=
  ∀ n : ℤ, ∃ p₀ : ℤ, ∀ ⦃p : ℤ⦄, p₀ ≤ p →
    IsZero (derivedExtGroup M (DerivedCategory.Q.obj (K.stage p)) n)

/-- For every total degree, the canonical maps `Ext^n(M, F^p K) → Ext^n(M, K)` are
isomorphisms for all sufficiently small filtration indices `p`. -/
def EventualDerivedExtStabilizesBelow (M : D) (K : FilteredComplex) : Prop :=
  ∀ n : ℤ, ∃ p₁ : ℤ, ∀ ⦃p : ℤ⦄, p ≤ p₁ →
    IsIso (derivedExtGroupMap M (DerivedCategory.Q.map (K.stageInclusion p)) n)

-- Proof sketch: choose a filtered K-injective replacement `K^• ⟶ J^•` as in Lemma 19.13.7 and a
-- complex representing `M`; form the filtered Hom complex `Hom^•(M^•, J^•)` with filtration by
-- the stages `Hom^•(M^•, F^p J^•)`. Apply the filtered-complex spectral sequence from Chapter 12
-- to that filtered Hom complex, identify its `E₁`-page with `Ext^{p+q}(M, gr^p K)`, and use
-- Lemma 12.24.13 together with the two eventual Ext hypotheses to obtain boundedness and
-- convergence to `Ext^{p+q}(M, K)`.
/-- Remark 19.13.8: for a Grothendieck abelian category `𝒜`, a filtered complex `K^•`, and an
object `M` of `D(𝒜)`, there is a spectral sequence in abelian groups with
`E₁^{p,q} = Ext^{p + q}(M, gr^p(K^•))`; moreover, if `Ext^n(M, F^p K)` vanishes for `p ≫ 0` and
the canonical map `Ext^n(M, F^p K) → Ext^n(M, K)` is an isomorphism for `p ≪ 0`, then this
spectral sequence is bounded and converges to `Ext^{p + q}(M, K)`. The source-facing bridge in
this file is the explicit auxiliary filtered `Hom` complex together with the canonical owner
predicate `IsAssociatedToFilteredComplex`, the Chapter `12` convergence owner
`FilteredComplex.convergesToCohomology`, and the page-one and abutment comparison isomorphisms. -/
theorem filteredComplexExtSpectralSequence_exists
    (M : D) (K : FilteredComplex) :
    ∃ (filteredHomComplex : AbFilteredComplex)
      (E : CohomologicalSpectralSequence AddCommGrpCat 0)
      (_ : IsAssociatedToFilteredComplex filteredHomComplex E)
      (pageOneIso :
        ∀ p q : ℤ,
          (E.page 1).X (p, q) ≅
            derivedExtGroup M (DerivedCategory.Q.obj (K.gradedPiece p)) (p + q))
      (abutmentIso :
        ∀ n : ℤ,
          filteredHomComplex.underlying.homology n ≅
            derivedExtGroup M (DerivedCategory.Q.obj K.underlying) n),
      (EventualDerivedExtVanishesAbove M K →
        EventualDerivedExtStabilizesBelow M K →
        CohomologicalSpectralSequence.IsBounded E) ∧
      (EventualDerivedExtVanishesAbove M K →
        EventualDerivedExtStabilizesBelow M K →
        filteredHomComplex.convergesToCohomology E) := sorry

end CategoryTheory

/-! ### Remark_19_13_9 (from Chap19) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe t w v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [LocallySmall 𝒜] [WellPowered 𝒜]
  [HasWidePullbacks 𝒜] [HasCoproducts 𝒜] [InitialMonoClass 𝒜] [IsGrothendieckAbelian.{w} 𝒜]
  [HasDerivedCategory.{t} 𝒜]

local notation "D" => DerivedCategory 𝒜
local notation "single0" => DerivedCategory.singleFunctor 𝒜 (0 : ℤ)
local notation "H" => DerivedCategory.homologyFunctor 𝒜

/-- The bounded-below condition on an object of `D(\mathcal A)`. -/
def DerivedCategoryIsBoundedBelow (K : D) : Prop :=
  ∃ n : ℤ, ∀ i : ℤ, i < n →
    IsZero ((H i).obj K)

/-- The bounded-above condition on an object of `D(\mathcal A)`. -/
def DerivedCategoryIsBoundedAbove (K : D) : Prop :=
  ∃ n : ℤ, ∀ i : ℤ, n < i →
    IsZero ((H i).obj K)

/-- A renumbered cohomological spectral sequence computing `Ext^*(M, K)` from the cohomology
objects `H^j(K)` of an object `K` in the derived category. -/
structure DerivedExtCohomologySpectralSequenceData (M K : D) where
  /-- The spectral sequence starting on the `E₂`-page. -/
  spectralSequence : E₂CohomologicalSpectralSequence AddCommGrpCat
  /-- The `E₂`-page is identified with the groups `Ext^i(M, H^j(K))`, where `H^j(K)` is viewed as
  an object of the derived category concentrated in degree `0`. -/
  pageTwoIso :
    ∀ i j : ℤ,
      (spectralSequence.page 2).X (i, j) ≅
        derivedExtGroup M ((single0).obj ((H j).obj K)) i
  /-- The chosen abutment objects of the spectral sequence. -/
  abutment : ℤ → AddCommGrpCat
  /-- The abutment identifies with the groups `Ext^n(M, K)`. -/
  abutmentIso :
    ∀ n : ℤ,
      abutment n ≅ derivedExtGroup M K n
  /-- If `M ∈ D^-(𝒜)` and `K ∈ D^+(𝒜)`, then the spectral sequence is bounded. -/
  bounded_of_boundedness :
    DerivedCategoryIsBoundedAbove M →
      DerivedCategoryIsBoundedBelow K →
      CohomologicalSpectralSequence.IsBounded spectralSequence

/-- A cohomological spectral sequence computing `Ext^*(M, Q.obj K)` from the terms `K^p` of a
bounded-below cochain complex `K^•`, using the stupid filtration `σ_{\ge p}`. -/
structure DerivedExtTermwiseSpectralSequenceData (M : D) (K : CochainComplex 𝒜 ℤ) where
  /-- The filtered complex of abelian groups producing the spectral sequence. -/
  filteredComplex : FilteredComplex AddCommGrpCat
  /-- The spectral sequence starting on the `E₁`-page. -/
  spectralSequence : CohomologicalSpectralSequence AddCommGrpCat 0
  /-- The chosen spectral sequence is associated to the filtered complex. -/
  associated : IsAssociatedToFilteredComplex filteredComplex spectralSequence
  /-- The `E₁`-page is identified with the groups `Ext^q(M, K^p)`, with `K^p` placed in degree
  `0` of the derived category. -/
  pageOneIso :
    ∀ p q : ℤ,
      (spectralSequence.page 1).X (p, q) ≅
        derivedExtGroup M ((single0).obj (K.X p)) q
  /-- The abutment cohomology of the filtered complex identifies with `Ext^n(M, Q.obj K)`. -/
  abutmentIso :
    ∀ n : ℤ,
      filteredComplex.underlying.homology n ≅ derivedExtGroup M (DerivedCategory.Q.obj K) n
  /-- If `M ∈ D^-(𝒜)` and `K^•` is bounded below, then the associated spectral sequence
  converges to the cohomology of the underlying filtered complex in the Chapter `12` sense. -/
  converges_of_boundedness :
    DerivedCategoryIsBoundedAbove M →
      (∃ n : ℤ, K.IsStrictlyGE n) →
      filteredComplex.convergesToCohomology spectralSequence

attribute [instance] DerivedExtTermwiseSpectralSequenceData.associated

-- Proof sketch: apply Remark `19.13.8` to a representative `K^•` of `K` filtered by
-- `F^p K^• := τ_{\le -p}K^•`, identify the graded pieces with the cohomology objects `H^{-p}(K)`,
-- and then renumber indices by `p = -j` and `q = i + 2j`. The resulting `E₂`-spectral sequence
-- depends only on the derived object `K`, which is the independence-of-representative statement.
/-- Remark 19.13.9: for objects `M, K` of `D(\mathcal A)`, there is a cohomological spectral
sequence starting on the `E₂`-page with
`(E'_2)^{i,j} = \operatorname{Ext}^i(M, H^j(K))`, and this package depends only on the derived
object `K`, not on a chosen representative complex. If `M ∈ D^-(\mathcal A)` and
`K ∈ D^+(\mathcal A)`, the package also records boundedness, so it abuts to
`\operatorname{Ext}^{i + j}(M, K)`. -/
theorem derivedExtCohomologySpectralSequence_exists
    (M K : D) :
    Nonempty (DerivedExtCohomologySpectralSequenceData M K) := sorry

-- Proof sketch: filter a bounded-below representative `K^•` by the stupid filtration
-- `F^p K^• := σ_{\ge p}K^•`, apply the filtered-complex Ext spectral sequence from
-- Remark `19.13.8`, identify the graded pieces with the single-term complexes on the objects
-- `K^p`, and use the bounded-above hypothesis on `M` together with bounded-belowness of `K^•`
-- to obtain boundedness.
/-- Using the stupid filtration `σ_{\ge p}` on a bounded-below representative `K^•` yields a
cohomological spectral sequence with `E_1^{p,q} = \operatorname{Ext}^q(M, K^p)` abutting to
`\operatorname{Ext}^{p + q}(M, Q.obj K)`. The chosen package records the filtered-complex model,
its associated spectral sequence, and the Chapter `12` convergence witness under the boundedness
hypotheses. -/
theorem derivedExtTermwiseSpectralSequence_exists
    (M : D) (K : CochainComplex 𝒜 ℤ) :
    Nonempty (DerivedExtTermwiseSpectralSequenceData M K) := sorry

end CategoryTheory

/-! ### Remark_19_13_10 (from Chap19) -/
open CategoryTheory
open CategoryTheory.Limits
open FilteredComplex

noncomputable section

universe w v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [LocallySmall 𝒜] [WellPowered 𝒜]
  [HasWidePullbacks 𝒜] [HasCoproducts 𝒜] [InitialMonoClass 𝒜] [IsGrothendieckAbelian.{w} 𝒜]
  [HasDerivedCategory 𝒜]

local notation "FilteredComplex" => CategoryTheory.FilteredComplex 𝒜
local notation "AbFilteredComplex" => CategoryTheory.FilteredComplex AddCommGrpCat

-- Proof sketch: composition in the derived category is additive in the second factor, so
-- precomposition with `f` defines an additive homomorphism on morphism groups.
/-- Precomposition with a morphism in the first variable is additive on derived `Ext` groups. -/
theorem derivedExtGroupPrecomp_add
    (K : DerivedCategory 𝒜) {X Y : DerivedCategory 𝒜} (f : X ⟶ Y) (n : ℤ)
    (α β : Y ⟶ K⟦n⟧) :
    f ≫ (α + β) = f ≫ α + f ≫ β := sorry

/-- The map on derived `Ext` groups induced contravariantly by a morphism in the first variable.
-/
def derivedExtGroupPrecomp
    (K : DerivedCategory 𝒜) {X Y : DerivedCategory 𝒜} (f : X ⟶ Y) (n : ℤ) :
    derivedExtGroup Y K n ⟶ derivedExtGroup X K n :=
  AddCommGrpCat.ofHom <|
    AddMonoidHom.mk'
      (fun α ↦ f ≫ α)
      (derivedExtGroupPrecomp_add K f n)

/-- For every total degree, the groups `Ext^n(M / F^p M, K)` vanish for all sufficiently small
filtration indices `p`. -/
def EventualQuotientDerivedExtVanishesBelow
    (M : FilteredComplex) (K : DerivedCategory 𝒜) : Prop :=
  ∀ n : ℤ, ∃ p₀ : ℤ, ∀ ⦃p : ℤ⦄, p ≤ p₀ →
    IsZero (derivedExtGroup (DerivedCategory.Q.obj (M.quotient p)) K n)

/-- For every total degree, the canonical maps `Ext^n(M / F^p M, K) → Ext^n(M, K)` are
isomorphisms for all sufficiently large filtration indices `p`. -/
def EventualQuotientDerivedExtStabilizesAbove
    (M : FilteredComplex) (K : DerivedCategory 𝒜) : Prop :=
  ∀ n : ℤ, ∃ p₁ : ℤ, ∀ ⦃p : ℤ⦄, p₁ ≤ p →
    IsIso (derivedExtGroupPrecomp K (DerivedCategory.Q.map (M.underlyingToQuotient p)) n)

/-- A filtered-complex model for the dual Ext spectral sequence
`E_1^{p,q} = Ext^{p + q}(gr^{-p} M, K)` attached to a filtered complex `M^•` and a derived object
`K`. -/
structure FilteredComplexSourceExtSpectralSequenceData
    (M : FilteredComplex) (K : DerivedCategory 𝒜) where
  /-- The filtered complex of abelian groups producing the spectral sequence. -/
  filteredHomComplex : AbFilteredComplex
  /-- The cohomological spectral sequence attached to the chosen filtered Hom complex. -/
  spectralSequence : CohomologicalSpectralSequence AddCommGrpCat 0
  /-- The spectral sequence is associated to the chosen filtered Hom complex. -/
  associated : IsAssociatedToFilteredComplex filteredHomComplex spectralSequence
  /-- The `E₁`-page identifies with the derived `Ext` groups of the shifted graded pieces
  `gr^{-p}(M^•)`. -/
  pageOneIso : ∀ p q : ℤ,
    (spectralSequence.page 1).X (p, q) ≅
      derivedExtGroup (DerivedCategory.Q.obj (M.gradedPiece (-p))) K (p + q)
  /-- The abutment cohomology of the filtered Hom complex identifies with `Ext^n(M, K)`. -/
  abutmentIso : ∀ n : ℤ,
    filteredHomComplex.underlying.homology n ≅
      derivedExtGroup (DerivedCategory.Q.obj (M.underlying)) K n
  /-- The eventual quotient-Ext vanishing and stabilization hypotheses force the spectral
  sequence to be bounded. -/
  bounded_of_eventualQuotientExt_control :
    EventualQuotientDerivedExtVanishesBelow M K →
      EventualQuotientDerivedExtStabilizesAbove M K →
      CohomologicalSpectralSequence.IsBounded spectralSequence
  /-- The same hypotheses force convergence of the associated filtered complex to its abutment
  cohomology. -/
  converges_of_eventualQuotientExt_control :
    EventualQuotientDerivedExtVanishesBelow M K →
      EventualQuotientDerivedExtStabilizesAbove M K →
      CategoryTheory.FilteredComplex.convergesToCohomology filteredHomComplex spectralSequence

-- Proof sketch: choose a K-injective complex `I^•` representing `K`, form the filtered complex
-- `Hom^•(M^•, I^•)` with filtration
-- `F^p Hom^•(M^•, I^•) = Hom^•(M^• / F^{-p + 1} M^•, I^•)`, and apply the filtered-complex
-- spectral sequence from Chapter 12. The `E₁`-page identifies with
-- `Ext^{p+q}(gr^{-p} M, K)`, while Lemma 12.24.13 turns the eventual vanishing and eventual
-- stabilization hypotheses on `Ext^n(M / F^p M, K)` into boundedness and convergence to
-- `Ext^{p+q}(M, K)`.
/-- Remark 19.13.10: for a Grothendieck abelian category `𝒜`, a filtered complex `M^•`, and an
object `K` of `D(𝒜)`, there is a spectral sequence in abelian groups with
`E₁^{p,q} = Ext^{p + q}(gr^{-p}(M^•), K)`; moreover, if `Ext^n(M / F^p M, K)` vanishes for
`p ≪ 0` and the canonical map `Ext^n(M / F^p M, K) → Ext^n(M, K)` is an isomorphism for
`p ≫ 0`, then this spectral sequence is bounded and converges to `Ext^{p + q}(M, K)`. In this
file, the chosen spectral sequence is packaged as
`FilteredComplexSourceExtSpectralSequenceData M K`. -/
theorem filteredComplexSourceExtSpectralSequence_exists
    (M : FilteredComplex) (K : DerivedCategory 𝒜) :
    Nonempty (FilteredComplexSourceExtSpectralSequenceData M K) := sorry

end CategoryTheory

/-! ### Remark_19_13_11 (from Chap19) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe w v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A] [LocallySmall A] [WellPowered A]
  [HasWidePullbacks A] [HasCoproducts A] [InitialMonoClass A] [IsGrothendieckAbelian.{w} A]

/-- The `AddCommGrpCat`-valued filtered complexes used to package the spectral sequences in this
item. -/
abbrev AbFilteredComplex :=
  CochainComplex (FilteredObject AddCommGrpCat) ℤ

/-- The standard derived-category model attached to a Grothendieck abelian category in this item.
-/
local instance grothendieckAbelian_hasDerivedCategoryForRemark_19_13_11 :
    HasDerivedCategory A :=
  HasDerivedCategory.standard A

/-- The bounded-below condition on a derived object, i.e. membership in `D^+(A)`. -/
def derivedCategoryPlusProperty (K : DerivedCategory A) : Prop :=
  ∃ n : ℤ, K.IsGE n

/-- The bounded-above condition on a derived object, i.e. membership in `D^-(A)`. -/
def derivedCategoryMinusProperty (K : DerivedCategory A) : Prop :=
  ∃ n : ℤ, K.IsLE n

/-- A cochain complex is bounded above when it is zero in all sufficiently high degrees. -/
def cochainComplexIsBoundedAbove (M : CochainComplex A ℤ) : Prop :=
  ∃ n : ℤ, M.IsStrictlyLE n

/-- The cohomology object `H^n(F^•)` of the underlying complex of an `AddCommGrpCat`-valued
filtered complex. -/
abbrev addCommGrpFilteredComplexCohomologyObject
    (F : AbFilteredComplex) (n : ℤ) : AddCommGrpCat :=
  (FilteredComplex.underlying F).homology n

/-- The convergence package used in this file: the spectral sequence is associated to a filtered
complex and is bounded, so it converges to the cohomology of the underlying complex. -/
def filteredComplexAssociatedSpectralSequenceConverges
    (F : AbFilteredComplex)
    (E : CohomologicalSpectralSequence AddCommGrpCat 0) : Prop :=
  IsAssociatedToFilteredComplex F E ∧ CohomologicalSpectralSequence.IsBounded E

/-- The derived object corresponding to the cohomology object `H^j(M)` placed in degree `0`. -/
abbrev derivedCohomologyAsDerivedObject
    (M : DerivedCategory A) (j : ℤ) : DerivedCategory A :=
  (DerivedCategory.singleFunctor A 0).obj ((DerivedCategory.homologyFunctor A j).obj M)

/-- The derived object corresponding to the term `M^j` of a cochain complex, placed in degree `0`.
-/
abbrev cochainTermAsDerivedObject
    (M : CochainComplex A ℤ) (j : ℤ) : DerivedCategory A :=
  (DerivedCategory.singleFunctor A 0).obj (M.X j)

/-- A chosen renumbered spectral sequence computing `Ext^*(M, K)` from the cohomology objects
`H^{-j}(M)` of `M`. The owner objects are an `AddCommGrpCat`-valued filtered complex and its
associated cohomological spectral sequence. -/
structure DerivedExtCohomologySpectralSequenceData
    (M K : DerivedCategory A) where
  /-- The filtered complex of abelian groups producing the spectral sequence. -/
  filteredComplex : AbFilteredComplex
  /-- The cohomological spectral sequence attached to the chosen filtered complex. -/
  spectralSequence : CohomologicalSpectralSequence AddCommGrpCat 0
  /-- The chosen spectral sequence is associated to the filtered complex. -/
  associated : IsAssociatedToFilteredComplex filteredComplex spectralSequence
  /-- The `E'_2`-page identifies with `Ext^i(H^{-j}(M), K)`. -/
  pageTwoIso :
    ∀ i j : ℤ,
      (spectralSequence.page 2).X (i, j) ≅
        derivedExtGroup (derivedCohomologyAsDerivedObject M (-j)) K i
  /-- The abutment cohomology of the filtered complex identifies with `Ext^n(M, K)`. -/
  abutmentIso :
    ∀ n : ℤ,
      addCommGrpFilteredComplexCohomologyObject filteredComplex n ≅
        derivedExtGroup M K n
  /-- If `M ∈ D^-(A)` and `K ∈ D^+(A)`, then the renumbered spectral sequence is bounded and
  converges to `Ext^*(M, K)`. -/
  converges_of_boundedness :
    derivedCategoryMinusProperty M →
      derivedCategoryPlusProperty K →
      filteredComplexAssociatedSpectralSequenceConverges filteredComplex spectralSequence

/-- A chosen spectral sequence obtained from the filtration `F^p M^• = σ_{\ge p} M^•` on a
cochain complex `M^•`. The owner objects are an `AddCommGrpCat`-valued filtered complex and its
associated cohomological spectral sequence. -/
structure DerivedExtStupidFiltrationSpectralSequenceData
    (M : CochainComplex A ℤ) (K : DerivedCategory A) where
  /-- The filtered complex of abelian groups producing the spectral sequence. -/
  filteredComplex : AbFilteredComplex
  /-- The cohomological spectral sequence attached to the chosen filtered complex. -/
  spectralSequence : CohomologicalSpectralSequence AddCommGrpCat 0
  /-- The chosen spectral sequence is associated to the filtered complex. -/
  associated : IsAssociatedToFilteredComplex filteredComplex spectralSequence
  /-- The `E_1`-page identifies with `Ext^q(M^{-p}, K)`. -/
  pageOneIso :
    ∀ p q : ℤ,
      (spectralSequence.page 1).X (p, q) ≅
        derivedExtGroup (cochainTermAsDerivedObject M (-p)) K q
  /-- The abutment cohomology of the filtered complex identifies with `Ext^n(M, K)` for the
  derived object represented by `M^•`. -/
  abutmentIso :
    ∀ n : ℤ,
      addCommGrpFilteredComplexCohomologyObject filteredComplex n ≅
        derivedExtGroup (DerivedCategory.Q.obj M) K n
  /-- If `M^•` is bounded above and `K ∈ D^+(A)`, then the spectral sequence is bounded and
  converges to `Ext^*(M, K)`. -/
  converges_of_boundedness :
    cochainComplexIsBoundedAbove M →
      derivedCategoryPlusProperty K →
      filteredComplexAssociatedSpectralSequenceConverges filteredComplex spectralSequence

-- Proof sketch: choose a complex representing `M`, filter it by the canonical truncations
-- `τ_{\le -p}`, apply Remark 19.13.8 to the resulting filtered Hom complex, and then renumber
-- the indices by `p = -j` and `q = i + 2j`. The resulting spectral sequence depends only on the
-- derived object `M`, not on the chosen representative, because quasi-isomorphic representatives
-- have canonically identified cohomology objects and give isomorphic filtered-Hom constructions.
/-- Remark 19.13.11: for objects `M, K` of the derived category of a Grothendieck abelian
category, there is a renumbered spectral sequence with `E'_2{}^{\, i, j} = Ext^i(H^{-j}(M), K)`;
if `M ∈ D^-(A)` and `K ∈ D^+(A)`, then this spectral sequence is bounded and converges to
`Ext^{i + j}(M, K)`. In this file, the chosen spectral sequence is packaged as
`DerivedExtCohomologySpectralSequenceData M K`. -/
theorem derivedExt_cohomology_spectralSequence_exists
    (M K : DerivedCategory A) :
    Nonempty (DerivedExtCohomologySpectralSequenceData M K) := sorry

-- Proof sketch: filter the chosen cochain complex `M^•` by the stupid truncations
-- `σ_{\ge p} M^•`, apply Remark 19.13.8 to the resulting filtered Hom complex, and identify the
-- graded pieces of the filtration with the single-term complexes `M^{-p}[p]`. If `M^•` is
-- bounded above and `K ∈ D^+(A)`, the same boundedness argument gives convergence to
-- `Ext^*(DerivedCategory.Q.obj M, K)`.
/-- The stupid-filtration spectral sequence associated to a cochain complex `M^•` has
`E_1^{p,q} = Ext^q(M^{-p}, K)` and converges to `Ext^{p + q}(M, K)` when `M^•` is bounded above
and `K ∈ D^+(A)`. -/
theorem derivedExt_stupidFiltration_spectralSequence_exists
    (M : CochainComplex A ℤ) (K : DerivedCategory A) :
    Nonempty (DerivedExtStupidFiltrationSpectralSequenceData M K) := sorry

end CategoryTheory

/-! ### Lemma_19_13_12 (from Chap19) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe w v u

namespace CategoryTheory

section

variable {A : Type u} [Category.{v} A] [Abelian A]

attribute [local instance] HasDerivedCategory.standard

/-
Domain-style sampling for Lemma 19.13.12:
- primary domain: filtered complexes in a Grothendieck abelian category and their realization in
  the derived category;
- sampled owner declarations:
  `Cocone`,
  `FilteredComplex`,
  `FilteredComplex.underlying`,
  `FilteredComplex.stage`,
  `FilteredComplex.stageInclusion`,
  `FilteredComplex.stageMapOfLE`,
  `DerivedCategory.Q`,
  `Cocone.precompose`;
- best owner abstraction: `FilteredComplex A`;
- primitive data: a filtered complex `K : FilteredComplex A`;
- derived API: the stage tower `K.stageTower : ℤᵒᵖ ⥤ DerivedCategory A`, its canonical cocone
  `K.stageTowerCocone`, and the comparison to a given cocone `c : Cocone system` via
  `Cocone.precompose`;
- source/core/bridge triage:
  `source-facing`: `FilteredComplex.RealizesInverseSystem` and the existence theorem below;
  `core/canonical`: the owner object `FilteredComplex A`;
  `bridge/view`: the derived-category functor `stageTower`, the cocone `stageTowerCocone`, and
    cocone isomorphisms against a prescribed inverse-system cocone.

The previous version still unpacked realization as objectwise isomorphisms plus manually stated
compatibility squares. This file keeps the owner public and records the compatible target family at
the canonical functor/cocone layer. -/

namespace FilteredComplex

/-- The inverse-system tower in `D(A)` attached to the filtration stages of `K`. -/
noncomputable def stageTower (K : FilteredComplex A) : ℤᵒᵖ ⥤ DerivedCategory A where
  obj i := DerivedCategory.Q.obj (K.stage i.unop)
  map {i j} f := DerivedCategory.Q.map (K.stageMapOfLE f.unop.le)
  map_id i := by
    simp [FilteredComplex.stageMapOfLE_refl]
  map_comp f g := by
    rw [← DerivedCategory.Q.map_comp, FilteredComplex.stageMapOfLE_comp]

/-- The canonical cocone from the stage tower of `K` to the derived object represented by its
underlying complex. -/
noncomputable def stageTowerCocone (K : FilteredComplex A) : Cocone K.stageTower where
  pt := DerivedCategory.Q.obj K.underlying
  ι :=
    { app := fun i ↦ DerivedCategory.Q.map (K.stageInclusion i.unop)
      naturality := by
        intro i j f
        change
          DerivedCategory.Q.map (K.stageMapOfLE f.unop.le) ≫
              DerivedCategory.Q.map (K.stageInclusion j.unop) =
            DerivedCategory.Q.map (K.stageInclusion i.unop)
        rw [← DerivedCategory.Q.map_comp, FilteredComplex.stageMapOfLE_comp_stageInclusion] }

/-- A filtered complex realizes an inverse system in the derived category if its stage tower is
naturally isomorphic to the system and its canonical cocone identifies with the prescribed cocone
after transport along that natural isomorphism. -/
def RealizesInverseSystem
    (K : FilteredComplex A) {system : ℤᵒᵖ ⥤ DerivedCategory A} (c : Cocone system) : Prop :=
  ∃ stageIso : K.stageTower ≅ system,
    ∃ coconeHom : K.stageTowerCocone ⟶ (Cocone.precompose stageIso.hom).obj c,
      IsIso coconeHom

end FilteredComplex

variable [IsGrothendieckAbelian.{w} A]

-- Proof sketch: choose a K-injective complex representing `c.pt`, realize the inverse system by a
-- compatible tower of complexes mapping to that representative, and then build a filtered
-- cochain complex whose `i`-th stage is the chosen complex for `E^i`. The compatibility of the
-- tower maps with the cocone legs into `c.pt` gives the stated stagewise identifications in the derived
-- category.
/-- Lemma 19.13.12: for a compatible inverse system
`... ⟶ E^{i + 1} ⟶ E^i ⟶ E^{i - 1} ⟶ ... ⟶ E` in the derived category of a Grothendieck abelian
category, encoded by a cocone `c : Cocone system`, there exists a filtered complex whose
underlying complex represents `c.pt` and whose
filtration stages `F^i K^•` represent the objects `E^i` compatibly with the given cocone legs. -/
theorem exists_filteredCochainComplexRealization_of_inverseSystem
    (system : ℤᵒᵖ ⥤ DerivedCategory A) (c : Cocone system) :
    ∃ K : FilteredComplex A, K.RealizesInverseSystem c := sorry

end

end CategoryTheory

/-! ### Lemma_19_13_13 (from Chap19) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe w v u

namespace CategoryTheory

section

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]

/-
Domain-style sampling for Lemma 19.13.13:
- primary domain: bifiltered complexes in a Grothendieck abelian category, with each filtration
  realizing an inverse system in the derived category;
- sampled owner declarations:
  `FilteredComplex`,
  `FilteredComplex.RealizesInverseSystem`,
  `FilteredComplex.underlying`,
  `Cocone.mk`,
  `FilteredObject`;
- best owner abstraction: the two filtered-complex owners carried by a bifiltered complex, namely
  the first filtration `K.base` and the second filtration `K.second`;
- primitive data: two filtered complexes with a common underlying cochain complex;
- derived API: the realization predicates for the two inverse-system cocones, together with the
  common-underlying comparison `K.underlying_eq`;
- source/core/bridge triage:
  `source-facing`: the existence theorem below for one bifiltered complex realizing two inverse
    systems with common target;
  `core/canonical`: `FilteredComplex A` together with
    `FilteredComplex.RealizesInverseSystem`;
  `bridge/view`: the common-underlying equality between the two filtered-complex owners.

The previous downstream API duplicated the owner-level `FilteredComplex` abstraction by storing
the second filtration degreewise and then rebuilding a filtered complex from that stagewise data.
This file keeps the source-facing bifiltered owner, but its primitive fields now live directly at
the canonical `FilteredComplex` layer reused from Lemma 19.13.12. -/

attribute [local instance] HasDerivedCategory.standard

/-- A bifiltered cochain complex is a filtered cochain complex together with a second decreasing
filtration on the same underlying complex that is preserved by the differentials. -/
structure BifilteredCochainComplex (A : Type u) [Category.{v} A] [Abelian A] where
  /-- The first filtration on the complex. -/
  base : FilteredComplex A
  /-- The second filtration on the same underlying cochain complex. -/
  second : FilteredComplex A
  /-- The two filtered-complex owners have the same underlying cochain complex. -/
  underlying_eq : second.underlying = base.underlying

namespace BifilteredCochainComplex

variable (K : BifilteredCochainComplex A)

omit [IsGrothendieckAbelian.{w} A] in
@[simp] theorem second_underlying :
    K.second.underlying = K.base.underlying := K.underlying_eq

end BifilteredCochainComplex

-- Proof sketch: first choose a filtered realization of the system `E^i ⟶ E` as in Lemma
-- `19.13.12`, then choose a second filtered realization of `(E')^i ⟶ E`. Replace the first one by
-- a filtered K-injective complex using Lemma `19.13.7`, map the second realization into that
-- K-injective representative, and add an acyclic K-injective correction so that both maps into a
-- common target become termwise injective quasi-isomorphisms. Transport the two filtrations by
-- images to the common target to obtain the required bifiltered complex.
/-- Lemma 19.13.13: given two compatible inverse systems `E^i ⟶ E` and `(E')^i ⟶ E` in the
derived category of a Grothendieck abelian category, there exists a bifiltered cochain complex
whose underlying complex represents `E`, whose first filtration stages `F^i K^•` represent
`E^i`, and whose second filtration stages `(F')^i K^•` represent `(E')^i`, compatibly with the
given maps. -/
theorem exists_bifilteredCochainComplexRealization_of_inverseSystems
    (system system' : ℤᵒᵖ ⥤ DerivedCategory A) (E : DerivedCategory A)
    (π : system ⟶ (Functor.const ℤᵒᵖ).obj E)
    (π' : system' ⟶ (Functor.const ℤᵒᵖ).obj E) :
    ∃ K : BifilteredCochainComplex A,
      K.base.RealizesInverseSystem (Cocone.mk E π) ∧
        K.second.RealizesInverseSystem (Cocone.mk E π') := sorry

end

end CategoryTheory
