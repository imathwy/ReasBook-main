import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u₁ v₁ u₂ v₂ w

namespace CategoryTheory

section

variable {C₁ : Type u₁} [Category.{v₁} C₁]
variable {C₂ : Type u₂} [Category.{v₂} C₂]
variable {B : Type w} [CommRing B]

local notation "BPresheaf₁" => C₁ᵒᵖ ⥤ ModuleCat B
local notation "BPresheaf₂" => C₂ᵒᵖ ⥤ ModuleCat B
local notation "ProductBPresheaf" => (C₁ × C₂)ᵒᵖ ⥤ ModuleCat B
local notation "Qis₁" => HomotopyCategory.quasiIso BPresheaf₁ (up ℤ)
local notation "Qis₂" => HomotopyCategory.quasiIso BPresheaf₂ (up ℤ)
local notation "QisProduct" => HomotopyCategory.quasiIso ProductBPresheaf (up ℤ)

/-- The homotopy-to-derived functor obtained by taking colimits of `B`-module valued presheaf
complexes on `C₁`. -/
private abbrev firstColimitToDerived [HasColimitsOfShape C₁ᵒᵖ (ModuleCat B)] :
    HomotopyCategory BPresheaf₁ (up ℤ) ⥤ DerivedCategory (ModuleCat B) :=
  (colim : BPresheaf₁ ⥤ ModuleCat B).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The homotopy-to-derived functor obtained by taking colimits of `B`-module valued presheaf
complexes on `C₂`. -/
private abbrev secondColimitToDerived [HasColimitsOfShape C₂ᵒᵖ (ModuleCat B)] :
    HomotopyCategory BPresheaf₂ (up ℤ) ⥤ DerivedCategory (ModuleCat B) :=
  (colim : BPresheaf₂ ⥤ ModuleCat B).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The homotopy-to-derived functor obtained by taking colimits of `B`-module valued presheaf
complexes on the product category `C₁ × C₂`. -/
private abbrev productColimitToDerived [HasColimitsOfShape (C₁ × C₂)ᵒᵖ (ModuleCat B)] :
    HomotopyCategory ProductBPresheaf (up ℤ) ⥤ DerivedCategory (ModuleCat B) :=
  (colim : ProductBPresheaf ⥤ ModuleCat B).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The exact inverse-image functor on derived categories induced by precomposition with the first
projection `C₁ × C₂ ⥤ C₁`. -/
private abbrev productLeftProjectionDerivedInverseImage :
    DerivedCategory BPresheaf₁ ⥤ DerivedCategory ProductBPresheaf :=
  ((Functor.whiskeringLeft (C₁ × C₂)ᵒᵖ C₁ᵒᵖ (ModuleCat B)).obj
      (CategoryTheory.Prod.fst C₁ C₂).op).mapDerivedCategory

/-- The exact inverse-image functor on derived categories induced by precomposition with the
second projection `C₁ × C₂ ⥤ C₂`. -/
private abbrev productRightProjectionDerivedInverseImage :
    DerivedCategory BPresheaf₂ ⥤ DerivedCategory ProductBPresheaf :=
  ((Functor.whiskeringLeft (C₁ × C₂)ᵒᵖ C₂ᵒᵖ (ModuleCat B)).obj
      (CategoryTheory.Prod.snd C₁ C₂).op).mapDerivedCategory

/-- The derived lower shriek `L\pi_{1,!}` from `B`-module valued presheaves on `C₁` to
`D(B)`. -/
private abbrev firstDerivedLowerShriek
    [HasColimitsOfShape C₁ᵒᵖ (ModuleCat B)]
    [Functor.HasLeftDerivedFunctor firstColimitToDerived Qis₁] :
    DerivedCategory BPresheaf₁ ⥤ DerivedCategory (ModuleCat B) :=
  Functor.totalLeftDerived firstColimitToDerived
    (DerivedCategory.Qh : HomotopyCategory BPresheaf₁ (up ℤ) ⥤ DerivedCategory BPresheaf₁)
    Qis₁

/-- The derived lower shriek `L\pi_{2,!}` from `B`-module valued presheaves on `C₂` to
`D(B)`. -/
private abbrev secondDerivedLowerShriek
    [HasColimitsOfShape C₂ᵒᵖ (ModuleCat B)]
    [Functor.HasLeftDerivedFunctor secondColimitToDerived Qis₂] :
    DerivedCategory BPresheaf₂ ⥤ DerivedCategory (ModuleCat B) :=
  Functor.totalLeftDerived secondColimitToDerived
    (DerivedCategory.Qh : HomotopyCategory BPresheaf₂ (up ℤ) ⥤ DerivedCategory BPresheaf₂)
    Qis₂

/-- The derived lower shriek `L(\pi₁ × \pi₂)_!` from `B`-module valued presheaves on
`C₁ × C₂` to `D(B)`. -/
private abbrev productDerivedLowerShriek
    [HasColimitsOfShape (C₁ × C₂)ᵒᵖ (ModuleCat B)]
    [Functor.HasLeftDerivedFunctor productColimitToDerived QisProduct] :
    DerivedCategory ProductBPresheaf ⥤ DerivedCategory (ModuleCat B) :=
  Functor.totalLeftDerived productColimitToDerived
    (DerivedCategory.Qh :
      HomotopyCategory ProductBPresheaf (up ℤ) ⥤ DerivedCategory ProductBPresheaf)
    QisProduct

-- Proof sketch: resolve both inputs by projective complexes built from the generators
-- `j_{U!}\underline B_U` and `j_{V!}\underline B_V`, use Example `21.39.3` to identify the exact
-- inverse images along the two projection functors, and compute both derived colimits using
-- Lemma `21.37.2`. On the generators both sides evaluate to `B`, and functoriality plus passage
-- to derived colimits yields the comparison isomorphism.
/-- Lemma 21.39.9: for the projection functors `uᵢ : \mathcal C₁ × \mathcal C₂ \to \mathcal Cᵢ`,
the derived lower shriek from the product category to a point sends the tensor product of the two
inverse images `g₁^{-1} K₁` and `g₂^{-1} K₂` to the tensor product of the derived lower shrieks
`L\pi_{1,!}(K₁)` and `L\pi_{2,!}(K₂)` in `D(B)`. This is the product-site, module-valued
presheaf formalization of the Stacks identity
`L(\pi₁ × \pi₂)_!(g₁^{-1} K₁ \otimes_{\underline B}^{\mathbf L} g₂^{-1} K₂)
  = L\pi_{1,!}(K₁) \otimes_B^{\mathbf L} L\pi_{2,!}(K₂)`. -/
theorem product_derivedLowerShriek_tensor_projectionInverseImages_isomorphic
    [HasColimitsOfShape C₁ᵒᵖ (ModuleCat B)]
    [HasColimitsOfShape C₂ᵒᵖ (ModuleCat B)]
    [HasColimitsOfShape (C₁ × C₂)ᵒᵖ (ModuleCat B)]
    [Functor.HasLeftDerivedFunctor firstColimitToDerived Qis₁]
    [Functor.HasLeftDerivedFunctor secondColimitToDerived Qis₂]
    [Functor.HasLeftDerivedFunctor productColimitToDerived QisProduct]
    [MonoidalCategory (DerivedCategory BPresheaf₁)]
    [MonoidalCategory (DerivedCategory BPresheaf₂)]
    [MonoidalCategory (DerivedCategory ProductBPresheaf)]
    [MonoidalCategory (DerivedCategory (ModuleCat B))]
    (K₁ : DerivedCategory BPresheaf₁) (K₂ : DerivedCategory BPresheaf₂) :
    IsIsomorphic
      ((productDerivedLowerShriek).obj
        (((productLeftProjectionDerivedInverseImage).obj K₁) ⊗
          ((productRightProjectionDerivedInverseImage).obj K₂)))
      (((firstDerivedLowerShriek).obj K₁) ⊗ ((secondDerivedLowerShriek).obj K₂)) := sorry

end

end CategoryTheory
