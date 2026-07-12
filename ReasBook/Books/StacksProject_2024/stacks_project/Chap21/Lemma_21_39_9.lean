import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksProject_2024.Chap15.Definition_15_59_13
import StacksProject_2024.Chap21.Lemma_21_39_8

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open scoped CategoryTheory DerivedTensorProduct

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace CategoryTheory

section

variable {C₁ : Type u} [Category.{v} C₁]
variable {C₂ : Type u} [Category.{v} C₂]
variable {B : Type w} [CommRing B]

variable [HasColimitsOfShape C₁ᵒᵖ (ModuleCat B)]
variable [HasColimitsOfShape C₂ᵒᵖ (ModuleCat B)]
variable [HasColimitsOfShape (C₁ × C₂)ᵒᵖ (ModuleCat B)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived C₁ (ModuleCat B) :
    HomotopyCategory (C₁ᵒᵖ ⥤ ModuleCat B) (up ℤ) ⥤ DerivedCategory (ModuleCat B))
  (HomotopyCategory.quasiIso (C₁ᵒᵖ ⥤ ModuleCat B) (up ℤ))]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived C₂ (ModuleCat B) :
    HomotopyCategory (C₂ᵒᵖ ⥤ ModuleCat B) (up ℤ) ⥤ DerivedCategory (ModuleCat B))
  (HomotopyCategory.quasiIso (C₂ᵒᵖ ⥤ ModuleCat B) (up ℤ))]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (C₁ × C₂) (ModuleCat B) :
    HomotopyCategory ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat B) (up ℤ) ⥤
      DerivedCategory (ModuleCat B))
  (HomotopyCategory.quasiIso ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat B) (up ℤ))]
variable [MonoidalCategory (DerivedCategory ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat B))]

local notation "BPresheaf₁" => C₁ᵒᵖ ⥤ ModuleCat B
local notation "BPresheaf₂" => C₂ᵒᵖ ⥤ ModuleCat B
local notation "π₁" => Prod.fst C₁ C₂
local notation "π₂" => Prod.snd C₁ C₂
local notation "π₁⁻¹[" A "]" => Functor.presheafInverseImage π₁ A
local notation "π₂⁻¹[" A "]" => Functor.presheafInverseImage π₂ A
local notation "π₁⁻¹ᴰ" => Functor.mapDerivedCategory (π₁⁻¹[(ModuleCat B)])
local notation "π₂⁻¹ᴰ" => Functor.mapDerivedCategory (π₂⁻¹[(ModuleCat B)])
local notation "Lπ₁!" => Lπ![C₁, (ModuleCat B)]
local notation "Lπ₂!" => Lπ![C₂, (ModuleCat B)]
local notation "Lπ₁₂!" => Lπ![(C₁ × C₂), (ModuleCat B)]

/- Domain-style sampling for Lemma 21.39.9:
- primary domain: derived lower shriek for category-over-a-point with `B`-module valued
  presheaves, together with exact inverse image along the two projection functors and tensor
  compatibility;
- sampled owner declarations:
  the whiskering inverse-image functors along `π₁.op` and `π₂.op`,
  `Functor.mapDerivedCategory`,
  the monoidal tensor object on `DerivedCategory ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat B)`,
  `CategoryTheory.derivedTensorProduct`,
  `categoryOverPointDerivedColimit`,
  the whiskering construction `Functor.whiskeringLeft`;
- best owner abstraction: the projection pullbacks are the canonical precomposition functors
  induced by `π₁.op` and `π₂.op`, used directly via `Functor.whiskeringLeft` and their exact lift
  `mapDerivedCategory`, while the source tensor on
  `DerivedCategory ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat B)` is the canonical monoidal tensor owner of that
  derived category and the target-side tensor in `DerivedCategory (ModuleCat B)` should use the
  Chapter 15 source-facing owner `⊗[B]^L` rather than an arbitrary ambient monoidal tensor;
- primitive data here: the two projection functors and the derived objects `K₁`, `K₂`;
- derived API here: the tensor-compatibility comparison for the existing lower-shriek owner.

Source/core/bridge triage:
- `source-facing`: the product-site Kunneth-style comparison for the lower shriek to a point;
- `core/canonical`: `Functor.whiskeringLeft`, `Functor.mapDerivedCategory`,
  the monoidal tensor object on `DerivedCategory ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat B)`, and
  `categoryOverPointDerivedColimit`;
- `bridge/view`: the Chapter 15 notation `⊗[B]^L` for the target derived tensor product.
-/

-- Proof sketch: resolve both inputs by projective complexes built from the generators
-- `j_{U!}\underline B_U` and `j_{V!}\underline B_V`, use Example `21.39.3` to identify the exact
-- inverse images `π₁⁻¹ K₁`, `π₂⁻¹ K₂` along the two projection functors, and compute both
-- derived colimits using Lemma `21.37.2`. On the generators both sides evaluate to `B`, and
-- functoriality plus passage to derived colimits yields the comparison isomorphism.
/-- Lemma 21.39.9: for the projection functors
`πᵢ : C₁ × C₂ ⥤ Cᵢ`, the derived lower shriek from the product category to a point sends the
tensor object of the two projection inverse images to the derived tensor product of the two
derived lower shrieks in `DerivedCategory (ModuleCat B)`. This is the source-facing
`IsIsomorphic` form of the Stacks identity saying that the derived lower shriek of
`π₁⁻¹ K₁ ⊗ π₂⁻¹ K₂` is isomorphic to the canonical tensor object
`Lπ₁!(K₁) ⊗[B]^L Lπ₂!(K₂)` on `DerivedCategory (ModuleCat B)`, which is the repository owner for
the derived tensor product over `B`. -/
@[stacks 08QB]
theorem categoryOverPointDerivedColimit_tensorProjectionInverseImages_isomorphic
    (K₁ : DerivedCategory BPresheaf₁) (K₂ : DerivedCategory BPresheaf₂) :
    IsIsomorphic
      ((Lπ₁₂!).obj ((π₁⁻¹ᴰ.obj K₁) ⊗ (π₂⁻¹ᴰ.obj K₂)))
      (((Lπ₁!).obj K₁) ⊗[B]^L ((Lπ₂!).obj K₂)) := by
  sorry

end

end CategoryTheory
