import Mathlib
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Triangulated.Subcategory
import StacksProject_2024.Chap13.Definition_13_8_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped CategoryTheory

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Preadditive 𝒜] [Preadditive ℬ]
  [HasZeroObject 𝒜] [HasZeroObject ℬ]
  [HasBinaryBiproducts 𝒜] [HasBinaryBiproducts ℬ]

/- Domain-style sampling for Lemma 13.10.6:
- primary domain: triangulated full subcategories of homotopy categories and exact functors
  between them;
- sampled owner declarations:
  `boundedBelowHomotopyProperty`,
  `boundedAboveHomotopyProperty`,
  `ObjectProperty.lift`,
  `CategoryTheory.ObjectProperty.IsTriangulated`;
- best owner abstraction: the bounded homotopy categories `K⁺(𝒜)`, `K⁻(𝒜)`, and `Kᵇ(𝒜)` are the
  source-facing full-subcategory views inside `K(𝒜)`, while the canonical core is the
  triangulated object-property API together with `ObjectProperty.lift` for restricted functors;
- primitive data: the boundedness object properties from `Definition_13_8_1` and the ambient
  additive functor `F.mapHomotopyCategory (up ℤ)`;
- derived API: the triangulated instances for those object properties, the landing lemmas for the
  restricted functors, and the induced functors on bounded homotopy categories;
- source/core/bridge triage:
  `source-facing`: the exact functors on `K(𝒜)`, `K⁺(𝒜)`, `K⁻(𝒜)`, and `Kᵇ(𝒜)`;
  `core/canonical`: `ObjectProperty.IsTriangulated` and `ObjectProperty.lift`;
  `bridge/view`: the bounded full-subcategory realizations inside the ambient homotopy category.

The boundedness owners already live upstream in `Definition_13_8_1`, so this file keeps only the
bridge/view declarations needed to transport triangulated and functorial structure to those full
subcategories. -/

/-- The bounded-below objects in the homotopy category form a triangulated object property. -/
instance boundedBelowHomotopyProperty_isTriangulated :
    (boundedBelowHomotopyProperty 𝒜).IsTriangulated := sorry

/-- The bounded-above objects in the homotopy category form a triangulated object property. -/
instance boundedAboveHomotopyProperty_isTriangulated :
    (boundedAboveHomotopyProperty 𝒜).IsTriangulated := sorry

/-- The bounded objects in the homotopy category form a triangulated object property. -/
instance boundedHomotopyProperty_isTriangulated :
    (boundedHomotopyProperty 𝒜).IsTriangulated := sorry

variable (F : 𝒜 ⥤ ℬ) [F.Additive]

-- Proof sketch: represent `X` by a bounded-below cochain complex and apply `F` termwise; an
-- additive functor preserves zero objects, so the same lower bound still works after applying `F`.
/-- The functor on homotopy categories induced by an additive functor preserves bounded-below
objects. -/
theorem mapHomotopyCategory_obj_mem_boundedBelowHomotopyProperty
    (X : K⁺(𝒜)) :
    boundedBelowHomotopyProperty ℬ ((F.mapHomotopyCategory (up ℤ)).obj X.obj) := sorry

-- Proof sketch: represent `X` by a bounded-above cochain complex and apply `F` termwise; an
-- additive functor preserves zero objects, so the same upper bound still works after applying `F`.
/-- The functor on homotopy categories induced by an additive functor preserves bounded-above
objects. -/
theorem mapHomotopyCategory_obj_mem_boundedAboveHomotopyProperty
    (X : K⁻(𝒜)) :
    boundedAboveHomotopyProperty ℬ ((F.mapHomotopyCategory (up ℤ)).obj X.obj) := sorry

-- Proof sketch: combine the bounded-below and bounded-above preservation statements for the same
-- object of the bounded homotopy category.
/-- The functor on homotopy categories induced by an additive functor preserves bounded objects. -/
theorem mapHomotopyCategory_obj_mem_boundedHomotopyProperty
    (X : Kᵇ(𝒜)) :
    boundedHomotopyProperty ℬ ((F.mapHomotopyCategory (up ℤ)).obj X.obj) := sorry

/-- The restriction of `F.mapHomotopyCategory (up ℤ)` to bounded-below homotopy categories. -/
abbrev mapBoundedBelowHomotopyCategory :
    K⁺(𝒜) ⥤ K⁺(ℬ) :=
  ObjectProperty.lift (boundedBelowHomotopyProperty ℬ)
    (ObjectProperty.ι (boundedBelowHomotopyProperty 𝒜) ⋙ F.mapHomotopyCategory (up ℤ))
    (mapHomotopyCategory_obj_mem_boundedBelowHomotopyProperty F)

/-- The restriction of `F.mapHomotopyCategory (up ℤ)` to bounded-above homotopy categories. -/
abbrev mapBoundedAboveHomotopyCategory :
    K⁻(𝒜) ⥤ K⁻(ℬ) :=
  ObjectProperty.lift (boundedAboveHomotopyProperty ℬ)
    (ObjectProperty.ι (boundedAboveHomotopyProperty 𝒜) ⋙ F.mapHomotopyCategory (up ℤ))
    (mapHomotopyCategory_obj_mem_boundedAboveHomotopyProperty F)

/-- The restriction of `F.mapHomotopyCategory (up ℤ)` to bounded homotopy categories. -/
abbrev mapBoundedHomotopyCategory :
    Kᵇ(𝒜) ⥤ Kᵇ(ℬ) :=
  ObjectProperty.lift (boundedHomotopyProperty ℬ)
    (ObjectProperty.ι (boundedHomotopyProperty 𝒜) ⋙ F.mapHomotopyCategory (up ℤ))
    (mapHomotopyCategory_obj_mem_boundedHomotopyProperty F)

/- Lemma 13.10.6 (1): the additive functor `F : \mathcal A \to \mathcal B` induces an exact
functor `K(\mathcal A) \to K(\mathcal B)` on homotopy categories; in the canonical API, exactness
is the triangulated-functor instance below, together with the canonical shift-commuting structure
on `F.mapHomotopyCategory (up ℤ)`. -/
#check (inferInstance : (F.mapHomotopyCategory (up ℤ)).IsTriangulated)

/- Lemma 13.10.6 (2): the induced functor on bounded-below homotopy categories
`K^{+}(\mathcal A) \to K^{+}(\mathcal B)` is exact; it is the restriction of
`F.mapHomotopyCategory (up ℤ)` to the full subcategories of bounded-below objects. -/
#check (inferInstance : (mapBoundedBelowHomotopyCategory F).IsTriangulated)

/- Lemma 13.10.6 (3): the induced functor on bounded-above homotopy categories
`K^{-}(\mathcal A) \to K^{-}(\mathcal B)` is exact; it is the restriction of
`F.mapHomotopyCategory (up ℤ)` to the full subcategories of bounded-above objects. -/
#check (inferInstance : (mapBoundedAboveHomotopyCategory F).IsTriangulated)

/- Lemma 13.10.6 (4): the induced functor on bounded homotopy categories
`K^{b}(\mathcal A) \to K^{b}(\mathcal B)` is exact; it is the restriction of
`F.mapHomotopyCategory (up ℤ)` to the full subcategories of bounded objects. -/
#check (inferInstance : (mapBoundedHomotopyCategory F).IsTriangulated)

end

end CategoryTheory
