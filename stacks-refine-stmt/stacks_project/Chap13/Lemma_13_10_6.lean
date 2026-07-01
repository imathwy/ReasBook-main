import Mathlib
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Triangulated.Subcategory
import stacks_project.Chap13.Lemma_13_10_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
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
  `HomotopyCategory.plus`,
  `HomotopyCategory.minus`,
  `HomotopyCategory.bounded`,
  `ObjectProperty.lift`,
  `CategoryTheory.ObjectProperty.IsTriangulated`;
- best owner abstraction: the bounded homotopy categories `K⁺(𝒜)`, `K⁻(𝒜)`, and `Kᵇ(𝒜)` are the
  source-facing full-subcategory views inside `K(𝒜)`, while the canonical core is the
  triangulated object-property API together with the owner-level lift `(·).lift` for restricted
  functors;
- primitive data: the boundedness object properties from `Definition_13_8_1`, the owner-level
  triangulated instances from `Lemma_13_10_5`, and the ambient additive functor
  `F.mapHomotopyCategory (up ℤ)`;
- derived API: the induced functors on bounded homotopy categories;
- source/core/bridge triage:
  `source-facing`: the exact functors on `K(𝒜)`, `K⁺(𝒜)`, `K⁻(𝒜)`, and `Kᵇ(𝒜)`;
  `core/canonical`: `ObjectProperty.IsTriangulated` and `ObjectProperty.lift`;
  `bridge/view`: the bounded full-subcategory realizations inside the ambient homotopy category.

The boundedness owners live in `Definition_13_8_1`, and their triangulated object-property
instances are owned upstream by `Lemma_13_10_5`. This file therefore keeps only the bridge/view
declarations needed to transport functorial structure to those full subcategories. The
bounded-below and bounded-above restriction functors are kept as named bridges because they are
used throughout the later Chapter 13 derived-functor development; the bounded case is recorded
below by direct canonical recall. -/

variable (F : 𝒜 ⥤ ℬ) [F.Additive]

/-- The homotopy functor induced by `F` sends bounded-below objects to bounded-below objects. -/
theorem mapHomotopyCategory_obj_mem_boundedBelow
    (X : K⁺(𝒜)) :
    (HomotopyCategory.plus ℬ)
      ((F.mapHomotopyCategory (up ℤ)).obj X.obj) := by
  -- Proof sketch: represent `X` by a bounded-below complex and apply `F` termwise; additivity
  -- preserves zero objects, so the same lower bound still works after applying `F`.
  sorry

/-- The restriction of `F.mapHomotopyCategory (up ℤ)` to bounded-below homotopy categories. -/
abbrev mapBoundedBelowHomotopyCategory :
    K⁺(𝒜) ⥤ K⁺(ℬ) :=
  (HomotopyCategory.plus ℬ).lift
    ((HomotopyCategory.plus 𝒜).ι ⋙ F.mapHomotopyCategory (up ℤ))
    (mapHomotopyCategory_obj_mem_boundedBelow F)

/-- The homotopy functor induced by `F` sends bounded-above objects to bounded-above objects. -/
theorem mapHomotopyCategory_obj_mem_boundedAbove
    (X : K⁻(𝒜)) :
    (HomotopyCategory.minus ℬ)
      ((F.mapHomotopyCategory (up ℤ)).obj X.obj) := by
  -- Proof sketch: represent `X` by a bounded-above complex and apply `F` termwise; additivity
  -- preserves zero objects, so the same upper bound still works after applying `F`.
  sorry

/-- The restriction of `F.mapHomotopyCategory (up ℤ)` to bounded-above homotopy categories. -/
abbrev mapBoundedAboveHomotopyCategory :
    K⁻(𝒜) ⥤ K⁻(ℬ) :=
  (HomotopyCategory.minus ℬ).lift
    ((HomotopyCategory.minus 𝒜).ι ⋙ F.mapHomotopyCategory (up ℤ))
    (mapHomotopyCategory_obj_mem_boundedAbove F)

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
#check
  (inferInstance :
    ((HomotopyCategory.bounded ℬ).lift
      ((HomotopyCategory.bounded 𝒜).ι ⋙ F.mapHomotopyCategory (up ℤ))
      (fun X : Kᵇ(𝒜) ↦ by
        -- Proof sketch: combine the bounded-below and bounded-above arguments for the same
        -- bounded object.
        sorry)).IsTriangulated)

end

end CategoryTheory
