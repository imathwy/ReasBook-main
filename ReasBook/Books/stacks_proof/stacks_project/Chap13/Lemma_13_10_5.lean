import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import StacksProject_2024.Chap13.Definition_13_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory

universe v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜]
  [HasZeroObject 𝒜] [HasBinaryBiproducts 𝒜]

/- Domain-style sampling:
- primary domain: triangulated bounded homotopy categories of cochain complexes;
- sampled owner declarations:
  `HomotopyCategory.plus`,
  `HomotopyCategory.minus`,
  `HomotopyCategory.bounded`,
  `CategoryTheory.ObjectProperty.IsTriangulated`,
  `ObjectProperty.FullSubcategory`,
  `CategoryTheory.IsTriangulated`;
- best owner abstraction: the bounded homotopy categories `K⁺(𝒜)`, `K⁻(𝒜)`, and `Kᵇ(𝒜)` from
  `Definition_13_8_1`, viewed as the full subcategories cut out by the canonical boundedness
  object properties on `K(𝒜)`;
- primitive data: the object properties `HomotopyCategory.plus 𝒜`,
  `HomotopyCategory.minus 𝒜`, and `HomotopyCategory.bounded 𝒜`;
- derived API: the triangulated full-subcategory instances on `K⁺(𝒜)`, `K⁻(𝒜)`, and `Kᵇ(𝒜)`.
- source/core/bridge triage:
  `source-facing`: the bounded homotopy categories `K^{+}(\mathcal A)`, `K^{-}(\mathcal A)`,
    and `K^{b}(\mathcal A)`;
  `core/canonical`: the triangulated object-property API on `K(\mathcal A)`;
  `bridge/view`: the realization of those object properties as full subcategories.

This file is therefore the owner for the triangulated boundedness properties on `K(\mathcal A)`,
while the source-facing full-subcategory statements remain direct instance recalls.
-/

/-- The bounded-below objects in the homotopy category form a triangulated object property. -/
instance :
    (HomotopyCategory.plus 𝒜).IsTriangulated := sorry

/-- The bounded-above objects in the homotopy category form a triangulated object property. -/
instance :
    (HomotopyCategory.minus 𝒜).IsTriangulated := sorry

/-- The bounded objects in the homotopy category form a triangulated object property. -/
instance :
    (HomotopyCategory.bounded 𝒜).IsTriangulated := sorry

/- Lemma 13.10.5: the bounded-below, bounded-above, and bounded full subcategories
`K^{+}(\mathcal A)`, `K^{-}(\mathcal A)`, and `K^{b}(\mathcal A)` of `K(\mathcal A)` are
triangulated. In the chapter API these are the source-facing full-subcategory views of the three
owner instances above, so the textbook statement is recovered below by direct instance recall. -/
#check (inferInstance :
  IsTriangulated (K⁺(𝒜)))
#check (inferInstance :
  IsTriangulated (K⁻(𝒜)))
#check (inferInstance :
  IsTriangulated (Kᵇ(𝒜)))

end

end CategoryTheory
