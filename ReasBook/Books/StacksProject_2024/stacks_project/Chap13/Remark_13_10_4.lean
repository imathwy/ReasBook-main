import StacksProject_2024.stacks_project.Chap13.Lemma_13_10_5

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory

universe v u

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜]

variable (𝒜) [HasZeroObject 𝒜] [HasBinaryBiproducts 𝒜]

/- Domain-style sampling:
- primary domain: triangulated structures on bounded homotopy categories;
- relevant owner declarations in this domain:
  `HomotopyCategory.plus`,
  `HomotopyCategory.minus`,
  `HomotopyCategory.bounded`,
  `CategoryTheory.ObjectProperty.IsTriangulated`;
- source/core/bridge triage:
  `source-facing`: the direct triangulated structures on the bounded homotopy categories
    `K^{+}(\mathcal A)`, `K^{-}(\mathcal A)`, and `K^{b}(\mathcal A)`;
  `core/canonical`: the triangulated object-property instances on
    `HomotopyCategory.plus 𝒜`, `HomotopyCategory.minus 𝒜`, and `HomotopyCategory.bounded 𝒜`;
  `bridge/view`: the full-subcategory realizations `K⁺(𝒜)`, `K⁻(𝒜)`, and `Kᵇ(𝒜)` inside `K(𝒜)`.

Primitive data for the boundedness notions lives in `Definition_13_8_1`, while the triangulated
owner instances are established in `Lemma_13_10_5`. This remark is therefore a direct recall of
those source-facing full-subcategory consequences, not a second owner file and not a new bridge.
-/

/- Remark 13.10.4: for an additive category `\mathcal A`, the same cone argument as in
Proposition 13.10.3 shows that the bounded-below, bounded-above, and bounded homotopy categories
`K^{+}(\mathcal A)`, `K^{-}(\mathcal A)`, and `K^{b}(\mathcal A)` are triangulated; below this is
reproved by identifying them as triangulated subcategories of `K(\mathcal A)`. Here we record the
direct triangulated structures on the corresponding homotopy categories of bounded complexes. -/
#check (inferInstance :
  IsTriangulated (K⁺(𝒜)))

/- Companion recall: the bounded-above homotopy category `K^{-}(\mathcal A)` is triangulated. -/
#check (inferInstance :
  IsTriangulated (K⁻(𝒜)))

/- Companion recall: the bounded homotopy category `K^{b}(\mathcal A)` is triangulated. -/
#check (inferInstance :
  IsTriangulated (Kᵇ(𝒜)))
