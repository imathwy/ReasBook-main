import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_4_1 (from Chap04) -/
universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {X Y P : C} {p : P ⟶ X} {q : P ⟶ Y}

/- Domain-style sampling for Definition 4.4.1:
- primary domain: binary products in category theory, expressed via limit cones on the walking-pair
  diagram;
- inspected owner declarations:
  `BinaryFan.mk`,
  `IsLimit`,
  `IsLimit.existsUnique`,
  `BinaryFan.isLimitMk`;
- best owner abstraction: the textbook statement is already the canonical owner-level predicate
  `IsLimit (BinaryFan.mk p q)`;
- primitive data: the two morphisms `p : P ⟶ X` and `q : P ⟶ Y`, assembled into the binary fan
  `BinaryFan.mk p q`;
- derived API: the universal factorization theorem `IsLimit.existsUnique` and the converse
  constructor `BinaryFan.isLimitMk`.

Source/core/bridge triage:
- `source-facing`: the statement that `p` and `q` exhibit `P` as a product of `X` and `Y`;
- `core/canonical`: `IsLimit (BinaryFan.mk p q)`;
- `bridge/view`: `IsLimit.existsUnique` and `BinaryFan.isLimitMk`. -/

/- Definition 4.4.1: morphisms `p : P ⟶ X` and `q : P ⟶ Y` exhibit `P` as a product of `X` and
`Y` precisely when the binary fan `BinaryFan.mk p q` is limiting. -/
#check IsLimit (BinaryFan.mk p q)

/- Companion recall: the unique-factorization clause in the textbook definition is the canonical
theorem `IsLimit.existsUnique`. -/
recall IsLimit.existsUnique

/- Companion recall: the converse direction from the textbook `∃!` universal property to a
limiting binary fan is the binary-product-specific constructor `BinaryFan.isLimitMk`. -/
recall BinaryFan.isLimitMk

end CategoryTheory.Limits

/-! ### Definition_4_4_2 (from Chap04) -/
universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {X Y : C}

/- Domain-style sampling for Definition 4.4.2:
- primary domain: binary products as limits of pair diagrams.
- sampled owner declarations:
  `HasBinaryProduct X Y`,
  `HasBinaryProducts C`,
  `hasBinaryProducts_of_hasLimit_pair`,
  `pair X Y`.
- owner split:
  `HasBinaryProducts C` is the core/canonical owner abstraction for products of pairs in `C`,
  while `HasBinaryProduct X Y` is the canonical fixed-pair abbreviation.
- primitive data: for each pair `X`, `Y`, the existence of a limit of `pair X Y`.
- derived API: the canonical owner `HasBinaryProducts C`, the fixed-pair abbreviation
  `HasBinaryProduct X Y`, and the constructor `hasBinaryProducts_of_hasLimit_pair`.
-/

/- Source/core/bridge triage for Definition 4.4.2:
- `source-facing`: the textbook property that every pair of objects admits a product.
- `core/canonical`: the mathlib typeclass `HasBinaryProducts C`.
- `bridge/view`: the pointwise abbreviation `HasBinaryProduct X Y` and the constructor
  `hasBinaryProducts_of_hasLimit_pair` connecting the global owner to the pointwise formulation. -/

/- Canonical recall: the Stacks notion that a category has products of pairs is the canonical
mathlib typeclass `CategoryTheory.Limits.HasBinaryProducts`. -/
recall HasBinaryProducts

/- Definition 4.4.2 also uses the canonical fixed-pair abbreviation for the statement that
`X` and `Y` admit a binary product. -/
#check HasBinaryProduct X Y

section

variable [∀ {X Y : C}, HasLimit (pair X Y)]

/- Companion recall: once the primitive limit data `HasLimit (pair X Y)` is available for every
pair `X`, `Y`, the corresponding global owner instance is the canonical theorem
`hasBinaryProducts_of_hasLimit_pair`. -/
recall hasBinaryProducts_of_hasLimit_pair

end

end CategoryTheory.Limits
