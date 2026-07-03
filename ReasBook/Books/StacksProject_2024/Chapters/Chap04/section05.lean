import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_5_1 (from Chap04) -/
universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {X Y P : C} {ι₁ : X ⟶ P} {ι₂ : Y ⟶ P}

/- Domain-style sampling for Definition 4.5.1:
- primary domain: binary coproducts in category theory.
- relevant owner abstractions already upstream:
  `BinaryCofan.mk`, `BinaryCofan.isColimitMk`, `HasBinaryCoproduct`, `coprod.inl`,
  `coprod.desc`, and `coprodIsCoprod`.

Primitive-vs-derived split:
- primitive data in the source-facing statement: the vertex object `P` and the coprojections
  `ι₁`, `ι₂`.
- derived API: the mediating morphisms and uniqueness clause are canonically packaged by
  `IsColimit`; the chosen-object interface `X ⨿ Y`, `coprod.inl`, `coprod.desc` belongs to the
  downstream existence layer `[HasBinaryCoproduct X Y]`. -/

/- Source/core/bridge triage for Definition 4.5.1:
- `source-facing`: the textbook assertion that `ι₁`, `ι₂` exhibit `P` as a coproduct of `X`,
  `Y`.
- `core/canonical`: `IsColimit (BinaryCofan.mk ι₁ ι₂)`.
- `bridge/view`: the chosen binary coproduct object API, accessed later through
  `HasBinaryCoproduct` and `coprodIsCoprod`. -/

/- Definition 4.5.1: morphisms `ι₁ : X ⟶ P` and `ι₂ : Y ⟶ P` exhibit `P` as a coproduct of `X`
and `Y` precisely when the binary cofan `BinaryCofan.mk ι₁ ι₂` is colimiting. -/
#check IsColimit (BinaryCofan.mk ι₁ ι₂)

/- Companion recall: the unique-factorization clause in the textbook definition is the canonical
theorem `IsColimit.existsUnique`. -/
recall IsColimit.existsUnique

/- Companion recall: for a binary cofan of the form `BinaryCofan.mk ι₁ ι₂`, the converse
direction is the binary-coproduct-specific constructor `BinaryCofan.isColimitMk`. -/
recall BinaryCofan.isColimitMk

end CategoryTheory.Limits

/-! ### Definition_4_5_2 (from Chap04) -/
universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {X Y : C}

/- Domain-style sampling for Definition 4.5.2:
- primary domain: binary coproducts in `CategoryTheory.Limits`;
- sampled owner declarations:
  `HasBinaryCoproducts`,
  `HasBinaryCoproduct`,
  `hasBinaryCoproducts_of_hasColimit_pair`,
  `Definition_4_4_2` as the product-side chapter analogue;
- owner split:
  `HasBinaryCoproducts C` is the core/canonical owner abstraction for coproducts of pairs in `C`,
  while `HasBinaryCoproduct X Y` is the canonical pointwise abbreviation for a fixed pair.
- primitive data: for each pair `X`, `Y`, the existence of a colimit of `pair X Y`.
- derived API: the pointwise abbreviation `HasBinaryCoproduct X Y`, the canonical owner
  `HasBinaryCoproducts C`, and the constructor `hasBinaryCoproducts_of_hasColimit_pair`.
-/

/- Source/core/bridge triage for Definition 4.5.2:
- `source-facing`: the textbook property that every pair of objects admits a coproduct.
- `core/canonical`: the mathlib typeclass `HasBinaryCoproducts C`.
- `bridge/view`: the pointwise abbreviation `HasBinaryCoproduct X Y` and the constructor
  `hasBinaryCoproducts_of_hasColimit_pair` connecting the global owner to the pointwise
  formulation. -/

/- Canonical recall: the Stacks notion that a category has coproducts of pairs is the canonical
mathlib typeclass `CategoryTheory.Limits.HasBinaryCoproducts`. -/
recall HasBinaryCoproducts

/-
Definition 4.5.2 also uses the canonical fixed-pair abbreviation for the statement that `X` and
`Y` admit a binary coproduct.
-/
#check HasBinaryCoproduct X Y

section

variable [∀ {X Y : C}, HasColimit (pair X Y)]

/- Companion recall: once the primitive colimit data `HasColimit (pair X Y)` is available for
every pair `X`, `Y`, the corresponding global owner instance is the canonical theorem
`hasBinaryCoproducts_of_hasColimit_pair`. -/
recall hasBinaryCoproducts_of_hasColimit_pair

end

end CategoryTheory.Limits
