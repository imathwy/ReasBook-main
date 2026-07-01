import Mathlib
import stacks_project.Chap04.Definition_4_31_2
import stacks_project.Chap04.Example_4_31_3

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory.Limits

open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped Bicategory CategoricalPullback

variable {A : Type (max u v)} [Category.{v} A]
variable {B : Type (max u v)} [Category.{v} B]
variable {C : Type (max u v)} [Category.{v} C]
variable (F : A ⥤ C) (G : B ⥤ C)

/- Domain-style sampling for Lemma 4.31.4:
- primary domain: bicategorical `2`-fibre products in `Cat`, presented through the categorical
  pullback model of Example `4.31.3`;
- inspected owner-level declarations:
  `BicategoricalTwoCommutativeSquare`,
  `Bicategory.IsFinal`,
  `CategoricalPullback.toCatCommSqOver`,
  `CatCommSqOver.toBicategoricalSquare`,
  `CategoricalPullback.functorEquiv`;
- best owner abstraction: the chapter's source-facing owner is
  `Bicategory.IsFinal (categoricalPullbackSquare F G)`, where the square itself is the canonical
  pullback square from Example `4.31.3` viewed in the bicategory of `2`-commutative squares;
- primitive data: the categorical pullback object `F ⊡ G` and its canonical square
  `toCatCommSqOver F G (F ⊡ G)`;
- derived API: the universal property equivalence `CategoricalPullback.functorEquiv F G X`,
  transferred to the chapter's square owner by `CatCommSqOver.toBicategoricalSquare`.

Source/core/bridge triage:
- `source-facing`: the square `categoricalPullbackSquare F G` and its `2`-fibre-product property;
- `core/canonical`: `Bicategory.IsFinal (categoricalPullbackSquare F G)`;
- `bridge/view`: `CategoricalPullback.functorEquiv F G X` and
  `CatCommSqOver.toBicategoricalSquare`. -/

/-- The canonical square from Example 4.31.3, viewed as an object of the chapter's bicategory of
`2`-commutative squares over `F` and `G`. -/
abbrev categoricalPullbackSquare :
    BicategoricalTwoCommutativeSquare F.toCatHom G.toCatHom :=
  ((toCatCommSqOver F G (F ⊡ G)).obj (𝟭 (F ⊡ G))).toBicategoricalSquare

/-- Lemma 4.31.4: the canonical square carried by the categorical pullback `F ⊡ G` is a
`2`-fibre product square in the bicategory of `2`-commutative squares over `F` and `G`. -/
theorem categoricalPullback_isTwoFibreProduct :
    Bicategory.IsFinal (categoricalPullbackSquare F G) := by
  sorry

/- Companion bridge/view: the universal property above is implemented by the canonical pullback
equivalence between functors into `F ⊡ G` and commutative squares over `F` and `G`. -/
recall CategoricalPullback.functorEquiv

end CategoryTheory.Limits
