import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {U V : SimplicialObject C} [HasBinaryProduct U V]

/- Domain-style sampling for Lemma 14.6.2:
- primary domain: binary products in the functor category `SimplicialObject C`;
- sampled owner declarations:
  `functorCategoryHasLimitsOfShape`,
  `prodIsProd`,
  `prod.lift'`,
  `prod.hom_ext`;
- best owner abstraction: the canonical binary-product limit witness `prodIsProd U V`,
  with existence supplied by the general functor-category limit instance;
- primitive data: only the simplicial objects `U`, `V`, `W` and the chosen binary product `U ⨯ V`;
- derived API: the canonical lift `prod.lift`, its projection formulas `prod.lift_fst`,
  `prod.lift_snd`, the packaged lift `prod.lift'`, and uniqueness via `prod.hom_ext`.

Source/core/bridge triage:
- `source-facing`: morphisms `W ⟶ U ⨯ V` are exactly pairs of morphisms `W ⟶ U` and `W ⟶ V`;
- `core/canonical`: `prodIsProd U V`;
- `bridge/view`: the simplicial-object specialization of the generic binary-product universal
  property.

This file carries no simplicial-specific primitive product data, so the correct refinement is to
reuse the generic product owner directly rather than define a parallel simplicial-object
equivalence. -/

/- Lemma 14.6.2: for simplicial objects, the universal property of `U ⨯ V` is the canonical
binary-product owner `prodIsProd U V`. -/
recall prodIsProd

/- The map induced by a pair of morphisms into the two factors is the canonical product lift
`prod.lift`. -/
recall prod.lift

/- The first projection formula for that lift is the canonical lemma `prod.lift_fst`. -/
recall prod.lift_fst

/- The second projection formula for that lift is the canonical lemma `prod.lift_snd`. -/
recall prod.lift_snd

/- The packaged source-facing lift with both projection identities is `prod.lift'`. -/
recall prod.lift'

/- Uniqueness of a morphism into the product is the canonical extensionality lemma
`prod.hom_ext`. -/
recall prod.hom_ext

end CategoryTheory.Limits
