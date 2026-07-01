import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v u

section

variable {C : Type u} [Category.{v} C]
variable (U U' : SimplicialObject C)

/- Domain-style sampling for Definition 14.3.1:
- primary domain: simplicial objects as presheaves on `SimplexCategory`;
- sampled owner API:
  `CategoryTheory.SimplicialObject`,
  `SimplicialObject.δ`,
  `SimplicialObject.const`,
  `SSet`;
- source/core/bridge triage:
  `source-facing`: the textbook notion of a simplicial object in `C`;
  `core/canonical`: the owner abbreviation `SimplicialObject C := SimplexCategoryᵒᵖ ⥤ C`;
  `bridge/view`: the specialization `SSet` and the underlying functor-category morphism view.

Primitive data are only the ambient category `C`. Face maps, degeneracy maps, constant simplicial
objects, and specializations such as simplicial sets or simplicial abelian groups are derived API
from this owner, so this file should recall the canonical owner directly rather than introduce any
parallel wrapper.
-/

/- Definition 14.3.1: a simplicial object of a category `C` is a contravariant functor from
`SimplexCategory` to `C`; this is the canonical mathlib abbreviation `SimplicialObject C`. -/
recall SimplicialObject

/- Companion check: a morphism of simplicial objects is canonically just a natural transformation
`U ⟶ U'`. -/
#check (U ⟶ U')

/- Companion recall: a simplicial set is a simplicial object in the category of types; this is the
canonical abbreviation `SSet`. -/
recall SSet

/- Companion check: a simplicial abelian group is a simplicial object in the category
`AddCommGrpCat`. -/
#check (SimplicialObject AddCommGrpCat)

end
