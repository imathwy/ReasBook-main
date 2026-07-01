import stacks_project.Chap14.Definition_14_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v u

section

variable {C : Type u} [Category.{v} C]
variable (U U' : SimplicialObject C)

/- Domain-style sampling for 14.4.0.1:
- primary domain: morphisms in the functor category `SimplexCategoryᵒᵖ ⥤ C`
- same-kind upstream declarations inspected:
  `CategoryTheory.SimplicialObject`,
  `CategoryTheory.NatTrans`,
  `SimplicialObject.hom_ext`,
  `Definition_14_3_1`
- best owner abstraction: `SimplicialObject C := SimplexCategoryᵒᵖ ⥤ C`, whose morphisms are
  inherited directly from the functor category
- primitive data: only the simplicial objects `U` and `U'`
- derived API: the natural-transformation spelling of `U ⟶ U'` and extensionality via
  `SimplicialObject.hom_ext`
- source/core/bridge triage:
  `source-facing`: the textbook identification of a morphism `U ⟶ U'` with the corresponding hom
  between the underlying `C`-valued presheaves on `Δ`
  `core/canonical`: the owner category `SimplicialObject C`
  `bridge/view`: the inherited hom type `U ⟶ U'`, read as the natural-transformation hom in
  `SimplexCategoryᵒᵖ ⥤ C`
- layer target: `bridge/view`, since this numbered item adds no new owner-level structure beyond
  the inherited hom type

Primitive data are only `U` and `U'`. The `C`-valued functor-morphism description is derived API
from the owner `SimplicialObject C`, so this file should stay at the bridge/view layer and record
only the inherited hom type instead of restating a separate long functor-category alias.
-/

/- 14.4.0.1 is the bridge/view reading of the canonical owner: a morphism of simplicial objects is
the inherited natural-transformation hom in `SimplexCategoryᵒᵖ ⥤ C`, so no separate local wrapper
or duplicate type alias is needed. -/
#check (U ⟶ U')

end
