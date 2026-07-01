import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v u

section

variable {C : Type u} [Category.{v} C]
variable (U U' : CosimplicialObject C)

/- Domain-style sampling for Definition 14.5.1:
- primary domain: simplicial/cosimplicial objects as functor categories on `SimplexCategory`;
- sampled owner API:
  `CategoryTheory.CosimplicialObject`,
  `CosimplicialObject.δ`,
  `CosimplicialObject.σ`,
  `CosimplicialObject.const`;
- source/core/bridge triage:
  `source-facing`: the textbook notion of a cosimplicial object in `C`;
  `core/canonical`: the owner `CosimplicialObject C := SimplexCategory ⥤ C`;
  `bridge/view`: the specialization to concrete target categories such as `Type` or
  `AddCommGrpCat`, and the morphism view `U ⟶ U'` as a natural transformation.
- layer target: `core/canonical`, since Definition 14.5.1 only recalls the ambient owner notion
  itself rather than adding new source-facing structure.

Primitive data are only the ambient category `C`. Coface maps, codegeneracy maps, constant
cosimplicial objects, and specializations such as cosimplicial sets or cosimplicial abelian groups
are derived API from this owner, so this file should recall the canonical owner directly rather
than introduce any parallel wrapper. Unlike simplicial sets, mathlib does not provide a separate
owner abbreviation for cosimplicial `Type`-valued objects, so the direct type expression
`CosimplicialObject (Type u)` is already the canonical companion surface.
-/

/- Definition 14.5.1: a cosimplicial object of a category `C` is a covariant functor from
`SimplexCategory` to `C`; this is the canonical mathlib notion `CosimplicialObject C`. -/
recall CosimplicialObject

/- Companion check: a morphism of cosimplicial objects is canonically just a natural
transformation `U ⟶ U'`. -/
#check (U ⟶ U')

/- Companion check: since there is no separate upstream abbreviation for cosimplicial sets, the
canonical specialization is the direct type expression `CosimplicialObject (Type u)`. -/
#check (CosimplicialObject (Type u))

/- Companion check: cosimplicial abelian groups are cosimplicial objects in `AddCommGrpCat`. -/
#check (CosimplicialObject AddCommGrpCat)

end
