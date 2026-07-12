import Mathlib.CategoryTheory.Simple
import Mathlib.Tactic.Recall

namespace CategoryTheory

universe v u

/- Domain triage:
- primary domain: simple objects in an abelian category, using the canonical owner that already
  lives in the broader zero-morphism setting.
- `source-facing`: the textbook predicate that an object is simple.
- `core/canonical`: `Simple X`.
- `bridge/view`: `simple_iff_subobject_isSimpleOrder`.
- Primitive data vs derived API: `Simple` is the primitive owner predicate; the subobject-lattice
  characterization is derived API.
-/

section

variable {C : Type u} [Category.{v} C] [Abelian C] (X : C)

/- Definition 12.9.1: a simple object of an abelian category is the canonical mathlib predicate
`Simple X`; this packages that the object is nonzero and has only the trivial subobjects. -/
#check Simple X

/- Companion recall: `simple_iff_subobject_isSimpleOrder` is the canonical subobject-lattice
characterization of simplicity. -/
recall simple_iff_subobject_isSimpleOrder

end

end CategoryTheory
