import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v u

section

variable {C : Type u} [Category.{v} C]
variable (M : C)

/- Domain-style sampling for Definition 19.11.2:
- primary domain: subobject posets in a category, measured by cardinality;
- sampled owner API:
  `Subobject`,
  `Cardinal.mk`,
  `mk_subobject_le_two_pow_lift_hom_card`,
  `is_alpha_small_wrt_monomorphisms_of_subobject_cardinal_lt_cof`;
- best owner abstraction: the canonical type `Subobject M`; the source notion "the size of `M`" is
  derived data, namely the cardinal `Cardinal.mk (Subobject M)`;
- primitive data: the object `M` and its canonical subobject type `Subobject M`;
- derived API: the chapter's later size comparisons and smallness bounds, which specialize this
  same canonical expression under stronger Grothendieck abelian hypotheses.

Source/core/bridge triage:
- `source-facing`: the Stacks definition names the size of `M` as the number of its subobjects;
- `core/canonical`: `Subobject M` together with `Cardinal.mk`;
- `bridge/view`: none.

This file therefore targets the `core/canonical` layer: no local `subobject_size` owner should sit
in parallel with the canonical expression already used downstream.
-/

/- Definition 19.11.2: the size of an object `M` is the cardinality of its type of subobjects.
In the Grothendieck abelian setting of the Stacks chapter, Lean expresses this by the same
canonical formula, which already makes sense in any category. -/
#check Cardinal.mk (Subobject M)

end
