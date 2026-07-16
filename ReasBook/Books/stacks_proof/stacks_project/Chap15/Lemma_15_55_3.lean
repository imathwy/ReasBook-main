import Mathlib.Algebra.Category.ModuleCat.Basic
import stacks_proof.stacks_project.Chap12.Lemma_12_27_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Abelian

universe u

namespace CategoryTheory

section

attribute [local instance] CategoryTheory.HasExt.standard

variable (R : Type u) [Ring R]
variable (J : ModuleCat.{u} R)

/- Domain-style sampling:
- primary domain: injective objects and degree-one `Ext` in the abelian category `ModuleCat R`;
- inspected owner declarations:
  `CategoryTheory.injective_iff_ext_one_eq_zero`,
  `subsingleton_iff_forall_eq 0`;
- best owner abstraction: the canonical owner is `Injective J`, with `Ext M J 1` as the derived
  degree-one obstruction group;
- primitive data: only the ring `R` and module object `J`;
- derived API: the vanishing formulation `∀ M, ∀ e : Ext M J 1, e = 0`, exposed directly by the
  chapter-level companion theorem.
- layer: `bridge/view`; this file only specializes the Chapter 12 owner theorem to `ModuleCat R`,
  so it should recall that canonical declaration directly instead of keeping a parallel local
  theorem name.

This item is the module-category specialization of the canonical injective-versus-`Ext¹`
criterion, so the main entry should be a direct specialization of the Chapter 12 owner theorem,
not a duplicate local shell. -/

/- Lemma 15.55.3: an `R`-module `J` is injective if and only if `Ext^1_R(M, J)` vanishes for
every `R`-module `M`. This is exactly the canonical owner theorem
`injective_iff_ext_one_eq_zero`, specialized to `ModuleCat R`. -/
#check (injective_iff_ext_one_eq_zero J :
  Injective J ↔ ∀ M : ModuleCat R, ∀ e : Ext M J 1, e = 0)

end

end CategoryTheory
