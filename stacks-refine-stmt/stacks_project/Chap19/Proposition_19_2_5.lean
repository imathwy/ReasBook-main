import Mathlib
import stacks_project.Chap19.Definition_19_2_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ModuleCat

universe u v

namespace CategoryTheory

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-
Domain-style sampling for 19.2.5:
- primary domain: transfinite smallness in `ModuleCat R`, with the source-specific size bound
  expressed by the lattice of `R`-submodules of `M`;
- sampled owner declarations:
  `is_alpha_small_wrt`,
  `ModuleCat.subobjectModule`,
  `ConcreteCategory.injective_eq_monomorphisms`,
  `is_alpha_small_wrt_monomorphisms_of_subobject_cardinal_lt_cof`;
- best owner abstraction: the conclusion should use the canonical morphism-property owner
  `MorphismProperty.monomorphisms (ModuleCat R)`, while the source-facing cardinal bound may remain
  on `Submodule R M`;
- primitive data: the module `M`, the ordinal `α`, and the cardinal inequality
  `Cardinal.mk (Submodule R M) < α.cof`;
- derived API: the categorical smallness statement `is_alpha_small_wrt (of R M) ... α`.

Source/core/bridge triage:
- `source-facing`: the module-theoretic cardinal bound on `Submodule R M`;
- `core/canonical`: `is_alpha_small_wrt (of R M) (MorphismProperty.monomorphisms (ModuleCat R)) α`;
- `bridge/view`: the order isomorphism `ModuleCat.subobjectModule` and the concrete-category
  identification of injective maps with monomorphisms.
-/

-- Proof sketch: for an `α`-indexed transfinite system of injective module maps and a morphism
-- `M ⟶ colimit B`, consider the `R`-submodules `f ⁻¹(B_β) ⊆ M`. There are at most
-- `Cardinal.mk (Submodule R M)` distinct such submodules, so when this cardinal is strictly below
-- `α.cof`, the corresponding indices are bounded in `α`; then the map factors through one stage,
-- which is exactly the required smallness criterion.
/-- Proposition 19.2.5: if the cofinality of `α` is strictly larger than the cardinality of the
set of `R`-submodules of `M`, then `M` is `α`-small with respect to injections, i.e. with
respect to monomorphisms in `ModuleCat R`. -/
theorem moduleCat_is_alpha_small_wrt_monomorphisms_of_submodule_cardinal_lt_cof
    (α : Ordinal) (hα : Cardinal.mk (Submodule R M) < α.cof) :
    is_alpha_small_wrt (of R M) (MorphismProperty.monomorphisms (ModuleCat R)) α := sorry

end

end CategoryTheory
