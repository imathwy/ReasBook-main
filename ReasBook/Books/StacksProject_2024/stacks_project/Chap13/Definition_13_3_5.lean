import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {D : Type u₁} [Category.{v₁} D] [Limits.HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {A : Type u₂} [Category.{v₂} A] [Abelian A]

/- Domain-style sampling for Definition 13.3.5:
- primary domain: homological functors from pretriangulated categories to abelian categories, and
  the contravariant/cohomological view obtained by passing to opposites;
- sampled core/canonical declarations:
  `Functor.IsHomological`,
  `Functor.map_distinguished_exact`,
  `Functor.rightOp`;
- best owner abstraction: `Functor.IsHomological`;
- primitive data: only the functor itself; homologicality/cohomologicality is a property, not
  additional packaged data;
- derived API: exactness on distinguished triangles, shift-sequence long exact sequences, and the
  contravariant cohomological view via `H.rightOp`, together with the generic bridge instance
  turning `[H.IsHomological]` into `[H.rightOp.IsHomological]`;
- source/core/bridge triage:
`source-facing`: the Stacks notion of a cohomological contravariant functor `H : Dᵒᵖ ⥤ A`;
  `core/canonical`: `Functor.IsHomological`;
  `bridge/view`: the passage from `H` to `H.rightOp : D ⥤ Aᵒᵖ`.

No local `IsCohomological` wrapper is needed here: the source notion is exactly the canonical
homological owner applied to the opposite-valued functor. -/

/- Definition 13.3.5 first recalls the covariant owner: the Stacks notion of a homological
functor `H : D ⥤ A` is the canonical predicate `Functor.IsHomological`. In this setting, the
exactness on distinguished triangles is primitive for the owner, and additivity is derived from
that owner rather than extra packaged data. -/
recall Functor.IsHomological

/- Companion recall: the defining exactness statement for the canonical owner is exposed by
`Functor.map_distinguished_exact`. -/
#check Functor.map_distinguished_exact

/- Companion recall: the contravariant source-facing functor `H : Dᵒᵖ ⥤ A` is converted to the
opposite-valued covariant functor by the canonical bridge `Functor.rightOp`. -/
variable (H : Dᵒᵖ ⥤ A) in
#check H.rightOp

/- Definition 13.3.5: for a contravariant functor `H : Dᵒᵖ ⥤ A`, the Stacks condition
"cohomological" is exactly the canonical homologicality condition on the opposite-valued
functor `H.rightOp : D ⥤ Aᵒᵖ`. -/
variable (H : Dᵒᵖ ⥤ A) in
#check H.rightOp.IsHomological

namespace Functor

open Pretriangulated.Opposite

/- Companion bridge: if `H : Dᵒᵖ ⥤ A` is homological on the opposite category, then its
opposite-valued covariant view `H.rightOp : D ⥤ Aᵒᵖ` is homological. This keeps the cohomological
source-facing reading attached to the canonical owner rather than to a separate local wrapper. -/
instance (H : Dᵒᵖ ⥤ A) [H.IsHomological] : H.rightOp.IsHomological := by
  refine ⟨fun T hT ↦ ?_⟩
  change (((Pretriangulated.shortComplexOfDistTriangle T hT).op.map H).op).Exact
  exact (H.map_distinguished_op_exact T hT).op

end Functor

end CategoryTheory
