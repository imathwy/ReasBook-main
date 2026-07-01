import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type v} [Semiring R] [PartialOrder R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

/-
Source/core/bridge triage:
- `source-facing`: Proposition 2.5.14 states that every linear subspace of a module is a convex
  cone, so the chapter surface should use `Set.IsConvexCone`.
- `core/canonical`: the canonical owner abstraction for linear subspaces is
  `Submodule.toConvexCone`.
- `bridge/view`: the source-facing set-level statement is obtained by forgetting the bundled owner
  with `ConvexCone.isConvexCone`.
- Primitive data vs derived API: additive and scalar closure are primitive at the bundled
  `ConvexCone` owner; the chapter statement is the derived unbundled view.
- Layer target: keep `Submodule.toConvexCone` as the owner-level root and expose
  `Set.IsConvexCone` only as the source-facing bridge.
-/

namespace Submodule

/-- Helper for Proposition 2.5.14: forgetting a submodule's canonical bundled cone gives a
source-facing convex cone. -/
theorem toConvexCone_isConvexCone (S : Submodule R E) :
    Set.IsConvexCone R (S.toConvexCone : Set E) := by
  -- The bundled convex cone already carries the required source-facing property.
  simpa using (S.toConvexCone.isConvexCone)

/-- Proposition 2.5.14: every linear subspace is a convex cone in the chapter's source-facing
set-level sense. -/
theorem isConvexCone (S : Submodule R E) : Set.IsConvexCone R (S : Set E) := by
  -- Forget the bundled cone structure and identify its carrier with the submodule itself.
  simpa using S.toConvexCone_isConvexCone

end Submodule

end
