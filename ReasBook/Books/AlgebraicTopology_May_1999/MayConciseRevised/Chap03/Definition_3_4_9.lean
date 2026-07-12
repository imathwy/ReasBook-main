import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

variable (B : Type u) [Groupoid.{v} B]

/- Definition 3.4.9: a functor from a small groupoid `B` to sets is the canonical functor type
`B ⥤ Type v`; this is the source-facing notion of an action of `B` on sets. -/
#check (B ⥤ Type w)

namespace CategoryTheory.Functor

variable {B : Type u} [Groupoid.{v} B]

/-- For a functor `T : B ⥤ Type v`, the source-facing vertex group `π(B, b)` acts on the fiber
`T.obj b`. Since `T` is covariant, the corresponding left action is given by inverse loops. -/
noncomputable abbrev vertexGroupAction (T : B ⥤ Type w) (b : B) :
    MulAction (b ⟶ b) (T.obj b) :=
  MulAction.ofEndHom
    { toFun := fun g : b ⟶ b => fun x ↦ T.map g⁻¹ x
      map_one' := by
        funext x
        simp [Function.End.one_def]
      map_mul' := by
        intro g h
        funext x
        simp [Function.End.mul_def] }

/-- The source-facing vertex-group action attached to `T` evaluates a loop by applying `T.map` to
its inverse. -/
@[simp] theorem vertexGroupAction_smul_eq_map_inv (T : B ⥤ Type w) (b : B)
    (g : b ⟶ b) (x : T.obj b) :
    letI := vertexGroupAction T b
    g • x = T.map g⁻¹ x := by
  rfl

/-- The implementation-level `End b`-action corresponding to `vertexGroupAction T b`. Since
`CategoryTheory.End b` reverses categorical multiplication, this bridge evaluates a loop directly
by `T.map`. -/
noncomputable abbrev vertexGroupMulAction (T : B ⥤ Type w) (b : B) :
    MulAction (CategoryTheory.End b) (T.obj b) :=
  MulAction.ofEndHom
    { toFun := T.map
      map_one' := T.map_id b
      map_mul' := by
        intro g h
        change T.map (h ≫ g) = T.map g ∘ T.map h
        exact T.map_comp h g }

/-- The vertex-group action attached to `T` evaluates a loop by applying `T.map`. -/
@[simp] theorem vertexGroupMulAction_smul_eq_map (T : B ⥤ Type w) (b : B)
    (g : CategoryTheory.End b) (x : T.obj b) :
    letI := vertexGroupMulAction T b
    g • x = T.map g x := by
  change (vertexGroupMulAction T b).smul g x = T.map g x
  rfl

end CategoryTheory.Functor
