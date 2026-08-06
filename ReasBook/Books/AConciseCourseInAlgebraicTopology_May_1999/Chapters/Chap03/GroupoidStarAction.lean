module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.GroupTheory.GroupAction.Defs

public section

universe u v

open CategoryTheory

namespace CategoryTheory.Groupoid

variable {B : Type u} [Groupoid.{v} B]

/-- The vertex group `End b` acts on the star `b ⟶ x` by precomposition with inverse loops. -/
noncomputable instance homMulAction (b x : B) : MulAction (End b) (b ⟶ x) :=
  MulAction.ofEndHom
    { toFun := fun g : End b ↦ fun f : b ⟶ x ↦ CategoryTheory.inv g ≫ f
      map_one' := by
        funext f
        change CategoryTheory.inv (1 : End b) ≫ f = f
        simp [End.one_def]
      map_mul' := by
        intro g h
        funext f
        change CategoryTheory.inv (g * h) ≫ f =
          CategoryTheory.inv g ≫ (CategoryTheory.inv h ≫ f)
        simp [Category.assoc] }

/-- The `End b`-action on `b ⟶ x` evaluates a loop by precomposition with its inverse. -/
@[simp] theorem homMulAction_smul (b x : B) (g : End b) (f : b ⟶ x) :
    g • f = CategoryTheory.inv g ≫ f := by
  change (CategoryTheory.inv g ≫ f) = CategoryTheory.inv g ≫ f
  rfl

end CategoryTheory.Groupoid
