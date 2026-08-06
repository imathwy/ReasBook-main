import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Opposites

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

open CategoryTheory

variable (C : Type u₁) [Category.{v₁} C]
variable (D : Type u₂) [Category.{v₂} D]

/- Definition 2.2.2: a contravariant functor from `C` to `D` is equivalently a covariant
functor from the opposite category `Cᵒᵖ` to `D`, so it reverses the direction of morphisms while
keeping the same underlying objects. -/
#check (Cᵒᵖ ⥤ D)

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/- A contravariant functor assigns to each object `X` of `C` the object
`F.obj (Opposite.op X)` of `D`. -/
#check fun (F : Cᵒᵖ ⥤ D) (X : C) ↦ F.obj (Opposite.op X)

/- A contravariant functor sends a morphism `f : X ⟶ Y` to the morphism
`F.map f.op : F.obj (Opposite.op Y) ⟶ F.obj (Opposite.op X)`, reversing its direction. -/
#check fun (F : Cᵒᵖ ⥤ D) {X Y : C} (f : X ⟶ Y) ↦
  (F.map f.op : F.obj (Opposite.op Y) ⟶ F.obj (Opposite.op X))
