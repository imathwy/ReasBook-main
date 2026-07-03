import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

open CategoryTheory

variable (C : Type u₁) [Category.{v₁} C]
variable (D : Type u₂) [Category.{v₂} D]

/- Definition 2.2.2: a contravariant functor from `C` to `D` is equivalently a covariant
functor from the opposite category `Cᵒᵖ` to `D`, so it reverses the direction of morphisms while
keeping the same underlying objects. -/
#check (Cᵒᵖ ⥤ D)
