import Mathlib.CategoryTheory.Opposites

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

section

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/- Definition 3.19-extra-5: a contravariant functor from `C` to `D` is canonically a functor
`Cᵒᵖ ⥤ D`. -/
#check (Cᵒᵖ ⥤ D)

end
