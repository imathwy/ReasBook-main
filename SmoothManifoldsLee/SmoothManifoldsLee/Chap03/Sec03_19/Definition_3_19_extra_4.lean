import Mathlib.CategoryTheory.Functor.Basic

open scoped CategoryTheory
open CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 3.19-extra-4: a covariant functor from a category `C` to a category `D` is
canonically an element of `C ⥤ D`, i.e. of `CategoryTheory.Functor C D`; its primitive data are
the object assignment `obj` and morphism assignment `map`, and its functoriality axioms are
`map_id` and `map_comp`. -/
#check (C ⥤ D)
