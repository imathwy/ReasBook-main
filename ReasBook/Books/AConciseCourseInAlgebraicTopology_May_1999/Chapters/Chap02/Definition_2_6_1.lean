import Mathlib.CategoryTheory.Functor.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

open CategoryTheory

variable (D : Type u₁) [Category.{v₁} D]
variable (C : Type u₂) [Category.{v₂} C]

/- Definition 2.6.1: for a small category `D` and a category `C`, a `D`-shaped diagram in `C`
is just a covariant functor as in Definition 2.2.1, namely the canonical functor type `D ⥤ C`
(equivalently, `CategoryTheory.Functor D C`). -/
#check (D ⥤ C)
