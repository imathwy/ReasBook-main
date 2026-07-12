import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe v u₁ u₂

open CategoryTheory

variable (D : Type u₁) [SmallCategory D]
variable (C : Type u₂) [Category.{v} C]

/- Definition 2.6.1: for a small category `D` and a category `C`, a `D`-shaped diagram in `C`
is just a covariant functor as in Definition 2.2.1, namely the canonical functor type `D ⥤ C`
(equivalently, `CategoryTheory.Functor D C`). -/
#check (D ⥤ C)
