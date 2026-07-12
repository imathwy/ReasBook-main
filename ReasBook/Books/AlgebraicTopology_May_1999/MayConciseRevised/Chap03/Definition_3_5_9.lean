import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Endomorphism

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

variable {E B : Type u} [Groupoid.{v} E] [Groupoid.{v} B] (p : E ⥤ B)

/- Definition 3.5.9: for a cover of the base groupoid `B` represented by a functor `p : E ⥤ B`,
its automorphism group is the categorical automorphism group of the corresponding object
`Over.mk p.toCatHom` in the over-category `Over (Cat.of B)`. Equivalently, its elements are
invertible maps of coverings from `p` to itself. -/
#check (Aut (Over.mk p.toCatHom))
