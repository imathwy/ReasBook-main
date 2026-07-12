import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Tactic.Recall

open CategoryTheory

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 3.19-extra-4: a covariant functor from a category `C` to a category `D` is
canonically a `CategoryTheory.Functor C D`, written `C ⥤ D`; its primitive data are the object
assignment `obj` and morphism assignment `map`, and its functoriality axioms are `map_id` and
`map_comp`. -/
recall CategoryTheory.Functor
