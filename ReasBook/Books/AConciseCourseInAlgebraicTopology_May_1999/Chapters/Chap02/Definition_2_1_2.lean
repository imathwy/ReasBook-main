import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory

/- Definition 2.1.2: a category is small when its objects form a set; in mathlib this is
the canonical abbreviation `SmallCategory`, expressing that the objects and morphisms live in
the same universe level. -/
recall SmallCategory (C : Type u) : Type (u + 1)
