import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_7_4
import Mathlib.CategoryTheory.Endomorphism

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))

/-- Definition 3.7.10: for a covering space `p : E → B`, `CoveringSpaceAut p` is the
categorical automorphism group of the corresponding object `Over.mk (TopCat.ofHom p)` in the
over-category `Over (TopCat.of B)`. Equivalently, its elements are invertible maps of covering
spaces from `p` to itself over `B`. -/
abbrev CoveringSpaceAut (p : C(E, B)) : Type _ :=
  Aut (Over.mk (TopCat.ofHom p))

#check (CoveringSpaceAut p)
