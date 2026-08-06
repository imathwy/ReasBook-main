import Mathlib.CategoryTheory.Comma.Over.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Lemma_13_2_8

open scoped TopCat

noncomputable section

universe u

/-- The canonical Chapter 15 based-space model of the indexed wedge `wedgeOfNSpheres n ι`,
obtained from the Chapter 13 pointed model by forgetting to `BasedSpace`. -/
abbrev basedWedgeOfNSpheres
    (n : ℕ) (ι : Type u) : CategoryTheory.Under (⊤_ TopCat.{u}) :=
  PointedCompactlyGenerated.toBasedSpace
    (wedgeOfNSpheres n ι : PointedCompactlyGenerated.{u, u})
