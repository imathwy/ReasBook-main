import Mathlib.Algebra.Category.ModuleCat.AB
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.Construction_14_1_3

open CategoryTheory Limits

noncomputable section

/-- Reduced singular homology with integer coefficients, computed from a Chapter 13 integral
pair-homology theory on a based space. -/
abbrev integralReducedHomology
    (H : PairHomologyTheory ℤ) (k : ℕ) (X : BasedSpace) : ModuleCat ℤ :=
  ModuleCat.of ℤ (basedReducedHomology H (k : ℤ) X)
