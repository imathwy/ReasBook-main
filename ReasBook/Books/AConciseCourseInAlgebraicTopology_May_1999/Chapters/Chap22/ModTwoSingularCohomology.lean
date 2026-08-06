import Mathlib.Data.ZMod.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Construction_16_1_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Problem_22_6_2

open AlgebraicTopology
open CategoryTheory
open scoped SingularChains

noncomputable section

/-- Singular cohomology with `ZMod 2` coefficients, modeled via the singular chain complex and the
coefficient-cohomology owner from Problem 22.6.2. -/
abbrev modTwoSingularCohomology (X : TopCat) (n : ℕ) : ModuleCat ℤ :=
  coefficientCohomology (C_*(X)) (ModuleCat.of ℤ (ZMod 2)) n
