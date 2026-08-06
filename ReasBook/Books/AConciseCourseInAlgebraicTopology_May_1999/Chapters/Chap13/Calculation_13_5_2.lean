import Mathlib.LinearAlgebra.Dimension.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Example_10_1_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.IntegralSingularHomology
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Problem_13_6_3

open AlgebraicTopology

noncomputable section

/- Calculation 13.5.2 (1): for the standard torus CW structure, the degree-`1` cellular
differential is zero. -/
#check torusCellularChainComplex_d_one_zero

/- Calculation 13.5.2 (2): for the standard torus CW structure, the degree-`2` cellular
differential is zero. -/
#check torusCellularChainComplex_d_two_one

/-- Calculation 13.5.2 (3): the degree-`0` integral homology of the torus has rank `1`. -/
theorem torus_integralHomology_zero :
    Module.rank ℤ (integralSingularHomology 0 (TopCat.of TorusFromSquare)) = 1 := sorry

/-- Calculation 13.5.2 (4): the degree-`1` integral homology of the torus has rank `2`. -/
theorem torus_integralHomology_one :
    Module.rank ℤ (integralSingularHomology 1 (TopCat.of TorusFromSquare)) = 2 := sorry

/-- Calculation 13.5.2 (5): the degree-`2` integral homology of the torus has rank `1`. -/
theorem torus_integralHomology_two :
    Module.rank ℤ (integralSingularHomology 2 (TopCat.of TorusFromSquare)) = 1 := sorry
