import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Algorithm_5_7_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Algorithm_5_7_2

noncomputable section

/-!
Chapter05 Exercise 5.10

This exercise asks for a MATLAB or FORTRAN implementation of the L-BFGS algorithm from `§5.9`
rather than a new theorem. In this project the relevant implementation surface already belongs to
the upstream Chapter 5 owners `LBFGSHistoryEntry`, `lbfgsTwoLoopRecursion`, and `LBFGSMethod`,
so this file remains a recall-only entry and introduces no new local declaration.
-/

/- Chapter05 Exercise 5.10: recall the canonical Chapter 5 L-BFGS implementation owners. -/
#check LBFGSHistoryEntry
#check lbfgsTwoLoopRecursion
#check LBFGSMethod
