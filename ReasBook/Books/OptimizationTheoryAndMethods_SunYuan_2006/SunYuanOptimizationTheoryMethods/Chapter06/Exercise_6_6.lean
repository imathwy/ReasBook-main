import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.SunYuanOptimizationTheoryMethods.Chapter04.Exercise_4_3

-- Domain sampling:
-- * primary domain: benchmark objective functions reused across unconstrained optimization
--   methods;
-- * inspected project declarations: `rosenbrockFunction`, `extendedRosenbrockFunction`,
--   `OptimizationProblem`;
-- * source/core/bridge triage:
--   this exercise block is source-facing recall-only,
--   `extendedRosenbrockFunction` is the core owner already introduced in Chapter 4,
--   and `OptimizationProblem` is a heavier packaged view that would add no mathematics here.
-- This trust-region quasi-Newton exercise therefore reuses the Chapter 4 benchmark owner
-- directly rather than introducing a parallel local objective wrapper.

/-
Chapter06 Exercise 6.6: use a trust-region quasi-Newton method to minimize
`extendedRosenbrockFunction` from Appendix Problem 1.2.
-/
#check extendedRosenbrockFunction
