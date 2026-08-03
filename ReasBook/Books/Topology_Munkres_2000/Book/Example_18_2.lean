module

import Mathlib.Analysis.InnerProductSpace.PiL2

/- Example 18.2. The general predicate `Continuous` applies to plane curves,
space curves, real functions of two and three variables, and planar vector fields. -/
#check (Continuous : (ℝ → EuclideanSpace ℝ (Fin 2)) → Prop)
#check (Continuous : (ℝ → EuclideanSpace ℝ (Fin 3)) → Prop)
#check (Continuous : (EuclideanSpace ℝ (Fin 2) → ℝ) → Prop)
#check (Continuous : (EuclideanSpace ℝ (Fin 3) → ℝ) → Prop)
#check (Continuous :
  (EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) → Prop)
