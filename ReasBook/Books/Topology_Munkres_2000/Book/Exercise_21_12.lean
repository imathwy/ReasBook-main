module

import Mathlib.Topology.Instances.Real.Lemmas

/- Exercise 21.12 (a): Addition on `ℝ` is continuous. -/
#check (continuous_add : Continuous (fun p : ℝ × ℝ ↦ p.1 + p.2))

/- Exercise 21.12 (b): Multiplication on `ℝ` is continuous. -/
#check (continuous_mul : Continuous (fun p : ℝ × ℝ ↦ p.1 * p.2))

/- Exercise 21.12 (c): Taking reciprocals is continuous from `ℝ \ {0}` to `ℝ`. -/
#check Real.continuous_inv

/- Exercise 21.12 (d): Subtraction on `ℝ` is continuous. -/
#check (continuous_sub : Continuous (fun p : ℝ × ℝ ↦ p.1 - p.2))

/- Exercise 21.12 (d): Division is continuous on pairs with nonzero denominator. -/
#check (continuousOn_div :
  ContinuousOn (fun p : ℝ × ℝ ↦ p.1 / p.2) {p | p.2 ≠ 0})
