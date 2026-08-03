module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/- Assumption 4.1: The real numbers `ℝ` form an ordered field with the
least-upper-bound property and dense order. -/
#check ℝ
#synth Field ℝ
#synth LinearOrder ℝ
#synth IsStrictOrderedRing ℝ
#synth ConditionallyCompleteLinearOrder ℝ
#check Real.exists_isLUB
#synth DenselyOrdered ℝ
