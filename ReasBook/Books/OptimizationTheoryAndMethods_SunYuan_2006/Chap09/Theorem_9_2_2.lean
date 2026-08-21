import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Order.Bounds.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Theorem_9_2_1

noncomputable section

namespace QuadraticProgram

variable {n me mi : ℕ}

/-- Chapter09 Theorem 9.2.2: if `G` is positive definite, then the primal problem
`(9.1.1)`-`(9.1.3)` is infeasible if and only if the dual problem `(9.2.8)`-`(9.2.10)` is
unbounded above. -/
theorem primalInfeasible_iff_dualUnboundedAbove
    (P : QuadraticProgram n me mi) (hG : P.G.PosDef) :
    P.feasibleSet = ∅ ↔ ¬ BddAbove ((P.dualObjective hG) '' P.dualFeasibleSet) := sorry

end QuadraticProgram
