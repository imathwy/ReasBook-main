import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.ERealSMul
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_27_3
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

namespace OrdinaryConvexProgram

-- Proof sketch: closedness of the objective and constraint data on the closed constraint set makes
-- the indicator-extended weighted objective attached to `(lam, μ)` a closed proper convex
-- function. The singleton hypothesis says that this weighted objective has a unique minimizer
-- `xBar`. Section 27 then gives existence of an optimal solution of `P`, while
-- `weightedObjectiveComplementaryMinimizerSet_eq_optimalSolutionSet` identifies every optimal
-- solution with a weighted-objective minimizer, forcing every optimal solution to equal `xBar`.
/-- Corollary 6.28.1: if `(lam, μ)` is a Kuhn--Tucker vector for an ordinary convex program `P`,
the objective and all constraint functions are closed on the closed constraint set, and the
weighted objective attached to `(lam, μ)` has canonical minimum set `{xBar}`, then `xBar` is the
unique optimal solution of `P`, expressed as equality between the canonical
`optimalSolutionSet` and the singleton `{xBar}`. -/
theorem optimalSolutionSet_eq_singleton_of_minimumSet_weightedObjective_eq_singleton
    {r s : ℕ} (P : OrdinaryConvexProgram ℝ E EReal r s)
    (lam : Fin r → ℝ) (μ : Fin s → ℝ) (hKT : P.IsKuhnTuckerVector lam μ)
    (hC_closed : IsClosed P.constraintSet)
    (hobjective_closed : LowerSemicontinuous P.objective)
    (hinequality_closed : ∀ i, LowerSemicontinuous (P.inequality i))
    (hequality_closed : ∀ j, LowerSemicontinuous (P.equality j))
    (xBar : E)
    (hminimum : minimumSet (P.weightedObjective lam μ) = {xBar}) :
    P.optimalSolutionSet = {xBar} := sorry

end OrdinaryConvexProgram

end
