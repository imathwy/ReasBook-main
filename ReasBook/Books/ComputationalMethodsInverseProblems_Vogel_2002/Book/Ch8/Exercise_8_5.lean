module

public import ComputationalMethodsInverseProblems_Vogel_2002.Book.Ch8.Example_8_5

public section

namespace VariationalRegularization

/-- Exercise 8.5. For `0 < β`, the closed-unit-ball supremum from `(8.30)` is
equal to the explicit formula `(8.31)`, namely
`Real.sqrt (‖x‖ ^ 2 + β ^ 2)`. -/
theorem closedUnitBallDualSup_eq_sqrt {d : ℕ}
    (β : ℝ) (hβ : 0 < β) (x : EuclideanSpace ℝ (Fin d)) :
    sSup ((fun y : EuclideanSpace ℝ (Fin d) ↦
      inner ℝ x y + β * Real.sqrt (1 - ‖y‖ ^ 2)) ''
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) =
      Real.sqrt (‖x‖ ^ 2 + β ^ 2) := by
  simpa [smoothNormPenalty_def] using
    (smoothNormPenalty_eq_sSup_closedUnitBall β hβ x).symm

end VariationalRegularization
