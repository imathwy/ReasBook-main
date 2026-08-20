module

public import ComputationalMethodsInverseProblems_Vogel_2002.Book.Ch6.Example_6_2.DiffusionMatrices

public section

open OneDimensionalDiffusion

/-- Exercise 6.7. The `j`th least-squares gradient entry equals the negative
mesh-scaled product of the `j`th discrete first differences of `u` and `z`. -/
theorem leastSquaresGradientEntry_eq_negDifferenceProduct
    (n : ℕ) (u z : Fin (n + 1) → ℝ) (j : Fin n) :
    -((n + 1 : ℝ) * Matrix.mulVec (Matrix.transpose (differenceMatrix n)) u j *
        Matrix.mulVec (Matrix.transpose (differenceMatrix n)) z j) =
      -((n + 1 : ℝ) * (u (Fin.castSucc j) - u j.succ) *
        (z (Fin.castSucc j) - z j.succ)) := by
  simp [differenceMatrixTranspose_mulVec_apply]
