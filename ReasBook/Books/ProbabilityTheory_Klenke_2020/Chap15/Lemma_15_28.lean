import ProbabilityTheory_Klenke_2020.Chap15.Definition_15_27

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ComplexOrder

-- Proof sketch: expand the quadratic form of the matrix
-- `((MeasureTheory.charFun μ (t i - t j)))` using the integral formula for the characteristic
-- function, rearrange the finite sums under the integral, and identify the integrand as the
-- pointwise squared norm `‖∑ i, z i * exp (⟪x, t i⟫ * Complex.I)‖^2`.
/-- Lemma 15.28: the characteristic function of a finite measure on `ℝ^d` is positive
semidefinite. The matrix formulation is the finite-family specialization of this owner-level
statement. -/
theorem charFun_isPositiveSemidefiniteFunction_of_isFiniteMeasure {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ] :
    IsPositiveSemidefiniteFunction (charFun μ) := by
  sorry

/-- Lemma 15.28, matrix form: every finite difference-kernel matrix associated with the
characteristic function of a finite measure on `ℝ^d` is positive semidefinite. -/
theorem charFun_posSemidef {d n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure μ] (t : Fin n → EuclideanSpace ℝ (Fin d)) :
    (Matrix.of fun i j ↦ charFun μ (t i - t j)).PosSemidef := by
  simpa [IsPositiveSemidefiniteFunction] using
    charFun_isPositiveSemidefiniteFunction_of_isFiniteMeasure μ n t
