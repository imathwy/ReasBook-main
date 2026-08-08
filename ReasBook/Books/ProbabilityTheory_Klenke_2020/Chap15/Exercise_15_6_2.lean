import ProbabilityTheory_Klenke_2020.Chap15.Exercise_15_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} {d : ℕ}
variable {W : Ω → EuclideanSpace ℝ (Fin d)}
variable {μ : EuclideanSpace ℝ (Fin d)}
variable {A C : Matrix (Fin d) (Fin d) ℝ}

-- Proof sketch: apply the real-matrix Cholesky/LDL factorization to the positive definite matrix
-- `C`; over `ℝ`, positive definiteness already gives the required symmetry, and the factor can be
-- chosen lower triangular.
/-- A positive definite real matrix admits a lower triangular factor whose product with its
transpose is the matrix itself. -/
theorem exists_lowerTriangular_mul_transpose_eq_of_posDef (hC : C.PosDef) :
    ∃ A : Matrix (Fin d) (Fin d) ℝ, A.BlockTriangular OrderDual.toDual ∧ A * A.transpose = C :=
  sorry

-- Proof sketch: first choose a lower triangular factor `A` with `A Aᵀ = C` from
-- `exists_lowerTriangular_mul_transpose_eq_of_posDef`. Since
-- `multivariateGaussian 0 1 = stdGaussian (EuclideanSpace ℝ (Fin d))`, the Gaussian-law part is
-- the `C = 1` instance of `hasLaw_matrix_image_of_hasLaw_multivariateGaussian` from
-- Exercise 15.6.1.
/-- Exercise 15.6.2: a positive definite real covariance matrix `C` admits a lower triangular factor
`A`, and for a standard Gaussian vector `W` the affine transform `ω ↦ μ + A (W ω)` has law
`N_{μ,C}`. -/
theorem exists_lowerTriangular_factor_hasLaw_multivariateGaussian_of_hasLaw_stdGaussian
    (hC : C.PosDef) (hW : HasLaw W (stdGaussian (EuclideanSpace ℝ (Fin d))) P) :
    ∃ A : Matrix (Fin d) (Fin d) ℝ,
      A.BlockTriangular OrderDual.toDual ∧
      A * A.transpose = C ∧
      HasLaw (fun ω ↦ μ + Matrix.toEuclideanLin A (W ω))
        (multivariateGaussian μ C) P :=
  sorry
