import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_15_6_1 (from Items/Chap15) -/
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory RealInnerProductSpace

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: push forward the law `multivariateGaussian μ C` along the continuous linear map
-- `Matrix.toEuclideanLin A`. The image law is still Gaussian by `HasGaussianLaw.map`, and
-- `integral_id_multivariateGaussian` together with `covariance_eval_multivariateGaussian` and
-- Gaussian measure extensionality identifies its mean and covariance matrix as `A μ` and
-- `A * C * A.transpose`.
/-- Exercise 15.6.1: if `X` has multivariate Gaussian law with mean `μ` and covariance matrix `C`,
then the linear image `A X` has multivariate Gaussian law with mean `A μ` and covariance matrix
`A C Aᵀ`. -/
theorem hasLaw_matrix_image_of_hasLaw_multivariateGaussian
    {P : Measure Ω} {d m : ℕ} {X : Ω → EuclideanSpace ℝ (Fin d)}
    (μ : EuclideanSpace ℝ (Fin d)) (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosSemidef)
    (A : Matrix (Fin m) (Fin d) ℝ) (hX : HasLaw X (multivariateGaussian μ C) P) :
    HasLaw (fun ω ↦ Matrix.toEuclideanLin A (X ω))
      (multivariateGaussian (Matrix.toEuclideanLin A μ) (A * C * A.transpose)) P := by
  let L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (Matrix.toEuclideanLin A).toContinuousLinearMap
  have hAC : (A * C * A.transpose).PosSemidef :=
    hC.mul_mul_conjTranspose_same A
  have hA :
      HasLaw L
        (multivariateGaussian (Matrix.toEuclideanLin A μ) (A * C * A.transpose))
        (multivariateGaussian μ C) := by
    refine ⟨by fun_prop, ?_⟩
    apply IsGaussian.ext
    · simp only [id_eq, integral_id_multivariateGaussian]
      rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id L,
        integral_id_multivariateGaussian]
      simp [L]
    · ext x y
      have hLadj : L.adjoint = (Matrix.toEuclideanLin A.transpose).toContinuousLinearMap := by
        rw [show L = (Matrix.toEuclideanLin A).toContinuousLinearMap by rfl,
          ← LinearMap.adjoint_toContinuousLinearMap (Matrix.toEuclideanLin A)]
        simpa using congrArg LinearMap.toContinuousLinearMap
          (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm
      have hx : (L.adjoint x).ofLp = A.transpose.mulVec x.ofLp := by
        rw [hLadj]
        change ((Matrix.toLpLin 2 2 A.transpose) x).ofLp = A.transpose.mulVec x.ofLp
        simp
      have hy : (L.adjoint y).ofLp = A.transpose.mulVec y.ofLp := by
        rw [hLadj]
        change ((Matrix.toLpLin 2 2 A.transpose) y).ofLp = A.transpose.mulVec y.ofLp
        simp
      calc
        covarianceBilin ((multivariateGaussian μ C).map L) x y
            = covarianceBilin (multivariateGaussian μ C) (L.adjoint x) (L.adjoint y) := by
                simpa using covarianceBilin_map IsGaussian.memLp_two_id L x y
        _ = (L.adjoint x).ofLp ⬝ᵥ (C.mulVec (L.adjoint y).ofLp) := by
              rw [covarianceBilin_multivariateGaussian hC]
        _ = A.transpose.mulVec x.ofLp ⬝ᵥ (C.mulVec (A.transpose.mulVec y.ofLp)) := by rw [hx, hy]
        _ = x.ofLp ⬝ᵥ ((A * C * A.transpose).mulVec y.ofLp) := by
              rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, Matrix.dotProduct_mulVec,
                Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mul_assoc]
              simp [Matrix.mul_assoc]
        _ =
            covarianceBilin
              (multivariateGaussian (Matrix.toEuclideanLin A μ) (A * C * A.transpose)) x y := by
              rw [covarianceBilin_multivariateGaussian hAC]
  simpa [L, Function.comp] using hA.comp hX

/-! ### Exercise_15_6_2 (from Items/Chap15) -/
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

/-! ### Theorem_15_6 (from Items/Chap15) -/
noncomputable section

open MeasureTheory ProbabilityTheory

namespace MeasureTheory.FiniteMeasure

/-
Theorem 15.6 is `source-facing`: its public content is uniqueness of finite measures on `[0, ∞)`
from their Laplace transforms.

The owner abstractions are:
* `ProbabilityTheory.mgf` for the transform itself;
* `finiteMeasure_eq_of_forall_mem_integral_eq_of_separating_boundedContinuousFamily` from
  Chapter 15 for uniqueness from a separating bounded-continuous family.

Accordingly, the local API stays thin: `laplaceTransform_def` is only the bridge from the textbook
kernel `x ↦ exp (-t x)` to `mgf`, while the main theorem remains the source statement.
-/

/-- The canonical owner `ProbabilityTheory.mgf ((↑) : NNReal → ℝ)` at the parameter `-(t : ℝ)` is
the textbook Laplace-transform integral against `x ↦ exp (-t x)` on `[0, ∞)`. -/
theorem laplaceTransform_def (μ : FiniteMeasure NNReal) (t : NNReal) :
    mgf ((↑) : NNReal → ℝ) (μ : Measure NNReal) (-(t : ℝ)) =
      ∫ x, Real.exp (-((t : ℝ) * (x : ℝ))) ∂(μ : Measure NNReal) := by
  simp [ProbabilityTheory.mgf, neg_mul]

-- Proof sketch: the forward direction is immediate from equality of measures. For the converse,
-- pass to the one-point compactification of `[0, ∞)`, observe that the functions
-- `x ↦ exp (-λ x)` for `λ ≥ 0` form a multiplicatively closed separating class containing the
-- constants, and apply the separating-class uniqueness theorem from Corollary 15.3.
/-- Theorem 15.6: two finite measures on `[0, ∞)` are equal exactly when their Laplace transforms
agree at every nonnegative parameter. -/
theorem ext_iff_laplaceTransform_eq (μ ν : FiniteMeasure NNReal) :
    μ = ν ↔
      ∀ t : NNReal,
        mgf ((↑) : NNReal → ℝ) (μ : Measure NNReal) (-(t : ℝ)) =
          mgf ((↑) : NNReal → ℝ) (ν : Measure NNReal) (-(t : ℝ)) := sorry

end MeasureTheory.FiniteMeasure
