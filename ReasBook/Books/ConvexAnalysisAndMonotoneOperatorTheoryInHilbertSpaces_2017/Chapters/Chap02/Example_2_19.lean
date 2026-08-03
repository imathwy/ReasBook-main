import Mathlib

noncomputable section

open Matrix
open scoped Matrix.Norms.Frobenius

universe u v

private lemma toEuclideanLin_apply_le_frobenius_norm {𝕜 : Type*} [RCLike 𝕜]
    {m : Type u} {n : Type v} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    ‖A.toEuclideanLin.toContinuousLinearMap x‖ ≤ ‖A‖ * ‖x‖ := by
  have hmulVec :
      ‖replicateCol (Fin 1) (A.mulVec x.ofLp)‖ = ‖WithLp.toLp 2 (A.mulVec x.ofLp)‖ :=
    frobenius_norm_replicateCol (ι := Fin 1) (v := A.mulVec x.ofLp)
  have hx :
      ‖replicateCol (Fin 1) x.ofLp‖ = ‖WithLp.toLp 2 x.ofLp‖ :=
    frobenius_norm_replicateCol (ι := Fin 1) (v := x.ofLp)
  calc
    ‖A.toEuclideanLin.toContinuousLinearMap x‖ = ‖WithLp.toLp 2 (A.mulVec x.ofLp)‖ := by
      change ‖A.toEuclideanLin x‖ = _
      rfl
    _ = ‖replicateCol (Fin 1) (A.mulVec x.ofLp)‖ := by
      symm
      exact hmulVec
    _ = ‖A * replicateCol (Fin 1) x.ofLp‖ := by
      rw [← replicateCol_mulVec]
    _ ≤ ‖A‖ * ‖replicateCol (Fin 1) x.ofLp‖ := frobenius_norm_mul A _
    _ = ‖A‖ * ‖WithLp.toLp 2 x.ofLp‖ := by
      rw [hx]
    _ = ‖A‖ * ‖x‖ := by
      rfl

namespace Matrix

/-- The singular values of a matrix over an `RCLike` field, exposed on the matrix owner surface by
transporting the canonical singular-value sequence of the associated Euclidean linear map. This
bridge keeps the proof-only `DecidableEq n` instance out of downstream theorem statements. -/
noncomputable abbrev singularValues {𝕜 : Type*} [RCLike 𝕜]
    {m : Type u} {n : Type v} [Fintype m] [Fintype n] (A : Matrix m n 𝕜) : ℕ →₀ ℝ :=
  let _ : DecidableEq n := Classical.decEq n
  A.toEuclideanLin.singularValues

theorem singularValues_nonneg {𝕜 : Type*} [RCLike 𝕜]
    {m : Type u} {n : Type v} [Fintype m] [Fintype n] (A : Matrix m n 𝕜) (i : ℕ) :
    0 ≤ A.singularValues i := by
  let _ : DecidableEq n := Classical.decEq n
  simpa [singularValues] using A.toEuclideanLin.singularValues_nonneg i

theorem singularValues_antitone {𝕜 : Type*} [RCLike 𝕜]
    {m : Type u} {n : Type v} [Fintype m] [Fintype n] (A : Matrix m n 𝕜) :
    Antitone A.singularValues := by
  let _ : DecidableEq n := Classical.decEq n
  simpa [singularValues] using A.toEuclideanLin.singularValues_antitone

theorem singularValues_of_finrank_le {𝕜 : Type*} [RCLike 𝕜]
    {m : Type u} {n : Type v} [Fintype m] [Fintype n] (A : Matrix m n 𝕜) {i : ℕ}
    (hi : Module.finrank 𝕜 (EuclideanSpace 𝕜 n) ≤ i) :
    A.singularValues i = 0 := by
  let _ : DecidableEq n := Classical.decEq n
  simpa [singularValues] using A.toEuclideanLin.singularValues_of_finrank_le hi

/-- The continuous linear map induced by a matrix on Euclidean space has operator norm bounded by
its Frobenius norm. -/
theorem toEuclideanLin_opNorm_le_frobenius_norm {𝕜 : Type*} [RCLike 𝕜]
    {m : Type u} {n : Type v} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n 𝕜) :
    ‖A.toEuclideanLin.toContinuousLinearMap‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound
      A.toEuclideanLin.toContinuousLinearMap (norm_nonneg A) fun x ↦ ?_
  simpa using toEuclideanLin_apply_le_frobenius_norm A x

end Matrix

/-- Example 2.19: the operator norm of the continuous linear map induced by a matrix is bounded by
its Frobenius norm. -/
theorem matrix_operator_norm_le_frobenius_norm {𝕜 : Type*} [RCLike 𝕜]
    {m : Type u} {n : Type v} [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n 𝕜) :
    ‖A.toEuclideanLin.toContinuousLinearMap‖ ≤ ‖A‖ :=
  Matrix.toEuclideanLin_opNorm_le_frobenius_norm A
