import BauschkeLean.Chap12.Definition_12_16
import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap24.Proposition_24_68

open ERealFunction
open Matrix
open scoped BigOperators

noncomputable section

-- Semantic recall/local precedent: `lean_leansearch` only returned generic matrix norm facts, so
-- this item specializes the local Chapter 24 singular-value penalty owner from Proposition 24.68
-- together with the Chapter 12 scaled proximal notation `Prox[γ, ·]`.

namespace Matrix

/-- The nuclear norm of a real rectangular matrix, written as the full singular-value sum. -/
def nuclearNorm {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℝ) : ℝ :=
  ∑ i : Fin (min M N), A.singularValues i.1

/- Example 24.69: the textbook nuclear norm is written `‖A‖_*`. -/
notation "‖" A "‖_*" => nuclearNorm A

/-- Example 24.69 (1): for a real `M × N` matrix, the nuclear norm is the sum of the first
`A.rank` singular values, which is the zero-indexed form of `(24.137)`. -/
theorem nuclearNorm_eq_sum_range_rank_singularValues
    {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℝ) :
    ‖A‖_* = Finset.sum (Finset.range A.rank) (fun i ↦ A.singularValues i) := sorry

/-- The source matrix `Σ_nuc` from `(24.138)`, obtained by soft-thresholding the nonzero singular
values of `A` at the level `γ`. -/
abbrev nuclearSoftThresholdDiagonal {M N : ℕ}
    (γ : PosReal) (A : Matrix (Fin M) (Fin N) ℝ) :
    Matrix (Fin M) (Fin N) ℝ :=
  proxSingularValueDiagonal
    (γ • scaledNormKernel 1)
    (smul_mem_gammaZero
      (scaledNormKernel 1)
      (scaledNormKernel_mem_gammaZero 1)
      γ)
    A

/-- Evaluating `nuclearSoftThresholdDiagonal γ A` unfolds the diagonal soft-thresholding formula.
-/
@[simp] theorem nuclearSoftThresholdDiagonal_apply
    {M N : ℕ} (γ : PosReal) (A : Matrix (Fin M) (Fin N) ℝ) (i : Fin M) (j : Fin N) :
    nuclearSoftThresholdDiagonal γ A i j =
      if _ : i.1 = j.1 then
        if _ : i.1 < A.rank then max (A.singularValues i.1 - (γ : ℝ)) 0 else 0
      else 0 := sorry

end Matrix

namespace ERealFunction

/-- The `Γ₀` owner representing the nuclear-norm penalty on `RectangularMatrixSpace M N`. -/
abbrev nuclearNormPenalty {M N : ℕ} :
    RectangularMatrixSpace M N → Set.Ioi (⊥ : EReal) :=
  rectangularMatrixSingularValuePenalty (scaledNormKernel 1)

/-- The matrix `U * nuclearSoftThresholdDiagonal γ A * Vᵀ` attached to a chosen singular value
decomposition of `A`. -/
abbrev nuclearSoftThresholdSvdRecomposition {M N : ℕ}
    (γ : PosReal) (A : Matrix (Fin M) (Fin N) ℝ)
    (U : Matrix.orthogonalGroup (Fin M) ℝ)
    (V : Matrix.orthogonalGroup (Fin N) ℝ) :
    Matrix (Fin M) (Fin N) ℝ :=
  proxSvdRecomposition
    (γ • scaledNormKernel 1)
    (smul_mem_gammaZero
      (scaledNormKernel 1)
      (scaledNormKernel_mem_gammaZero 1)
      γ)
    A U V

/-- Evaluating `nuclearNormPenalty` at a matrix recovers the singular-value sum `‖A‖_*`. -/
@[simp] theorem nuclearNormPenalty_apply {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℝ) :
    (nuclearNormPenalty (matrixToEuclidean A) : EReal) = (‖A‖_* : ℝ) := sorry

/-- The nuclear-norm penalty belongs to `Γ₀(RectangularMatrixSpace M N)`. -/
theorem nuclearNormPenalty_mem_gammaZero {M N : ℕ} :
    nuclearNormPenalty ∈ Γ₀(RectangularMatrixSpace M N) := sorry

/-- Bridge view: Example 24.69 is the `φ = γ • scaledNormKernel 1` specialization of the
canonical singular-value proximal recomposition formula from Proposition 24.68. -/
theorem prox_nuclearNormPenalty_eq_proxSvdRecomposition
    {M N : ℕ} (γ : PosReal)
    (A : Matrix (Fin M) (Fin N) ℝ)
    (U : Matrix.orthogonalGroup (Fin M) ℝ)
    (V : Matrix.orthogonalGroup (Fin N) ℝ)
    (hsvd : A = svdRecomposition A U V) :
    Prox[γ, nuclearNormPenalty, nuclearNormPenalty_mem_gammaZero] (matrixToEuclidean A) =
      matrixToEuclidean
        (proxSvdRecomposition
          (γ • scaledNormKernel 1)
          (smul_mem_gammaZero
            (scaledNormKernel 1)
            (scaledNormKernel_mem_gammaZero 1)
            γ)
          A U V) := sorry

/-- Example 24.69 (2): if
`A = svdRecomposition A U V` is a chosen singular value decomposition, then the scaled proximity
operator of the nuclear norm is the conjugation of the source soft-thresholded diagonal matrix
`nuclearSoftThresholdDiagonal γ A` from `(24.138)`, which is the `scaledNormKernel 1`
specialization of Proposition 24.68 and yields formula `(24.139)`. -/
theorem prox_nuclearNormPenalty_eq_orthogonal_conj_nuclearSoftThresholdDiagonal
    {M N : ℕ} (γ : PosReal)
    (A : Matrix (Fin M) (Fin N) ℝ)
    (U : Matrix.orthogonalGroup (Fin M) ℝ)
    (V : Matrix.orthogonalGroup (Fin N) ℝ)
    (hsvd : A = svdRecomposition A U V) :
    Prox[γ, nuclearNormPenalty, nuclearNormPenalty_mem_gammaZero] (matrixToEuclidean A) =
      matrixToEuclidean (nuclearSoftThresholdSvdRecomposition γ A U V) := by
  simpa [nuclearSoftThresholdSvdRecomposition] using
    prox_nuclearNormPenalty_eq_proxSvdRecomposition γ A U V hsvd

end ERealFunction

end
