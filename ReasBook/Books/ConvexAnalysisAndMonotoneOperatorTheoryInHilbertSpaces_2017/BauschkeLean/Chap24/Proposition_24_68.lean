import Mathlib.Analysis.InnerProductSpace.PiL2
import BauschkeLean.Chap03.Example_3_9
import BauschkeLean.Chap12.ProximityOperator

open Matrix
open scoped BigOperators Matrix.Norms.Frobenius

noncomputable section

namespace ERealFunction

-- Semantic recall/local precedent: `lean_leansearch` only surfaced unrelated complex-analysis
-- proximity owners, so this item follows the local rectangular SVD owner
-- `singularValueDiagonal` from Chapter 3 together with the Chapter 12 proximal owner `Prox[_, _]`.

/-- The ambient Euclidean coordinate model `ℝ^(M×N)` for real `M × N` matrices. -/
abbrev RectangularMatrixSpace (M N : ℕ) : Type :=
  EuclideanSpace ℝ (Fin M × Fin N)

/-- The Euclidean vectorization of a real `M × N` matrix. -/
abbrev matrixToEuclidean {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℝ) :
    RectangularMatrixSpace M N :=
  (EuclideanSpace.equiv (Fin M × Fin N) ℝ).symm (fun p ↦ A p.1 p.2)

/-- The matrix represented by a vector in `RectangularMatrixSpace M N`. -/
abbrev euclideanToMatrix {M N : ℕ} (x : RectangularMatrixSpace M N) :
    Matrix (Fin M) (Fin N) ℝ :=
  fun i j ↦ (EuclideanSpace.equiv (Fin M × Fin N) ℝ x) (i, j)

@[simp] theorem matrixToEuclidean_apply {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℝ)
    (p : Fin M × Fin N) :
    matrixToEuclidean A p = A p.1 p.2 := by
  simp [matrixToEuclidean]

@[simp] theorem euclideanToMatrix_apply {M N : ℕ} (x : RectangularMatrixSpace M N)
    (i : Fin M) (j : Fin N) :
    euclideanToMatrix x i j = x (i, j) := by
  simp [euclideanToMatrix]

@[simp] theorem euclideanToMatrix_matrixToEuclidean {M N : ℕ}
    (A : Matrix (Fin M) (Fin N) ℝ) :
    euclideanToMatrix (matrixToEuclidean A) = A := by
  ext i j
  simp

@[simp] theorem matrixToEuclidean_euclideanToMatrix {M N : ℕ}
    (x : RectangularMatrixSpace M N) :
    matrixToEuclidean (euclideanToMatrix x) = x := by
  apply (EuclideanSpace.equiv (Fin M × Fin N) ℝ).injective
  funext p
  simp

/-- Helper for Proposition 24.68: the singular-value sum attached to `φ` stays in `]-∞,+∞]`. -/
theorem rectangularMatrixSingularValuePenalty_value_mem_Ioi_bot
    {M N : ℕ} (φ : ℝ → Set.Ioi (⊥ : EReal)) (x : RectangularMatrixSpace M N) :
    (∑ i : Fin (min M N), (φ ((euclideanToMatrix x).singularValues i.1) : EReal)) ∈
      Set.Ioi (⊥ : EReal) := sorry

/-- The singular-value penalty `A ↦ ∑ i, φ (σᵢ(A))`, represented on the ambient Euclidean model
`RectangularMatrixSpace M N`. -/
def rectangularMatrixSingularValuePenalty {M N : ℕ}
    (φ : ℝ → Set.Ioi (⊥ : EReal)) :
    RectangularMatrixSpace M N → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    ⟨∑ i : Fin (min M N), (φ ((euclideanToMatrix x).singularValues i.1) : EReal),
      rectangularMatrixSingularValuePenalty_value_mem_Ioi_bot φ x⟩

/-- Evaluating `rectangularMatrixSingularValuePenalty φ` gives the source sum
`∑ i, φ (σᵢ(A))`. -/
@[simp] theorem rectangularMatrixSingularValuePenalty_apply
    {M N : ℕ} (φ : ℝ → Set.Ioi (⊥ : EReal)) (x : RectangularMatrixSpace M N) :
    (rectangularMatrixSingularValuePenalty φ x : EReal) =
      ∑ i : Fin (min M N), (φ ((euclideanToMatrix x).singularValues i.1) : EReal) :=
  rfl

/-- Evaluating `rectangularMatrixSingularValuePenalty φ` at the Euclidean image of a matrix
recovers the source singular-value sum `∑ i, φ (σᵢ(A))`. -/
@[simp] theorem rectangularMatrixSingularValuePenalty_matrixToEuclidean_apply
    {M N : ℕ} (φ : ℝ → Set.Ioi (⊥ : EReal)) (A : Matrix (Fin M) (Fin N) ℝ) :
    (rectangularMatrixSingularValuePenalty φ (matrixToEuclidean A) : EReal) =
      ∑ i : Fin (min M N), (φ (A.singularValues i.1) : EReal) := by
  simpa using
    congrArg
      (fun B : Matrix (Fin M) (Fin N) ℝ ↦
        ∑ i : Fin (min M N), (φ (B.singularValues i.1) : EReal))
      (euclideanToMatrix_matrixToEuclidean A)

/-- The source diagonal matrix `Σ_f`, whose first `A.rank` diagonal entries are
`Prox[φ, hφ] (σᵢ(A))` and whose remaining diagonal entries are `0`. -/
def proxSingularValueDiagonal {M N : ℕ}
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (A : Matrix (Fin M) (Fin N) ℝ) :
    Matrix (Fin M) (Fin N) ℝ :=
  fun i j ↦
    if _ : i.1 = j.1 then
      if _ : i.1 < A.rank then Prox[φ, hφ] (A.singularValues i.1) else 0
    else 0

/-- Evaluating `proxSingularValueDiagonal φ hφ A` unfolds its diagonal-zero definition. -/
@[simp] theorem proxSingularValueDiagonal_apply
    {M N : ℕ} (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (A : Matrix (Fin M) (Fin N) ℝ) (i : Fin M) (j : Fin N) :
    proxSingularValueDiagonal φ hφ A i j =
      if _ : i.1 = j.1 then
        if _ : i.1 < A.rank then Prox[φ, hφ] (A.singularValues i.1) else 0
      else 0 :=
  rfl

/-- The matrix `U * singularValueDiagonal A * Vᵀ` attached to a chosen SVD of `A`. -/
abbrev svdRecomposition {M N : ℕ}
    (A : Matrix (Fin M) (Fin N) ℝ)
    (U : Matrix.orthogonalGroup (Fin M) ℝ)
    (V : Matrix.orthogonalGroup (Fin N) ℝ) :
    Matrix (Fin M) (Fin N) ℝ :=
  ((U : Matrix (Fin M) (Fin M) ℝ) * singularValueDiagonal A) *
    (V : Matrix (Fin N) (Fin N) ℝ)ᵀ

/-- The matrix `U * proxSingularValueDiagonal φ hφ A * Vᵀ` from Proposition 24.68. -/
abbrev proxSvdRecomposition {M N : ℕ}
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ))
    (A : Matrix (Fin M) (Fin N) ℝ)
    (U : Matrix.orthogonalGroup (Fin M) ℝ)
    (V : Matrix.orthogonalGroup (Fin N) ℝ) :
    Matrix (Fin M) (Fin N) ℝ :=
  ((U : Matrix (Fin M) (Fin M) ℝ) * proxSingularValueDiagonal φ hφ A) *
    (V : Matrix (Fin N) (Fin N) ℝ)ᵀ

/-- If `2 ≤ min M N` and `φ ∈ Γ₀(ℝ)` is even, then the singular-value penalty
`rectangularMatrixSingularValuePenalty φ` belongs to `Γ₀(RectangularMatrixSpace M N)`. -/
theorem rectangularMatrixSingularValuePenalty_mem_gammaZero
    {M N : ℕ} (hm : 2 ≤ min M N)
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ)) (heven : Function.Even φ) :
    rectangularMatrixSingularValuePenalty φ ∈ Γ₀(RectangularMatrixSpace M N) := sorry

/-- Proposition 24.68: if `2 ≤ min M N`, if `φ ∈ Γ₀(ℝ)` is even, and if
`A = U * singularValueDiagonal A * Vᵀ` is a chosen singular value decomposition of `A`, then the
matrix represented by the proximity operator of `rectangularMatrixSingularValuePenalty φ` at `A`
is `U * proxSingularValueDiagonal φ hφ A * Vᵀ`. -/
theorem prox_rectangularMatrixSingularValuePenalty_eq_orthogonal_conj_proxSingularValueDiagonal
    {M N : ℕ} (hm : 2 ≤ min M N)
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ)) (heven : Function.Even φ)
    (A : Matrix (Fin M) (Fin N) ℝ)
    (U : Matrix.orthogonalGroup (Fin M) ℝ)
    (V : Matrix.orthogonalGroup (Fin N) ℝ)
    (hsvd : A = svdRecomposition A U V) :
    euclideanToMatrix
        (Prox[rectangularMatrixSingularValuePenalty φ,
          rectangularMatrixSingularValuePenalty_mem_gammaZero hm φ hφ heven]
          (matrixToEuclidean A)) =
      proxSvdRecomposition φ hφ A U V := sorry

/-- The coordinate-model form of Proposition 24.68 is obtained by re-vectorizing the matrix-side
proximal identity. -/
theorem prox_rectangularMatrixSingularValuePenalty_matrixToEuclidean
    {M N : ℕ} (hm : 2 ≤ min M N)
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(ℝ)) (heven : Function.Even φ)
    (A : Matrix (Fin M) (Fin N) ℝ)
    (U : Matrix.orthogonalGroup (Fin M) ℝ)
    (V : Matrix.orthogonalGroup (Fin N) ℝ)
    (hsvd : A = svdRecomposition A U V) :
    Prox[rectangularMatrixSingularValuePenalty φ,
      rectangularMatrixSingularValuePenalty_mem_gammaZero hm φ hφ heven] (matrixToEuclidean A) =
      matrixToEuclidean (proxSvdRecomposition φ hφ A U V) := by
  simpa using
    congrArg matrixToEuclidean
      (prox_rectangularMatrixSingularValuePenalty_eq_orthogonal_conj_proxSingularValueDiagonal
        hm φ hφ heven A U V hsvd)

end ERealFunction
