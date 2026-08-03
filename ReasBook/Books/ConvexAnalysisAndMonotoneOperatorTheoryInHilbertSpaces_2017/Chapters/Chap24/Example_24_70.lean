import BauschkeLean.Chap24.Example_24_38
import BauschkeLean.Chap24.Proposition_24_68

open Matrix
open scoped BigOperators

noncomputable section

-- Semantic recall/local precedent: `lean_leansearch` did not surface a project Schatten owner, so
-- this file follows Proposition 24.68's full singular-value indexing over `Fin (min M N)` and
-- exposes Example 24.70 as the identification with the truncated rank sum from the source.

namespace Matrix

/-- Helper definition: the Schatten `p`-norm written as the `ℓ^p` expression over the full
singular-value index set `Fin (min M N)`. -/
def schattenNorm {M N : ℕ} (p : ℝ) (A : Matrix (Fin M) (Fin N) ℝ) : ℝ :=
  (∑ i : Fin (min M N), A.singularValues i.1 ^ p) ^ (1 / p)

/- Example 24.70: the textbook Schatten `p`-norm is written `‖A‖_Sch[p]`. -/
notation "‖" A "‖_Sch[" p "]" => schattenNorm p A

/-- Example 24.70: if `p ∈ ]1,+∞[`, then the Schatten `p`-norm of a real rectangular matrix `A`
is the `ℓ^p` norm of the nonzero singular values,
`(∑ i in Finset.range A.rank, A.singularValues i ^ p) ^ (1 / p)`. -/
theorem schattenNorm_eq_sum_range_rank_singularValues
    {M N : ℕ} (p : ℝ) (hp : 1 < p) (A : Matrix (Fin M) (Fin N) ℝ) :
    ‖A‖_Sch[p] =
      (Finset.sum (Finset.range A.rank) fun i ↦ A.singularValues i ^ p) ^ (1 / p) := sorry

end Matrix

namespace ERealFunction

/-- The Example 24.70 Schatten-power penalty `A ↦ γ * ‖A‖_Sch[p]^p`, packaged through
the rectangular singular-value penalty owner from Proposition 24.68 specialized to
`φ = γ • absPowerFunction p`. -/
abbrev schattenPowerPenalty {M N : ℕ} (p : ℝ) (γ : PosReal) :
    RectangularMatrixSpace M N → Set.Ioi (⊥ : EReal) :=
  rectangularMatrixSingularValuePenalty (γ • absPowerFunction p)

/-- The scalar power model `η ↦ |η|^p`, viewed as an `EReal`-valued owner, is even. -/
theorem absPowerFunction_even (p : ℝ) :
    Function.Even (absPowerFunction p) := by
  intro ξ
  apply Subtype.ext
  simp [absPowerFunction, abs_neg]

/-- Positive scaling preserves the evenness of the scalar power model `η ↦ |η|^p`. -/
theorem smul_absPowerFunction_even (p : ℝ) (γ : PosReal) :
    Function.Even (γ • absPowerFunction p) := by
  intro ξ
  apply Subtype.ext
  simp [abs_neg]

/-- The source diagonal matrix whose first `A.rank` diagonal entries are the scalar proximal
points from Example 24.38 applied to the singular values of `A`, and whose remaining diagonal
entries are `0`. -/
abbrev proxSchattenPowerSingularValueDiagonal {M N : ℕ}
    (p : ℝ) (hp : 1 < p) (γ : PosReal) (A : Matrix (Fin M) (Fin N) ℝ) :
    Matrix (Fin M) (Fin N) ℝ :=
  proxSingularValueDiagonal (γ • absPowerFunction p)
    (smul_mem_gammaZero (absPowerFunction p) (absPowerFunction_mem_gammaZero p hp) γ) A

/-- The matrix `U * proxSchattenPowerSingularValueDiagonal p hp γ A * Vᵀ` attached to a chosen
singular value decomposition of `A`. -/
abbrev proxSchattenPowerSvdRecomposition {M N : ℕ}
    (p : ℝ) (hp : 1 < p) (γ : PosReal) (A : Matrix (Fin M) (Fin N) ℝ)
    (U : Matrix.orthogonalGroup (Fin M) ℝ)
    (V : Matrix.orthogonalGroup (Fin N) ℝ) :
    Matrix (Fin M) (Fin N) ℝ :=
  proxSvdRecomposition (γ • absPowerFunction p)
    (smul_mem_gammaZero (absPowerFunction p) (absPowerFunction_mem_gammaZero p hp) γ) A U V

/-- Evaluating `schattenPowerPenalty p γ` at a matrix gives the source penalty
`γ * ‖A‖_Sch[p]^p`. -/
theorem schattenPowerPenalty_apply_eq_smul_schattenNorm
    {M N : ℕ} (p : ℝ) (hp : 1 < p) (γ : PosReal) (A : Matrix (Fin M) (Fin N) ℝ) :
    (schattenPowerPenalty p γ (matrixToEuclidean A) : EReal) =
      (((γ : ℝ) * ‖A‖_Sch[p] ^ p) : ℝ) := sorry

/-- Evaluating `schattenPowerPenalty p γ` at a matrix gives the source sum
`γ * ∑_{i < rank A} σᵢ(A)^p`. -/
theorem schattenPowerPenalty_apply_eq_smul_sum_range_rank_singularValues
    {M N : ℕ} (p : ℝ) (hp : 1 < p) (γ : PosReal) (A : Matrix (Fin M) (Fin N) ℝ) :
    (schattenPowerPenalty p γ (matrixToEuclidean A) : EReal) =
      (((γ : ℝ) *
          Finset.sum (Finset.range A.rank) fun i ↦ A.singularValues i ^ p) : ℝ) := sorry

/-- Bridge view: under the dimension hypothesis required by Proposition 24.68, the Schatten-power
penalty `A ↦ γ * ‖A‖_Sch[p]^p` belongs to `Γ₀(RectangularMatrixSpace M N)`. -/
theorem schattenPowerPenalty_mem_gammaZero
    {M N : ℕ} (hm : 2 ≤ min M N) (p : ℝ) (hp : 1 < p) (γ : PosReal) :
    schattenPowerPenalty p γ ∈ Γ₀(RectangularMatrixSpace M N) := by
  simpa [schattenPowerPenalty] using
    rectangularMatrixSingularValuePenalty_mem_gammaZero hm
      (γ • absPowerFunction p)
      (smul_mem_gammaZero (absPowerFunction p) (absPowerFunction_mem_gammaZero p hp) γ)
      (smul_absPowerFunction_even p γ)

/-- Applying Proposition 24.68 with `φ = γ • absPowerFunction p` yields the proximal
point of the Schatten-power penalty by conjugating the diagonal matrix of scalar
proximal points of the singular values. -/
theorem prox_schattenPowerPenalty_eq_orthogonal_conj_proxSingularValueDiagonal
    {M N : ℕ} (hm : 2 ≤ min M N) (p : ℝ) (hp : 1 < p) (γ : PosReal)
    (A : Matrix (Fin M) (Fin N) ℝ)
    (U : Matrix.orthogonalGroup (Fin M) ℝ)
    (V : Matrix.orthogonalGroup (Fin N) ℝ)
    (hsvd : A = svdRecomposition A U V) :
    Prox[schattenPowerPenalty p γ,
      schattenPowerPenalty_mem_gammaZero hm p hp γ] (matrixToEuclidean A) =
      matrixToEuclidean
        (proxSchattenPowerSvdRecomposition p hp γ A U V) := by
  simpa [schattenPowerPenalty, proxSchattenPowerSvdRecomposition] using
    prox_rectangularMatrixSingularValuePenalty_matrixToEuclidean hm
      (γ • absPowerFunction p)
      (smul_mem_gammaZero (absPowerFunction p) (absPowerFunction_mem_gammaZero p hp) γ)
      (smul_absPowerFunction_even p γ)
      A U V hsvd

end ERealFunction
