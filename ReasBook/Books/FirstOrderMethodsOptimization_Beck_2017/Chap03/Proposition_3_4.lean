import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_14
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_33

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

noncomputable section

section SymmetricMatrices

open Matrix

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "𝕊" => symmetricMatrices n

/- Proposition 3.4 is `source-facing` in the chapter spectral-extendedRealSubdifferential API. The ambient
owner object for the matrix variable is the canonical submodule `symmetricMatrices n = 𝕊^n` from
Definition 1.30, while the spectral owner data comes from mathlib's
`Matrix.IsHermitian.eigenvalues`. The public declarations below keep the book's
maximum-eigenvalue function and rank-one symmetric matrix as the source-facing views derived from
those owners. -/

recall euclideanSubdifferentialAt

-- Proof sketch: the project owner criterion `mem_symmetricMatrices_iff` identifies membership in
-- `𝕊^n` with symmetry. The transpose of `vvᵀ` is again `vvᵀ` by `transpose_vecMulVec`.
/-- The real rank-one matrix `vvᵀ` belongs to the symmetric-matrix space `𝕊^n`. -/
private theorem rankOneMatrix_mem_symmetricMatrices (v : E) :
    vecMulVec v v ∈ symmetricMatrices n := by
  rw [mem_symmetricMatrices_iff, transpose_vecMulVec]

variable [NeZero n]

/-- `symmetricMaxEigenvalue X` is the largest eigenvalue of the symmetric matrix `X`, using the
canonical descending ordering of the Hermitian spectrum. -/
noncomputable def symmetricMaxEigenvalue (X : 𝕊) : ℝ :=
  let hX := X.property.isHermitian
  hX.eigenvalues 0

/-- `symmetricRankOne v` is the symmetric rank-one matrix `vvᵀ`, regarded as an element of
`𝕊^n`. -/
def symmetricRankOne (v : E) : 𝕊 :=
  ⟨vecMulVec v v, rankOneMatrix_mem_symmetricMatrices v⟩

-- Proof sketch: use the Rayleigh quotient characterization
-- `λ_max Y = max_{‖u‖ = 1} uᵀYu`, evaluate it at the given eigenvector `v`, and rewrite
-- `vᵀ(Y - X)v` as the Frobenius inner product with `vvᵀ`, then apply the Riesz identification
-- between `𝕊^n` and its continuous dual, as packaged by `euclideanSubdifferentialAt`.
/-- Proposition 3.4: if `v` is a unit eigenvector of the symmetric matrix `X` for the largest
eigenvalue, then the rank-one matrix `vvᵀ` belongs to the Euclidean extendedRealSubdifferential of the
maximum-eigenvalue function at `X`; equivalently, via the Frobenius trace-pairing Riesz
identification, it represents a dual subgradient at `X`. -/
theorem symmetricRankOne_mem_euclideanSubdifferentialAt_symmetricMaxEigenvalue
    (X : 𝕊) (v : E) (hv_norm : ‖v‖ = 1)
    (hv_eigen : (X : Matrix (Fin n) (Fin n) ℝ) *ᵥ v = symmetricMaxEigenvalue X • v) :
    symmetricRankOne v ∈ euclideanSubdifferentialAt symmetricMaxEigenvalue X := sorry

end SymmetricMatrices
