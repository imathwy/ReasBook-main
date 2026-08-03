import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Recall
import BauschkeLean.Chap02.Example_2_4
import BauschkeLean.Chap02.Example_2_19

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open Matrix
open WithLp
open scoped BigOperators

variable {m : Type u} {n : Type v} [Fintype m] [Fintype n]

/- Fact 24.67 (1): for real rectangular matrices, the Hilbert inner product on the iterated `L2`
model of matrices is given by `trace (Aᵀ * B)`. This is the canonical matrix owner theorem already
recorded in Chapter 2. -/
recall Matrix.inner_toLp_eq_trace_transpose_mul

/-- Fact 24.67 (1), absolute-value form. -/
theorem matrix_to_hilbert_inner_abs_eq_trace_transpose_mul_abs
    (A B : Matrix m n ℝ) :
    |trace (Aᵀ * B)| =
      |inner ℝ (toLp 2 (fun i ↦ toLp 2 (A i))) (toLp 2 (fun i ↦ toLp 2 (B i)))| := by
  simpa using congrArg abs (Matrix.inner_toLp_eq_trace_transpose_mul A B).symm

/-- Helper for Fact 24.67: the symmetric dilation `[[0, A], [Aᵀ, 0]]` attached to a rectangular
real matrix `A`. -/
private def symmetric_dilation (A : Matrix m n ℝ) : Matrix (m ⊕ n) (m ⊕ n) ℝ :=
  Matrix.fromBlocks 0 A Aᵀ 0

/-- Helper for Fact 24.67: cyclically rewriting the mixed block trace shows
`trace (A * Bᵀ) = trace (Aᵀ * B)`. -/
private theorem trace_mul_transpose_eq_trace_transpose_mul
    (A B : Matrix m n ℝ) :
    trace (A * Bᵀ) = trace (Aᵀ * B) := by
  -- First cycle the product, then identify the cycled term as the transpose of `Aᵀ * B`.
  calc
    trace (A * Bᵀ) = trace (Bᵀ * A) := Matrix.trace_mul_comm A Bᵀ
    _ = trace ((Bᵀ * A)ᵀ) := by rw [Matrix.trace_transpose]
    _ = trace (Aᵀ * B) := by simp [Matrix.transpose_mul]

omit [Fintype m] [Fintype n] in
/-- Helper for Fact 24.67: negating the rectangular matrix negates its symmetric dilation blockwise.
-/
private theorem symmetric_dilation_neg
    (A : Matrix m n ℝ) :
    symmetric_dilation (-A) = - symmetric_dilation A := by
  -- Each block changes sign entrywise, and `(−A)ᵀ = −Aᵀ` on the lower-left block.
  ext i j
  cases i <;> cases j <;> simp [symmetric_dilation]

omit [Fintype m] [Fintype n] in
/-- Helper for Fact 24.67: the symmetric dilation of a real matrix is Hermitian. -/
private theorem symmetric_dilation_isHermitian
    (A : Matrix m n ℝ) :
    (symmetric_dilation A).IsHermitian := by
  -- Each diagonal block is zero-Hermitian and the off-diagonal blocks are transposes of each
  -- other, so the block Hermitian criterion applies directly.
  refine Matrix.IsHermitian.fromBlocks ?_ ?_ ?_
  · simp
  · simp
  · simp

/-- Helper for Fact 24.67: squaring the symmetric dilation separates into the two Gram blocks
`A * Aᵀ` and `Aᵀ * A`. -/
private theorem symmetric_dilation_mul_self
    (A : Matrix m n ℝ) :
    symmetric_dilation A * symmetric_dilation A =
      Matrix.fromBlocks (A * Aᵀ) 0 0 (Aᵀ * A) := by
  -- The off-diagonal blocks vanish because every term there contains a zero factor.
  simp [symmetric_dilation, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul]

/-- Helper for Fact 24.67: conjugating by the block sign involution sends the symmetric dilation to
its negative, which is the source-facing sign symmetry of the dilation spectrum. -/
private theorem block_sign_conj_symmetric_dilation_eq_neg
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) :
    let J : Matrix (m ⊕ n) (m ⊕ n) ℝ :=
      Matrix.fromBlocks (1 : Matrix m m ℝ) 0 0 (- (1 : Matrix n n ℝ))
    J * symmetric_dilation A * Jᵀ = - symmetric_dilation A := by
  classical
  dsimp
  -- Left multiplication flips the lower block, and right multiplication flips the right block.
  rw [show Matrix.fromBlocks (1 : Matrix m m ℝ) 0 0 (- (1 : Matrix n n ℝ)) *
      symmetric_dilation A =
        Matrix.fromBlocks 0 A (-Aᵀ) 0 by
          simp [symmetric_dilation, Matrix.fromBlocks_multiply, Matrix.mul_zero,
            Matrix.zero_mul]]
  rw [show Matrix.fromBlocks 0 A (-Aᵀ) 0 *
      (Matrix.fromBlocks (1 : Matrix m m ℝ) 0 0 (- (1 : Matrix n n ℝ)))ᵀ =
        Matrix.fromBlocks 0 (-A) (-Aᵀ) 0 by
          simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.mul_zero]]
  -- The resulting blocks are exactly the entrywise negation of `symmetric_dilation A`.
  simpa [symmetric_dilation] using symmetric_dilation_neg A

/-- Helper for Fact 24.67: the Frobenius pairing of rectangular matrices is encoded by the trace of
their symmetric dilations, up to the expected factor `2`. -/
private theorem symmetric_dilation_trace_mul_eq_two_trace_transpose_mul
    (A B : Matrix m n ℝ) :
    trace (symmetric_dilation A * symmetric_dilation B) =
      2 * trace (Aᵀ * B) := by
  -- Multiply the block matrices, split the trace over the two diagonal blocks, and then identify
  -- the top-left trace with the bottom-right trace by a cyclic transpose rewrite.
  rw [show symmetric_dilation A * symmetric_dilation B =
      Matrix.fromBlocks (A * Bᵀ) 0 0 (Aᵀ * B) by
        simp [symmetric_dilation, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul]]
  rw [Matrix.trace, Fintype.sum_sum_type]
  simp [Matrix.trace, two_mul]
  simpa [Matrix.trace] using trace_mul_transpose_eq_trace_transpose_mul A B

/-- Helper for Fact 24.67: if `P` and `Q` are orthogonal matrices, then the overlap coefficients
`c i j = |P i j| * |Q j i|` have every row sum and every column sum bounded by `1`. -/
private theorem orthogonal_overlap_abs_mul_row_col_sum_le_one {N : ℕ}
    (P Q : Matrix (Fin N) (Fin N) ℝ)
    (hP : P ∈ Matrix.orthogonalGroup (Fin N) ℝ)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin N) ℝ) :
    (∀ i, ∑ j, |P i j| * |Q j i| ≤ 1) ∧
      (∀ j, ∑ i, |P i j| * |Q j i| ≤ 1) := by
  have hPP_left : P * Pᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (n := Fin N) (R := ℝ)).mp hP
  have hPP_right : Pᵀ * P = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := Fin N) (R := ℝ)).mp hP
  have hQQ_left : Q * Qᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (n := Fin N) (R := ℝ)).mp hQ
  have hQQ_right : Qᵀ * Q = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := Fin N) (R := ℝ)).mp hQ
  constructor
  · intro i
    have hrow : ∑ j, |P i j| ^ 2 = 1 := by
      -- Read the squared `ℓ²` norm of the `i`-th row off the diagonal of `P * Pᵀ = 1`.
      have hdiag := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => M i i) hPP_left
      simp [Matrix.mul_apply] at hdiag
      simpa [pow_two] using hdiag
    have hcol : ∑ j, |Q j i| ^ 2 = 1 := by
      -- Read the squared `ℓ²` norm of the `i`-th column off the diagonal of `Qᵀ * Q = 1`.
      have hdiag := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => M i i) hQQ_right
      simp [Matrix.mul_apply] at hdiag
      simpa [pow_two] using hdiag
    -- Cauchy-Schwarz bounds the overlap row by the product of the row and column norms.
    have hcs :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun j : Fin N => |P i j|) (fun j ↦ |Q j i|)
    rw [hrow, hcol] at hcs
    simpa using hcs
  · intro j
    have hcol : ∑ i, |P i j| ^ 2 = 1 := by
      -- This time use `Pᵀ * P = 1` to read the squared norm of the `j`-th column of `P`.
      have hdiag := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => M j j) hPP_right
      simp [Matrix.mul_apply] at hdiag
      simpa [pow_two] using hdiag
    have hrow : ∑ i, |Q j i| ^ 2 = 1 := by
      -- And use `Q * Qᵀ = 1` to read the squared norm of the `j`-th row of `Q`.
      have hdiag := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => M j j) hQQ_left
      simp [Matrix.mul_apply] at hdiag
      simpa [pow_two] using hdiag
    -- The same Cauchy-Schwarz step gives the column bound.
    have hcs :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i : Fin N => |P i j|) (fun i ↦ |Q j i|)
    rw [hcol, hrow] at hcs
    simpa using hcs

/-- Helper for Fact 24.67: the squared-entry matrix of an orthogonal matrix is doubly stochastic. -/
private theorem sq_entry_matrix_mem_doublyStochastic
    {N : ℕ} {W : Matrix (Fin N) (Fin N) ℝ}
    (hWWt : W * Wᵀ = 1) (hWtW : Wᵀ * W = 1) :
    (fun i j ↦ (W i j) ^ 2) ∈ doublyStochastic ℝ (Fin N) := by
  let M : Matrix (Fin N) (Fin N) ℝ := fun i j ↦ (W i j) ^ 2
  change M ∈ doublyStochastic ℝ (Fin N)
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact sq_nonneg (W i j)
  · intro i
    -- Read the row sum of squared entries off the diagonal of `W * Wᵀ = 1`.
    have hdiag := congrArg (fun A : Matrix (Fin N) (Fin N) ℝ ↦ A i i) hWWt
    simp [Matrix.mul_apply] at hdiag
    simpa [M, pow_two] using hdiag
  · intro j
    -- Read the column sum of squared entries off the diagonal of `Wᵀ * W = 1`.
    have hdiag := congrArg (fun A : Matrix (Fin N) (Fin N) ℝ ↦ A j j) hWtW
    simp [Matrix.mul_apply] at hdiag
    simpa [M, pow_two] using hdiag

/-- Helper for Fact 24.67: conjugating a diagonal matrix by an orthogonal matrix averages its
diagonal entries against the squared-entry matrix. -/
private theorem diag_orthogonal_conj_diagonal_eq_sq_entry_mulVec
    {N : ℕ} (W : Matrix (Fin N) (Fin N) ℝ) (d : Fin N → ℝ) :
    Matrix.diag (W * Matrix.diagonal d * Wᵀ) = (fun i j ↦ (W i j) ^ 2) *ᵥ d := by
  -- Expand the diagonal entry and collapse the intermediate diagonal matrix to a single sum.
  ext i
  rw [Matrix.diag_apply, Matrix.mul_apply]
  simp [Matrix.mulVec, dotProduct, pow_two, mul_left_comm, mul_comm]

/-- Helper for Fact 24.67: after diagonalizing two Hermitian matrices in orthogonal coordinates,
their trace pairing depends only on the overlap matrix of squared coordinates. -/
private theorem trace_orthogonal_conj_diagonal_mul_eq_dotProduct_sq_entry_mulVec_fin
    {N : ℕ} (U V : Matrix.orthogonalGroup (Fin N) ℝ) (a b : Fin N → ℝ) :
    let W : Matrix (Fin N) (Fin N) ℝ :=
      (U : Matrix (Fin N) (Fin N) ℝ)ᵀ * (V : Matrix (Fin N) (Fin N) ℝ)
    Matrix.trace
        (((((U : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal a) *
              (U : Matrix (Fin N) (Fin N) ℝ)ᵀ) *
            (((V : Matrix (Fin N) (Fin N) ℝ) * Matrix.diagonal b) *
              (V : Matrix (Fin N) (Fin N) ℝ)ᵀ)) : Matrix (Fin N) (Fin N) ℝ) =
      dotProduct a (((fun i j ↦ (W i j) ^ 2) : Matrix (Fin N) (Fin N) ℝ) *ᵥ b) := by
  classical
  let UM : Matrix (Fin N) (Fin N) ℝ := U
  let VM : Matrix (Fin N) (Fin N) ℝ := V
  let W : Matrix (Fin N) (Fin N) ℝ := UMᵀ * VM
  have hUtU : UMᵀ * UM = 1 := by
    -- Orthogonality identifies the transpose of `U` with its inverse on the left.
    simpa [UM] using Unitary.coe_star_mul_self U
  have hUUt : UM * UMᵀ = 1 := by
    -- The same orthogonality relation also gives the right inverse identity.
    simpa [UM] using Unitary.coe_mul_star_self U
  -- Move the outer orthogonal change of basis through the trace and read off the diagonal core.
  calc
    Matrix.trace (((UM * Matrix.diagonal a) * UMᵀ) * ((VM * Matrix.diagonal b) * VMᵀ))
        = Matrix.trace (UM * (Matrix.diagonal a * (W * Matrix.diagonal b * Wᵀ)) * UMᵀ) := by
            simp [UM, VM, W, Matrix.mul_assoc, hUUt]
    _ = Matrix.trace (((UMᵀ * UM) * (Matrix.diagonal a * (W * Matrix.diagonal b * Wᵀ))) :
          Matrix (Fin N) (Fin N) ℝ) := by
            simpa [Matrix.mul_assoc] using
              (Matrix.trace_mul_cycle UM (Matrix.diagonal a * (W * Matrix.diagonal b * Wᵀ)) UMᵀ)
    _ = Matrix.trace ((Matrix.diagonal a) * (W * Matrix.diagonal b * Wᵀ)) := by
          simp [hUtU]
    _ = dotProduct a (Matrix.diag (W * Matrix.diagonal b * Wᵀ)) := by
          simp [Matrix.trace, Matrix.mul_apply, dotProduct]
    _ = dotProduct a (((fun i j ↦ (W i j) ^ 2) : Matrix (Fin N) (Fin N) ℝ) *ᵥ b) := by
          rw [diag_orthogonal_conj_diagonal_eq_sq_entry_mulVec W b]
