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

/-- Helper for Fact 24.67: the block sign matrix is its own transpose. -/
private theorem block_sign_transpose_eq_self
    [DecidableEq m] [DecidableEq n] :
    let J : Matrix (m ⊕ n) (m ⊕ n) ℝ :=
      Matrix.fromBlocks (1 : Matrix m m ℝ) 0 0 (- (1 : Matrix n n ℝ))
    Jᵀ = J := by
  classical
  dsimp
  -- The sign matrix is diagonal by blocks, so transposition leaves it unchanged.
  simp [Matrix.fromBlocks_transpose]

/-- Helper for Fact 24.67: the block sign matrix is an involution. -/
private theorem block_sign_mul_self
    [DecidableEq m] [DecidableEq n] :
    let J : Matrix (m ⊕ n) (m ⊕ n) ℝ :=
      Matrix.fromBlocks (1 : Matrix m m ℝ) 0 0 (- (1 : Matrix n n ℝ))
    J * J = 1 := by
  classical
  dsimp
  -- Squaring the block signs cancels the lower `-1` block and leaves the identity matrix.
  ext i j <;> cases i <;> cases j <;> simp [Matrix.fromBlocks_multiply, Matrix.one_apply]

/-- Helper for Fact 24.67: the sign-conjugation symmetry forces the symmetric dilation and its
negative to have the same characteristic polynomial. -/
private theorem symmetric_dilation_charpoly_eq_neg
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) :
    (symmetric_dilation A).charpoly = (- symmetric_dilation A).charpoly := by
  classical
  let J : Matrix (m ⊕ n) (m ⊕ n) ℝ :=
    Matrix.fromBlocks (1 : Matrix m m ℝ) 0 0 (- (1 : Matrix n n ℝ))
  let Junit : (Matrix (m ⊕ n) (m ⊕ n) ℝ)ˣ :=
    ⟨J, J, by
      -- The block sign involution is its own inverse.
      simpa [J] using (block_sign_mul_self (m := m) (n := n)),
      by
      simpa [J] using (block_sign_mul_self (m := m) (n := n))⟩
  have hconj :
      J * symmetric_dilation A * J = - symmetric_dilation A := by
    -- Route correction: rewrite the earlier `J * D(A) * Jᵀ = -D(A)` identity using `Jᵀ = J`.
    have hJT : Jᵀ = J := by
      simpa [J] using (block_sign_transpose_eq_self (m := m) (n := n))
    calc
      J * symmetric_dilation A * J = J * symmetric_dilation A * Jᵀ := by rw [hJT]
      _ = - symmetric_dilation A := by
            simpa [J] using
              (block_sign_conj_symmetric_dilation_eq_neg (m := m) (n := n) (A := A))
  -- Conjugation by the involution preserves the characteristic polynomial.
  simpa [Junit, hconj] using
    (Matrix.charpoly_units_conj Junit (symmetric_dilation A)).symm

/-- Helper for Fact 24.67: the symmetric dilation has zero trace because its diagonal blocks are
zero. -/
private theorem symmetric_dilation_trace_eq_zero
    (A : Matrix m n ℝ) :
    trace (symmetric_dilation A) = 0 := by
  -- Expand the block trace and note that every diagonal entry comes from a zero block.
  rw [symmetric_dilation, Matrix.trace, Fintype.sum_sum_type]
  simp [Matrix.trace]

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

/-- Helper for Fact 24.67: multiplying on the left by a diagonal matrix weights the diagonal by the
same coefficient vector, so the trace becomes the corresponding dot product. -/
private theorem trace_diagonal_mul_eq_dotProduct_diag
    {N : ℕ} (a : Fin N → ℝ) (X : Matrix (Fin N) (Fin N) ℝ) :
    Matrix.trace (Matrix.diagonal a * X) = dotProduct a (Matrix.diag X) := by
  -- Only the diagonal entry of `Matrix.diagonal a` survives in each trace summand.
  have hdiag :
      Matrix.diag (Matrix.diagonal a * X) = fun i ↦ a i * X i i := by
    ext i
    rw [Matrix.diag_apply, Matrix.mul_apply]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · simp
    · intro j hj hji
      rw [Matrix.diagonal_apply_ne (d := a) hji.symm]
      simp
  calc
    Matrix.trace (Matrix.diagonal a * X) = ∑ i, Matrix.diag (Matrix.diagonal a * X) i := by
      simp [Matrix.trace]
    _ = ∑ i, a i * X i i := by rw [hdiag]
    _ = dotProduct a (Matrix.diag X) := by
      rfl

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
    simpa [UM] using
      (Matrix.mem_orthogonalGroup_iff' (n := Fin N) (R := ℝ)
        (A := (U : Matrix (Fin N) (Fin N) ℝ))).mp U.prop
  have hUUt : UM * UMᵀ = 1 := by
    -- The same orthogonality relation also gives the right inverse identity.
    simpa [UM] using
      (Matrix.mem_orthogonalGroup_iff (n := Fin N) (R := ℝ)
        (A := (U : Matrix (Fin N) (Fin N) ℝ))).mp U.prop
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
          rw [trace_diagonal_mul_eq_dotProduct_diag]
    _ = dotProduct a (((fun i j ↦ (W i j) ^ 2) : Matrix (Fin N) (Fin N) ℝ) *ᵥ b) := by
          rw [diag_orthogonal_conj_diagonal_eq_sq_entry_mulVec W b]

/-- Helper for Fact 24.67: once the squared-entry overlap matrix is written as a Birkhoff sum,
its action on a vector is the corresponding convex combination of permuted vectors. -/
private theorem birkhoff_sum_permMatrix_mulVec_eq_sum_smul_comp_perm_fin
    {N : ℕ} (b : Fin N → ℝ) (w : Equiv.Perm (Fin N) → ℝ) :
    ((((∑ σ, w σ • σ.permMatrix ℝ) : Matrix (Fin N) (Fin N) ℝ)) *ᵥ b) =
      ∑ σ, w σ • (b ∘ σ) := by
  classical
  -- Push the matrix sum through `mulVec`, then evaluate each permutation matrix on `b`.
  calc
    ((((∑ σ, w σ • σ.permMatrix ℝ) : Matrix (Fin N) (Fin N) ℝ)) *ᵥ b)
        = ∑ σ, ((w σ • σ.permMatrix ℝ : Matrix (Fin N) (Fin N) ℝ) *ᵥ b) := by
            simpa using
              (Matrix.sum_mulVec Finset.univ
                (fun σ : Equiv.Perm (Fin N) ↦
                  (w σ • σ.permMatrix ℝ : Matrix (Fin N) (Fin N) ℝ))
                b)
    _ = ∑ σ, w σ • (b ∘ σ) := by
          refine Finset.sum_congr rfl ?_
          intro σ hσ
          rw [smul_mulVec, Matrix.permMatrix_mulVec]

/-- Helper for Fact 24.67: pairing the Birkhoff sum action with a fixed vector turns the matrix
rewrite into the corresponding convex combination of rearrangement terms. -/
private theorem dotProduct_birkhoff_sum_permMatrix_mulVec_eq_sum_mul_dotProduct_comp_perm_fin
    {N : ℕ} (a b : Fin N → ℝ) (w : Equiv.Perm (Fin N) → ℝ) :
    dotProduct a ((((∑ σ, w σ • σ.permMatrix ℝ) : Matrix (Fin N) (Fin N) ℝ)) *ᵥ b) =
      ∑ σ, w σ * dotProduct a (b ∘ σ) := by
  classical
  -- First normalize the `mulVec`, then distribute the dot product over the resulting finite sum.
  calc
    dotProduct a ((((∑ σ, w σ • σ.permMatrix ℝ) : Matrix (Fin N) (Fin N) ℝ)) *ᵥ b)
        = dotProduct a (∑ σ, w σ • (b ∘ σ)) := by
            rw [birkhoff_sum_permMatrix_mulVec_eq_sum_smul_comp_perm_fin]
    _ = ∑ σ, dotProduct a (w σ • (b ∘ σ)) := by
          simpa using
            (dotProduct_sum a Finset.univ
              (fun σ : Equiv.Perm (Fin N) ↦ w σ • (b ∘ σ)))
    _ = ∑ σ, w σ * dotProduct a (b ∘ σ) := by
          refine Finset.sum_congr rfl ?_
          intro σ hσ
          rw [dotProduct_smul]
          simp [smul_eq_mul]

/-- Helper for Fact 24.67: the rearrangement inequality is stable under convex combinations of the
permuted second factor. -/
private theorem convex_sum_dotProduct_comp_perm_le_dotProduct_fin
    {N : ℕ} (a b : Fin N → ℝ) (w : Equiv.Perm (Fin N) → ℝ)
    (hw_nonneg : ∀ σ, 0 ≤ w σ) (hw_sum : ∑ σ, w σ = 1) (hmono : Monovary a b) :
    ∑ σ, w σ * dotProduct a (b ∘ σ) ≤ dotProduct a b := by
  classical
  have hterm : ∀ σ : Equiv.Perm (Fin N), dotProduct a (b ∘ σ) ≤ dotProduct a b := by
    intro σ
    -- Each permutation term is bounded by the aligned dot product via rearrangement.
    simpa [dotProduct] using (hmono.sum_mul_comp_perm_le_sum_mul (σ := σ))
  -- Sum the pointwise rearrangement bounds with the nonnegative Birkhoff weights.
  calc
    ∑ σ, w σ * dotProduct a (b ∘ σ)
        ≤ ∑ σ, w σ * dotProduct a b := by
            refine Finset.sum_le_sum ?_
            intro σ hσ
            exact mul_le_mul_of_nonneg_left (hterm σ) (hw_nonneg σ)
    _ = (∑ σ, w σ) * dotProduct a b := by
          rw [Finset.sum_mul]
    _ = dotProduct a b := by
          simp [hw_sum]

/-- Helper for Fact 24.67: for real Hermitian matrices on `Fin N`, the trace pairing is bounded by
the dot product of the decreasing eigenvalue lists. -/
private theorem trace_le_eigenvalues_dotProduct_local {N : ℕ}
    {H K : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) (hK : K.IsHermitian) :
    Matrix.trace (H * K) ≤ dotProduct hH.eigenvalues hK.eigenvalues := by
  classical
  let a : Fin N → ℝ := hH.eigenvalues
  let b : Fin N → ℝ := hK.eigenvalues
  let UM : Matrix (Fin N) (Fin N) ℝ := hH.eigenvectorUnitary
  let VM : Matrix (Fin N) (Fin N) ℝ := hK.eigenvectorUnitary
  let e : Fin N ≃ Fin (Fintype.card (Fin N)) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin N)))).symm
  let U : Matrix.orthogonalGroup (Fin N) ℝ :=
    ⟨UM, by
      simpa [UM] using hH.eigenvectorUnitary.prop⟩
  let V : Matrix.orthogonalGroup (Fin N) ℝ :=
    ⟨VM, by
      simpa [VM] using hK.eigenvectorUnitary.prop⟩
  let W : Matrix (Fin N) (Fin N) ℝ := UMᵀ * VM
  have hHdiag :
      H = (UM * Matrix.diagonal a) * UMᵀ := by
    -- The spectral theorem diagonalizes `H` in its orthogonal eigenbasis.
    simpa [a, UM, Matrix.conjTranspose_eq_transpose_of_trivial, Unitary.conjStarAlgAut_apply,
      Matrix.mul_assoc] using hH.spectral_theorem
  have hKdiag :
      K = (VM * Matrix.diagonal b) * VMᵀ := by
    -- The same orthogonal diagonalization surface holds for `K`.
    simpa [b, VM, Matrix.conjTranspose_eq_transpose_of_trivial, Unitary.conjStarAlgAut_apply,
      Matrix.mul_assoc] using hK.spectral_theorem
  have hUtU : UMᵀ * UM = 1 := by
    -- Orthogonality of the eigenvector matrix gives the left inverse relation.
    simpa [UM] using
      (Matrix.mem_orthogonalGroup_iff' (n := Fin N) (R := ℝ) (A := UM)).mp U.prop
  have hUUt : UM * UMᵀ = 1 := by
    -- The same orthogonality also gives the right inverse relation.
    simpa [UM] using
      (Matrix.mem_orthogonalGroup_iff (n := Fin N) (R := ℝ) (A := UM)).mp U.prop
  have hVtV : VMᵀ * VM = 1 := by
    -- Repeat the orthogonality identities for the eigenbasis of `K`.
    simpa [VM] using
      (Matrix.mem_orthogonalGroup_iff' (n := Fin N) (R := ℝ) (A := VM)).mp V.prop
  have hVVt : VM * VMᵀ = 1 := by
    simpa [VM] using
      (Matrix.mem_orthogonalGroup_iff (n := Fin N) (R := ℝ) (A := VM)).mp V.prop
  have hWWt : W * Wᵀ = 1 := by
    -- The overlap matrix `W = UᵀV` is orthogonal, so its squared entries form a doubly
    -- stochastic matrix in the next step.
    calc
      W * Wᵀ = (UMᵀ * VM) * (VMᵀ * UM) := by
        simp [W, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = UMᵀ * (VM * VMᵀ) * UM := by
        simp [Matrix.mul_assoc]
      _ = UMᵀ * UM := by
        simp [hVVt]
      _ = 1 := hUtU
  have hWtW : Wᵀ * W = 1 := by
    calc
      Wᵀ * W = (VMᵀ * UM) * (UMᵀ * VM) := by
        simp [W, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = VMᵀ * (UM * UMᵀ) * VM := by
        simp [Matrix.mul_assoc]
      _ = VMᵀ * VM := by
        simp [hUUt]
      _ = 1 := hVtV
  have hM :
      (fun i j ↦ (W i j) ^ 2 : Matrix (Fin N) (Fin N) ℝ) ∈ doublyStochastic ℝ (Fin N) := by
    -- The overlap coefficients are nonnegative and every row/column sum is `1`.
    simpa [W] using sq_entry_matrix_mem_doublyStochastic (W := W) hWWt hWtW
  obtain ⟨w, hw_nonneg, hw_sum, hwM⟩ :=
    exists_eq_sum_perm_of_mem_doublyStochastic hM
  have hmono₀ : Monovary hH.eigenvalues₀ hK.eigenvalues₀ :=
    Antitone.monovary hH.eigenvalues₀_antitone hK.eigenvalues₀_antitone
  have hmono : Monovary a b := by
    intro i j hij
    -- `eigenvalues` is the common reindex of the antitone `eigenvalues₀` lists, so monovariance
    -- is preserved under this simultaneous transport.
    have htransport : hK.eigenvalues₀ (e i) < hK.eigenvalues₀ (e j) := by
      simpa [b, e, Matrix.IsHermitian.eigenvalues] using hij
    have hle : hH.eigenvalues₀ (e i) ≤ hH.eigenvalues₀ (e j) := hmono₀ htransport
    simpa [a, e, Matrix.IsHermitian.eigenvalues] using hle
  have htraceCore :
      Matrix.trace
          (((UM * Matrix.diagonal a) * UMᵀ) * ((VM * Matrix.diagonal b) * VMᵀ)) =
        dotProduct a (((fun i j ↦ (W i j) ^ 2 : Matrix (Fin N) (Fin N) ℝ)) *ᵥ b) := by
    -- Freeze the spectral rewrite before substituting back into the original trace.
    simpa [U, V, UM, VM, W] using
      trace_orthogonal_conj_diagonal_mul_eq_dotProduct_sq_entry_mulVec_fin U V a b
  -- Route correction: the remaining source-faithful step is the Birkhoff decomposition of the
  -- squared-entry overlap matrix, followed by the scalar rearrangement inequality.
  calc
    Matrix.trace (H * K)
        = Matrix.trace
            (((UM * Matrix.diagonal a) * UMᵀ) * ((VM * Matrix.diagonal b) * VMᵀ)) := by
            rw [hHdiag, hKdiag]
    _ = dotProduct a (((fun i j ↦ (W i j) ^ 2 : Matrix (Fin N) (Fin N) ℝ)) *ᵥ b) := htraceCore
    _ = dotProduct a ((((∑ σ, w σ • σ.permMatrix ℝ) : Matrix (Fin N) (Fin N) ℝ)) *ᵥ b) := by
          rw [← hwM]
    _ = ∑ σ, w σ * dotProduct a (b ∘ σ) := by
          rw [dotProduct_birkhoff_sum_permMatrix_mulVec_eq_sum_mul_dotProduct_comp_perm_fin]
    _ ≤ dotProduct a b :=
          convex_sum_dotProduct_comp_perm_le_dotProduct_fin a b w hw_nonneg hw_sum hmono
    _ = dotProduct hH.eigenvalues hK.eigenvalues := by
          simp [a, b]

/-- Helper for Fact 24.67: on `Fin N`, the common reindex from `eigenvalues₀` to `eigenvalues`
does not change their dot product. -/
private theorem dotProduct_eigenvalues_eq_dotProduct_eigenvalues₀_fin {N : ℕ}
    {H K : Matrix (Fin N) (Fin N) ℝ} (hH : H.IsHermitian) (hK : K.IsHermitian) :
    dotProduct hH.eigenvalues hK.eigenvalues = dotProduct hH.eigenvalues₀ hK.eigenvalues₀ := by
  let e : Fin N ≃ Fin (Fintype.card (Fin N)) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin N)))).symm
  -- Both `eigenvalues` lists are the same simultaneous permutation of the `eigenvalues₀` lists.
  unfold Matrix.IsHermitian.eigenvalues
  simpa [dotProduct, e] using
    (Equiv.sum_comp e (fun i : Fin (Fintype.card (Fin N)) ↦ hH.eigenvalues₀ i * hK.eigenvalues₀ i))

/-- Helper for Fact 24.67: transporting a dot product along the canonical card-preserving cast
between `Fin N` and `Fin (card (Fin N))` does not change its value. -/
private theorem dotProduct_cast_card_fin_eq {N : ℕ}
    (a b : Fin (Fintype.card (Fin N)) → ℝ) :
    dotProduct a b =
      dotProduct (fun i : Fin N ↦ a ((finCongr (Fintype.card_fin N).symm) i))
        (fun i : Fin N ↦ b ((finCongr (Fintype.card_fin N).symm) i)) := by
  let e : Fin N ≃ Fin (Fintype.card (Fin N)) :=
    finCongr (Fintype.card_fin N).symm
  -- This is a pure reindexing of the same finite sum.
  unfold dotProduct
  simpa [e] using
    (Equiv.sum_comp e (fun i : Fin (Fintype.card (Fin N)) ↦ a i * b i)).symm

/-- Helper for Fact 24.67: reindexing a Hermitian matrix to `Fin (Fintype.card ι)` preserves its
canonical ordered spectrum `eigenvalues₀`. -/
private theorem reindexFin_eigenvalues₀_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℝ} (hH : H.IsHermitian) :
    let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
    let hHfin : (Matrix.reindex e e H).IsHermitian := hH.reindex e
    List.ofFn hHfin.eigenvalues₀ = List.ofFn hH.eigenvalues₀ := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let hHfin : (Matrix.reindex e e H).IsHermitian := hH.reindex e
  -- Both canonical spectra are the same sorted real roots of the common characteristic polynomial.
  calc
    List.ofFn hHfin.eigenvalues₀
        = ((Matrix.reindex e e H).charpoly.roots.map RCLike.re).sort (· ≥ ·) := by
            simpa [hHfin] using hHfin.sort_roots_charpoly_eq_eigenvalues₀.symm
    _ = (H.charpoly.roots.map RCLike.re).sort (· ≥ ·) := by
          rw [Matrix.charpoly_reindex]
    _ = List.ofFn hH.eigenvalues₀ := by
          simpa using hH.sort_roots_charpoly_eq_eigenvalues₀

/-- Helper for Fact 24.67: reindexing a square matrix along an equivalence preserves its trace. -/
private theorem trace_reindex_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (M : Matrix ι ι ℝ) :
    Matrix.trace (Matrix.reindex e e M) = Matrix.trace M := by
  -- Reindexing only permutes the diagonal summands in the trace.
  unfold Matrix.trace
  simpa [Matrix.diag_apply, Matrix.reindex_apply] using
    (Equiv.sum_comp e.symm (fun i : ι ↦ M i i))

/-- Helper for Fact 24.67: reindexing to `Fin (Fintype.card ι)` packages the general Hermitian
trace bound in a single canonical `Fin` model. -/
private theorem trace_le_reindexFin_eigenvalues_dotProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H K : Matrix ι ι ℝ} (hH : H.IsHermitian) (hK : K.IsHermitian) :
    let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
    let Hfin : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℝ := Matrix.reindex e e H
    let Kfin : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℝ := Matrix.reindex e e K
    let hHfin : Hfin.IsHermitian := hH.reindex e
    let hKfin : Kfin.IsHermitian := hK.reindex e
    Matrix.trace (H * K) ≤ dotProduct hHfin.eigenvalues hKfin.eigenvalues := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let Hfin : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℝ := Matrix.reindex e e H
  let Kfin : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℝ := Matrix.reindex e e K
  let hHfin : Hfin.IsHermitian := hH.reindex e
  let hKfin : Kfin.IsHermitian := hK.reindex e
  have htrace :
      Matrix.trace (H * K) = Matrix.trace (Hfin * Kfin) := by
    -- Multiplication commutes with reindexing, and the resulting diagonal sum is unchanged.
    calc
      Matrix.trace (H * K) = Matrix.trace (Matrix.reindex e e (H * K)) := by
        rw [trace_reindex_eq e (H * K)]
      _ = Matrix.trace (Hfin * Kfin) := by
        simp [Hfin, Kfin]
  -- Route correction: the `Fin` theorem is now packaged once, so the dilation proof only needs
  -- the source-faithful ordered-spectrum rewrite for the symmetric dilation itself.
  calc
    Matrix.trace (H * K) = Matrix.trace (Hfin * Kfin) := htrace
    _ ≤ dotProduct hHfin.eigenvalues hKfin.eigenvalues :=
          trace_le_eigenvalues_dotProduct_local hHfin hKfin

/-- Helper for Fact 24.67: the Hermitian trace bound can be stated directly in terms of the
canonical ordered spectra `eigenvalues₀`. -/
private theorem trace_le_eigenvalues₀_dotProduct {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H K : Matrix ι ι ℝ} (hH : H.IsHermitian) (hK : K.IsHermitian) :
    Matrix.trace (H * K) ≤ dotProduct hH.eigenvalues₀ hK.eigenvalues₀ := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let Hfin : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℝ := Matrix.reindex e e H
  let Kfin : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℝ := Matrix.reindex e e K
  let hHfin : Hfin.IsHermitian := hH.reindex e
  let hKfin : Kfin.IsHermitian := hK.reindex e
  let a₀ : Fin (Fintype.card ι) → ℝ := fun i ↦
    hHfin.eigenvalues₀ (Fin.cast (Fintype.card_fin (Fintype.card ι)).symm i)
  let b₀ : Fin (Fintype.card ι) → ℝ := fun i ↦
    hKfin.eigenvalues₀ (Fin.cast (Fintype.card_fin (Fintype.card ι)).symm i)
  have htrace_bound :
      Matrix.trace (H * K) ≤ dotProduct hHfin.eigenvalues hKfin.eigenvalues := by
    -- First move to the canonical `Fin` model where the local trace theorem applies.
    simpa [e, Hfin, Kfin, hHfin, hKfin] using trace_le_reindexFin_eigenvalues_dotProduct hH hK
  have hH₀ : a₀ = hH.eigenvalues₀ := by
    -- Then remove the reindexing from the canonical ordered spectrum.
    apply List.ofFn_inj.mp
    simpa [a₀, e, Hfin, hHfin, Fintype.card_fin] using
      (reindexFin_eigenvalues₀_eq (ι := ι) (H := H) (hH := hH))
  have hK₀ : b₀ = hK.eigenvalues₀ := by
    -- The same transport is used for the second Hermitian matrix.
    apply List.ofFn_inj.mp
    simpa [b₀, e, Kfin, hKfin, Fintype.card_fin] using
      (reindexFin_eigenvalues₀_eq (ι := ι) (H := K) (hH := hK))
  have ha₀_finCongr :
      (fun i : Fin (Fintype.card ι) ↦
        hHfin.eigenvalues₀ ((finCongr (Fintype.card_fin (Fintype.card ι)).symm) i)) = a₀ := by
    -- The `finCongr` and `Fin.cast` presentations of the same index transport agree pointwise.
    funext i
    cases i
    rfl
  have hb₀_finCongr :
      (fun i : Fin (Fintype.card ι) ↦
        hKfin.eigenvalues₀ ((finCongr (Fintype.card_fin (Fintype.card ι)).symm) i)) = b₀ := by
    -- The same transport agreement is used for the second ordered spectrum.
    funext i
    cases i
    rfl
  have hcast_dot :
      dotProduct hHfin.eigenvalues₀ hKfin.eigenvalues₀ = dotProduct a₀ b₀ := by
    -- Pull the `Fin (card (Fin _))` sum back to the canonical `Fin _` indexing, then rewrite the
    -- transport into the `Fin.cast` form used by `a₀` and `b₀`.
    calc
      dotProduct hHfin.eigenvalues₀ hKfin.eigenvalues₀
          = dotProduct
              (fun i : Fin (Fintype.card ι) ↦
                hHfin.eigenvalues₀ ((finCongr (Fintype.card_fin (Fintype.card ι)).symm) i))
              (fun i : Fin (Fintype.card ι) ↦
                hKfin.eigenvalues₀ ((finCongr (Fintype.card_fin (Fintype.card ι)).symm) i)) := by
                  simpa using dotProduct_cast_card_fin_eq hHfin.eigenvalues₀ hKfin.eigenvalues₀
      _ = dotProduct a₀ b₀ := by
            rw [ha₀_finCongr, hb₀_finCongr]
  have hdot₀ :
      dotProduct hHfin.eigenvalues hKfin.eigenvalues = dotProduct a₀ b₀ := by
    -- Replace `eigenvalues` by `eigenvalues₀` on the `Fin` model and then discharge the reindex.
    calc
      dotProduct hHfin.eigenvalues hKfin.eigenvalues
          = dotProduct hHfin.eigenvalues₀ hKfin.eigenvalues₀ := by
              simpa using dotProduct_eigenvalues_eq_dotProduct_eigenvalues₀_fin hHfin hKfin
      _ = dotProduct a₀ b₀ := hcast_dot
  calc
    Matrix.trace (H * K) ≤ dotProduct hHfin.eigenvalues hKfin.eigenvalues := htrace_bound
    _ = dotProduct a₀ b₀ := hdot₀
    _ = dotProduct hH.eigenvalues₀ hK.eigenvalues₀ := by
          rw [hH₀, hK₀]

/-- Helper for Fact 24.67: negating a real matrix does not change its singular-value sequence. -/
private theorem singularValues_neg
    (A : Matrix m n ℝ) :
    (-A).singularValues = A.singularValues := by
  classical
  ext i
  by_cases hi : Fintype.card n ≤ i
  · -- Beyond the domain dimension, both singular-value sequences vanish.
    rw [Matrix.singularValues_of_finrank_le (-A) (by simpa using hi),
      Matrix.singularValues_of_finrank_le A (by simpa using hi)]
  · let j : Fin (Module.finrank ℝ (EuclideanSpace ℝ n)) := ⟨i, by
        simpa using Nat.lt_of_not_ge hi⟩
    have hsq :
        ((-A).singularValues i) ^ 2 = (A.singularValues i) ^ 2 := by
      -- In the finite range, both sides are the same eigenvalue of `T⋆T`, since negation cancels
      -- in the quadratic operator defining singular values.
      have hsq_lin :
          (((-A).toEuclideanLin).singularValues i) ^ 2 =
            ((A.toEuclideanLin).singularValues i) ^ 2 := by
        rw [((-A).toEuclideanLin).sq_singularValues_fin rfl j,
          (A.toEuclideanLin).sq_singularValues_fin rfl j]
        simp
      simpa [Matrix.singularValues] using hsq_lin
    have hnonneg_neg : 0 ≤ (-A).singularValues i := Matrix.singularValues_nonneg (-A) i
    have hnonneg : 0 ≤ A.singularValues i := Matrix.singularValues_nonneg A i
    exact le_antisymm (le_of_sq_le_sq hsq.le hnonneg) (le_of_sq_le_sq hsq.ge hnonneg_neg)

/-- Helper for Fact 24.67: the sign-conjugation symmetry identifies the ordered eigenvalue list of
`D(A)` with that of `D(-A) = -D(A)`. -/
private theorem symmetric_dilation_eigenvalues_eq_neg_dilation
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) :
    (symmetric_dilation_isHermitian A).eigenvalues =
      (symmetric_dilation_isHermitian (-A)).eigenvalues := by
  -- Transfer the already-proved characteristic-polynomial symmetry through the Hermitian
  -- `eigenvalues_eq_eigenvalues_iff` equivalence.
  let hD := symmetric_dilation_isHermitian A
  let hNeg := symmetric_dilation_isHermitian (-A)
  exact (hD.eigenvalues_eq_eigenvalues_iff (hB := hNeg)).2 <|
    by simpa [symmetric_dilation_neg] using
      symmetric_dilation_charpoly_eq_neg (m := m) (n := n) (A := A)

/-- Helper for Fact 24.67: the same sign-conjugation symmetry already identifies the canonical
ordered spectrum `eigenvalues₀` of `D(A)` with that of `D(-A) = -D(A)`. -/
private theorem symmetric_dilation_eigenvalues₀_eq_neg_dilation
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) :
    (symmetric_dilation_isHermitian A).eigenvalues₀ =
      (symmetric_dilation_isHermitian (-A)).eigenvalues₀ := by
  apply List.ofFn_inj.mp
  -- Route correction: work directly with the sorted real roots that define `eigenvalues₀`, so the
  -- remaining blocker is only the reverse-negation indexing and not another transport layer.
  calc
    List.ofFn (symmetric_dilation_isHermitian A).eigenvalues₀
        = ((symmetric_dilation A).charpoly.roots.map RCLike.re).sort (· ≥ ·) := by
            simpa using
              (symmetric_dilation_isHermitian A).sort_roots_charpoly_eq_eigenvalues₀.symm
    _ = ((symmetric_dilation (-A)).charpoly.roots.map RCLike.re).sort (· ≥ ·) := by
          rw [show (symmetric_dilation A).charpoly = (symmetric_dilation (-A)).charpoly by
            simpa [symmetric_dilation_neg] using
              symmetric_dilation_charpoly_eq_neg (m := m) (n := n) (A := A)]
    _ = List.ofFn (symmetric_dilation_isHermitian (-A)).eigenvalues₀ := by
          simpa using
            (symmetric_dilation_isHermitian (-A)).sort_roots_charpoly_eq_eigenvalues₀

/-- Helper for Fact 24.67: the ordered eigenvalues of the symmetric dilation sum to zero, matching
the zero diagonal blocks of `D(A)`. -/
private theorem symmetric_dilation_sum_eigenvalues_eq_zero
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℝ) :
    ∑ i, (symmetric_dilation_isHermitian A).eigenvalues i = 0 := by
  -- Translate the blockwise zero-trace calculation through the Hermitian trace/eigenvalue formula.
  simpa [symmetric_dilation_trace_eq_zero A] using
    ((symmetric_dilation_isHermitian A).trace_eq_sum_eigenvalues).symm

/-- Helper for Fact 24.67: the symmetric-dilation trace pairing is controlled by twice the
singular-value sum. -/
private theorem symmetric_dilation_trace_le_twice_singular_sum
    (A B : Matrix m n ℝ) :
    trace (symmetric_dilation A * symmetric_dilation B) ≤
      2 * Finset.sum (Finset.range (min (Fintype.card m) (Fintype.card n))) fun i ↦
        A.singularValues i * B.singularValues i := by
  classical
  have htrace_bound :
      trace (symmetric_dilation A * symmetric_dilation B) ≤
        dotProduct (symmetric_dilation_isHermitian A).eigenvalues₀
          (symmetric_dilation_isHermitian B).eigenvalues₀ := by
    -- The transport layer is now packaged once, so the dilation proof works directly with the
    -- canonical ordered spectra.
    simpa using
      trace_le_eigenvalues₀_dotProduct
      (symmetric_dilation_isHermitian A) (symmetric_dilation_isHermitian B)
  suffices hspectral₀ :
      dotProduct (symmetric_dilation_isHermitian A).eigenvalues₀
          (symmetric_dilation_isHermitian B).eigenvalues₀ ≤
        2 * Finset.sum (Finset.range (min (Fintype.card m) (Fintype.card n))) fun i ↦
          A.singularValues i * B.singularValues i by
    -- Once the ordered dilation spectrum is rewritten by singular values, the trace bound follows.
    exact le_trans htrace_bound hspectral₀
  -- TODO: the transport step is now closed, so only the source-faithful dilation spectrum
  -- identification remains. Compute the positive head of `D(A)^2`, lift it to the positive head of
  -- `D(A)` using the sign symmetry `symmetric_dilation_charpoly_eq_neg`, then derive the tail from
  -- `-A` and evaluate the dot product of the signed profiles.
  sorry

/-- Fact 24.67 (2): von Neumann's trace inequality for real rectangular matrices, written with
mathlib's zero-indexed matrix singular-value bridge and the canonical sum over
`Finset.range (min (Fintype.card m) (Fintype.card n))`. -/
theorem von_neumann_trace_inequality
    (A B : Matrix m n ℝ) :
    |trace (Aᵀ * B)| ≤
      Finset.sum (Finset.range (min (Fintype.card m) (Fintype.card n))) fun i ↦
        A.singularValues i * B.singularValues i := by
  classical
  -- Route correction: switch from the missing rectangular-SVD witness route to the symmetric
  -- dilation reduction planned in the previous round.
  let S :=
    Finset.sum (Finset.range (min (Fintype.card m) (Fintype.card n))) fun i ↦
      A.singularValues i * B.singularValues i
  let DA : Matrix (m ⊕ n) (m ⊕ n) ℝ := symmetric_dilation A
  let DB : Matrix (m ⊕ n) (m ⊕ n) ℝ := symmetric_dilation B
  let DBneg : Matrix (m ⊕ n) (m ⊕ n) ℝ := symmetric_dilation (-B)
  have hsum_nonneg : 0 ≤ S := by
    -- The singular values are nonnegative termwise, so their weighted sum is nonnegative.
    refine Finset.sum_nonneg ?_
    intro i hi
    exact mul_nonneg (Matrix.singularValues_nonneg A i) (Matrix.singularValues_nonneg B i)
  have htrace :
      trace (DA * DB) = 2 * trace (Aᵀ * B) := by
    -- The block trace identity is the exact bridge from the Hermitian square theorem back to the
    -- rectangular pairing.
    simpa [DA, DB] using symmetric_dilation_trace_mul_eq_two_trace_transpose_mul A B
  have htrace_neg :
      trace (DA * DBneg) = -(2 * trace (Aᵀ * B)) := by
    -- Applying the same block trace identity to `-B` flips the rectangular pairing sign.
    have hnegCore :
        trace (DA * DBneg) = 2 * trace (Aᵀ * (-B)) := by
      simpa [DA, DBneg] using symmetric_dilation_trace_mul_eq_two_trace_transpose_mul A (-B)
    rw [hnegCore]
    simp [two_mul]
  have hupper :
      2 * trace (Aᵀ * B) ≤ 2 * S := by
    -- The positive trace side is the unresolved dilation trace bound.
    calc
      2 * trace (Aᵀ * B) = trace (DA * DB) := htrace.symm
      _ ≤ 2 * S := by
            simpa [S, DA, DB] using symmetric_dilation_trace_le_twice_singular_sum A B
  have hupper_neg :
      -(2 * trace (Aᵀ * B)) ≤ 2 * S := by
    -- The negative trace side is the same bound applied to `-B`, whose singular values agree
    -- with those of `B`.
    calc
      -(2 * trace (Aᵀ * B)) = trace (DA * DBneg) := htrace_neg.symm
      _ ≤ 2 * S := by
            simpa [S, DA, DBneg, singularValues_neg] using
              symmetric_dilation_trace_le_twice_singular_sum A (-B)
  have hlower :
      -(2 * S) ≤ 2 * trace (Aᵀ * B) := by
    -- Reinterpret the `-B` bound as the lower half of the absolute-value estimate.
    nlinarith
  have habs :
      |2 * trace (Aᵀ * B)| ≤ 2 * S := by
    -- Combine the upper and lower trace estimates into the absolute-value form.
    exact abs_le.mpr ⟨hlower, hupper⟩
  -- Finally divide out the positive factor `2`.
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at habs
  nlinarith
