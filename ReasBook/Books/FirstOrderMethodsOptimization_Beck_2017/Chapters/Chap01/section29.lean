import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_29 (from Chap01) -/
open scoped BigOperators Matrix

section

variable (m n : ℕ)

/- Definition 1.29: the space `ℝ^{m × n}` is formalized as `Matrix (Fin m) (Fin n) ℝ`. The
textbook Frobenius pairing on this matrix space is canonically expressed by
`Matrix.trace (Aᵀ * B)`, and the bridge theorem below identifies that trace with the usual
entrywise double sum. -/
#check (Matrix (Fin m) (Fin n) ℝ)

variable {m n : ℕ}

-- Proof sketch: expand `Matrix.trace` and `Matrix.mul_apply`; the diagonal entry of `Aᵀ * B` at
-- `j` is `∑ i, A i j * B i j`, and then commute the outer and inner finite sums.
/-- The Frobenius pairing on real matrices is the trace formula `Tr(Aᵀ B)`, equivalently the sum
of the entrywise products. -/
theorem trace_transpose_mul_eq_sum_entrywise_mul (A B : Matrix (Fin m) (Fin n) ℝ) :
    Matrix.trace (Aᵀ * B) = ∑ i, ∑ j, A i j * B i j := by
  rw [show Matrix.trace (Aᵀ * B) = ∑ j, ∑ i, A i j * B i j by
    simp [Matrix.trace, Matrix.mul_apply]]
  rw [Finset.sum_comm]

end
