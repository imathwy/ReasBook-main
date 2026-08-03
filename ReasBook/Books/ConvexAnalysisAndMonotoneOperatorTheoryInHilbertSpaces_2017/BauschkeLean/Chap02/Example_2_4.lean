import Mathlib
import Mathlib.Analysis.InnerProductSpace.PiL2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix WithLp
open scoped Matrix.Norms.Frobenius

/-- After identifying a real matrix with an iterated `L²` space, its Hilbert inner product is
`trace (Aᵀ * B)`. -/
theorem Matrix.inner_toLp_eq_trace_transpose_mul
    {m n : Type*} [Fintype m] [Fintype n] (A B : Matrix m n ℝ) :
    inner ℝ (toLp 2 (fun i ↦ toLp 2 (A i))) (toLp 2 (fun i ↦ toLp 2 (B i))) =
      trace (Aᵀ * B) := by
  calc
    inner ℝ (toLp 2 (fun i ↦ toLp 2 (A i))) (toLp 2 (fun i ↦ toLp 2 (B i)))
      = trace (B * Aᵀ) := by
          rw [PiLp.inner_apply, Matrix.trace]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          simpa using inner_matrix_row_row A B i i
    _ = trace (Aᵀ * B) := Matrix.trace_mul_comm B Aᵀ

/-- Example 2.4: after identifying real `M × N` matrices with an iterated `L²` space, the inner
product is given by the canonical matrix trace formula `trace (Aᵀ B)`. -/
theorem matrixToHilbert_inner_eq_trace_transpose_mul
    (M N : ℕ) (A B : Matrix (Fin M) (Fin N) ℝ) :
    inner ℝ (toLp 2 (fun i ↦ toLp 2 (A i))) (toLp 2 (fun i ↦ toLp 2 (B i))) =
      trace (Aᵀ * B) := by
  simpa using Matrix.inner_toLp_eq_trace_transpose_mul A B

/-- Example 2.4: the canonical matrix norm on `Matrix (Fin M) (Fin N) ℝ` is the Frobenius norm,
written entrywise as the square root of the sum of the squares. -/
theorem matrixToHilbert_norm_eq_frobenius_formula
    (M N : ℕ) (A : Matrix (Fin M) (Fin N) ℝ) :
    ‖A‖ = Real.sqrt (∑ i, ∑ j, ‖A i j‖ * ‖A i j‖) := by
  simp [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow, sq]
