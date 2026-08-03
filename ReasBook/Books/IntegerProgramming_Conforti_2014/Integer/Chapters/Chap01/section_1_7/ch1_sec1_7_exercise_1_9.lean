import Mathlib
import Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_remark_1_1

open scoped BigOperators

-- Semantic search tooling was unavailable in this environment; the statement uses mathlib's
-- verified matrix APIs `A⁻¹`, `IsUnit A.det`, `Matrix.mulVec`, and `Rat.castHom`.

/-- A bit-length style encoding size for a rational matrix, obtained by summing the encoding sizes
of its rows. -/
def rational_matrix_encoding_size {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : ℕ :=
  ∑ i, rational_vector_encoding_size (A i)

/-- A bit-length style encoding size for a rational linear system, obtained by adding the encoding
size of the coefficient matrix and that of the right-hand side vector. -/
def rational_linear_system_encoding_size {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) : ℕ :=
  rational_matrix_encoding_size A + rational_vector_encoding_size b

/-- Exercise 1.9 (1): the encoding size of the inverse of a nonsingular rational square matrix is
bounded above by a polynomial in the encoding size of the original matrix. -/
theorem rational_matrix_inverse_encoding_size_is_polynomially_bounded :
    ∃ p : Polynomial ℕ, ∀ n : ℕ, ∀ A : Matrix (Fin n) (Fin n) ℚ,
      IsUnit A.det →
        rational_matrix_encoding_size A⁻¹ ≤ p.eval (rational_matrix_encoding_size A) := sorry

/-- Exercise 1.9 (2): if a rational linear system has a real solution, then it has a rational
solution whose encoding size is bounded above by a polynomial in the encoding size of the input
pair `(A, b)`. -/
theorem rational_linear_system_has_small_rational_solution :
    ∃ p : Polynomial ℕ, ∀ m n : ℕ, ∀ A : Matrix (Fin m) (Fin n) ℚ, ∀ b : Fin m → ℚ,
      (∃ xbar : Fin n → ℝ, (A.map (Rat.castHom ℝ)).mulVec xbar = fun i ↦ (b i : ℝ)) →
        ∃ x : Fin n → ℚ,
          A.mulVec x = b ∧
            rational_vector_encoding_size x ≤ p.eval (rational_linear_system_encoding_size A b) :=
  sorry
