import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {n : ℕ}

/- Definition 1.28: for vectors in `ℝ^n`, modeled as `Fin n → ℝ`, the Hadamard product is the
canonical pointwise multiplication on the function space `Fin n → ℝ`. -/
#check ((· * ·) : (Fin n → ℝ) → (Fin n → ℝ) → Fin n → ℝ)

/- The coordinates of the Hadamard product are given by the canonical `Pi.mul_apply` formula. -/
#check (Pi.mul_apply : ∀ a b : Fin n → ℝ, ∀ i : Fin n, (a * b) i = a i * b i)

end
