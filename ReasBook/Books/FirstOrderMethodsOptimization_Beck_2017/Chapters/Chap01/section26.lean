import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_26 (from Chap01) -/
section

variable {n : ℕ}

/- Definition 1.26: for a vector `x` in `ℝ^n`, modeled as `Fin n → ℝ`, the vector `|x|` is the
coordinatewise absolute-value vector, given canonically by `Pi.abs_def`. -/
#check (Pi.abs_def : ∀ x : Fin n → ℝ, |x| = fun i ↦ |x i|)

end
