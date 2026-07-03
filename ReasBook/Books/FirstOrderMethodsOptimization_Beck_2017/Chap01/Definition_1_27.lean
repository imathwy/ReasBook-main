import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {n : ℕ}

/-- Definition 1.27: For a vector `x` in `ℝ^n`, modeled as `Fin n → ℝ`, `sgn x` is the
coordinatewise sign vector whose `i`-th entry is `1` when `x i ≥ 0` and `-1` when `x i < 0`. -/
noncomputable def sgn (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ if 0 ≤ x i then 1 else -1

/-- The coordinates of `sgn x` are `1` on nonnegative entries of `x` and `-1` on negative ones. -/
@[simp] theorem sgn_apply (x : Fin n → ℝ) (i : Fin n) :
    sgn x i = if 0 ≤ x i then 1 else -1 :=
  rfl

end
