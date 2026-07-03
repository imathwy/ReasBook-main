import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_21 (from Chap01) -/
section

variable (n : ℕ)

/- Definition 1.21 (core/canonical): the nonnegative orthant `ℝ^n_+` is the principal upper set
`Set.Ici 0` in the pointwise order on `Fin n → ℝ`. -/
#check (Set.Ici (0 : Fin n → ℝ))

/-- Membership in the nonnegative orthant means that every coordinate is nonnegative. -/
theorem mem_nonnegativeOrthant_iff {x : Fin n → ℝ} :
    x ∈ Set.Ici (0 : Fin n → ℝ) ↔ ∀ i, 0 ≤ x i := by
  simp [Pi.le_def]

end
