import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

variable (n : ℕ)

/-- Definition 1.22: The positive orthant `ℝ^n_{++}` is the subset of `ℝ^n` consisting of the
vectors whose coordinates are all strictly positive. -/
def positiveOrthant : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ : Fin n ↦ Set.Ioi (0 : ℝ))

-- Proof sketch: unfold `positiveOrthant` and simplify membership in the product set.
/-- A vector belongs to the positive orthant exactly when each of its coordinates is positive. -/
theorem mem_positiveOrthant_iff {x : Fin n → ℝ} :
    x ∈ positiveOrthant n ↔ ∀ i, 0 < x i := by
  simp [positiveOrthant]

end
