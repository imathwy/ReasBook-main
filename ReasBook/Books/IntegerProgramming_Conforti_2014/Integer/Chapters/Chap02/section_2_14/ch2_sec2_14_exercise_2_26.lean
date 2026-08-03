import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- A real vector whose coordinates are all `0` or `1`. -/
def is_zero_one_vector {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ i, x i = 0 ∨ x i = 1

/-- A real matrix whose entries all belong to `{ -1, 0, 1 }`. -/
def has_signed_unit_entries {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ i j, D i j = -1 ∨ D i j = 0 ∨ D i j = 1

/-- Exercise 2.26. Every `0,1` set cut out by a real system `Ax ≤ b` can also be
written using a system `Dx ≤ d` whose matrix entries all lie in `{ -1, 0, 1 }`,
possibly with a different number of inequalities. -/
theorem zero_one_set_has_signed_unit_matrix_representation
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    ∃ p : ℕ, ∃ D : Matrix (Fin p) (Fin n) ℝ, ∃ d : Fin p → ℝ,
      has_signed_unit_entries D ∧
        {x : Fin n → ℝ | is_zero_one_vector x ∧ A.mulVec x ≤ b} =
          {x : Fin n → ℝ | is_zero_one_vector x ∧ D.mulVec x ≤ d} := sorry
