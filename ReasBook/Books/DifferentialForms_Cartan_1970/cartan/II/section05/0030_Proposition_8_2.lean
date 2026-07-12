import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0029_Definition_II_1_extra_18»
import DifferentialForms_Cartan_1970.II.section06.«0008_Theorem_2»

-- Declarations for this item will be appended below by the statement pipeline.

namespace Path

-- Proof sketch: choose logarithmic lifts for `γ₁` and `γ₂`; their pointwise sum is a logarithmic
-- lift of the product path, and the endpoint increments add.
/-- Proposition 8.2: the index with respect to the origin of the product of two closed paths is the
sum of the indices of the two paths; if `γ₁` has index `n₁` and `γ₂` has index `n₂` at `0`, then
their product path has index `n₁ + n₂` at `0`. -/
theorem HasIndexAt.mul {z₁ z₂ : ℂ} {γ₁ : Path z₁ z₁} {γ₂ : Path z₂ z₂} {n₁ n₂ : ℤ}
    (hγ₁ : γ₁.HasIndexAt 0 n₁) (hγ₂ : γ₂.HasIndexAt 0 n₂) :
    (γ₁.mul γ₂).HasIndexAt 0 (n₁ + n₂) := by
  rcases hγ₁ with ⟨w₁, hw₁exp, hw₁end⟩
  rcases hγ₂ with ⟨w₂, hw₂exp, hw₂end⟩
  refine ⟨w₁ + w₂, ?_, ?_⟩
  · intro t
    simpa [Complex.exp_add] using congrArg₂ (· * ·) (hw₁exp t) (hw₂exp t)
  · calc
      (w₁ + w₂) 1 = w₁ 1 + w₂ 1 := rfl
      _ = (w₁ 0 + ((2 * Real.pi : ℂ) * (n₁ : ℂ)) * Complex.I) +
            (w₂ 0 + ((2 * Real.pi : ℂ) * (n₂ : ℂ)) * Complex.I) := by
              rw [hw₁end, hw₂end]
      _ = (w₁ 0 + w₂ 0) +
            (((2 * Real.pi : ℂ) * (n₁ : ℂ)) * Complex.I +
              ((2 * Real.pi : ℂ) * (n₂ : ℂ)) * Complex.I) := by
              ring
      _ = (w₁ 0 + w₂ 0) + ((2 * Real.pi : ℂ) * ((n₁ + n₂ : ℤ) : ℂ)) * Complex.I := by
            simp [Int.cast_add, add_mul, mul_add]
      _ = (w₁ + w₂) 0 + ((2 * Real.pi : ℂ) * ((n₁ + n₂ : ℤ) : ℂ)) * Complex.I := rfl

end Path
