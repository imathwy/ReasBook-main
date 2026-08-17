module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

noncomputable section

namespace SpectralFilter

/-- The Landweber scalar filter `w_v(λ) = 1 - (1 - τ * λ)^v` from equation `(1.38)`. -/
def landweber (τ : ℝ) (v : ℕ) (lam : ℝ) : ℝ :=
  1 - (1 - τ * lam) ^ v

/-- The Landweber scalar filter expands to the defining formula from equation `(1.38)`. -/
theorem landweber_eq (τ : ℝ) (v : ℕ) (lam : ℝ) :
    landweber τ v lam = 1 - (1 - τ * lam) ^ v := by
  -- Unfold the canonical owner once; the theorem is exactly its defining equation.
  rfl

end SpectralFilter
