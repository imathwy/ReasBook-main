module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

namespace SpectralFilter

/-- The Exercise 1.16 owner for the Landweber scalar filter
`w_v(λ) = 1 - (1 - τ * λ)^v` from equation `(1.38)`. -/
def landweber (τ : ℝ) (v : ℕ) (lam : ℝ) : ℝ :=
  1 - (1 - τ * lam) ^ v

/-- Exercise 1.16. The Landweber scalar filter expands to the defining formula
from equation `(1.38)`. -/
theorem landweber_eq (τ : ℝ) (v : ℕ) (lam : ℝ) :
    landweber τ v lam = 1 - (1 - τ * lam) ^ v := by
  -- The theorem records the canonical closed form of the owner defined above.
  rfl

end SpectralFilter
