module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Real.Basic

public section

noncomputable section

namespace TsvdEstimation

/-- The explicit TSVD benchmark truncation-index sequence from `(7.63)`. -/
def optimalIndex (b c p q σ : ℝ) : ℕ → ℕ :=
  fun n ↦
    Nat.floor
      (((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))))

/-- The defining floor formula for `optimalIndex`. -/
theorem optimalIndex_def (b c p q σ : ℝ) (n : ℕ) :
    optimalIndex b c p q σ n =
      Nat.floor
        (((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q))))) := by
  rfl

end TsvdEstimation
