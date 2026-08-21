module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Real.Basic

public section

noncomputable section

namespace TsvdEstimation

/-- The explicit TSVD asymptotic constant `C₁^TSVD` from `(7.64)`. -/
def errorConstant (b c p q : ℝ) : ℝ :=
  ((p + q) / ((p + 1) * (q - 1))) * ((b ^ (p + 1) / c ^ (q - 1)) ^ (1 / (p + q)))

/-- The defining closed form for `errorConstant`. -/
theorem errorConstant_def (b c p q : ℝ) :
    errorConstant b c p q =
      ((p + q) / ((p + 1) * (q - 1))) *
        ((b ^ (p + 1) / c ^ (q - 1)) ^ (1 / (p + q))) := sorry

end TsvdEstimation
