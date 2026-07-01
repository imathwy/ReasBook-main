import Mathlib.Analysis.Complex.Exponential

-- Declarations for this item will be appended below by the statement pipeline.

namespace Complex

open Set

/-- Definition I.3-extra-8: a branch of the complex logarithm on a set `D` is a continuous
right inverse to `exp` on `D`. The openness and connectedness assumptions belong to the
source-facing propositions proved from this owner, not to the owner itself. -/
def IsLogBranchOn (f : ℂ → ℂ) (D : Set ℂ) : Prop :=
  ContinuousOn f D ∧ RightInvOn f exp D

end Complex
