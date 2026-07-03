import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set

namespace Complex

/-- Definition I.3-extra-8: a branch of `log t` on a connected open set `D` is a continuous
function on `D` whose exponential is the identity on `D`; the excluded-point condition
`0 ∉ D` is recovered as a theorem from this identity. -/
def IsLogBranchOn (f : ℂ → ℂ) (D : Set ℂ) : Prop :=
  IsOpen D ∧ IsConnected D ∧ ContinuousOn f D ∧ EqOn (exp ∘ f) id D

-- Proof sketch: if `0 ∈ D`, then the defining identity on `D` gives
-- `Complex.exp (f 0) = 0`, contradicting `Complex.exp_ne_zero (f 0)`.
/-- A branch of the complex logarithm cannot be defined at `0`. -/
theorem IsLogBranchOn.zero_not_mem {f : ℂ → ℂ} {D : Set ℂ} (hf : IsLogBranchOn f D) :
    (0 : ℂ) ∉ D := by
  rcases hf with ⟨_, _, _, hEq⟩
  intro h0
  -- Evaluate the branch identity at the forbidden point `0`.
  have hExpAtZero : exp (f 0) = 0 := by
    simpa [Function.comp] using hEq h0
  -- This contradicts the fact that the complex exponential never vanishes.
  exact exp_ne_zero (f 0) hExpAtZero

end Complex
