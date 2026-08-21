module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

public section

noncomputable section

namespace SpectralFilter

/-- The TSVD scalar filter `w_α(λ)` keeps the spectral component when `α ≤ λ`
and truncates it otherwise. -/
@[expose]
def tsvd (α lam : ℝ) : ℝ :=
  if α ≤ lam then 1 else 0

/-- The Tikhonov scalar filter `w_α(λ) = λ / (α + λ)`. -/
@[expose]
def tikhonov (α lam : ℝ) : ℝ :=
  lam / (α + lam)

end SpectralFilter
