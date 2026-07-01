import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Remark 15.55: in the multidimensional setting, degenerate normal laws with positive
semidefinite covariance matrix `C` are the canonical measures `multivariateGaussian μ C`. -/
recall ProbabilityTheory.multivariateGaussian

/- Their characteristic function is
`t ↦ exp (⟪t, μ⟫ * I - t ⬝ᵥ C *ᵥ t / 2)`. -/
recall ProbabilityTheory.charFun_multivariateGaussian
