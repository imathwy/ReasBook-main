import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Remark 4.5: For a nonnegative simple function `f`, the lower Lebesgue integral of the
underlying `ℝ≥0∞`-valued function agrees with its simple-function integral `I(f) = f.lintegral μ`.
Hence `MeasureTheory.lintegral` extends the map `I` from `E⁺` to nonnegative measurable
functions. -/
recall MeasureTheory.SimpleFunc.lintegral_eq_lintegral
