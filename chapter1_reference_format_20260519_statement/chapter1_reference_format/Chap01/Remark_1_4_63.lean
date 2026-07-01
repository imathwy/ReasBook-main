import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Remark 1.4.63: the modulus of the complex exponential depends only on the real part. In
particular, if `z = x + y * Complex.I`, then `‖Complex.exp z‖ = Real.exp x = |Real.exp x|`, which
is the textbook identity `|e^z| = |e^x|`. -/
recall Complex.norm_exp (z : ℂ) : ‖Complex.exp z‖ = Real.exp z.re
