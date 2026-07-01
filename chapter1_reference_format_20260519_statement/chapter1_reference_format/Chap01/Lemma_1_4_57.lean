import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 1.4.57: the usual complex modulus `‖·‖ : ℂ → ℝ` is an absolute value, hence a norm in
the textbook sense on the complex field `ℂ`. -/
recall Complex.isAbsoluteValueNorm : IsAbsoluteValue (‖·‖ : ℂ → ℝ)
