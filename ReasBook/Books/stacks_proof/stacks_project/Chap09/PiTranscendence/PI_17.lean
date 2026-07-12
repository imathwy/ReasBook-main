import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool unavailable in this environment; this item uses the direct complex
-- nonvanishing statement suggested by local precedent and standard `Real.pi` / `Complex.I` API.

/-- Chap09 PiTranscendence/PI 17: the complex number `(Real.pi : ℂ) * Complex.I` is nonzero. -/
theorem complex_pi_mul_I_ne_zero : ((Real.pi : ℂ) * Complex.I) ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast Real.pi_ne_zero
  · exact Complex.I_ne_zero
