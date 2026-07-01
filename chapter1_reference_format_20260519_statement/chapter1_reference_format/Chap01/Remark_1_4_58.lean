import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Remark 1.4.58: the standard norm on `ℂ` is also a norm when `ℂ` is regarded as a real vector
space; in Lean this is the canonical owner declaration `NormedSpace.complexToReal`, obtained from
the general restriction-of-scalars construction `NormedSpace.restrictScalars`. -/
#check (NormedSpace.complexToReal : NormedSpace ℝ ℂ)
