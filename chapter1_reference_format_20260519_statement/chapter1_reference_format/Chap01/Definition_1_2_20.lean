import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

variable (p : ℕ) [Fact p.Prime]

/- Definition 1.2.20: the field of `p`-adic numbers is the completion of `ℚ` with respect to the
`p`-adic absolute value `|·|_p`; the canonical owner is `Padic p`, written in source-facing
notation as `ℚ_[p]`. -/
recall Padic (p : ℕ) [Fact p.Prime] : Type

/- The standard notation for the field of `p`-adic numbers is `ℚ_[p]`. -/
#check (ℚ_[p])
