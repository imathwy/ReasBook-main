import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped NNReal

universe u

variable (K : Type u) [Field K]

/- Example 1.2.11 (1): in the chapter's source-facing sense of a norm on a field, the trivial norm
is the canonical absolute value `AbsoluteValue.trivial`, sending `0` to `0` and every nonzero
element to `1`. -/
open Classical in
#check (AbsoluteValue.trivial : AbsoluteValue K ℝ≥0)

variable (p : ℕ)

/- Example 1.2.11 (2): for a prime `p`, the source-facing `p`-adic norm on `ℚ` is the canonical
function `padicNorm p`, obtained from the `p`-adic valuation and extending the integer formula
`n ↦ p ^ (-v_p(n))`; the bundled absolute value owner is `Rat.AbsoluteValue.padic p`. -/
recall padicNorm (p : ℕ) : ℚ → ℚ

variable [Fact p.Prime]

#check (Rat.AbsoluteValue.padic p : AbsoluteValue ℚ ℝ)

#check Rat.AbsoluteValue.padic_eq_padicNorm

/- Example 1.2.11 (3): for prime `p`, the `p`-adic norm on `ℚ` is an absolute value. -/
#check (Rat.AbsoluteValue.padic p).isAbsoluteValue

/- Example 1.2.11 (4): for prime `p`, the `p`-adic norm satisfies the ultrametric inequality. -/
#check padicNorm.nonarchimedean
