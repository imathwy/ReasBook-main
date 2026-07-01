import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 1.2.19: Ostrowski's theorem on `ℚ` is the canonical mathlib result
`Rat.AbsoluteValue.equiv_real_or_padic`: every nontrivial real-valued absolute value on `ℚ` is
equivalent either to the usual absolute value `Rat.AbsoluteValue.real` (the place `∞`) or to the
unique `p`-adic absolute value `Rat.AbsoluteValue.padic p` for a prime `p`. -/
recall Rat.AbsoluteValue.equiv_real_or_padic
    (f : AbsoluteValue ℚ ℝ) (hf_nontrivial : f.IsNontrivial) :
    f ≈ Rat.AbsoluteValue.real ∨ ∃! p, ∃ (_ : Fact p.Prime), f ≈ Rat.AbsoluteValue.padic p
