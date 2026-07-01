import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Polynomial

variable (p : ℕ) [Fact p.Prime]

/- Proposition 1.3.13: the function on `𝔽_p[X]` defined by `|P| = 0` for `P = 0` and
`|P| = p ^ P.natDegree` for `P ≠ 0` is a norm; in mathlib this is the canonical absolute value
`Polynomial.cardPowDegree` on `(ZMod p)[X]`. -/
#check (Polynomial.cardPowDegree : AbsoluteValue (ZMod p)[X] ℤ)

namespace Polynomial

/-- Over `𝔽_p[X]`, the canonical owner `Polynomial.cardPowDegree` has the textbook evaluation
formula. -/
theorem cardPowDegree_apply_zmod (P : (ZMod p)[X]) :
    Polynomial.cardPowDegree P = if P = 0 then 0 else (p : ℤ) ^ P.natDegree := by
  simpa using (Polynomial.cardPowDegree_apply P)

end Polynomial
