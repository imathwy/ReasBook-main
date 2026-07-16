import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

-- Proof sketch: use mathlib's theorem `Liouville.transcendental` to obtain transcendence over
-- `ℤ`, then pass from `ℤ` to `ℚ` by restriction of scalars along `ℤ → ℚ`.
namespace Liouville

/-- Remark 1.6.1: a Liouville real number is transcendental over `ℚ`. -/
protected theorem transcendental_rat {x : ℝ} (hx : Liouville x) : Transcendental ℚ x := by
  letI : Algebra.IsAlgebraic ℤ ℚ :=
    (IsFractionRing.isAlgebraic_iff' ℤ ℤ ℚ).1 inferInstance
  exact fun hx_alg ↦ hx.transcendental (hx_alg.restrictScalars ℤ)

end Liouville

end
