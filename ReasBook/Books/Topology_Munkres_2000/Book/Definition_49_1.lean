import Mathlib.Data.Real.Basic

open Set

namespace UnitIntervalSecant

/-- The magnitude of the secant slope from `x` to `x + h`, or `0` when the
right endpoint does not lie in the closed unit interval. -/
private noncomputable def rightMagnitude (f : Icc (0 : ℝ) 1 → ℝ)
    (x : Icc (0 : ℝ) 1) (h : ℝ) : ℝ :=
  if hplus : x + h ∈ Icc (0 : ℝ) 1 then
    |(f ⟨x + h, hplus⟩ - f x) / h|
  else
    0

/-- The magnitude of the secant slope from `x` to `x - h`, or `0` when the
left endpoint does not lie in the closed unit interval. -/
private noncomputable def leftMagnitude (f : Icc (0 : ℝ) 1 → ℝ)
    (x : Icc (0 : ℝ) 1) (h : ℝ) : ℝ :=
  if hminus : x - h ∈ Icc (0 : ℝ) 1 then
    |(f ⟨x - h, hminus⟩ - f x) / (-h)|
  else
    0

/-- Definition 49.1. The larger magnitude of the available secant slopes at
`x` with displacement `h`, where an unavailable direction contributes `0`. -/
noncomputable def maxMagnitude (f : Icc (0 : ℝ) 1 → ℝ)
    (x : Icc (0 : ℝ) 1) (h : ℝ) : ℝ :=
  max (rightMagnitude f x h) (leftMagnitude f x h)

/-- The source notation `Δ f (x, h)` for the larger available secant-slope
magnitude of `f` at `x` and displacement `h`. -/
scoped notation:arg "Δ" f:arg " (" x ", " h ")" => maxMagnitude f x h

end UnitIntervalSecant
