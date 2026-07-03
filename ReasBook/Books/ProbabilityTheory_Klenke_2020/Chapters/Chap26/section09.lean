import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_26_9 (from Items/Chap26) -/
open MeasureTheory Set intervalIntegral

-- Proof sketch: define `F t = ∫ s in 0..t, f s` and differentiate
-- `t ↦ Real.exp (-C * t) * F t`. The hypothesis gives
-- `(Real.exp (-C * t) * F t)' ≤ Real.exp (-C * t) * g t`; integrate this differential inequality
-- from `0` to `t`, then substitute the resulting bound for `F t` back into the original estimate.
/-- Lemma 26.9: if `f` is bounded above on `[0,T]` by `g` plus `C` times its accumulated integral,
then `f` is bounded by the corresponding Gronwall convolution with `g`. -/
theorem gronwall_intervalIntegral_le
    {f g : ℝ → ℝ} {T C : ℝ}
    (hT : 0 ≤ T) (hC : 0 < C)
    (hf : IntervalIntegrable f volume 0 T)
    (hg : IntervalIntegrable g volume 0 T)
    (hfg : ∀ t ∈ Icc 0 T, f t ≤ g t + C * ∫ s in 0..t, f s) :
    ∀ t ∈ Icc 0 T, f t ≤ g t + C * ∫ s in 0..t, Real.exp (C * (t - s)) * g s := sorry

-- Proof sketch: apply `gronwall_intervalIntegral_le` with the constant function `g(t) = G`, then
-- compute the resulting exponential convolution explicitly to obtain `G * Real.exp (C * t)`.
/-- Constant-forcing specialization of the integral Gronwall inequality. -/
theorem gronwall_intervalIntegral_le_const
    {f : ℝ → ℝ} {T C G : ℝ}
    (hT : 0 ≤ T) (hC : 0 < C)
    (hf : IntervalIntegrable f volume 0 T)
    (hfg : ∀ t ∈ Icc 0 T, f t ≤ G + C * ∫ s in 0..t, f s) :
    ∀ t ∈ Icc 0 T, f t ≤ G * Real.exp (C * t) := sorry
