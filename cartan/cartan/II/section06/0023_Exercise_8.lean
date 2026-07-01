import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Proof sketch: consider the holomorphic function
-- `g z = (((a : ℂ) - (b : ℂ) * Complex.I) * f z)`. Its real part is constant on `D` because
-- `Complex.mul_re` gives `g z`.re = a * (f z).re + b * (f z).im`. Apply
-- `AnalyticOnNhd.eq_const_of_re_eq_const` to `g`, then use `a ≠ 0 ∨ b ≠ 0` to see that the scalar
-- `((a : ℂ) - (b : ℂ) * Complex.I)` is nonzero, so constancy of `g` forces constancy of `f`.
/-- Exercise 8: if a holomorphic function on a connected open set has a constant real linear
combination of its real and imaginary parts, then the function is constant on that set. -/
theorem exists_const_of_re_im_linear_eq_const
    {D : Set ℂ} (hD_open : IsOpen D) (hD_connected : IsConnected D) {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f D) {a b c : ℝ} (hab : a ≠ 0 ∨ b ≠ 0)
    (hconst : ∀ z ∈ D, a * (f z).re + b * (f z).im = c) :
    ∃ w : ℂ, ∀ z ∈ D, f z = w := by
  let α : ℂ := (a : ℂ) - (b : ℂ) * Complex.I
  have hα : α ≠ 0 := by
    intro hα0
    have ha0 : a = 0 := by
      simpa [α] using congrArg Complex.re hα0
    have hb0' : -b = 0 := by
      simpa [α] using congrArg Complex.im hα0
    have hb0 : b = 0 := by linarith
    exact hab.elim (fun ha ↦ ha ha0) (fun hb ↦ hb hb0)
  have hconst' : ∀ z ∈ D, ((α • f z)).re = c := by
    intro z hz
    simpa [α, Complex.mul_re, smul_eq_mul] using hconst z hz
  have hαf : AnalyticOnNhd ℂ (α • f) D := by
    simpa using (hf.const_smul : AnalyticOnNhd ℂ (α • f) D)
  obtain ⟨w, hw⟩ :=
    AnalyticOnNhd.eq_const_of_re_eq_const hαf hconst' hD_open hD_connected
  refine ⟨α⁻¹ * w, ?_⟩
  intro z hz
  have hz' : α * f z = w := by
    simpa [smul_eq_mul] using hw z hz
  have := congrArg (fun t : ℂ ↦ α⁻¹ * t) hz'
  simpa [α, hα, mul_assoc] using this
