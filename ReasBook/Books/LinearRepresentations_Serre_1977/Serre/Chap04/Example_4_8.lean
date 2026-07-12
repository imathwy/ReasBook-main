import Mathlib.Analysis.Fourier.AddCircle

open MeasureTheory
open scoped intervalIntegral

universe u

namespace Real.Angle

/-- Positivity witness for the period `2 * π` underlying `Real.Angle`. -/
private instance factTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/- Source/core/bridge triage:
- `source-facing`: the averaging formula on `C∞`, written via angles modulo `2π`;
- `core/canonical`: `AddCircle.integral_haarAddCircle` and
  `AddCircle.intervalIntegral_preimage`;
- `bridge/view`: specialize those canonical `AddCircle` results at
  `Real.Angle = AddCircle (2 * π)` and compose with `Real.Angle.toCircle`.
-/

/-- The normalized Haar integral on `Real.Angle = AddCircle (2 * π)` is `(2 * π)⁻¹` times the
interval integral over `0..2 * π`. -/
theorem integral_eq_inv_two_pi_smul_intervalIntegral {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Real.Angle → E) :
    (∫ θ : Real.Angle, f θ ∂AddCircle.haarAddCircle) =
      (2 * Real.pi)⁻¹ • ∫ a in (0 : ℝ)..(2 * Real.pi), f a := by
  change
    (∫ θ : AddCircle (2 * Real.pi), f θ ∂AddCircle.haarAddCircle) =
      (2 * Real.pi)⁻¹ • ∫ a in (0 : ℝ)..(2 * Real.pi), f (a : AddCircle (2 * Real.pi))
  rw [AddCircle.integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage (2 * Real.pi) 0]
  simp

/-- Example 4-8: if `C∞` is viewed as the unit complex circle via `Real.Angle.toCircle`, then
integrating a function on `C∞` against the normalized Haar measure is the same as averaging its
lift over `α ∈ [0, 2 * π]`. -/
theorem integral_toCircle_eq_inv_two_pi_smul_intervalIntegral {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Circle → E) :
    (∫ θ : Real.Angle, f θ.toCircle ∂AddCircle.haarAddCircle) =
      (2 * Real.pi)⁻¹ • ∫ a in (0 : ℝ)..(2 * Real.pi), f (Real.Angle.toCircle a) := by
  simpa using
    integral_eq_inv_two_pi_smul_intervalIntegral (fun θ : Real.Angle ↦ f θ.toCircle)

end Real.Angle
