import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_4_25 (from Items/Chap04) -/
open MeasureTheory Set Filter
open scoped Topology

-- Proof sketch: show that the oscillatory primitive `b ↦ ∫ x in 0..b, sin x / (1 + x)` converges
-- as `b → ∞` by Dirichlet's test or integration by parts, and use the failure of absolute
-- integrability on `[0, ∞)` to conclude that this gives only an improper Riemann integral.
/-- Remark 4.25: the function `x ↦ sin x / (1 + x)` on `[0, ∞)` has a convergent improper
Riemann integral, but its absolute value does not have finite Lebesgue integral on `[0, ∞)`. -/
theorem sine_decay_improper_integrable_not_hasFiniteIntegral_on_Ici :
    (∃ c : ℝ,
      Tendsto
        (fun b : ℝ ↦ ∫ x in (0 : ℝ)..b, Real.sin x / (1 + x))
        atTop (𝓝 c)) ∧
    ¬ HasFiniteIntegral (fun x : ℝ ↦ Real.sin x / (1 + x))
      (volume.restrict (Set.Ici (0 : ℝ))) := sorry

theorem not_integrableOn_abs_sine_decay_on_Ici :
    ¬ IntegrableOn (fun x : ℝ ↦ |Real.sin x / (1 + x)|) (Set.Ici (0 : ℝ)) := by
  intro h_integrable
  refine sine_decay_improper_integrable_not_hasFiniteIntegral_on_Ici.2 ?_
  rw [← hasFiniteIntegral_norm_iff (fun x : ℝ ↦ Real.sin x / (1 + x))]
  simpa [Real.norm_eq_abs, abs_div] using h_integrable.2
