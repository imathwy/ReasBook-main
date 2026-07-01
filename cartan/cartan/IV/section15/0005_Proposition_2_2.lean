import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.OpenMapping

-- Declarations for this item will be appended below by the statement pipeline.

open Complex InnerProductSpace Metric Set

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the statement surface was checked directly against
-- `HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq` and
-- `AnalyticOnNhd.eq_re_add_const_mul_I_of_re_eq_const`.

/-- Proposition 2.2 (1). A real-valued harmonic function on an open set of `ℂ` is, near each
point of that set, the real part of a holomorphic function. -/
theorem harmonicOnNhd_locally_exists_analytic_re_eq {D : Set ℂ} (hD : IsOpen D) {g : ℂ → ℝ}
    (hg : HarmonicOnNhd g D) {z : ℂ} (hz : z ∈ D) :
    ∃ r > 0, ∃ _ : ball z r ⊆ D, ∃ f : ℂ → ℂ,
      AnalyticOnNhd ℂ f (ball z r) ∧ EqOn (fun w ↦ (f w).re) g (ball z r) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hD z hz
  obtain ⟨f, hf, hfg⟩ := HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq <| hg.mono hball
  exact ⟨r, hr, hball, f, hf, hfg⟩

/-- Proposition 2.2 (2). On a common complex ball, two holomorphic functions with the same real
part differ by a purely imaginary additive constant. -/
theorem analyticOnNhd_eqOn_real_part_imp_eqOn_add_const_mul_I {z : ℂ} {r : ℝ} (hr : 0 < r)
    {f₁ f₂ : ℂ → ℂ} (hf₁ : AnalyticOnNhd ℂ f₁ (ball z r))
    (hf₂ : AnalyticOnNhd ℂ f₂ (ball z r))
    (hre : EqOn (fun w ↦ (f₁ w).re) (fun w ↦ (f₂ w).re) (ball z r)) :
    ∃ c : ℝ, EqOn f₁ (fun w ↦ f₂ w + c * I) (ball z r) := by
  have hre_zero : ∀ w ∈ ball z r, ((f₁ - f₂) w).re = 0 := by
    intro w hw
    simp [hre hw]
  obtain ⟨c, hc⟩ := AnalyticOnNhd.eq_re_add_const_mul_I_of_re_eq_const
    (hf₁.sub hf₂)
    hre_zero
    isOpen_ball
    (isConnected_ball hr)
  refine ⟨c, ?_⟩
  intro w hw
  specialize hc w hw
  simpa [add_comm] using sub_eq_iff_eq_add'.mp hc
