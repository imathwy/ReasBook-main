import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

/-- Remark III.4-extra-4: if the Laurent coefficients of `f` on the circle `|z| = r` are given by
the Cauchy integral formula and `M` bounds `‖f z‖` on that circle, then each coefficient satisfies
Cauchy's inequality `‖a n‖ ≤ M / r ^ n`. -/
-- Proof sketch: take norms in the Cauchy integral formula for `a n`, bound the integrand on the
-- circle `|z| = r` by `M / r ^ n`, and use the standard estimate for the circle integral over
-- `C(0, r)`.
lemma norm_laurent_coeff_le_circle_bound
    {f : ℂ → ℂ} {a : ℤ → ℂ} {r M : ℝ} (hr : 0 < r)
    (hM : ∀ z ∈ Metric.sphere (0 : ℂ) r, ‖f z‖ ≤ M)
    (n : ℤ)
    (ha : a n = (2 * (Real.pi : ℂ) * Complex.I : ℂ)⁻¹ *
      ∮ z in C(0, r), f z / z ^ (n + 1)) :
    ‖a n‖ ≤ M / r ^ n := by
  have hr0 : 0 ≤ r := hr.le
  rw [ha]
  -- On the circle, the integrand inherits the uniform bound after dividing by `z ^ (n + 1)`.
  have h_integrand :
      ∀ z ∈ Metric.sphere (0 : ℂ) r, ‖f z / z ^ (n + 1)‖ ≤ M / r ^ (n + 1) := by
    intro z hz
    have hz_norm : ‖z‖ = r := by
      simpa using mem_sphere_iff_norm.mp hz
    rw [norm_div, norm_zpow]
    have hpow_pos : 0 < r ^ (n + 1) := by
      positivity
    simpa [hz_norm] using
      (div_le_div_of_nonneg_right (hM z hz) hpow_pos.le)
  -- Bound the circle integral by controlling the integrand uniformly on `|z| = r`.
  have hbound_smul :=
    circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
      (f := fun z : ℂ ↦ f z / z ^ (n + 1)) (c := (0 : ℂ)) (R := r)
      (C := M / r ^ (n + 1)) hr0 h_integrand
  have hbound :
      ‖((2 * (Real.pi : ℂ) * Complex.I : ℂ)⁻¹) *
          ∮ z in C((0 : ℂ), r), f z / z ^ (n + 1)‖ ≤ r * (M / r ^ (n + 1)) := by
    simpa only [smul_eq_mul] using hbound_smul
  -- Normalize the remaining power of `r` to match the announced Cauchy bound.
  have hclose : r * (M / r ^ (n + 1)) = M / r ^ n := by
    have hr_ne : (r : ℝ) ≠ 0 := ne_of_gt hr
    have hpow_ne : r ^ n ≠ 0 := zpow_ne_zero n hr_ne
    have hpow_succ_ne : r ^ (n + 1) ≠ 0 := zpow_ne_zero (n + 1) hr_ne
    rw [div_eq_mul_inv, div_eq_mul_inv, zpow_add₀ hr_ne n 1, zpow_one]
    field_simp [hpow_ne, hpow_succ_ne]
  exact hbound.trans_eq hclose

/-- Two holomorphic extensions of a function from a punctured disc to the full disc coincide on
that disc. -/
-- Proof sketch: the two extensions agree on the punctured ball because they both agree with `f`;
-- this gives frequent equality near `0`, so the analytic identity theorem on the connected ball
-- forces equality on the whole ball.
lemma analytic_extension_on_ball_unique
    {ρ : ℝ} (hρ : 0 < ρ) {f g h : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) ρ))
    (hh : AnalyticOnNhd ℂ h (Metric.ball (0 : ℂ) ρ))
    (hfg : Set.EqOn f g (Metric.ball (0 : ℂ) ρ \ {(0 : ℂ)}))
    (hfh : Set.EqOn f h (Metric.ball (0 : ℂ) ρ \ {(0 : ℂ)})) :
    Set.EqOn g h (Metric.ball (0 : ℂ) ρ) := by
  let U := Metric.ball (0 : ℂ) ρ
  have hgh : Set.EqOn g h (U \ {(0 : ℂ)}) := fun _ hz ↦ (hfg hz).symm.trans (hfh hz)
  have hfrequently : ∃ᶠ z in 𝓝[≠] (0 : ℂ), g z = h z := by
    refine Filter.Eventually.frequently ?_
    filter_upwards [inter_mem_nhdsWithin ({(0 : ℂ)}ᶜ) (Metric.ball_mem_nhds (0 : ℂ) hρ)] with z hz
    exact hgh (by
      rcases hz with ⟨hz0, hzU⟩
      exact ⟨hzU, hz0⟩)
  exact hg.eqOn_of_preconnected_of_frequently_eq hh
    (by simpa [U] using (convex_ball (0 : ℂ) ρ).isPreconnected)
    (Metric.mem_ball_self hρ) hfrequently
