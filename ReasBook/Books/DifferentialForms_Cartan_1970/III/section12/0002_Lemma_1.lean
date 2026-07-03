import Mathlib
import DifferentialForms_Cartan_1970.III.section12.SectorArc

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Interval

/-
Semantic recall note: the source-facing owner here is the chapter-local `sectorArcIntegral`.
This lemma is source-facing rather than a new owner: it should keep the textbook quantity
`z * f z` on the arc, using the complex-valued bridge `sectorArcIntegral_def` rather than the
parameterization-derivative implementation of the owner.
-/

/-- Helper for Lemma 1: a uniform bound on `z * f z` along the angle interval bounds the norm of
the sector arc integral by that bound times the arc length. -/
lemma sectorArcIntegral_norm_le_of_uniform_weight_bound
    (f : ℂ → ℂ) (r θ₁ θ₂ C : ℝ)
    (hθ : θ₁ ≤ θ₂)
    (hC : ∀ θ ∈ Set.Icc θ₁ θ₂, ‖circleMap 0 r θ * f (circleMap 0 r θ)‖ ≤ C) :
    ‖sectorArcIntegral f r θ₁ θ₂‖ ≤ C * |θ₂ - θ₁| := by
  -- Rewrite the source-facing arc integral into the textbook `I * z * f z` form.
  rw [sectorArcIntegral_def]
  -- Apply the standard interval-integral norm estimate using the pointwise arc bound.
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθmem ↦ ?_
  have hmem : θ ∈ Set.Icc θ₁ θ₂ := by
    have hmem' : θ ∈ Set.Ioc θ₁ θ₂ := by
      simpa only [Set.uIoc_of_le hθ] using hθmem
    exact ⟨le_of_lt hmem'.1, hmem'.2⟩
  calc
    ‖Complex.I * circleMap 0 r θ * f (circleMap 0 r θ)‖
        = ‖circleMap 0 r θ * f (circleMap 0 r θ)‖ := by
          simp only [norm_mul, Complex.norm_I, one_mul]
    _ ≤ C := hC θ hmem

/-- Lemma 1: if `z ↦ z * f z` tends uniformly to `0` on the angle interval
`θ₁ ≤ θ ≤ θ₂` as `|z| → ∞`, and this arc integrand is eventually interval-integrable along the
radius-`r` parametrization, then the integral of `f(z) dz` over the circular arc `|z| = r`
contained in that sector tends to `0` as `r → +∞`. -/
theorem sectorArcIntegral_tendsto_zero_of_tendsto_zero_mul
    (f : ℂ → ℂ) (θ₁ θ₂ : ℝ)
    (hθ : θ₁ ≤ θ₂)
    (hint :
      ∀ᶠ r : ℝ in Filter.atTop,
        IntervalIntegrable
          (fun θ : ℝ ↦ circleMap 0 r θ * f (circleMap 0 r θ))
          MeasureTheory.volume
          θ₁
          θ₂)
    (hlim :
      TendstoUniformlyOn
        (fun (r : ℝ) θ ↦ circleMap 0 r θ * f (circleMap 0 r θ))
        0
        Filter.atTop
        (Set.Icc θ₁ θ₂)) :
    Filter.Tendsto (fun r : ℝ ↦ sectorArcIntegral f r θ₁ θ₂) Filter.atTop (nhds 0) := by
  -- The eventual integrability hypothesis is part of the source statement, but the norm estimate
  -- below already controls the interval integral directly.
  let _ := hint
  -- Prove convergence by the metric epsilon criterion for the arc-integral norm.
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  let δ : ℝ := ε / (|θ₂ - θ₁| + 1)
  have hlen_pos : 0 < |θ₂ - θ₁| + 1 := by
    positivity
  have hδpos : 0 < δ := by
    exact div_pos hε hlen_pos
  have hsmall :
      ∀ᶠ r : ℝ in Filter.atTop,
        ∀ θ ∈ Set.Icc θ₁ θ₂, ‖circleMap 0 r θ * f (circleMap 0 r θ)‖ < δ := by
    -- Convert uniform convergence to an eventual uniform norm bound on the angle interval.
    have hmetric :=
      hlim {p : ℂ × ℂ | dist p.1 p.2 < δ} (Metric.dist_mem_uniformity hδpos)
    filter_upwards [hmetric] with r hr θ hθmem
    simpa only [δ, Pi.zero_apply, dist_eq_norm, zero_sub, norm_neg] using hr θ hθmem
  have hδ_mul_lt : δ * |θ₂ - θ₁| < ε := by
    -- The chosen `δ` is smaller than `ε / |θ₂ - θ₁|`, so the arc-length factor stays below `ε`.
    have hlen_lt : |θ₂ - θ₁| < |θ₂ - θ₁| + 1 := by
      linarith [abs_nonneg (θ₂ - θ₁)]
    have hmul_lt :
        δ * |θ₂ - θ₁| < δ * (|θ₂ - θ₁| + 1) := by
      exact mul_lt_mul_of_pos_left hlen_lt hδpos
    have hcancel : δ * (|θ₂ - θ₁| + 1) = ε := by
      rw [show δ = ε / (|θ₂ - θ₁| + 1) by rfl]
      rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hlen_pos.ne', mul_one]
    exact hmul_lt.trans_eq hcancel
  filter_upwards [hsmall] with r hr
  -- Bound the arc integral by the uniform arc bound and then compare with `ε`.
  have hbound :
      ‖sectorArcIntegral f r θ₁ θ₂‖ ≤ δ * |θ₂ - θ₁| :=
    sectorArcIntegral_norm_le_of_uniform_weight_bound f r θ₁ θ₂ δ hθ
      (fun θ hmem ↦ (hr θ hmem).le)
  have hlt : ‖sectorArcIntegral f r θ₁ θ₂‖ < ε := by
    exact lt_of_le_of_lt hbound hδ_mul_lt
  simpa only [dist_eq_norm, sub_zero] using hlt
