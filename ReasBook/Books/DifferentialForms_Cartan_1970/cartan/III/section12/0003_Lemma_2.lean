import Mathlib
import DifferentialForms_Cartan_1970.cartan.III.section12.SectorArc

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Interval

/-
Semantic recall note: this file reuses the chapter-local owners `puncturedSector` and
`sectorArcIntegral` from the preceding item, together with mathlib's `nhdsWithin`
formulation of punctured limits inside a sector.
-/

/-- Helper for Lemma 2: a point on the radius-`r` circular arc with angle in `θ₁ ≤ θ ≤ θ₂`
belongs to the punctured sector whenever `r > 0`. -/
lemma circleMap_mem_puncturedSector
    {θ₁ θ₂ r θ : ℝ} (hr : 0 < r) (hθ : θ ∈ Set.Icc θ₁ θ₂) :
    circleMap 0 r θ ∈ puncturedSector θ₁ θ₂ := by
  -- Unpack the punctured-sector definition into closed-sector membership plus nonvanishing.
  rw [mem_puncturedSector_iff]
  constructor
  · exact mem_closedSector_iff.2 ⟨r, hr.le, θ, hθ, rfl⟩
  · exact circleMap_ne_center (c := 0) (R := r) (θ := θ) hr.ne'

/-- Helper for Lemma 2: the punctured-sector limit of `z * f z` gives a uniform bound on every
sufficiently small circular arc inside the sector. -/
lemma small_circle_weighted_bound
    (f : ℂ → ℂ) (θ₁ θ₂ : ℝ)
    (hlim :
      Filter.Tendsto (fun z : ℂ ↦ z * f z) (nhdsWithin 0 (puncturedSector θ₁ θ₂)) (nhds 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ⦃r θ : ℝ⦄, 0 < r → r < δ → θ ∈ Set.Icc θ₁ θ₂ →
      ‖circleMap 0 r θ * f (circleMap 0 r θ)‖ < ε := by
  -- Convert the punctured-sector limit into the usual `ε`-`δ` statement.
  obtain ⟨δ, hδ_pos, hδ⟩ := (Metric.tendsto_nhdsWithin_nhds.1 hlim) ε hε
  refine ⟨δ, hδ_pos, ?_⟩
  intro r θ hr hrδ hθ
  have hmem : circleMap 0 r θ ∈ puncturedSector θ₁ θ₂ :=
    circleMap_mem_puncturedSector hr hθ
  have hdist : dist (circleMap 0 r θ) 0 < δ := by
    simpa [dist_eq_norm, sub_zero, norm_circleMap_zero, abs_of_pos hr] using hrδ
  simpa [dist_eq_norm, sub_zero] using hδ hmem hdist

/-- Helper for Lemma 2: the norm of the sector-arc integral is bounded by the angular length times
a uniform bound for `‖z * f z‖` along the arc. -/
lemma norm_sectorArcIntegral_le_angle_mul_bound
    (f : ℂ → ℂ) (θ₁ θ₂ r M : ℝ) (hθ : θ₁ ≤ θ₂)
    (hM : ∀ θ ∈ Set.Icc θ₁ θ₂, ‖circleMap 0 r θ * f (circleMap 0 r θ)‖ ≤ M) :
    ‖sectorArcIntegral f r θ₁ θ₂‖ ≤ |θ₂ - θ₁| * M := by
  -- Rewrite the contour integral into the interval integral from the sector-arc owner.
  rw [sectorArcIntegral_def]
  have hbound :
      ‖∫ θ in θ₁..θ₂, Complex.I * circleMap 0 r θ * f (circleMap 0 r θ)‖
        ≤ ∫ θ in θ₁..θ₂, M := by
    refine intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) hθ ?_
      intervalIntegrable_const
    filter_upwards with θ
    intro hθ_mem
    simpa [norm_mul, mul_assoc] using hM θ (Set.Ioc_subset_Icc_self hθ_mem)
  -- Compute the constant integral and identify the interval length with `|θ₂ - θ₁|`.
  calc
    ‖∫ θ in θ₁..θ₂, Complex.I * circleMap 0 r θ * f (circleMap 0 r θ)‖
        ≤ ∫ θ in θ₁..θ₂, M := hbound
    _ = (θ₂ - θ₁) * M := by simp [intervalIntegral.integral_const]
    _ = |θ₂ - θ₁| * M := by rw [abs_of_nonneg (sub_nonneg.mpr hθ)]

/-- Lemma 2: if `f` is continuous on the punctured sector `θ₁ ≤ θ ≤ θ₂` and `z ↦ z * f z`
tends to `0` as `z → 0` through the punctured sector `θ₁ ≤ θ ≤ θ₂`, then the integral of `f(z) dz`
over the circular arc `|z| = r` contained in the sector tends to `0` as `r → 0+`. -/
theorem sectorArcIntegral_tendsto_zero_of_tendsto_zero_mul_at_zero
    (f : ℂ → ℂ) (θ₁ θ₂ : ℝ)
    (hθ : θ₁ ≤ θ₂)
    (hcont : ContinuousOn f (puncturedSector θ₁ θ₂))
    (hlim :
      Filter.Tendsto (fun z : ℂ ↦ z * f z) (nhdsWithin 0 (puncturedSector θ₁ θ₂)) (nhds 0)) :
    Filter.Tendsto
      (fun r : ℝ ↦ sectorArcIntegral f r θ₁ θ₂)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  -- Route correction: follow the source estimate directly by bounding `z * f z` on the shrinking
  -- arc, then multiply that bound by the arc length `|θ₂ - θ₁|`.
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  let η := ε / (|θ₂ - θ₁| + 1)
  have hη_pos : 0 < η := by
    dsimp [η]
    positivity
  obtain ⟨δ, hδ_pos, hδ⟩ := small_circle_weighted_bound f θ₁ θ₂ hlim hη_pos
  refine ⟨δ, hδ_pos, ?_⟩
  intro r hr hrδ
  have hr_pos : 0 < r := hr
  have hrδ' : r < δ := by
    simpa [dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_pos hr_pos] using hrδ
  have harc :
      ‖sectorArcIntegral f r θ₁ θ₂‖ ≤ |θ₂ - θ₁| * η := by
    refine norm_sectorArcIntegral_le_angle_mul_bound f θ₁ θ₂ r η hθ ?_
    intro θ hθ_mem
    exact le_of_lt (hδ hr_pos hrδ' hθ_mem)
  have hfrac_lt_one : |θ₂ - θ₁| / (|θ₂ - θ₁| + 1) < 1 := by
    have hden : 0 < |θ₂ - θ₁| + 1 := by positivity
    have hnum_lt : |θ₂ - θ₁| < |θ₂ - θ₁| + 1 := by linarith
    exact (div_lt_one hden).2 hnum_lt
  have hlt : |θ₂ - θ₁| * η < ε := by
    calc
      |θ₂ - θ₁| * η = ε * (|θ₂ - θ₁| / (|θ₂ - θ₁| + 1)) := by
        dsimp [η]
        ring
      _ < ε * 1 := by
        exact mul_lt_mul_of_pos_left hfrac_lt_one hε
      _ = ε := by ring
  -- Convert the norm estimate back into the metric target at `0`.
  simpa [dist_eq_norm, sub_zero] using lt_of_le_of_lt harc hlt
