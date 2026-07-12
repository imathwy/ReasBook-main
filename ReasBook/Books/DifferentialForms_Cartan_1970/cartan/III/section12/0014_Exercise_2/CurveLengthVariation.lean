import Mathlib

open Complex MeasureTheory
open scoped MeasureTheory Real Manifold

/-- Helper for Exercise 2: a preconnected set in a metric space has Hausdorff `1`-measure at least
the distance between any two of its points. -/
lemma hausdorffMeasure_ge_dist_of_isPreconnected
    {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {s : Set E} (hs : IsPreconnected s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ENNReal.ofReal (dist x y) ≤ μH[1] s := by
  let g : E → ℝ := dist x
  have hLip : LipschitzWith 1 g := LipschitzWith.dist_right x
  have hpre : IsPreconnected (g '' s) := hs.image g hLip.continuous.continuousOn
  have hsubset : Set.Icc 0 (dist x y) ⊆ g '' s := by
    -- The distance image is a preconnected subset of `ℝ` containing the endpoint distances.
    refine hpre.Icc_subset ?_ ?_
    · exact ⟨x, hx, by simp [g]⟩
    · exact ⟨y, hy, by simp [g]⟩
  -- Compare the image with the interval of distances, then use the Lipschitz upper bound.
  calc
    ENNReal.ofReal (dist x y) = μH[1] (Set.Icc 0 (dist x y)) := by
      rw [MeasureTheory.hausdorffMeasure_real, Real.volume_Icc]
      simp
    _ ≤ μH[1] (g '' s) := measure_mono hsubset
    _ ≤ μH[1] s := by
      simpa using hLip.hausdorffMeasure_image_le (d := (1 : ℝ)) (by norm_num) s

/-- Helper for Exercise 2: on a single closed interval cell, if the interval derivative stays
`δ`-close to a fixed vector `v`, then the speed integral is bounded by the chord length plus the
expected oscillation error. -/
lemma single_cell_speed_le_chord_add_derivWithin_oscillation
    {γ : ℝ → ℂ} {x y δ : ℝ} {v : ℂ} (hxy : x ≤ y)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc x y))
    (hδ : ∀ t ∈ Set.Icc x y, ‖derivWithin γ (Set.Icc x y) t - v‖ ≤ δ) :
    ∫ t in x..y, ‖derivWithin γ (Set.Icc x y) t‖ ≤
      dist (γ x) (γ y) + 2 * δ * (y - x) := by
  by_cases hEq : x = y
  · -- On a degenerate cell both the speed integral and the chord length vanish.
    subst hEq
    simp
  have hxy_lt : x < y := lt_of_le_of_ne hxy hEq
  have hδ_nonneg : 0 ≤ δ := by
    have hx_mem : x ∈ Set.Icc x y := ⟨le_rfl, hxy⟩
    exact le_trans (by simpa using norm_nonneg (derivWithin γ (Set.Icc x y) x - v)) (hδ x hx_mem)
  have hderivCont :
      ContinuousOn (derivWithin γ (Set.Icc x y)) (Set.Icc x y) :=
    hγ.continuousOn_derivWithin (s := Set.Icc x y) (uniqueDiffOn_Icc hxy_lt) (by norm_num)
  have hderivInt :
      IntervalIntegrable (fun t : ℝ ↦ derivWithin γ (Set.Icc x y) t) volume x y :=
    hderivCont.intervalIntegrable_of_Icc hxy
  have hnormInt :
      IntervalIntegrable (fun t : ℝ ↦ ‖derivWithin γ (Set.Icc x y) t‖) volume x y :=
    hderivCont.norm.intervalIntegrable_of_Icc hxy
  have hshiftInt :
      IntervalIntegrable (fun t : ℝ ↦ derivWithin γ (Set.Icc x y) t - v) volume x y :=
    (hderivCont.sub continuousOn_const).intervalIntegrable_of_Icc hxy
  have hshiftNormInt :
      IntervalIntegrable (fun t : ℝ ↦ ‖derivWithin γ (Set.Icc x y) t - v‖) volume x y :=
    (hderivCont.sub continuousOn_const).norm.intervalIntegrable_of_Icc hxy
  have hconstNormInt :
      IntervalIntegrable (fun _ : ℝ ↦ ‖v‖ + δ) volume x y :=
    continuous_const.intervalIntegrable _ _
  have hconstShiftInt :
      IntervalIntegrable (fun _ : ℝ ↦ δ) volume x y :=
    continuous_const.intervalIntegrable _ _
  have hconstInt :
      IntervalIntegrable (fun _ : ℝ ↦ v) volume x y :=
    continuous_const.intervalIntegrable _ _
  have hderivIntegral :
      ∫ t in x..y, derivWithin γ (Set.Icc x y) t = γ y - γ x :=
    intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc hγ hxy
  have herror_eq :
      ∫ t in x..y, (derivWithin γ (Set.Icc x y) t - v) =
        γ y - γ x - (y - x) • v := by
    -- Separate the constant part of the interval derivative and rewrite the derivative integral.
    have hsub :
        ∫ t in x..y, (derivWithin γ (Set.Icc x y) t - v) =
          (∫ t in x..y, derivWithin γ (Set.Icc x y) t) - (y - x) • v := by
      simpa [intervalIntegral.integral_const] using intervalIntegral.integral_sub hderivInt hconstInt
    calc
      ∫ t in x..y, (derivWithin γ (Set.Icc x y) t - v) =
          (∫ t in x..y, derivWithin γ (Set.Icc x y) t) - (y - x) • v := hsub
      _ = γ y - γ x - (y - x) • v := by rw [hderivIntegral]
  have herror_bound :
      ‖∫ t in x..y, (derivWithin γ (Set.Icc x y) t - v)‖ ≤ δ * (y - x) := by
    -- The interval derivative oscillation is pointwise `≤ δ`, so its integral has norm
    -- bounded by `δ * (y - x)`.
    calc
      ‖∫ t in x..y, (derivWithin γ (Set.Icc x y) t - v)‖ ≤
          ∫ t in x..y, ‖derivWithin γ (Set.Icc x y) t - v‖ := by
            exact intervalIntegral.norm_integral_le_integral_norm hxy
      _ ≤ ∫ t in x..y, δ := by
            refine intervalIntegral.integral_mono_on_of_le_Ioo hxy hshiftNormInt hconstShiftInt ?_
            intro t ht
            exact hδ t ⟨ht.1.le, ht.2.le⟩
      _ = δ * (y - x) := by simpa [smul_eq_mul, mul_comm] using intervalIntegral.integral_const δ
  have hv_bound :
      (y - x) * ‖v‖ ≤ dist (γ x) (γ y) + δ * (y - x) := by
    -- Rewrite the fixed-vector contribution as the main chord plus the integral error term.
    have hsmul_eq :
        (y - x) • v =
          (γ y - γ x) - ∫ t in x..y, (derivWithin γ (Set.Icc x y) t - v) := by
      rw [herror_eq]
      abel
    calc
      (y - x) * ‖v‖ = ‖(y - x) • v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy)]
      _ = ‖(γ y - γ x) - ∫ t in x..y, (derivWithin γ (Set.Icc x y) t - v)‖ := by
            rw [hsmul_eq]
      _ ≤ ‖γ y - γ x‖ + ‖∫ t in x..y, (derivWithin γ (Set.Icc x y) t - v)‖ := by
            exact norm_sub_le _ _
      _ ≤ ‖γ y - γ x‖ + δ * (y - x) := by
            gcongr
      _ = ‖γ x - γ y‖ + δ * (y - x) := by rw [norm_sub_rev]
      _ = dist (γ x) (γ y) + δ * (y - x) := by rw [dist_eq_norm]
  have hspeed_bound :
      ∫ t in x..y, ‖derivWithin γ (Set.Icc x y) t‖ ≤ (‖v‖ + δ) * (y - x) := by
    -- Pointwise, the speed cannot exceed the frozen derivative norm by more than `δ`.
    calc
      ∫ t in x..y, ‖derivWithin γ (Set.Icc x y) t‖ ≤ ∫ t in x..y, (‖v‖ + δ) := by
        refine intervalIntegral.integral_mono_on_of_le_Ioo hxy hnormInt hconstNormInt ?_
        intro t ht
        calc
          ‖derivWithin γ (Set.Icc x y) t‖ ≤ ‖v‖ + ‖derivWithin γ (Set.Icc x y) t - v‖ := by
                simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                  norm_add_le (derivWithin γ (Set.Icc x y) t - v) v
          _ ≤ ‖v‖ + δ := by gcongr; exact hδ t ⟨ht.1.le, ht.2.le⟩
      _ = (‖v‖ + δ) * (y - x) := by
            simpa [smul_eq_mul, mul_comm] using intervalIntegral.integral_const (‖v‖ + δ)
  -- Combine the fixed-vector lower bound on the chord with the pointwise upper bound on the speed.
  linarith

/-- Helper for Exercise 2: a unit-speed parametrization is `1`-Lipschitz on its parameter set. -/
lemma hasUnitSpeedOn_lipschitzOnWith_one
    {E : Type*} [PseudoMetricSpace E] {φ : ℝ → E} {s : Set ℝ}
    (hφ : HasUnitSpeedOn φ s) :
    LipschitzOnWith 1 φ s := by
  have hspeed : HasConstantSpeedOnWith φ s 1 := by
    simpa [HasUnitSpeedOn] using hφ
  rw [hasConstantSpeedOnWith_iff_ordered] at hspeed
  have hordered :
      ∀ ⦃x⦄ (_ : x ∈ s) ⦃y⦄ (_ : y ∈ s),
        x ≤ y → eVariationOn φ (s ∩ Set.Icc x y) = ENNReal.ofReal (y - x) := by
    intro x hx y hy hxy
    simpa using hspeed hx hy hxy
  intro x hx y hy
  rcases le_total x y with hxy | hyx
  · have hx' : x ∈ s ∩ Set.Icc x y := ⟨hx, le_rfl, hxy⟩
    have hy' : y ∈ s ∩ Set.Icc x y := ⟨hy, hxy, le_rfl⟩
    -- On an ordered pair, the unit-speed variation formula bounds the endpoint distance.
    calc
      edist (φ x) (φ y) ≤ eVariationOn φ (s ∩ Set.Icc x y) :=
        eVariationOn.edist_le φ hx' hy'
      _ = ENNReal.ofReal (y - x) := hordered hx hy hxy
      _ = edist x y := by
        simpa [edist_dist, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy)]
      _ = 1 * edist x y := by simp
  · -- The reverse-ordered case follows by symmetry of the ambient distance.
    calc
      edist (φ x) (φ y) = edist (φ y) (φ x) := edist_comm _ _
      _ ≤ eVariationOn φ (s ∩ Set.Icc y x) := by
        exact eVariationOn.edist_le φ ⟨hy, le_rfl, hyx⟩ ⟨hx, hyx, le_rfl⟩
      _ = ENNReal.ofReal (x - y) := hordered hy hx hyx
      _ = edist x y := by
        simpa [edist_dist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx)]
      _ = 1 * edist x y := by simp

/-- Helper for Exercise 2: the variation parameter on `Icc a b` takes values in `[0, V]`, where
`V` is the total variation on that interval. -/
lemma variation_parameter_image_subset_interval
    {E : Type*} [PseudoEMetricSpace E] {γ : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hbv : LocallyBoundedVariationOn γ (Set.Icc a b)) :
    variationOnFromTo γ (Set.Icc a b) a '' Set.Icc a b ⊆
      Set.Icc 0 (eVariationOn γ (Set.Icc a b)).toReal := by
  let v : ℝ → ℝ := variationOnFromTo γ (Set.Icc a b) a
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hmono : MonotoneOn v (Set.Icc a b) := variationOnFromTo.monotoneOn hbv ha
  intro t ht
  rcases ht with ⟨x, hx, rfl⟩
  constructor
  · -- Monotonicity from the left endpoint gives the nonnegativity of the parameter.
    have hx0 : v a ≤ v x := hmono ha hx hx.1
    simpa [v, variationOnFromTo.self] using hx0
  · -- Monotonicity up to the right endpoint bounds the parameter by the total variation.
    have hxtop : v x ≤ v b := hmono hx hb hx.2
    simpa [v, variationOnFromTo.eq_of_le (f := γ) (s := Set.Icc a b) hab] using hxtop

/-- Helper for Exercise 2: the natural parameterization on `Icc a b` has exactly the same image as
the original curve on that interval, once the parameter set is identified with the variation image.
-/
lemma naturalParameterization_image_eq_interval_image
    {E : Type*} [MetricSpace E] {γ : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hbv : LocallyBoundedVariationOn γ (Set.Icc a b)) :
    naturalParameterization γ (Set.Icc a b) a ''
        (variationOnFromTo γ (Set.Icc a b) a '' Set.Icc a b) =
      γ '' Set.Icc a b := by
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  ext z
  constructor
  · rintro ⟨t, ⟨x, hx, rfl⟩, rfl⟩
    -- Unfold the inverse-choice definition only after the variation parameter is known to come
    -- from the interval image.
    refine ⟨Function.invFunOn (variationOnFromTo γ (Set.Icc a b) a) (Set.Icc a b)
        (variationOnFromTo γ (Set.Icc a b) a x), ?_, ?_⟩
    · exact Function.invFunOn_apply_mem (f := variationOnFromTo γ (Set.Icc a b) a) hx
    · rfl
  · rintro ⟨x, hx, rfl⟩
    refine ⟨variationOnFromTo γ (Set.Icc a b) a x, ⟨x, hx, rfl⟩, ?_⟩
    -- The natural parameterization agrees with the original curve at matching variation values.
    exact edist_eq_zero.mp <|
      edist_naturalParameterization_eq_zero hbv ha hx

/-- Helper for Exercise 2: after reparameterizing by variation, the `1`-dimensional Hausdorff
measure of the image is bounded above by the total variation on `Icc a b`. -/
lemma hausdorffMeasure_naturalParameterization_image_le_variation
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hbv : LocallyBoundedVariationOn γ (Set.Icc a b)) :
    μH[1] (naturalParameterization γ (Set.Icc a b) a ''
        (variationOnFromTo γ (Set.Icc a b) a '' Set.Icc a b)) ≤
      eVariationOn γ (Set.Icc a b) := by
  let s : Set ℝ := variationOnFromTo γ (Set.Icc a b) a '' Set.Icc a b
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hvar : eVariationOn γ (Set.Icc a b) ≠ ⊤ := by
    simpa [BoundedVariationOn, Set.inter_self] using hbv a b ha hb
  have hunit :
      HasUnitSpeedOn (naturalParameterization γ (Set.Icc a b) a) s := by
    simpa [s] using has_unit_speed_naturalParameterization γ hbv ha
  have hLip :
      LipschitzOnWith 1 (naturalParameterization γ (Set.Icc a b) a) s :=
    hasUnitSpeedOn_lipschitzOnWith_one hunit
  -- The natural parameterization is `1`-Lipschitz on the variation image, so its image measure is
  -- controlled by the measure of the parameter interval.
  calc
    μH[1] (naturalParameterization γ (Set.Icc a b) a '' s) ≤ μH[1] s := by
      simpa [s] using hLip.hausdorffMeasure_image_le (d := (1 : ℝ)) (by norm_num)
    _ ≤ μH[1] (Set.Icc 0 (eVariationOn γ (Set.Icc a b)).toReal) := by
      exact measure_mono (variation_parameter_image_subset_interval (γ := γ) hab hbv)
    _ = eVariationOn γ (Set.Icc a b) := by
      rw [MeasureTheory.hausdorffMeasure_real, Real.volume_Icc]
      simp [hvar]

/-- Helper for Exercise 2: the norm of the derivative of a `C¹` curve on a closed interval is
interval-integrable. -/
lemma intervalIntegrable_norm_deriv_of_contDiffOn_Icc
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b)) :
    IntervalIntegrable (fun t : ℝ ↦ ‖deriv γ t‖) volume a b := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  have hcont :
      ContinuousOn (derivWithin γ (Set.Icc a b)) (Set.Icc a b) :=
    hγ.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) (by norm_num)
  have hIntWithin :
      IntervalIntegrable (fun t : ℝ ↦ ‖derivWithin γ (Set.Icc a b) t‖) volume a b :=
    hcont.norm.intervalIntegrable_of_Icc hab
  -- On the interior of the interval, `derivWithin` agrees with the ordinary derivative.
  refine hIntWithin.congr_ae ?_
  simp only [hab, Set.uIoc_of_le]
  rw [← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

/-- Helper for Exercise 2: on a `C¹` interval, each chord is bounded by the integral of the speed
over the corresponding subinterval. -/
lemma dist_le_integral_norm_deriv_of_contDiffOn_Icc
    {γ : ℝ → ℂ} {a b x y : ℝ} (hxy : x ≤ y)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b))
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    dist (γ x) (γ y) ≤ ∫ t in x..y, ‖deriv γ t‖ := by
  have hsub :
      ContDiffOn ℝ 1 γ (Set.Icc x y) := by
    -- Restrict the `C¹` regularity from the large interval to the chosen cell.
    refine hγ.mono ?_
    intro t ht
    exact ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩
  have hInt : IntervalIntegrable (fun t : ℝ ↦ ‖deriv γ t‖) volume x y :=
    intervalIntegrable_norm_deriv_of_contDiffOn_Icc hxy hsub
  -- Apply the fundamental theorem of calculus and estimate the norm of the resulting integral.
  calc
    dist (γ x) (γ y) = ‖γ y - γ x‖ := by rw [dist_eq_norm, norm_sub_rev]
    _ = ‖∫ t in x..y, deriv γ t‖ := by
      rw [intervalIntegral.integral_deriv_of_contDiffOn_Icc hsub hxy]
    _ ≤ ∫ t in x..y, ‖deriv γ t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hxy
