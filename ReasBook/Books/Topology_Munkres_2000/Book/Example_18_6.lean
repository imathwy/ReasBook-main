module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homeomorph.Defs

public section

/-- The standard one-turn parametrization of the unit circle by the half-open interval
`[0, 1)`, obtained by restricting `Real.fourierChar`. -/
noncomputable def halfOpenUnitIntervalToCircle : Set.Ico (0 : ℝ) 1 → Circle :=
  fun t ↦ Real.fourierChar t

/-- The complex coordinates of `halfOpenUnitIntervalToCircle`; its real and imaginary parts are
respectively `Real.cos (2 * Real.pi * t)` and `Real.sin (2 * Real.pi * t)`. -/
theorem halfOpenUnitIntervalToCircle_apply (t : Set.Ico (0 : ℝ) 1) :
    (halfOpenUnitIntervalToCircle t : ℂ) =
      Real.cos (2 * Real.pi * t) + Real.sin (2 * Real.pi * t) * Complex.I := by
  -- Expand the Fourier character into the standard complex exponential formula.
  simp only [halfOpenUnitIntervalToCircle, Real.fourierChar_apply, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- The initial quarter `[0, 1 / 4)` as a subset of the half-open unit interval. -/
def initialQuarterInterval : Set (Set.Ico (0 : ℝ) 1) :=
  {t | (t : ℝ) < 1 / 4}

/-- Companion for Example 18.6: the standard map from `[0, 1)` to the unit circle is continuous. -/
theorem halfOpenUnitIntervalToCircle_continuous :
    Continuous halfOpenUnitIntervalToCircle := by
  -- Restrict the continuous Fourier character along the subtype inclusion.
  exact Real.continuous_fourierChar.comp continuous_subtype_val

/-- Helper for Example 18.6: `Real.fourierChar` is bijective on one half-open period. -/
lemma fourierChar_bijOn_unitIco :
    Set.BijOn Real.fourierChar (Set.Ico (0 : ℝ) 1) Set.univ := by
  -- The range condition is automatic because the target set is universal.
  refine ⟨Set.mapsTo_univ _ _, ?_, ?_⟩
  · -- Scale `[0,1)` into `[0,2π)` and use injectivity of `Circle.exp` there.
    intro x hx y hy hxy
    obtain ⟨hxLower, hxUpper⟩ := hx
    obtain ⟨hyLower, hyUpper⟩ := hy
    have hTwoPiPos : 0 < 2 * Real.pi := by nlinarith [Real.pi_pos]
    have hScaled : 2 * Real.pi * x = 2 * Real.pi * y := by
      apply Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi)
      · norm_num
      · constructor
        · exact mul_nonneg (by positivity) hxLower
        · simpa only [mul_one] using mul_lt_mul_of_pos_left hxUpper hTwoPiPos
      · constructor
        · exact mul_nonneg (by positivity) hyLower
        · simpa only [mul_one] using mul_lt_mul_of_pos_left hyUpper hTwoPiPos
      · simpa only [Real.fourierChar_apply'] using hxy
    nlinarith [Real.pi_pos]
  · -- Choose the argument in `[0,π]`, or shift a negative argument by one full turn.
    intro z hz
    by_cases harg : 0 ≤ Complex.arg z
    · refine ⟨Complex.arg z / (2 * Real.pi), ?_, ?_⟩
      · constructor
        · exact div_nonneg harg (by positivity)
        · have hArgLe : Complex.arg z ≤ Real.pi := Complex.arg_le_pi z
          apply (div_lt_one (by positivity)).2
          nlinarith [Real.pi_pos]
      · rw [Real.fourierChar_apply']
        have hScale : 2 * Real.pi * (Complex.arg z / (2 * Real.pi)) = Complex.arg z := by
          field_simp [Real.pi_ne_zero]
        rw [hScale, Circle.exp_arg]
    · refine ⟨(Complex.arg z + 2 * Real.pi) / (2 * Real.pi), ?_, ?_⟩
      · have hArgNeg : Complex.arg z < 0 := lt_of_not_ge harg
        have hNegPi : -Real.pi < Complex.arg z := Complex.neg_pi_lt_arg z
        constructor
        · apply div_nonneg
          · nlinarith [Real.pi_pos]
          · positivity
        · apply (div_lt_one (by positivity)).2
          linarith
      · rw [Real.fourierChar_apply']
        have hScale : 2 * Real.pi * ((Complex.arg z + 2 * Real.pi) / (2 * Real.pi)) =
            Complex.arg z + 2 * Real.pi := by
          field_simp [Real.pi_ne_zero]
        rw [hScale, Circle.exp_add_two_pi, Circle.exp_arg]

/-- Companion for Example 18.6: the standard map from `[0, 1)` to the unit circle is bijective. -/
theorem halfOpenUnitIntervalToCircle_bijective :
    Function.Bijective halfOpenUnitIntervalToCircle := by
  -- Transfer the one-period `BijOn` statement to the subtype restriction.
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact fourierChar_bijOn_unitIco.2.1 x.property y.property hxy
  · intro z
    obtain ⟨t, ht, htz⟩ := fourierChar_bijOn_unitIco.2.2 (Set.mem_univ z)
    exact ⟨⟨t, ht⟩, htz⟩

/-- Example 18.6. The continuous bijection from `[0, 1)` to the unit circle is not a
homeomorphism. -/
theorem halfOpenUnitIntervalToCircle_not_isHomeomorph :
    ¬ IsHomeomorph halfOpenUnitIntervalToCircle := by
  -- A homeomorphism would make the noncompact half-open interval compact.
  intro hHomeomorph
  have hCompactSpace : CompactSpace (Set.Ico (0 : ℝ) 1) :=
    (hHomeomorph.homeomorph halfOpenUnitIntervalToCircle).symm.compactSpace
  have hCompact : IsCompact (Set.Ico (0 : ℝ) 1) :=
    isCompact_iff_compactSpace.mpr hCompactSpace
  have hImpossible : (1 : ℝ) ≤ 0 := isCompact_Ico_iff.mp hCompact
  norm_num at hImpossible

/-- Companion for Example 18.6: the initial quarter interval is open in the subspace `[0, 1)`. -/
theorem initialQuarterInterval_isOpen : IsOpen initialQuarterInterval := by
  -- View the interval as the preimage of the open ray below `1 / 4`.
  have hSet : initialQuarterInterval = Subtype.val ⁻¹' Set.Iio (1 / 4 : ℝ) := by
    ext t
    rfl
  rw [hSet]
  exact isOpen_Iio.preimage continuous_subtype_val

/-- Helper for Example 18.6: Fourier points approaching the cut converge to the unit point. -/
lemma fourierChar_cutApproach_tendsto :
    Filter.Tendsto
      (fun n : ℕ ↦ Real.fourierChar (1 - (((n + 2 : ℕ) : ℝ)⁻¹)))
      Filter.atTop (nhds (1 : Circle)) := by
  -- The parameters tend to `1`, whose Fourier value equals the value at `0`.
  have hParameters : Filter.Tendsto
      (fun n : ℕ ↦ 1 - (((n + 2 : ℕ) : ℝ)⁻¹)) Filter.atTop (nhds (1 : ℝ)) := by
    simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_ofNat, sub_zero] using
      tendsto_const_nhds.sub
        (tendsto_inv_atTop_zero.comp
          ((tendsto_natCast_atTop_atTop :
              Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop).comp
            (Filter.tendsto_add_atTop_nat 2)))
  have hFourier := Real.continuous_fourierChar.continuousAt.tendsto.comp hParameters
  have hAtOne : Real.fourierChar (1 : ℝ) = (1 : Circle) := by
    rw [Real.fourierChar_apply', mul_one, Circle.exp_two_pi]
  rw [hAtOne] at hFourier
  exact hFourier

/-- Helper for Example 18.6: points approaching the cut are outside the initial-quarter image. -/
lemma fourierChar_cutApproach_not_mem_initialQuarterImage (n : ℕ) :
    Real.fourierChar (1 - (((n + 2 : ℕ) : ℝ)⁻¹)) ∉
      halfOpenUnitIntervalToCircle '' initialQuarterInterval := by
  -- The approaching parameter lies in `[1 / 2, 1)`, so injectivity excludes a quarter parameter.
  intro hMem
  obtain ⟨t, htQuarter, htImage⟩ := hMem
  have hNatTwo : (2 : ℝ) ≤ (n + 2 : ℕ) := by norm_num
  have hNatPos : (0 : ℝ) < (n + 2 : ℕ) := by positivity
  have hInvPos : 0 < (((n + 2 : ℕ) : ℝ)⁻¹) := inv_pos.mpr hNatPos
  have hInvLeHalf : (((n + 2 : ℕ) : ℝ)⁻¹) ≤ (2 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) hNatTwo
  have hApproachMem : 1 - (((n + 2 : ℕ) : ℝ)⁻¹) ∈ Set.Ico (0 : ℝ) 1 := by
    constructor
    · norm_num at hInvLeHalf ⊢
      linarith
    · linarith
  have hEqual : (t : ℝ) = 1 - (((n + 2 : ℕ) : ℝ)⁻¹) := by
    apply fourierChar_bijOn_unitIco.2.1 t.property hApproachMem
    simpa only [halfOpenUnitIntervalToCircle] using htImage
  have htUpper : (t : ℝ) < 1 / 4 := htQuarter
  rw [hEqual] at htUpper
  have hApproachLower : (1 / 2 : ℝ) ≤ 1 - (((n + 2 : ℕ) : ℝ)⁻¹) := by
    norm_num at hInvLeHalf ⊢
    linarith
  norm_num at htUpper hApproachLower
  linarith

/-- Companion for Example 18.6: the image of the initial quarter interval is not open in the unit
circle. -/
theorem halfOpenUnitIntervalToCircle_image_initialQuarter_not_isOpen :
    ¬ IsOpen (halfOpenUnitIntervalToCircle '' initialQuarterInterval) := by
  -- Openness at the cut point would eventually contain the approaching sequence.
  intro hOpen
  have hZeroMem : (⟨0, by norm_num⟩ : Set.Ico (0 : ℝ) 1) ∈ initialQuarterInterval := by
    norm_num [initialQuarterInterval]
  have hOneMem : (1 : Circle) ∈ halfOpenUnitIntervalToCircle '' initialQuarterInterval := by
    refine ⟨⟨0, by norm_num⟩, hZeroMem, ?_⟩
    rw [halfOpenUnitIntervalToCircle, Real.fourierChar_apply', mul_zero, Circle.exp_zero]
  have hEventually :=
    fourierChar_cutApproach_tendsto.eventually (hOpen.eventually_mem hOneMem)
  have hEventuallyFalse : ∀ᶠ n : ℕ in Filter.atTop, False := by
    filter_upwards [hEventually] with n hn
    exact fourierChar_cutApproach_not_mem_initialQuarterImage n hn
  have hAtTopBot : (Filter.atTop : Filter ℕ) = ⊥ :=
    Filter.eventually_false_iff_eq_bot.mp hEventuallyFalse
  exact Filter.atTop_neBot.ne hAtTopBot
