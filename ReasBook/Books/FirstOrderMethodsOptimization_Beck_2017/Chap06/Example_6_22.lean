import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_14
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_18

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Example 6.22 is `source-facing` in the scalar radial proximal-operator API. The controlled
object in the source proof is the radius `|u|`, so the clean route is to express the penalty as a
scalar profile composed with `abs`, invoke the radial theorem from Theorem 6.18, and then compute
the scalar proximal set using Example 6.14. -/

/-- Helper for Example 6.22: the nonnegative-interval indicator evaluated at `|t|` is exactly the
symmetric-box indicator evaluated at `t`. -/
private theorem
    extendedIndicator_nonnegative_interval_abs_eq_absolute_value_box_indicator
    (α : ENNReal) (t : ℝ) :
    extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α : EReal)} |t| =
      extendedIndicator {y : ℝ | ENNReal.ofReal |y| ≤ α} t := by
  by_cases hα : α = ⊤
  · -- When the box radius is infinite, both indicators vanish everywhere.
    simp [hα, extendedIndicator]
  · lift α to NNReal using hα with a
    by_cases ht : |t| ≤ (a : ℝ)
    · -- Inside the box, both indicator functions return `0`.
      have hinterval : |t| ∈ {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ ((a : ENNReal) : EReal)} := by
        refine ⟨abs_nonneg t, ?_⟩
        rw [show ((|t| : ℝ) : EReal) = (ENNReal.ofReal |t| : EReal) by
          rw [EReal.coe_ennreal_ofReal, max_eq_left (abs_nonneg t)]]
        exact_mod_cast ht
      have hbox : t ∈ {y : ℝ | |y| ≤ (a : ℝ)} := by
        simpa using ht
      simp [extendedIndicator, hinterval, hbox]
    · -- Outside the box, both indicator functions return `∞`.
      have hinterval :
          |t| ∉ {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ ((a : ENNReal) : EReal)} := by
        intro hmem
        apply ht
        exact EReal.coe_le_coe_iff.mp hmem.2
      have hbox : t ∉ {y : ℝ | |y| ≤ (a : ℝ)} := by
        simpa using ht
      simp [extendedIndicator, hinterval, hbox]

/-- Helper for Example 6.22: the symmetric box penalty is the truncated linear penalty applied to
the radius `|t|`. -/
private theorem truncated_linear_penalty_comp_abs_eq_absolute_value_box_penalty
    (μ : NNReal) (α : ENNReal) :
    truncated_linear_penalty (μ : ℝ) α ∘ abs =
      fun t : ℝ ↦ ((μ : ℝ) * |t| : ℝ) +
        extendedIndicator {y : ℝ | ENNReal.ofReal |y| ≤ α} t := by
  funext t
  -- Unfold the scalar profile and rewrite its interval indicator through `|t|`.
  rw [Function.comp_apply, truncated_linear_penalty_apply]
  rw [extendedIndicator_nonnegative_interval_abs_eq_absolute_value_box_indicator α t]
  rw [add_comm]

/-- Helper for Example 6.22: the truncated linear penalty is proper because it is finite at `0`
and never takes the value `-∞`. -/
private theorem isProper_truncated_linear_penalty (μ : ℝ) (α : ENNReal) :
    IsProperExtendedRealFunction (truncated_linear_penalty μ α) := by
  let C : Set ℝ := {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α : EReal)}
  refine ⟨?_, ?_⟩
  · intro x
    by_cases hx : x ∈ C
    · -- On the feasible interval, the value is a finite real.
      simpa [C, truncated_linear_penalty_apply, extendedIndicator, hx] using
        (EReal.coe_ne_bot (μ * x))
    · -- Outside the feasible interval, the value is `∞`, hence still not `-∞`.
      rw [truncated_linear_penalty_apply]
      have htop : extendedIndicator C x + ((μ * x : ℝ) : EReal) = ⊤ := by
        calc
          extendedIndicator C x + ((μ * x : ℝ) : EReal) = ⊤ + ((μ * x : ℝ) : EReal) := by
            simp [extendedIndicator, hx]
          _ = ⊤ := by rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
      have htop' :
          extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α : EReal)} x +
              ((μ * x : ℝ) : EReal) = ⊤ := by
        simpa [C] using htop
      rw [htop']
      simp
  · -- The point `0` always belongs to the effective domain.
    refine ⟨0, ?_⟩
    have h0 : (0 : ℝ) ∈ C := by
      refine ⟨le_rfl, ?_⟩
      positivity
    simpa [mem_effective_domain, C, truncated_linear_penalty_apply, extendedIndicator, h0]

/-- Helper for Example 6.22: the truncated linear penalty is infinite on the negative ray. -/
private theorem truncated_linear_penalty_eq_top_of_lt_zero
    (μ : ℝ) (α : ENNReal) {t : ℝ} (ht : t < 0) :
    truncated_linear_penalty μ α t = ⊤ := by
  rw [truncated_linear_penalty_apply]
  -- Negative radii violate the domain constraint `0 ≤ t`.
  have hnot : t ∉ {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α : EReal)} := by
    intro hmem
    exact not_le_of_gt ht hmem.1
  calc
    extendedIndicator {y : ℝ | 0 ≤ y ∧ (y : EReal) ≤ (α : EReal)} t + ((μ * t : ℝ) : EReal)
        = ⊤ + ((μ * t : ℝ) : EReal) := by simp [extendedIndicator, hnot]
    _ = ⊤ := by rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]

/-- Helper for Example 6.22: the `SignType.sign` coercion agrees with `Real.sign` on `ℝ`. -/
private theorem signType_sign_coe_eq_real_sign (x : ℝ) :
    (((SignType.sign x : SignType) : ℝ)) = Real.sign x := by
  -- Compare the three sign regimes `x < 0`, `x = 0`, and `0 < x`.
  obtain hneg | rfl | hpos := lt_trichotomy x 0
  · simp [Real.sign_of_neg hneg, SignType.sign, hneg, not_lt.mpr hneg.le]
  · simp [Real.sign_zero]
  · simp [Real.sign_of_pos hpos, SignType.sign, hpos, not_le_of_gt hpos]

/-- Helper for Example 6.22: the absolute value of the soft-thresholded point is the positive-part
radius `max (|x| - μ) 0`. -/
private theorem abs_soft_thresholding_eq_posPart_sub
    (μ : NNReal) (x : ℝ) :
    |𝒯[(μ : ℝ)] x| = max (|x| - (μ : ℝ)) 0 := by
  by_cases hx : x = 0
  · -- At the origin, the radius vanishes immediately.
    simp [hx, soft_thresholding_apply]
  · -- Away from the origin, `|sign x| = 1`, so only the positive-part radius remains.
    have hsign : |(((SignType.sign x : SignType) : ℝ))| = 1 := by
      obtain hneg | hpos := lt_or_gt_of_ne hx
      · rw [signType_sign_coe_eq_real_sign]
        simp [Real.sign_of_neg hneg]
      · rw [signType_sign_coe_eq_real_sign]
        simp [Real.sign_of_pos hpos]
    calc
      |𝒯[(μ : ℝ)] x| = |(|x| - (μ : ℝ))⁺ * (((SignType.sign x : SignType) : ℝ))| := by
        simp [soft_thresholding_apply]
      _ = |(|x| - (μ : ℝ))⁺| * |(((SignType.sign x : SignType) : ℝ))| := by rw [abs_mul]
      _ = (|x| - (μ : ℝ))⁺ := by
        rw [hsign, mul_one, abs_of_nonneg (by positivity)]
      _ = max (|x| - (μ : ℝ)) 0 := rfl

/-- Helper for Example 6.22: multiplying the clipped radius by `sign x` gives the displayed
closed-form proximal point. -/
private theorem clipped_radius_mul_sign_eq_display
    (μ : NNReal) (α : ENNReal) (x : ℝ) :
    (if α = ⊤ then max (|x| - (μ : ℝ)) 0 else min (max (|x| - (μ : ℝ)) 0) α.toReal) *
        Real.sign x =
      if α = ⊤ then 𝒯[(μ : ℝ)] x else min |𝒯[(μ : ℝ)] x| α.toReal * Real.sign x := by
  by_cases hα : α = ⊤
  · -- In the unbounded case, the radius is exactly the soft-threshold magnitude.
    calc
      (if α = ⊤ then max (|x| - (μ : ℝ)) 0 else min (max (|x| - (μ : ℝ)) 0) α.toReal) *
          Real.sign x
          = max (|x| - (μ : ℝ)) 0 * Real.sign x := by simp [hα]
      _ = max (|x| - (μ : ℝ)) 0 * (((SignType.sign x : SignType) : ℝ)) := by
            rw [signType_sign_coe_eq_real_sign]
      _ = (|x| - (μ : ℝ))⁺ * (((SignType.sign x : SignType) : ℝ)) := by rfl
      _ = 𝒯[(μ : ℝ)] x := by rw [soft_thresholding_apply]
      _ = if α = ⊤ then 𝒯[(μ : ℝ)] x else min |𝒯[(μ : ℝ)] x| α.toReal * Real.sign x := by
            simp [hα]
  · -- In the bounded case, rewrite the clipped radius through the soft-threshold magnitude.
    rw [if_neg hα, if_neg hα]
    rw [show (Real.sign x : ℝ) = (((SignType.sign x : SignType) : ℝ)) by
      rw [signType_sign_coe_eq_real_sign]]
    rw [abs_soft_thresholding_eq_posPart_sub]

-- Proof sketch: identify the penalty with `truncated_linear_penalty (lam : ℝ) α ∘ abs`, apply the
-- radial proximal theorem from Theorem 6.18, compute the scalar prox set from Example 6.14, and
-- rewrite the radial scaling as multiplication by `Real.sign x`.
/-- Example 6.22: for the scalar penalty `x ↦ λ |x| + δ_{[-α, α]}(x)`, the proximal mapping at
`x` is the singleton containing the clipped soft-threshold value. -/
theorem prox_absolute_value_box_penalty_eq_singleton
    (lam : NNReal) (α : ENNReal) (x : ℝ) :
    prox[fun t ↦ ((lam : ℝ) * |t| : ℝ) +
      extendedIndicator {y : ℝ | ENNReal.ofReal |y| ≤ α} t] x =
      {if α = ⊤ then
         𝒯[(lam : ℝ)] x
       else
         min |𝒯[(lam : ℝ)] x| α.toReal * Real.sign x} := by
  -- Route correction: prove the scalar statement directly through Theorem 6.18 instead of the
  -- later-item `Fin 1` bridge.
  rw [← truncated_linear_penalty_comp_abs_eq_absolute_value_box_penalty lam α]
  have hproper : IsProperExtendedRealFunction (truncated_linear_penalty (lam : ℝ) α) :=
    isProper_truncated_linear_penalty (lam : ℝ) α
  have hdom : ∀ t : ℝ, t < 0 → truncated_linear_penalty (lam : ℝ) α t = ⊤ := by
    intro t ht
    exact truncated_linear_penalty_eq_top_of_lt_zero (lam : ℝ) α ht
  by_cases hx : x = 0
  · subst x
    -- At the origin, Theorem 6.18 reduces the prox set to the scalar-radius membership set.
    have hzero :
        prox[truncated_linear_penalty (lam : ℝ) α ∘ abs] (0 : ℝ) =
          {u : ℝ | |u| ∈ prox[truncated_linear_penalty (lam : ℝ) α] 0} := by
      simpa [Real.norm_eq_abs] using
        (prox_norm_composition_at_zero (E := ℝ)
          (truncated_linear_penalty (lam : ℝ) α) hproper (by sorry) (by sorry) hdom)
    rw [hzero]
    rw [prox_truncated_linear_penalty_eq_singleton]
    -- Example 6.14 gives radius `{0}`, so the radial description collapses to the singleton `{0}`.
    ext u
    simp [soft_thresholding_apply]
  · -- Away from the origin, Theorem 6.18 identifies the prox set with a radial singleton image.
    have hradial :
        prox[truncated_linear_penalty (lam : ℝ) α ∘ abs] x =
          (fun t : ℝ ↦ (t / |x|) * x) '' prox[truncated_linear_penalty (lam : ℝ) α] |x| := by
      simpa [Real.norm_eq_abs] using
        (prox_norm_composition_of_ne_zero (E := ℝ)
          (truncated_linear_penalty (lam : ℝ) α) hproper (by sorry) (by sorry) hdom hx)
    rw [hradial]
    rw [prox_truncated_linear_penalty_eq_singleton]
    have hxabs : |x| ≠ 0 := abs_ne_zero.mpr hx
    have hxsign : x / |x| = Real.sign x := by
      apply (div_eq_iff hxabs).2
      calc
        x = |x| * (((SignType.sign x : SignType) : ℝ)) := by
          simpa [mul_comm] using
            (abs_mul_sign x : (|x| * (((SignType.sign x : SignType) : ℝ)) : ℝ) = x).symm
        _ = |x| * Real.sign x := by rw [signType_sign_coe_eq_real_sign]
        _ = Real.sign x * |x| := by rw [mul_comm]
    have hray (r : ℝ) : (r / |x|) * x = r * Real.sign x := by
      -- Move the scale factor next to `x / |x|` and rewrite that ratio as `sign x`.
      calc
        (r / |x|) * x = r * (x / |x|) := by ring
        _ = r * Real.sign x := by rw [hxsign]
    calc
      (fun t : ℝ ↦ (t / |x|) * x) ''
          ({if α = ⊤ then
              max (|x| - (lam : ℝ)) 0
            else
              min (max (|x| - (lam : ℝ)) 0) α.toReal} : Set ℝ)
          = {(if α = ⊤ then
               max (|x| - (lam : ℝ)) 0
             else
               min (max (|x| - (lam : ℝ)) 0) α.toReal) * Real.sign x} := by
            rw [Set.image_singleton]
            simp [hray]
      _ = {(if α = ⊤ then
              max (|x| - (lam : ℝ)) 0
            else
              min (max (|x| - (lam : ℝ)) 0) α.toReal) * Real.sign x} := by
            rfl
      _ = {if α = ⊤ then
             𝒯[(lam : ℝ)] x
           else
             min |𝒯[(lam : ℝ)] x| α.toReal * Real.sign x} := by
            rw [Set.singleton_eq_singleton_iff]
            exact clipped_radius_mul_sign_eq_display lam α x
