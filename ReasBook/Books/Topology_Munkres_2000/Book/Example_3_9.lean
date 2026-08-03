module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Interval.Set.Defs

public section

open Set

/-- The rational map from `Set.Ioo (-1 : ℝ) 1` to `ℝ` used in Example 3.9. -/
@[expose]
noncomputable def openUnitIntervalToReal (x : Set.Ioo (-1 : ℝ) 1) : ℝ :=
  x / (1 - x ^ 2)

/-- The real-valued inverse formula for `openUnitIntervalToReal`. -/
@[expose]
noncomputable def realToOpenUnitIntervalValue (y : ℝ) : ℝ :=
  2 * y / (1 + Real.sqrt (1 + 4 * y ^ 2))

/-- Helper for Example 3.9: the denominator of `openUnitIntervalToReal` is positive. -/
lemma openUnitIntervalToReal_denominator_pos (x : Set.Ioo (-1 : ℝ) 1) :
    0 < 1 - (x : ℝ) ^ 2 := by
  -- Factor the denominator using the two endpoint inequalities.
  have hLeft : 0 < 1 + (x : ℝ) := by
    linarith [x.property.1]
  have hFactors : 0 < (1 - (x : ℝ)) * (1 + (x : ℝ)) :=
    mul_pos (sub_pos.mpr x.property.2) hLeft
  nlinarith

/-- The inverse formula lies in the open unit interval. -/
theorem realToOpenUnitIntervalValue_mem (y : ℝ) :
    realToOpenUnitIntervalValue y ∈ Set.Ioo (-1 : ℝ) 1 := by
  -- Compare both signed numerators with the defining square root.
  have hDenominator : 0 < 1 + Real.sqrt (1 + 4 * y ^ 2) := by
    nlinarith [Real.sqrt_nonneg (1 + 4 * y ^ 2)]
  have hUpperRadical : 2 * y < Real.sqrt (1 + 4 * y ^ 2) := by
    apply Real.lt_sqrt_of_sq_lt
    nlinarith
  have hLowerRadical : -2 * y < Real.sqrt (1 + 4 * y ^ 2) := by
    apply Real.lt_sqrt_of_sq_lt
    nlinarith
  unfold realToOpenUnitIntervalValue
  constructor
  · rw [lt_div_iff₀ hDenominator]
    nlinarith
  · rw [div_lt_iff₀ hDenominator]
    nlinarith

/-- The subtype-valued inverse of `openUnitIntervalToReal`. -/
@[expose]
noncomputable def realToOpenUnitInterval (y : ℝ) : Set.Ioo (-1 : ℝ) 1 :=
  ⟨realToOpenUnitIntervalValue y, realToOpenUnitIntervalValue_mem y⟩

/-- Helper for Example 3.9: the radical after applying the forward map has a rational form. -/
lemma openUnitIntervalToReal_sqrt_identity (x : Set.Ioo (-1 : ℝ) 1) :
    Real.sqrt (1 + 4 * openUnitIntervalToReal x ^ 2) =
      (1 + (x : ℝ) ^ 2) / (1 - (x : ℝ) ^ 2) := by
  -- Identify the nonnegative square root by comparing squares.
  have hDenominator := openUnitIntervalToReal_denominator_pos x
  have hRadicand : 0 ≤ 1 + 4 * openUnitIntervalToReal x ^ 2 := by positivity
  have hValue : 0 ≤ (1 + (x : ℝ) ^ 2) / (1 - (x : ℝ) ^ 2) := by positivity
  apply (Real.sqrt_eq_iff_eq_sq hRadicand hValue).2
  unfold openUnitIntervalToReal
  field_simp [hDenominator.ne']
  ring

/-- The inverse formula is a left inverse of `openUnitIntervalToReal`. -/
theorem realToOpenUnitInterval_leftInverse :
    Function.LeftInverse realToOpenUnitInterval openUnitIntervalToReal := by
  intro x
  -- Rewrite the radical first, then normalize the remaining rational expression.
  apply Subtype.ext
  change realToOpenUnitIntervalValue (openUnitIntervalToReal x) = (x : ℝ)
  unfold realToOpenUnitIntervalValue
  rw [openUnitIntervalToReal_sqrt_identity]
  have hDenominator := openUnitIntervalToReal_denominator_pos x
  unfold openUnitIntervalToReal
  field_simp [hDenominator.ne']
  ring

/-- The inverse formula is a right inverse of `openUnitIntervalToReal`. -/
theorem realToOpenUnitInterval_rightInverse :
    Function.RightInverse realToOpenUnitInterval openUnitIntervalToReal := by
  intro y
  -- Use the square-root equation to simplify the inverse value's denominator.
  have hRadicand : 0 ≤ 1 + 4 * y ^ 2 := by positivity
  have hSquare : Real.sqrt (1 + 4 * y ^ 2) ^ 2 = 1 + 4 * y ^ 2 :=
    Real.sq_sqrt hRadicand
  have hDenominator : 0 < 1 + Real.sqrt (1 + 4 * y ^ 2) := by
    nlinarith [Real.sqrt_nonneg (1 + 4 * y ^ 2)]
  have hOneSubSquare :
      1 - (2 * y / (1 + Real.sqrt (1 + 4 * y ^ 2))) ^ 2 =
        2 / (1 + Real.sqrt (1 + 4 * y ^ 2)) := by
    field_simp [hDenominator.ne']
    ring_nf at hSquare ⊢
    nlinarith
  unfold openUnitIntervalToReal realToOpenUnitInterval realToOpenUnitIntervalValue
  rw [hOneSubSquare]
  field_simp [hDenominator.ne']

/-- The map `x ↦ x / (1 - x ^ 2)` is strictly order-preserving on
`Set.Ioo (-1 : ℝ) 1`. -/
theorem openUnitIntervalToReal_strictMono : StrictMono openUnitIntervalToReal := by
  intro x y hxy
  -- Cross-multiply through positive denominators and factor the difference.
  have hDenominatorX := openUnitIntervalToReal_denominator_pos x
  have hDenominatorY := openUnitIntervalToReal_denominator_pos y
  have hLeftX : 0 < 1 + (x : ℝ) := by
    linarith [x.property.1]
  have hLeftY : 0 < 1 + (y : ℝ) := by
    linarith [y.property.1]
  have hPositiveSum : 0 < (1 + (x : ℝ)) * (1 + (y : ℝ)) :=
    mul_pos hLeftX hLeftY
  have hPositiveDifference : 0 < (1 - (x : ℝ)) * (1 - (y : ℝ)) :=
    mul_pos (sub_pos.mpr x.property.2) (sub_pos.mpr y.property.2)
  have hProduct : 0 < 1 + (x : ℝ) * (y : ℝ) := by
    nlinarith
  have hFactored : 0 < ((y : ℝ) - (x : ℝ)) * (1 + (x : ℝ) * (y : ℝ)) :=
    mul_pos (sub_pos.mpr hxy) hProduct
  unfold openUnitIntervalToReal
  rw [div_lt_div_iff₀ hDenominatorX hDenominatorY]
  nlinarith

/-- The map `x ↦ x / (1 - x ^ 2)` is a bijection from
`Set.Ioo (-1 : ℝ) 1` to `ℝ`. -/
theorem openUnitIntervalToReal_bijective : Function.Bijective openUnitIntervalToReal :=
  ⟨openUnitIntervalToReal_strictMono.injective,
    realToOpenUnitInterval_rightInverse.surjective⟩

/-- Example 3.9: The order isomorphism from `Set.Ioo (-1 : ℝ) 1` to `ℝ` with forward map
`x ↦ x / (1 - x ^ 2)` and inverse `y ↦ 2 * y / (1 + Real.sqrt (1 + 4 * y ^ 2))`. -/
@[expose]
noncomputable def openUnitIntervalOrderIso : Set.Ioo (-1 : ℝ) 1 ≃o ℝ where
  toEquiv :=
    { toFun := openUnitIntervalToReal
      invFun := realToOpenUnitInterval
      left_inv := realToOpenUnitInterval_leftInverse
      right_inv := realToOpenUnitInterval_rightInverse }
  map_rel_iff' := openUnitIntervalToReal_strictMono.le_iff_le

/-- The forward map of `openUnitIntervalOrderIso` is `x ↦ x / (1 - x ^ 2)`. -/
@[simp]
theorem openUnitIntervalOrderIso_apply (x : Set.Ioo (-1 : ℝ) 1) :
    openUnitIntervalOrderIso x = x / (1 - x ^ 2) := rfl

/-- The inverse of `openUnitIntervalOrderIso` is the explicit inverse formula. -/
@[simp]
theorem openUnitIntervalOrderIso_symm_apply (y : ℝ) :
    ((openUnitIntervalOrderIso.symm y : Set.Ioo (-1 : ℝ) 1) : ℝ) =
      2 * y / (1 + Real.sqrt (1 + 4 * y ^ 2)) := rfl
