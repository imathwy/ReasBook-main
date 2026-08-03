module

public import Topology_Munkres_2000.Book.Corollary_24_2

public section

open Set

/-- Exercise 24.3 (1): every continuous self-map of the closed unit interval has a
fixed point. -/
theorem existsFixedPointClosedUnitInterval
    (f : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1) (hf : Continuous f) :
    ∃ x, Function.IsFixedPt f x := by
  -- Compare the identity map with the underlying real-valued map of `f`.
  have hZeroMem : (0 : ℝ) ∈ Icc 0 1 := by
    norm_num
  have hOneMem : (1 : ℝ) ∈ Icc 0 1 := by
    norm_num
  let leftEndpoint : Icc (0 : ℝ) 1 := ⟨0, hZeroMem⟩
  let rightEndpoint : Icc (0 : ℝ) 1 := ⟨1, hOneMem⟩
  have hDomain : PreconnectedSpace (Icc (0 : ℝ) 1) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  have hContinuousValue : Continuous (fun x ↦ (f x : ℝ)) :=
    continuous_subtype_val.comp hf
  have hLeft : (leftEndpoint : ℝ) ≤ (f leftEndpoint : ℝ) := by
    exact (f leftEndpoint).property.1
  have hRight : (f rightEndpoint : ℝ) ≤ (rightEndpoint : ℝ) := by
    exact (f rightEndpoint).property.2
  -- The intermediate value theorem gives a point where these two maps agree.
  obtain ⟨x, hx⟩ :=
    @intermediate_value_univ₂ (Icc (0 : ℝ) 1) ℝ _ _ _ _ hDomain
      leftEndpoint rightEndpoint (fun x ↦ (x : ℝ)) (fun x ↦ (f x : ℝ))
      continuous_subtype_val hContinuousValue hLeft hRight
  refine ⟨x, ?_⟩
  -- Equality of underlying real values is equality in the interval subtype.
  exact Subtype.ext hx.symm

namespace UnitIntervalFixedPoint

/-- The affine value `x ↦ (x + 1) / 2` used for the nonclosed interval examples. -/
@[expose]
noncomputable def shiftValue (x : ℝ) : ℝ :=
  (x + 1) / 2

/-- The affine value of a point of `Ico (0 : ℝ) 1` remains in that interval. -/
theorem shiftValue_mem_Ico (x : Ico (0 : ℝ) 1) :
    shiftValue x ∈ Ico (0 : ℝ) 1 := by
  -- The affine average stays nonnegative and remains strictly below `1`.
  constructor
  · unfold shiftValue
    linarith [x.property.1]
  · unfold shiftValue
    linarith [x.property.2]

/-- The affine fixed-point-free self-map of the half-open unit interval. -/
@[expose]
noncomputable def halfOpenShift (x : Ico (0 : ℝ) 1) : Ico (0 : ℝ) 1 :=
  ⟨shiftValue x, shiftValue_mem_Ico x⟩

/-- The underlying real value of `halfOpenShift x`. -/
@[simp]
theorem coe_halfOpenShift (x : Ico (0 : ℝ) 1) : (halfOpenShift x : ℝ) = shiftValue x := rfl

/-- Helper for Exercise 24.3: the ambient affine map `shiftValue` is continuous. -/
lemma continuous_shiftValue : Continuous shiftValue := by
  -- Continuity follows from continuity of addition and division by a constant.
  unfold shiftValue
  fun_prop

/-- The map `halfOpenShift` is continuous. -/
theorem continuous_halfOpenShift : Continuous halfOpenShift := by
  -- Restrict the continuous ambient affine map to the half-open interval.
  exact (continuous_shiftValue.comp continuous_subtype_val).subtype_mk shiftValue_mem_Ico

/-- Helper for Exercise 24.3: `shiftValue x` differs from `x` whenever `x < 1`. -/
lemma shiftValue_ne_self_of_lt_one {x : ℝ} (hx : x < 1) : shiftValue x ≠ x := by
  -- An affine fixed point would force `x = 1`.
  unfold shiftValue
  linarith

/-- The map `halfOpenShift` has no fixed point. -/
theorem halfOpenShift_hasNoFixedPoint :
    ¬ ∃ x, Function.IsFixedPt halfOpenShift x := by
  -- A subtype fixed point would give an impossible ambient fixed point.
  rintro ⟨x, hx⟩
  have hValue : shiftValue x = x := by
    simpa only [coe_halfOpenShift] using congrArg Subtype.val hx
  exact shiftValue_ne_self_of_lt_one x.property.2 hValue

/-- The affine value of a point of `Ioo (0 : ℝ) 1` remains in that interval. -/
theorem shiftValue_mem_Ioo (x : Ioo (0 : ℝ) 1) :
    shiftValue x ∈ Ioo (0 : ℝ) 1 := by
  -- The affine average is strictly between `0` and `1`.
  constructor
  · unfold shiftValue
    linarith [x.property.1]
  · unfold shiftValue
    linarith [x.property.2]

/-- The affine fixed-point-free self-map of the open unit interval. -/
@[expose]
noncomputable def openShift (x : Ioo (0 : ℝ) 1) : Ioo (0 : ℝ) 1 :=
  ⟨shiftValue x, shiftValue_mem_Ioo x⟩

/-- The underlying real value of `openShift x`. -/
@[simp]
theorem coe_openShift (x : Ioo (0 : ℝ) 1) : (openShift x : ℝ) = shiftValue x := rfl

/-- The map `openShift` is continuous. -/
theorem continuous_openShift : Continuous openShift := by
  -- Restrict the same ambient map to the open interval.
  exact (continuous_shiftValue.comp continuous_subtype_val).subtype_mk shiftValue_mem_Ioo

/-- The map `openShift` has no fixed point. -/
theorem openShift_hasNoFixedPoint :
    ¬ ∃ x, Function.IsFixedPt openShift x := by
  -- Again, pass any alleged subtype fixed point to the underlying real values.
  rintro ⟨x, hx⟩
  have hValue : shiftValue x = x := by
    simpa only [coe_openShift] using congrArg Subtype.val hx
  exact shiftValue_ne_self_of_lt_one x.property.2 hValue

end UnitIntervalFixedPoint

/-- Exercise 24.3 (2): the half-open unit interval admits a continuous self-map
without a fixed point. -/
theorem halfOpenIntervalCounterexample :
    ∃ f : Ico (0 : ℝ) 1 → Ico (0 : ℝ) 1,
      Continuous f ∧ ¬ ∃ x, Function.IsFixedPt f x :=
  ⟨UnitIntervalFixedPoint.halfOpenShift,
    UnitIntervalFixedPoint.continuous_halfOpenShift,
    UnitIntervalFixedPoint.halfOpenShift_hasNoFixedPoint⟩

/-- Exercise 24.3 (3): the open unit interval admits a continuous self-map without
a fixed point. -/
theorem openIntervalCounterexample :
    ∃ f : Ioo (0 : ℝ) 1 → Ioo (0 : ℝ) 1,
      Continuous f ∧ ¬ ∃ x, Function.IsFixedPt f x :=
  ⟨UnitIntervalFixedPoint.openShift,
    UnitIntervalFixedPoint.continuous_openShift,
    UnitIntervalFixedPoint.openShift_hasNoFixedPoint⟩
