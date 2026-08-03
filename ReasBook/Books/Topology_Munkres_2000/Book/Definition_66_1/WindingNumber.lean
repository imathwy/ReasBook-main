module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Homotopy.Lifting

noncomputable section

public section

open Set unitInterval

namespace PlaneLoop

/-- The quotient `(z - a) / ‖z - a‖` has norm one when `z ≠ a`. -/
theorem direction_mem (z a : ℂ) (h : z ≠ a) :
    (z - a) / ‖z - a‖ ∈ Metric.sphere (0 : ℂ) 1 := by
  -- Normalize the quotient by the nonzero norm of `z - a`.
  rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), div_self]
  exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)

/-- The direction from `a` to `z`, regarded as a point of the unit circle. -/
def direction (z a : ℂ) (h : z ≠ a) : Circle :=
  ⟨(z - a) / ‖z - a‖, direction_mem z a h⟩

/-- Coercing `direction z a h` to `ℂ` gives the normalized difference quotient. -/
theorem direction_coe (z a : ℂ) (h : z ≠ a) :
    (direction z a h : ℂ) = (z - a) / ‖z - a‖ := by
  -- The coercion exposes the quotient stored in the subtype.
  rfl

/-- A loop avoiding `a` never takes the value `a`. -/
theorem ne_of_not_mem_range {x : ℂ} (f : Path x x) (a : ℂ)
    (h_avoid : a ∉ Set.range f) (t : unitInterval) : f t ≠ a := by
  -- Equality at `t` would exhibit `a` as a value of the loop.
  intro hfa
  apply h_avoid
  exact ⟨t, hfa⟩

/-- The basepoint of a loop avoiding `a` differs from `a`. -/
theorem base_ne {x : ℂ} (f : Path x x) (a : ℂ)
    (h_avoid : a ∉ Set.range f) : x ≠ a := by
  -- Specialize pointwise avoidance at the source endpoint.
  simpa only [f.source] using ne_of_not_mem_range f a h_avoid 0

/-- The pointwise direction of a loop avoiding `a` varies continuously. -/
theorem continuous_direction {x : ℂ} (f : Path x x) (a : ℂ)
    (h_avoid : a ∉ Set.range f) :
    Continuous fun t ↦ direction (f t) a (ne_of_not_mem_range f a h_avoid t) := by
  -- Prove continuity on the complex carrier, then lift it to `Circle`.
  apply Continuous.subtype_mk
  apply Continuous.div₀
  · exact f.continuous.sub continuous_const
  · exact Complex.continuous_ofReal.comp (f.continuous.sub continuous_const).norm
  · intro t
    exact Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (ne_of_not_mem_range f a h_avoid t)))

/-- The normalized direction at the initial endpoint is the basepoint direction. -/
theorem direction_zero {x : ℂ} (f : Path x x) (a : ℂ)
    (h_avoid : a ∉ Set.range f) :
    direction (f 0) a (ne_of_not_mem_range f a h_avoid 0) =
      direction x a (base_ne f a h_avoid) := by
  -- Both circle points have the same complex value at the source endpoint.
  apply Subtype.ext
  simp only [direction_coe, f.source]

/-- The normalized direction at the terminal endpoint is the basepoint direction. -/
theorem direction_one {x : ℂ} (f : Path x x) (a : ℂ)
    (h_avoid : a ∉ Set.range f) :
    direction (f 1) a (ne_of_not_mem_range f a h_avoid 1) =
      direction x a (base_ne f a h_avoid) := by
  -- Both circle points have the same complex value at the terminal endpoint.
  apply Subtype.ext
  simp only [direction_coe, f.target]

/-- The normalized circle-valued loop determined by a plane loop avoiding `a`. -/
def normalizedLoop {x : ℂ} (f : Path x x) (a : ℂ)
    (h_avoid : a ∉ Set.range f) :
    Path (direction x a (base_ne f a h_avoid))
      (direction x a (base_ne f a h_avoid)) where
  toFun t := direction (f t) a (ne_of_not_mem_range f a h_avoid t)
  continuous_toFun := continuous_direction f a h_avoid
  source' := direction_zero f a h_avoid
  target' := direction_one f a h_avoid

/-- Evaluating `normalizedLoop` gives the pointwise normalized direction. -/
theorem normalizedLoop_apply {x : ℂ} (f : Path x x) (a : ℂ)
    (h_avoid : a ∉ Set.range f) (t : unitInterval) :
    normalizedLoop f a h_avoid t =
      direction (f t) a (ne_of_not_mem_range f a h_avoid t) := by
  -- Evaluation reduces to the function field of `normalizedLoop`.
  rfl

/-- The normalized loop transported to the period-one additive circle. -/
def angularLoop {x : ℂ} (f : Path x x) (a : ℂ)
    (h_avoid : a ∉ Set.range f) :
    Path ((AddCircle.homeomorphCircle one_ne_zero).symm
        (direction x a (base_ne f a h_avoid)))
      ((AddCircle.homeomorphCircle one_ne_zero).symm
        (direction x a (base_ne f a h_avoid))) :=
  (normalizedLoop f a h_avoid).map
    (AddCircle.homeomorphCircle one_ne_zero).symm.continuous

/-- Helper for Definition 66.1: transporting the angular loop back to `Circle` recovers the
normalized loop pointwise. -/
theorem homeomorphCircle_angularLoop_apply {x : ℂ} (f : Path x x) (a : ℂ)
    (h_avoid : a ∉ Set.range f) (t : unitInterval) :
    AddCircle.homeomorphCircle one_ne_zero (angularLoop f a h_avoid t) =
      normalizedLoop f a h_avoid t := by
  -- Cancel the inverse homeomorphism used to define the angular loop.
  simp [angularLoop]

/-- The standard unit-period covering map `ℝ → Circle`. -/
@[expose]
def standardCircleCovering : C(ℝ, Circle) :=
  ⟨fun t ↦ AddCircle.homeomorphCircle one_ne_zero (t : UnitAddCircle),
    (AddCircle.homeomorphCircle one_ne_zero).continuous.comp
      (AddCircle.continuous_mk' 1)⟩

/-- The standard unit-period covering is induced by the quotient `ℝ → UnitAddCircle`. -/
theorem standardCircleCovering_apply (t : ℝ) :
    standardCircleCovering t =
      AddCircle.homeomorphCircle one_ne_zero (t : UnitAddCircle) := rfl

/-- The chosen representative of the initial angular value projects to that value. -/
theorem angularLoop_zero_eq_rep {x : ℂ} (f : Path x x) (a : ℂ)
    (h_avoid : a ∉ Set.range f) :
    angularLoop f a h_avoid 0 =
      ((AddCircle.equivIco (1 : ℝ) 0 (angularLoop f a h_avoid 0) :
        Set.Ico (0 : ℝ) (0 + 1)) : ℝ) := by
  -- The chosen half-open-interval representative projects to the original point.
  exact AddCircle.coe_equivIco.symm

/-- The canonical real-valued lift of the angular loop through `ℝ → UnitAddCircle`. -/
def angularLift {x : ℂ} (f : Path x x) (a : ℂ)
    (h_avoid : a ∉ Set.range f) : C(unitInterval, ℝ) :=
  (AddCircle.isCoveringMap_coe (1 : ℝ)).liftPath (angularLoop f a h_avoid)
    (AddCircle.equivIco (1 : ℝ) 0 (angularLoop f a h_avoid 0) : ℝ)
    (angularLoop_zero_eq_rep f a h_avoid)

/-- The canonical angular lift projects to the transported additive-circle loop. -/
theorem angularLift_lifts_angularLoop {x : ℂ} (f : Path x x) (a : ℂ)
    (h_avoid : a ∉ Set.range f) (t : unitInterval) :
    (angularLift f a h_avoid t : UnitAddCircle) = angularLoop f a h_avoid t := by
  -- Evaluate the canonical path-lifting specification at `t`.
  exact congrFun ((AddCircle.isCoveringMap_coe (1 : ℝ)).liftPath_lifts
    (angularLoop f a h_avoid)
    (AddCircle.equivIco (1 : ℝ) 0 (angularLoop f a h_avoid 0) : ℝ)
    (angularLoop_zero_eq_rep f a h_avoid)) t

/-- The canonical angular lift projects through the standard covering to the normalized loop. -/
theorem angularLift_lifts {x : ℂ} (f : Path x x) (a : ℂ)
    (h_avoid : a ∉ Set.range f) (t : unitInterval) :
    standardCircleCovering (angularLift f a h_avoid t) = normalizedLoop f a h_avoid t := by
  change AddCircle.homeomorphCircle one_ne_zero
      (angularLift f a h_avoid t : UnitAddCircle) = _
  rw [angularLift_lifts_angularLoop]
  simp [angularLoop]

/-- The canonical angular lift starts at the half-open-interval representative. -/
theorem angularLift_zero {x : ℂ} (f : Path x x) (a : ℂ)
    (h_avoid : a ∉ Set.range f) :
    angularLift f a h_avoid 0 =
      (AddCircle.equivIco (1 : ℝ) 0 (angularLoop f a h_avoid 0) : ℝ) := by
  -- Use the initial-value computation rule for the chosen lift.
  exact (AddCircle.isCoveringMap_coe (1 : ℝ)).liftPath_zero
    (angularLoop f a h_avoid)
    (AddCircle.equivIco (1 : ℝ) 0 (angularLoop f a h_avoid 0) : ℝ)
    (angularLoop_zero_eq_rep f a h_avoid)

/-- The winding number of a plane loop about an omitted point. -/
def windingNumber {x : ℂ} (f : Path x x) (a : ℂ)
    (h_avoid : a ∉ Set.range f) : ℤ :=
  ⌊angularLift f a h_avoid 1 - angularLift f a h_avoid 0⌋

/-- Helper for Definition 66.1: the pointwise difference of two real lifts of the same
`UnitAddCircle`-valued map has constant projection. -/
private theorem liftDifference_projection_eq (γ : C(unitInterval, UnitAddCircle))
    (Γ Δ : C(unitInterval, ℝ))
    (hΓ : ∀ t, (Γ t : UnitAddCircle) = γ t)
    (hΔ : ∀ t, (Δ t : UnitAddCircle) = γ t) (s t : unitInterval) :
    ((Γ s - Δ s : ℝ) : UnitAddCircle) = ((Γ t - Δ t : ℝ) : UnitAddCircle) := by
  -- Project each real difference and cancel the common image in the additive circle.
  calc
    ((Γ s - Δ s : ℝ) : UnitAddCircle) =
        (Γ s : UnitAddCircle) - (Δ s : UnitAddCircle) :=
      AddCircle.coe_sub (1 : ℝ) _ _
    _ = γ s - γ s := congrArg₂ (· - ·) (hΓ s) (hΔ s)
    _ = 0 := sub_self _
    _ = γ t - γ t := (sub_self _).symm
    _ = (Γ t : UnitAddCircle) - (Δ t : UnitAddCircle) :=
      congrArg₂ (· - ·) (hΓ t).symm (hΔ t).symm
    _ = ((Γ t - Δ t : ℝ) : UnitAddCircle) :=
      (AddCircle.coe_sub (1 : ℝ) _ _).symm

/-- Helper for Definition 66.1: continuous real lifts of the same `UnitAddCircle`-valued path
have equal endpoint displacement. -/
private theorem liftEndpointDisplacement_eq (γ : C(unitInterval, UnitAddCircle))
    (Γ Δ : C(unitInterval, ℝ))
    (hΓ : ∀ t, (Γ t : UnitAddCircle) = γ t)
    (hΔ : ∀ t, (Δ t : UnitAddCircle) = γ t) :
    Γ 1 - Γ 0 = Δ 1 - Δ 0 := by
  -- The difference of two lifts projects to zero, so it is constant on the interval.
  have hconstant : Γ 1 - Δ 1 = Γ 0 - Δ 0 :=
    (AddCircle.isCoveringMap_coe (1 : ℝ)).const_of_comp
      (Γ.continuous.sub Δ.continuous)
      (liftDifference_projection_eq γ Γ Δ hΓ hΔ) 1 0
  -- Rearrange the constant-difference identity into equality of displacements.
  linarith

/-- Every lift of the transported additive-circle loop has endpoint displacement equal to the
winding number. -/
theorem windingNumber_spec_angularLoop {x : ℂ} (f : Path x x) (a : ℂ)
    (h_avoid : a ∉ Set.range f) (Γ : C(unitInterval, ℝ))
    (hΓ : ∀ t, (Γ t : UnitAddCircle) = angularLoop f a h_avoid t) :
    Γ 1 - Γ 0 = (windingNumber f a h_avoid : ℝ) := by
  -- The canonical lift has a deck displacement because its projected endpoints agree.
  have hcoe :
      ((angularLift f a h_avoid 1 - angularLift f a h_avoid 0 : ℝ) : UnitAddCircle) = 0 := by
    simp only [AddCircle.coe_sub, angularLift_lifts_angularLoop,
      (angularLoop f a h_avoid).target, (angularLoop f a h_avoid).source, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hcoe
  have hdisplacement :
      angularLift f a h_avoid 1 - angularLift f a h_avoid 0 = (n : ℝ) := by
    simpa using hn.symm
  -- Compare lifts, then identify the floor of the integral canonical displacement.
  calc
    Γ 1 - Γ 0 = angularLift f a h_avoid 1 - angularLift f a h_avoid 0 :=
      liftEndpointDisplacement_eq (angularLoop f a h_avoid) Γ
        (angularLift f a h_avoid) hΓ (angularLift_lifts_angularLoop f a h_avoid)
    _ = (n : ℝ) := hdisplacement
    _ = (windingNumber f a h_avoid : ℝ) := by
      simp only [windingNumber, hdisplacement, Int.floor_intCast]


end PlaneLoop
