module

public import Topology_Munkres_2000.Book.Exercise_58_9.Degree
public import Topology_Munkres_2000.Book.Exercise_66_1.NormalizedMap
import all Topology_Munkres_2000.Book.Exercise_66_1.LoopQuotient

public section

namespace CircleMap

/-- Helper for Exercise 66.1: a real lift with integral endpoint displacement has the
corresponding deck translation under addition by one. -/
theorem turnExpLift_add_one (h : C(Circle, Circle)) (F : C(ℝ, ℝ)) (d : ℤ)
    (hF_lifts : Circle.turnExp ∘ F =
      h.comp ⟨Circle.turnExp, Circle.isCoveringMap_turnExp.continuous⟩)
    (hF_displacement : F 1 - F 0 = (d : ℝ)) (x : ℝ) :
    F (x + 1) = F x + d := by
  -- Compare the lift shifted in its domain with the lift translated by the deck index.
  let shiftedDomain : ℝ → ℝ := fun z ↦ F (z + 1)
  let shiftedRange : ℝ → ℝ := fun z ↦ F z + d
  have shiftedDomain_continuous : Continuous shiftedDomain := by
    fun_prop
  have shiftedRange_continuous : Continuous shiftedRange := by
    fun_prop
  have shifted_comp : Circle.turnExp ∘ shiftedDomain =
      Circle.turnExp ∘ shiftedRange := by
    funext z
    have at_z_add_one := congrFun hF_lifts (z + 1)
    have at_z := congrFun hF_lifts z
    have turnExp_add_one : Circle.turnExp (z + 1) = Circle.turnExp z := by
      simpa using Circle.turnExp_add_int z (1 : ℤ)
    calc
      Circle.turnExp (shiftedDomain z) = h (Circle.turnExp (z + 1)) := at_z_add_one
      _ = h (Circle.turnExp z) := congrArg h turnExp_add_one
      _ = Circle.turnExp (F z) := at_z.symm
      _ = Circle.turnExp (shiftedRange z) := by
        symm
        exact Circle.turnExp_add_int (F z) d
  have shifted_zero : shiftedDomain 0 = shiftedRange 0 := by
    simp only [shiftedDomain, shiftedRange, zero_add]
    linarith
  have shifted_eq := Circle.isCoveringMap_turnExp.eq_of_comp_eq
    shiftedDomain_continuous shiftedRange_continuous shifted_comp 0 shifted_zero
  exact congrFun shifted_eq x

/-- Helper for Exercise 66.1: the degree of a circle map is the integral endpoint
displacement of any global lift through `Circle.turnExp`. -/
theorem degree_eq_of_turnExpLift (orientation : Circle.FundamentalOrientation)
    (h : C(Circle, Circle)) (F : C(ℝ, ℝ)) (d : ℤ)
    (hF_lifts : Circle.turnExp ∘ F =
      h.comp ⟨Circle.turnExp, Circle.isCoveringMap_turnExp.continuous⟩)
    (hF_displacement : F 1 - F 0 = (d : ℝ)) :
    degree orientation h = d := by
  -- Compare `F` with the linear lift of the integer-power circle map.
  let linearLift : C(ℝ, ℝ) :=
    ContinuousMap.const ℝ (d : ℝ) * ContinuousMap.id ℝ
  have linearLift_lifts : Circle.turnExp ∘ linearLift =
      (zpower d).comp
        ⟨Circle.turnExp, Circle.isCoveringMap_turnExp.continuous⟩ := by
    funext z
    simp only [Function.comp_apply, ContinuousMap.comp_apply, linearLift,
      ContinuousMap.mul_apply, ContinuousMap.const_apply, ContinuousMap.id_apply,
      zpower_apply]
    have turnExpMap_apply :
        (⟨Circle.turnExp, Circle.isCoveringMap_turnExp.continuous⟩ : C(ℝ, Circle)) z =
          Circle.turnExp z := rfl
    rw [turnExpMap_apply]
    have turnExp_apply (u : ℝ) :
        Circle.turnExp u = Circle.exp (2 * Real.pi * u) :=
      congrFun Circle.turnExp_eq_exp_scale u
    rw [turnExp_apply, turnExp_apply]
    rw [← Circle.exp_zsmul]
    congr 1
    ring
  have F_translate : ∀ x : ℝ, F (x + 1) = F x + d :=
    fun x ↦ turnExpLift_add_one h F d hF_lifts hF_displacement x
  have linearLift_translate : ∀ x : ℝ, linearLift (x + 1) = linearLift x + d := by
    intro x
    change (d : ℝ) * (x + 1) = (d : ℝ) * x + d
    ring
  have homotopic := homotopic_of_basedLifts_sameDeckTranslation
    h (zpower d) F linearLift d hF_lifts linearLift_lifts
      F_translate linearLift_translate
  -- Homotopy invariance and the power-map calculation identify the degree.
  calc
    degree orientation h = degree orientation (zpower d) :=
      degree_eq_of_homotopic orientation h (zpower d) homotopic
    _ = d := degree_zpower orientation d

end CircleMap

namespace PlaneLoop

/-- Helper for Exercise 66.1: the canonical angular lift projects to the normalized
circle map after parametrizing both circles by `Circle.turnExp`. -/
theorem angularLift_lifts_normalizedCircleMap {x : ℂ} (f : Path x x) (a : ℂ)
    (h_avoid : a ∉ Set.range f) (t : unitInterval) :
    Circle.turnExp (angularLift f a h_avoid t) =
      normalizedCircleMap f a h_avoid (Circle.turnExp (t : ℝ)) := by
  -- Normalize the two equivalent unit-period circle parametrizations at this boundary.
  have covering_eq (s : ℝ) : standardCircleCovering s = Circle.turnExp s := by
    rw [standardCircleCovering_apply, AddCircle.homeomorphCircle_apply,
      AddCircle.toCircle_apply_mk]
    rw [Circle.turnExp_eq_exp_scale]
    congr 1
    ring
  have interval_eq : Circle.intervalQuotient t = Circle.turnExp (t : ℝ) := by
    rw [Circle.intervalQuotient]
    change AddCircle.homeomorphCircle one_ne_zero ((t : ℝ) : UnitAddCircle) =
      Circle.turnExp (t : ℝ)
    rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
    rw [Circle.turnExp_eq_exp_scale]
    congr 1
    ring
  calc
    Circle.turnExp (angularLift f a h_avoid t) =
        standardCircleCovering (angularLift f a h_avoid t) :=
      (covering_eq _).symm
    _ = normalizedLoop f a h_avoid t := angularLift_lifts f a h_avoid t
    _ = normalizedCircleMap f a h_avoid (Circle.intervalQuotient t) :=
      (DFunLike.congr_fun (normalizedCircleMap_comp f a h_avoid) t).symm
    _ = normalizedCircleMap f a h_avoid (Circle.turnExp (t : ℝ)) :=
      congrArg (normalizedCircleMap f a h_avoid) interval_eq

/-- Helper for Exercise 66.1: the normalized circle map has a global real lift that
restricts to the canonical angular lift on the unit interval. -/
theorem exists_normalizedCircleMapTurnExpLift {x : ℂ} (f : Path x x) (a : ℂ)
    (h_avoid : a ∉ Set.range f) :
    ∃ F : C(ℝ, ℝ), F 0 = angularLift f a h_avoid 0 ∧
      Circle.turnExp ∘ F =
        (normalizedCircleMap f a h_avoid).comp
          ⟨Circle.turnExp, Circle.isCoveringMap_turnExp.continuous⟩ ∧
      ∀ t : unitInterval, F (t : ℝ) = angularLift f a h_avoid t := by
  -- Lift the normalized map globally from the prescribed initial angular value.
  have basepoint_eq : Circle.turnExp (angularLift f a h_avoid 0) =
      ((normalizedCircleMap f a h_avoid).comp
        ⟨Circle.turnExp, Circle.isCoveringMap_turnExp.continuous⟩) 0 := by
    have at_zero :=
      angularLift_lifts_normalizedCircleMap f a h_avoid (0 : unitInterval)
    have unitInterval_zero_coe : (((0 : unitInterval) : ℝ)) = 0 := rfl
    rw [unitInterval_zero_coe] at at_zero
    rw [ContinuousMap.comp_apply]
    have turnExpMap_zero :
        (⟨Circle.turnExp, Circle.isCoveringMap_turnExp.continuous⟩ : C(ℝ, Circle)) 0 =
          Circle.turnExp 0 := rfl
    rw [turnExpMap_zero]
    exact at_zero
  obtain ⟨F, ⟨hF_zero, hF_lifts⟩, -⟩ :=
    Circle.isCoveringMap_turnExp.existsUnique_continuousMap_lifts
      ((normalizedCircleMap f a h_avoid).comp
        ⟨Circle.turnExp, Circle.isCoveringMap_turnExp.continuous⟩)
      0 (angularLift f a h_avoid 0) basepoint_eq
  refine ⟨F, hF_zero, hF_lifts, ?_⟩
  -- Uniqueness of lifts identifies the global lift with the angular lift on `I`.
  have restricted_continuous : Continuous (fun t : unitInterval ↦ F (t : ℝ)) :=
    F.continuous.comp continuous_subtype_val
  have restricted_comp : Circle.turnExp ∘ (fun t : unitInterval ↦ F (t : ℝ)) =
      Circle.turnExp ∘ angularLift f a h_avoid := by
    funext t
    calc
      Circle.turnExp (F (t : ℝ)) =
          normalizedCircleMap f a h_avoid (Circle.turnExp (t : ℝ)) :=
        congrFun hF_lifts (t : ℝ)
      _ = Circle.turnExp (angularLift f a h_avoid t) :=
        (angularLift_lifts_normalizedCircleMap f a h_avoid t).symm
  have restricted_zero : F ((0 : unitInterval) : ℝ) =
      angularLift f a h_avoid 0 := by
    simpa using hF_zero
  have restricted_eq := Circle.isCoveringMap_turnExp.eq_of_comp_eq
    restricted_continuous (angularLift f a h_avoid).continuous
      restricted_comp 0 restricted_zero
  exact fun t ↦ congrFun restricted_eq t

/-- Exercise 66.1: The winding number of a plane loop about an omitted point equals the degree
of the circle map induced by its normalized direction loop. -/
theorem windingNumber_eq_degree {x : ℂ} (f : Path x x) (a : ℂ)
    (h_avoid : a ∉ Set.range f) (orientation : Circle.FundamentalOrientation) :
    windingNumber f a h_avoid =
      CircleMap.degree orientation (normalizedCircleMap f a h_avoid) := by
  -- Transfer the angular lift's endpoint displacement to a global lift of the circle map.
  obtain ⟨F, -, hF_lifts, hF_restrict⟩ :=
    exists_normalizedCircleMapTurnExpLift f a h_avoid
  have angular_displacement :
      angularLift f a h_avoid 1 - angularLift f a h_avoid 0 =
        (windingNumber f a h_avoid : ℝ) :=
    windingNumber_spec_angularLoop f a h_avoid (angularLift f a h_avoid)
      (angularLift_lifts_angularLoop f a h_avoid)
  have F_one : F 1 = angularLift f a h_avoid 1 := by
    simpa using hF_restrict (1 : unitInterval)
  have F_zero : F 0 = angularLift f a h_avoid 0 := by
    simpa using hF_restrict (0 : unitInterval)
  have F_displacement : F 1 - F 0 = (windingNumber f a h_avoid : ℝ) := by
    rw [F_one, F_zero]
    exact angular_displacement
  -- The global lift's deck translation computes the degree.
  exact (CircleMap.degree_eq_of_turnExpLift orientation
    (normalizedCircleMap f a h_avoid) F (windingNumber f a h_avoid)
      hF_lifts F_displacement).symm

end PlaneLoop
