module

public import Topology_Munkres_2000.Book.Example_53_4.Covering
public import Topology_Munkres_2000.Book.Example_53_4.Doughnut
public import Topology_Munkres_2000.Book.Definition_54_1.Lifting
import all Topology_Munkres_2000.Book.Example_53_4.Covering

public section

open Complex Set

/-- Helper for Exercise 54.5: the winding-`(1, 2)` torus parameter is continuous. -/
lemma continuous_torusPathParam :
    Continuous
      (fun t : unitInterval ↦
        (Circle.turnExp (t : ℝ), Circle.turnExp (2 * (t : ℝ)))) := by
  -- Compose the circle covering with each linear coordinate, then form their product.
  exact
    (Circle.isCoveringMap_turnExp.continuous.comp continuous_subtype_val).prodMk
      (Circle.isCoveringMap_turnExp.continuous.comp
        (continuous_const.mul continuous_subtype_val))

/-- Helper for Exercise 54.5: the winding-`(1, 2)` torus parameter begins and ends at
the basepoint. -/
lemma torusPathEndpoints :
    (Circle.turnExp ((0 : unitInterval) : ℝ),
        Circle.turnExp (2 * ((0 : unitInterval) : ℝ))) =
        ((1 : Circle), (1 : Circle)) ∧
      (Circle.turnExp ((1 : unitInterval) : ℝ),
        Circle.turnExp (2 * ((1 : unitInterval) : ℝ))) =
        ((1 : Circle), (1 : Circle)) := by
  -- Evaluate both integral winding coordinates at the interval endpoints.
  constructor
  · simp only [Set.Icc.coe_zero, mul_zero, Circle.turnExp_zero]
  · norm_num only [Set.Icc.coe_one, mul_one, Circle.turnExp_one]
    exact congrArg (fun z : Circle ↦ ((1 : Circle), z)) (Circle.turnExp_int 2)

/-- The loop that winds once around the first circle and twice around the second. -/
@[expose]
noncomputable def torusPath : Path ((1 : Circle), (1 : Circle)) (1, 1) where
  toFun t := (Circle.turnExp (t : ℝ), Circle.turnExp (2 * (t : ℝ)))
  continuous_toFun := continuous_torusPathParam
  source' := torusPathEndpoints.1
  target' := torusPathEndpoints.2

/-- The product-torus loop has the stated coordinate formula. -/
@[simp]
theorem torusPath_apply (t : unitInterval) :
    torusPath t = (Circle.turnExp (t : ℝ), Circle.turnExp (2 * (t : ℝ))) := rfl

/-- Helper for Exercise 54.5: the straight winding-coordinate parameter is continuous. -/
lemma continuous_planeLiftParam :
    Continuous (fun t : unitInterval ↦ ((t : ℝ), 2 * (t : ℝ))) := by
  -- Combine continuity of the interval coordinate with its constant multiple.
  exact continuous_subtype_val.prodMk (continuous_const.mul continuous_subtype_val)

/-- Helper for Exercise 54.5: the straight winding-coordinate parameter runs from
`(0, 0)` to `(1, 2)`. -/
lemma planeLiftEndpoints :
    (((0 : unitInterval) : ℝ), 2 * ((0 : unitInterval) : ℝ)) =
        ((0 : ℝ), (0 : ℝ)) ∧
      (((1 : unitInterval) : ℝ), 2 * ((1 : unitInterval) : ℝ)) =
        ((1 : ℝ), (2 : ℝ)) := by
  -- Coerce the interval endpoints to `ℝ` and normalize their coordinates.
  norm_num

/-- The explicit plane path with winding coordinates `(1, 2)`. -/
@[expose]
def planeLift : Path ((0 : ℝ), (0 : ℝ)) (1, 2) where
  toFun t := ((t : ℝ), 2 * (t : ℝ))
  continuous_toFun := continuous_planeLiftParam
  source' := planeLiftEndpoints.1
  target' := planeLiftEndpoints.2

/-- The plane lift has the stated coordinate formula. -/
@[simp]
theorem planeLift_apply (t : unitInterval) :
    planeLift t = ((t : ℝ), 2 * (t : ℝ)) := by simp [planeLift]

/-- Exercise 54.5 (1): Under the standard homeomorphism with the doughnut surface,
the loop is the image of `torusPath`. -/
@[expose]
noncomputable def doughnutPath :
    Path (Torus.doughnutHomeomorph ((1 : Circle), (1 : Circle)))
      (Torus.doughnutHomeomorph (1, 1)) :=
  torusPath.map Torus.doughnutHomeomorph.continuous

/-- The doughnut-model loop is given pointwise by the explicit doughnut parametrization. -/
@[simp]
theorem doughnutPath_apply (t : unitInterval) :
    (doughnutPath t : ℂ × ℝ) = Torus.doughnutMap (torusPath t) := rfl

/-- Helper for Exercise 54.5: `Torus.cover` applies the circle exponential in each
coordinate. -/
private theorem torusCover_apply (x : ℝ × ℝ) :
    Torus.cover x = (Circle.turnExp x.1, Circle.turnExp x.2) := by
  -- The implementation import exposes the coordinatewise product map at this bridge.
  rfl

/-- Exercise 54.5 (2): The straight-line plane path is a lift of `torusPath` through
the coordinatewise covering map `Torus.cover`. -/
theorem planeLift_isLift :
    ContinuousMap.IsLift Torus.cover torusPath.toContinuousMap planeLift.toContinuousMap := by
  -- Check pointwise that the winding vector `(1, 2)` exponentiates to the torus loop.
  rw [ContinuousMap.isLift_iff]
  funext t
  calc
    Torus.cover (planeLift.toContinuousMap t) = Torus.cover (planeLift t) := rfl
    _ = (Circle.turnExp (planeLift t).1, Circle.turnExp (planeLift t).2) :=
      torusCover_apply _
    _ = (Circle.turnExp (t : ℝ), Circle.turnExp (2 * (t : ℝ))) := by
      rw [planeLift_apply]
    _ = torusPath t := (torusPath_apply t).symm
    _ = torusPath.toContinuousMap t := rfl
