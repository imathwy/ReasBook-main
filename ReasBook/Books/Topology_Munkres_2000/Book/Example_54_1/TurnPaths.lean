module

public import Topology_Munkres_2000.Book.Theorem_53_1.CircleMap
public import Topology_Munkres_2000.Book.Definition_54_1.Lifting
public import Mathlib.Topology.Homotopy.Path

@[expose] public section

noncomputable section

open unitInterval

namespace Circle

/-- Helper for Example 54.1: the scaled circle parametrization has the expected endpoints. -/
lemma turnPathEndpoints (a : ℝ) :
    turnExp (a * ((0 : unitInterval) : ℝ)) = 1 ∧
      turnExp (a * ((1 : unitInterval) : ℝ)) = turnExp a := by
  -- Evaluate the scalar parametrization at the two endpoints of the unit interval.
  constructor
  · simp only [Set.Icc.coe_zero, mul_zero, turnExp_zero]
  · simp only [Set.Icc.coe_one, mul_one]

/-- Helper for Example 54.1: the linear real parametrization has endpoints `0` and `a`. -/
lemma turnLiftEndpoints (a : ℝ) :
    a * ((0 : unitInterval) : ℝ) = 0 ∧
      a * ((1 : unitInterval) : ℝ) = a := by
  -- Scalar multiplication by the endpoint coordinates reduces to multiplication by zero and one.
  constructor
  · simp only [Set.Icc.coe_zero, mul_zero]
  · simp only [Set.Icc.coe_one, mul_one]

/-- Helper for Example 54.1: the linear parametrization of the lift is continuous. -/
lemma continuous_turnLiftParam (a : ℝ) :
    Continuous (fun s : unitInterval ↦ a * (s : ℝ)) := by
  -- Multiplication preserves continuity of the subtype coercion.
  fun_prop

/-- Helper for Example 54.1: applying `turnExp` to the linear parametrization is continuous. -/
lemma continuous_turnPathParam (a : ℝ) :
    Continuous (fun s : unitInterval ↦ turnExp (a * (s : ℝ))) := by
  -- Rewrite only the circle parametrization at the continuity interface.
  rw [turnExp_eq_exp_scale]
  fun_prop

/-- The path from `1` to `turnExp a` making `a` turns under the one-turn parametrization. -/
def turnPath (a : ℝ) : Path (1 : Circle) (turnExp a) where
  toFun s := turnExp (a * (s : ℝ))
  continuous_toFun := continuous_turnPathParam a
  source' := (turnPathEndpoints a).1
  target' := (turnPathEndpoints a).2

/-- The explicit path from `0` to `a` lifting `turnPath a` through `turnExp`. -/
def turnLift (a : ℝ) : Path (0 : ℝ) a where
  toFun s := a * (s : ℝ)
  continuous_toFun := continuous_turnLiftParam a
  source' := (turnLiftEndpoints a).1
  target' := (turnLiftEndpoints a).2

/-- The value of the scaled turn path. -/
@[simp]
theorem turnPath_apply (a : ℝ) (s : unitInterval) :
    turnPath a s = turnExp (a * (s : ℝ)) := rfl

/-- The scaled turn path has the usual cosine-sine coordinate formula. -/
theorem coe_turnPath (a : ℝ) (s : unitInterval) :
    (turnPath a s : ℂ) =
      Real.cos (2 * Real.pi * (a * (s : ℝ))) +
        Real.sin (2 * Real.pi * (a * (s : ℝ))) * Complex.I := by
  -- Expose the path value and apply the coordinate formula for `turnExp`.
  rw [turnPath_apply]
  exact coe_turnExp _

/-- The value of the explicit linear lift. -/
@[simp]
theorem turnLift_apply (a : ℝ) (s : unitInterval) :
    turnLift a s = a * (s : ℝ) := rfl

/-- The path `turnLift a` lifts `turnPath a` through `turnExp`. -/
theorem turnLift_isLift (a : ℝ) :
    ContinuousMap.IsLift turnExp (turnPath a).toContinuousMap
      (turnLift a).toContinuousMap := by
  -- Check the lifting equation pointwise; both paths use the same scalar parameter.
  rw [ContinuousMap.isLift_iff]
  funext s
  calc
    turnExp ((turnLift a).toContinuousMap s) = turnExp (turnLift a s) := rfl
    _ = turnExp (a * (s : ℝ)) := congrArg turnExp (turnLift_apply a s)
    _ = turnPath a s := (turnPath_apply a s).symm
    _ = (turnPath a).toContinuousMap s := rfl

end Circle
