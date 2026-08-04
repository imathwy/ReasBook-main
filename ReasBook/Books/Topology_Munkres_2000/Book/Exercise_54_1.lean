module

public import Topology_Munkres_2000.Book.Example_53_2.CircleMap
public import Topology_Munkres_2000.Book.Example_54_1

public section

namespace Circle

/- Exercise 54.1 uses the local homeomorphism of Example 53.2. -/
#check positiveRealExp_isLocalHomeomorph

/-- Helper for Exercise 54.1: adding one full turn does not change `turnExp`. -/
lemma turnExp_add_one (x : ℝ) : turnExp (x + 1) = turnExp x := by
  -- Convert one unit in the parameter to the `2 * π` period of the circle exponential.
  rw [turnExp_eq_exp_scale]
  calc
    Circle.exp (2 * Real.pi * (x + 1)) =
        Circle.exp (2 * Real.pi * x + 2 * Real.pi) := by
      congr 1
      ring
    _ = Circle.exp (2 * Real.pi * x) := Circle.periodic_exp (2 * Real.pi * x)

/-- Helper for Exercise 54.1: the affine real path `t ↦ 1 - t` projects to the
clockwise one-turn path. -/
lemma clockwiseTurnProjection (t : unitInterval) :
    turnExp (1 - (t : ℝ)) = turnPath (-1) t := by
  -- Move the affine path back by one period and identify the resulting linear path.
  calc
    turnExp (1 - (t : ℝ)) = turnExp (-(t : ℝ) + 1) := by
      congr 1
      ring
    _ = turnExp (-(t : ℝ)) := turnExp_add_one (-(t : ℝ))
    _ = turnExp ((-1 : ℝ) * (t : ℝ)) := by
      congr 1
      ring
    _ = turnPath (-1) t := (turnPath_apply (-1) t).symm

/-- Helper for Exercise 54.1: a positive-real lift of the clockwise turn beginning
at `1` would have real endpoint `0`. -/
lemma clockwiseLift_endpoint_eq_zero
    (lift : C(unitInterval, Set.Ioi (0 : ℝ)))
    (hInitial : (lift 0 : ℝ) = 1)
    (hLift : ContinuousMap.IsLift positiveRealExp
      (turnPath (-1)).toContinuousMap lift) :
    (lift 1 : ℝ) = 0 := by
  -- Regard the hypothetical restricted lift as a continuous real-valued lift.
  have hLiftContinuous : Continuous (fun t : unitInterval ↦ (lift t : ℝ)) :=
    continuous_subtype_val.comp lift.continuous
  have hAffineContinuous : Continuous (fun t : unitInterval ↦ 1 - (t : ℝ)) :=
    continuous_const.sub continuous_subtype_val
  -- Both real-valued paths project to the same clockwise path.
  have hProjection :
      turnExp ∘ (fun t : unitInterval ↦ (lift t : ℝ)) =
        turnExp ∘ (fun t : unitInterval ↦ 1 - (t : ℝ)) := by
    funext t
    calc
      turnExp (lift t : ℝ) = positiveRealExp (lift t) :=
        (positiveRealExp_apply (lift t)).symm
      _ = turnPath (-1) t := hLift.apply t
      _ = turnExp (1 - (t : ℝ)) := (clockwiseTurnProjection t).symm
  have hInitialAgreement :
      (lift (0 : unitInterval) : ℝ) = 1 - ((0 : unitInterval) : ℝ) := by
    simpa only [Set.Icc.coe_zero, sub_zero] using hInitial
  -- Uniqueness for the covering `turnExp` identifies the paths, hence their endpoints.
  have hPathEquality := isCoveringMap_turnExp.eq_of_comp_eq
    hLiftContinuous hAffineContinuous hProjection 0 hInitialAgreement
  have hEndpointEquality := congrFun hPathEquality (1 : unitInterval)
  simpa only [Set.Icc.coe_one, sub_self] using hEndpointEquality

/-- Exercise 54.1. The clockwise loop making one full turn has no lift through
`positiveRealExp` that begins at the positive-real coordinate `1`. Thus the
existence conclusion of the path-lifting lemma fails for this local homeomorphism. -/
theorem positiveRealExp_clockwiseLoop_no_lift :
    ¬ ∃ lift : C(unitInterval, Set.Ioi (0 : ℝ)),
      (lift 0 : ℝ) = 1 ∧
        ContinuousMap.IsLift positiveRealExp (turnPath (-1)).toContinuousMap lift := by
  -- A lift would be forced to hit the omitted endpoint `0`, contradicting positivity.
  rintro ⟨lift, hInitial, hLift⟩
  have hEndpointZero := clockwiseLift_endpoint_eq_zero lift hInitial hLift
  exact (ne_of_gt (lift (1 : unitInterval)).property) hEndpointZero

end Circle
