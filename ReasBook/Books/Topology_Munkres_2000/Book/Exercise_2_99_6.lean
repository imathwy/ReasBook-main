module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Instances.AddCircle.Real

public section

open AddCircle

/-- Exercise 2.99.6: The quotient topological group `ℝ / ℤ` is the unit circle group. -/
noncomputable def UnitAddCircle.continuousAddEquivCircle :
    UnitAddCircle ≃ₜ+ Additive Circle where
  toEquiv := (homeomorphCircle one_ne_zero).toEquiv
  map_add' x y := by
    change homeomorphCircle one_ne_zero (x + y) =
      homeomorphCircle one_ne_zero x * homeomorphCircle one_ne_zero y
    simp only [homeomorphCircle_apply, toCircle_add]
  continuous_toFun := (homeomorphCircle one_ne_zero).continuous
  continuous_invFun := (homeomorphCircle one_ne_zero).continuous_symm

@[simp]
theorem UnitAddCircle.continuousAddEquivCircle_apply (x : UnitAddCircle) :
    continuousAddEquivCircle x = toCircle x := by
  exact homeomorphCircle_apply one_ne_zero x
