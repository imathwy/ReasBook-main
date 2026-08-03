module

public import Mathlib.Topology.MetricSpace.Defs

public section

universe u

namespace DiscreteMetric

variable {X : Type u}

/-- The `0`–`1` distance on an arbitrary type. -/
@[expose]
noncomputable def distance (x y : X) : ℝ :=
  @ite ℝ (x = y) (Classical.propDecidable _) 0 1

/-- The `0`–`1` distance vanishes on the diagonal. -/
theorem distance_self (x : X) : distance x x = 0 := by
  simp [distance]

/-- The `0`–`1` distance is symmetric. -/
theorem distance_comm (x y : X) : distance x y = distance y x := by
  by_cases hxy : x = y
  · simp [hxy, distance]
  · simp [hxy, Ne.symm hxy, distance]

/-- The `0`–`1` distance satisfies the triangle inequality. -/
theorem distance_triangle (x y z : X) :
    distance x z ≤ distance x y + distance y z := by
  by_cases hxy : x = y <;> by_cases hxz : x = z <;> by_cases hyz : y = z <;>
    simp_all [distance]

/-- Points at zero `0`–`1` distance are equal. -/
theorem eq_of_distance_eq_zero (x y : X) (h : distance x y = 0) : x = y := by
  by_contra hxy
  simp [distance, hxy] at h

/-- The metric space structure determined by the `0`–`1` distance. -/
@[expose, implicit_reducible]
noncomputable def space (X : Type u) : MetricSpace X :=
  { dist := distance
    dist_self := distance_self
    dist_comm := distance_comm
    dist_triangle := distance_triangle
    eq_of_dist_eq_zero := fun h ↦ eq_of_distance_eq_zero _ _ h }

/-- Use the `0`–`1` metric on an arbitrary type within the `DiscreteMetric` scope. -/
noncomputable scoped instance instMetricSpace (X : Type u) : MetricSpace X := space X

open scoped DiscreteMetric

/-- The distance field of `space` is the `0`–`1` distance. -/
theorem dist_eq (x y : X) : dist x y = distance x y := rfl

/-- Equal points have `0`–`1` distance zero. -/
theorem dist_eq_zero_of_eq {x y : X} (hxy : x = y) : dist x y = 0 := by
  subst y
  exact dist_self x

/-- Distinct points have `0`–`1` distance one. -/
theorem dist_eq_one_of_ne {x y : X} (hxy : x ≠ y) : dist x y = 1 := by
  simp [dist_eq, distance, hxy]

/-- The open ball of radius `1` in the `0`–`1` metric is a singleton. -/
theorem ball_one (x : X) : Metric.ball x 1 = {x} := by
  ext y
  rw [Metric.mem_ball, dist_eq]
  by_cases hyx : y = x <;> simp [distance, hyx]

/-- The topology induced by the `0`–`1` metric is discrete. -/
noncomputable scoped instance instDiscreteTopology (X : Type u) : DiscreteTopology X where
  eq_bot := by
    refine eq_bot_of_singletons_open fun x ↦ ?_
    rw [← ball_one x]
    exact Metric.isOpen_ball

end DiscreteMetric


end
