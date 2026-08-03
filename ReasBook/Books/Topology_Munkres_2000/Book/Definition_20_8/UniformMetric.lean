module

public import Topology_Munkres_2000.Book.Proposition_20_2.BoundedSpace
public import Mathlib.Topology.MetricSpace.UniformConvergence

public section

namespace RealSequence

/-- The uniform metric on real sequences `ℕ → ℝ`. -/
@[implicit_reducible]
noncomputable def metricSpace : MetricSpace (ℕ → ℝ) :=
  MetricSpace.induced UniformFun.ofFun UniformFun.ofFun.injective
    (@UniformFun.instMetricSpaceOfBoundedSpace ℕ ℝ
      (inferInstance : MetricSpace ℝ).standardBounded
      (MetricSpace.standardBounded.boundedSpace (inferInstance : MetricSpace ℝ)))

/-- The open ball for the uniform metric on real sequences. -/
def ball (x : ℕ → ℝ) (ε : ℝ) : Set (ℕ → ℝ) :=
  {y | metricSpace.dist y x < ε}

/-- The uniform distance on real sequences is the supremum of the coordinatewise standard
bounded real distances. -/
theorem dist_eq (x y : ℕ → ℝ) :
    metricSpace.dist x y = ⨆ n, min (dist (x n) (y n)) 1 := by
  -- Expose the explicitly chosen bounded real metric without changing ambient instances.
  calc
    metricSpace.dist x y =
        (@UniformFun.instMetricSpaceOfBoundedSpace ℕ ℝ
          (inferInstance : MetricSpace ℝ).standardBounded
          (MetricSpace.standardBounded.boundedSpace (inferInstance : MetricSpace ℝ))).dist
          (UniformFun.ofFun x) (UniformFun.ofFun y) := rfl
    _ = ⨆ n, (inferInstance : MetricSpace ℝ).standardBounded.dist (x n) (y n) := by
      exact @UniformFun.dist_def ℕ ℝ
        (inferInstance : MetricSpace ℝ).standardBounded.toPseudoMetricSpace
        (MetricSpace.standardBounded.boundedSpace (inferInstance : MetricSpace ℝ))
        (UniformFun.ofFun x) (UniformFun.ofFun y)
    _ = ⨆ n, min (dist (x n) (y n)) 1 := by
      congr 1
      funext n
      exact MetricSpace.standardBounded_dist (inferInstance : MetricSpace ℝ) (x n) (y n)

/-- Every uniform distance between real sequences is at most `1`. -/
theorem dist_le_one (x y : ℕ → ℝ) : metricSpace.dist x y ≤ 1 := by
  -- Rewrite the global distance and bound each truncated coordinate distance.
  rw [dist_eq]
  exact ciSup_le fun n ↦ min_le_right (dist (x n) (y n)) 1

/-- The topology induced by the uniform metric on real sequences. -/
noncomputable abbrev topology : TopologicalSpace (ℕ → ℝ) :=
  metricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The topology induced by `metricSpace` is the named uniform topology. -/
theorem topology_def :
    metricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = topology := rfl

end RealSequence

end
