module

public import Topology_Munkres_2000.Book.Definition_20_8.UniformMetric

public section

universe u v

namespace MetricSpace

variable {Y : Type v}

/-- The uniform metric on the raw function space `J → Y`, defined as the supremum of the
coordinatewise standard bounded distances. -/
@[implicit_reducible]
noncomputable def uniformFun (m : MetricSpace Y) (J : Type u) : MetricSpace (J → Y) :=
  MetricSpace.induced UniformFun.ofFun UniformFun.ofFun.injective
    (@UniformFun.instMetricSpaceOfBoundedSpace J Y m.standardBounded
      (MetricSpace.standardBounded.boundedSpace m))

/-- The distance in `MetricSpace.uniformFun` is the supremum of the coordinatewise standard
bounded distances. -/
theorem uniformFun_dist (m : MetricSpace Y) (J : Type u) (f g : J → Y) :
    (m.uniformFun J).dist f g = ⨆ j, min (m.dist (f j) (g j)) 1 := by
  -- Expose the bounded coordinate metric, compute the supremum, then unfold its truncation.
  calc
    (m.uniformFun J).dist f g =
        (@UniformFun.instMetricSpaceOfBoundedSpace J Y m.standardBounded
          (MetricSpace.standardBounded.boundedSpace m)).dist
          (UniformFun.ofFun f) (UniformFun.ofFun g) := rfl
    _ = ⨆ j, m.standardBounded.dist (f j) (g j) := by
      exact @UniformFun.dist_def J Y m.standardBounded.toPseudoMetricSpace
        (MetricSpace.standardBounded.boundedSpace m) (UniformFun.ofFun f) (UniformFun.ofFun g)
    _ = ⨆ j, min (m.dist (f j) (g j)) 1 := by
      congr 1
      funext j
      exact MetricSpace.standardBounded_dist m (f j) (g j)

/-- Every distance in `MetricSpace.uniformFun` is at most `1`. -/
theorem uniformFun_dist_le_one (m : MetricSpace Y) (J : Type u) (f g : J → Y) :
    (m.uniformFun J).dist f g ≤ 1 := by
  -- Bound the supremum by bounding every truncated coordinate distance.
  rw [uniformFun_dist]
  cases isEmpty_or_nonempty J with
  | inl _ => simp
  | inr _ => exact ciSup_le fun j ↦ min_le_right (m.dist (f j) (g j)) 1

end MetricSpace

namespace UniformMetric

/-- Definition 20.9: The uniform metric on `J → ℝ`. -/
noncomputable abbrev metricSpace (J : Type u) : MetricSpace (J → ℝ) :=
  (inferInstance : MetricSpace ℝ).uniformFun J

/-- The open ball for the uniform metric on `J → ℝ`. -/
def ball {J : Type u} (x : J → ℝ) (ε : ℝ) : Set (J → ℝ) :=
  {y | (metricSpace J).dist y x < ε}

/-- The uniform distance is the supremum of the coordinatewise standard bounded real distances. -/
theorem dist_eq {J : Type u} (x y : J → ℝ) :
    (metricSpace J).dist x y = ⨆ j, min (dist (x j) (y j)) 1 :=
  MetricSpace.uniformFun_dist (inferInstance : MetricSpace ℝ) J x y

/-- Every uniform distance is at most `1`. -/
theorem dist_le_one {J : Type u} (x y : J → ℝ) : (metricSpace J).dist x y ≤ 1 :=
  MetricSpace.uniformFun_dist_le_one (inferInstance : MetricSpace ℝ) J x y

/-- The topology induced by the uniform metric on `J → ℝ`. -/
noncomputable abbrev topology (J : Type u) : TopologicalSpace (J → ℝ) :=
  (metricSpace J).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The topology induced by `metricSpace` is the named uniform topology. -/
theorem topology_def {J : Type u} :
    (metricSpace J).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace = topology J := rfl

/-- Definition 20.9 specializes to the uniform metric of Definition 20.8 on real sequences. -/
theorem metricSpace_nat : metricSpace ℕ = RealSequence.metricSpace := by
  -- Identify the named metrics through their common coordinatewise distance formula.
  apply MetricSpace.ext
  ext x y
  exact (dist_eq x y).trans (RealSequence.dist_eq x y).symm

/-- Definition 20.9 specializes to the uniform topology of Definition 20.8 on real sequences. -/
theorem topology_nat : topology ℕ = RealSequence.topology := by
  -- Rewrite the inducing metric before comparing the two topology abbreviations.
  unfold topology RealSequence.topology
  rw [metricSpace_nat]

end UniformMetric

end
