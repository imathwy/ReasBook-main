module

public import Topology_Munkres_2000.Book.Definition_20_9
public import Mathlib.Topology.WithTopology

public section

universe u

namespace UniformMetric

/-- The space of real-valued functions on `X`, equipped with the uniform-metric topology. -/
abbrev FunctionSpace (X : Type u) :=
  WithTopology (X → ℝ) (topology X)

/-- Regard a real-valued function as a point of the uniform-metric function space. -/
def FunctionSpace.ofFun (f : X → ℝ) : FunctionSpace X :=
  WithTopology.toTopology (topology X) f

/-- Helper for Proposition 21.3: wrapping and then unwrapping a point of `FunctionSpace X`
returns that point. -/
@[simp]
theorem FunctionSpace.ofFun_ofTopology (f : FunctionSpace X) :
    FunctionSpace.ofFun f.ofTopology = f := by
  -- The wrapper and unwrapping maps for `WithTopology` are inverse.
  exact WithTopology.toTopology_ofTopology (topology X) f

/-- Helper for Proposition 21.3: the standard bounded metric induces the same uniform space as
the original metric. -/
private theorem standardBounded_uniformSpace_eq {Y : Type*} (m : MetricSpace Y) :
    m.standardBounded.toUniformSpace = m.toUniformSpace := by
  -- Compare the metric bases, shrinking the bounded-metric radius below `1` when necessary.
  apply UniformSpace.ext
  letI : MetricSpace Y := m.standardBounded
  have boundedBasis := @Metric.uniformity_basis_dist Y m.standardBounded.toPseudoMetricSpace
  letI : MetricSpace Y := m
  have originalBasis := @Metric.uniformity_basis_dist Y m.toPseudoMetricSpace
  refine boundedBasis.ext originalBasis ?_ ?_
  · intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro p hp
    change m.dist p.1 p.2 < ε at hp
    change m.standardBounded.dist p.1 p.2 < ε
    rw [MetricSpace.standardBounded_dist]
    exact lt_of_le_of_lt (min_le_left _ _) hp
  · intro ε hε
    refine ⟨min ε 1, lt_min hε zero_lt_one, ?_⟩
    intro p hp
    change m.standardBounded.dist p.1 p.2 < min ε 1 at hp
    change m.dist p.1 p.2 < ε
    rw [MetricSpace.standardBounded_dist] at hp
    have hdist_one : m.dist p.1 p.2 < 1 := by
      apply (min_lt_iff.mp (lt_of_lt_of_le hp (min_le_right ε 1))).resolve_right
      exact lt_irrefl 1
    rw [min_eq_left (le_of_lt hdist_one)] at hp
    exact lt_of_lt_of_le hp (min_le_left ε 1)

/-- Helper for Proposition 21.3: the named uniform metric is the metric induced from the
standard-bounded metric on `UniformFun`. -/
private theorem metricSpace_eq_induced_uniformFun (X : Type u) :
    metricSpace X =
      MetricSpace.induced UniformFun.ofFun UniformFun.ofFun.injective
        (@UniformFun.instMetricSpaceOfBoundedSpace X ℝ
          (inferInstance : MetricSpace ℝ).standardBounded
          (MetricSpace.standardBounded.boundedSpace (inferInstance : MetricSpace ℝ))) := by
  -- Compare distances using the exported formulas on both function spaces.
  apply MetricSpace.ext
  ext f g
  calc
    (metricSpace X).dist f g = ⨆ x, min (dist (f x) (g x)) 1 := dist_eq f g
    _ = (@UniformFun.instMetricSpaceOfBoundedSpace X ℝ
          (inferInstance : MetricSpace ℝ).standardBounded
          (MetricSpace.standardBounded.boundedSpace (inferInstance : MetricSpace ℝ))).dist
          (UniformFun.ofFun f) (UniformFun.ofFun g) := by
      symm
      calc
        (@UniformFun.instMetricSpaceOfBoundedSpace X ℝ
            (inferInstance : MetricSpace ℝ).standardBounded
            (MetricSpace.standardBounded.boundedSpace (inferInstance : MetricSpace ℝ))).dist
            (UniformFun.ofFun f) (UniformFun.ofFun g) =
            ⨆ x, (inferInstance : MetricSpace ℝ).standardBounded.dist (f x) (g x) := by
          exact @UniformFun.dist_def X ℝ
            (inferInstance : MetricSpace ℝ).standardBounded.toPseudoMetricSpace
            (MetricSpace.standardBounded.boundedSpace (inferInstance : MetricSpace ℝ))
            (UniformFun.ofFun f) (UniformFun.ofFun g)
        _ = ⨆ x, min (dist (f x) (g x)) 1 := by
          congr 1
          funext x
          exact MetricSpace.standardBounded_dist (inferInstance : MetricSpace ℝ) (f x) (g x)

/-- Helper for Proposition 21.3: the named uniform-metric topology is the topology induced by
the canonical map from raw functions to `UniformFun`. -/
private theorem topology_eq_induced_uniformFun (X : Type u) :
    topology X =
      TopologicalSpace.induced UniformFun.ofFun (UniformFun.topologicalSpace X ℝ) := by
  -- The target uniform structures agree because truncating the real metric preserves uniformity.
  have targetTopologyEq :
      (@UniformFun.instMetricSpaceOfBoundedSpace X ℝ
        (inferInstance : MetricSpace ℝ).standardBounded
        (MetricSpace.standardBounded.boundedSpace
          (inferInstance : MetricSpace ℝ))).toUniformSpace.toTopologicalSpace =
        UniformFun.topologicalSpace X ℝ := by
    change (@UniformFun.uniformSpace X ℝ
      (inferInstance : MetricSpace ℝ).standardBounded.toUniformSpace).toTopologicalSpace = _
    rw [standardBounded_uniformSpace_eq]
    rfl
  rw [← topology_def, metricSpace_eq_induced_uniformFun]
  exact congrArg (TopologicalSpace.induced UniformFun.ofFun) targetTopologyEq

/-- Helper for Proposition 21.3: the canonical map from the wrapped uniform-metric function
space to `UniformFun` is continuous. -/
private theorem continuous_functionSpace_toUniformFun (X : Type u) :
    Continuous (fun f : FunctionSpace X ↦ UniformFun.ofFun f.ofTopology) := by
  -- Unwrap continuously and then use the defining induced topology.
  have hOfFun : @Continuous (X → ℝ) (UniformFun X ℝ) (topology X)
      (UniformFun.topologicalSpace X ℝ) UniformFun.ofFun := by
    rw [topology_eq_induced_uniformFun]
    exact @continuous_induced_dom (X → ℝ) (UniformFun X ℝ) UniformFun.ofFun
      (UniformFun.topologicalSpace X ℝ)
  have hUnwrap : @Continuous (FunctionSpace X) (X → ℝ)
      (WithTopology.instTopologicalSpace (X → ℝ) (topology X)) (topology X)
      WithTopology.ofTopology :=
    WithTopology.continuous_ofTopology (topology X)
  exact @Continuous.comp' (FunctionSpace X) (X → ℝ) (UniformFun X ℝ)
    (WithTopology.instTopologicalSpace (X → ℝ) (topology X)) (topology X)
    (UniformFun.topologicalSpace X ℝ) WithTopology.ofTopology UniformFun.ofFun hOfFun hUnwrap

/-- Helper for Proposition 21.3: the canonical map from `UniformFun` to the wrapped
uniform-metric function space is continuous. -/
private theorem continuous_uniformFun_toFunctionSpace (X : Type u) :
    Continuous (fun f : UniformFun X ℝ ↦ FunctionSpace.ofFun f.toFun) := by
  -- The inverse equivalence is continuous into the induced topology, then wraps continuously.
  have hToFun : @Continuous (UniformFun X ℝ) (X → ℝ) (UniformFun.topologicalSpace X ℝ)
      (topology X) UniformFun.toFun := by
    rw [topology_eq_induced_uniformFun, continuous_induced_rng]
    exact @continuous_id (UniformFun X ℝ) (UniformFun.topologicalSpace X ℝ)
  have hWrap : @Continuous (X → ℝ) (FunctionSpace X) (topology X)
      (WithTopology.instTopologicalSpace (X → ℝ) (topology X))
      (FunctionSpace.ofFun : (X → ℝ) → FunctionSpace X) :=
    WithTopology.continuous_toTopology (topology X)
  exact @Continuous.comp' (UniformFun X ℝ) (X → ℝ) (FunctionSpace X)
    (UniformFun.topologicalSpace X ℝ) (topology X)
    (WithTopology.instTopologicalSpace (X → ℝ) (topology X)) UniformFun.toFun
    FunctionSpace.ofFun hWrap hToFun

/-- The uniform-metric function space is canonically homeomorphic to mathlib's space of
functions with the topology of uniform convergence. -/
noncomputable def functionSpaceHomeomorph (X : Type u) : FunctionSpace X ≃ₜ UniformFun X ℝ where
  toFun f := UniformFun.ofFun f.ofTopology
  invFun f := FunctionSpace.ofFun f.toFun
  left_inv _ := rfl
  right_inv f := UniformFun.ofFun_toFun f
  continuous_toFun := continuous_functionSpace_toUniformFun X
  continuous_invFun := continuous_uniformFun_toFunctionSpace X

@[simp]
theorem functionSpaceHomeomorph_apply (f : FunctionSpace X) :
    (functionSpaceHomeomorph X f).toFun = f.ofTopology := by
  -- Unfold the forward map of the canonical homeomorphism.
  rfl

@[simp]
theorem functionSpaceHomeomorph_symm_apply (f : UniformFun X ℝ) :
    (functionSpaceHomeomorph X).symm f = FunctionSpace.ofFun f.toFun := by
  -- Unfold the inverse map of the canonical homeomorphism.
  rfl

end UniformMetric

end
