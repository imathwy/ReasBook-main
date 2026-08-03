module

public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.UniformSpace.UniformApproximation

public section

universe u v

/-- Theorem 18.6 (Uniform Limit Theorem). A uniformly convergent sequence of
continuous maps from a topological space to a metric space has a continuous limit. -/
theorem continuous_of_tendstoUniformly {X : Type u} {Y : Type v}
    [TopologicalSpace X] [MetricSpace Y] {f : ℕ → X → Y} {g : X → Y}
    (hf : ∀ n, Continuous (f n)) (hfg : TendstoUniformly f g Filter.atTop) :
    Continuous g := hfg.continuous (Filter.Frequently.of_forall hf)
