module

public import Mathlib.Topology.Order.IntermediateValue

public section

universe u v

/-- Theorem 24.3 (Intermediate value theorem): a continuous map from a connected
space to a linearly ordered space with its order topology attains every value
between the images of two points. -/
theorem intermediateValue_of_connectedSpace
    {X : Type u} {Y : Type v} [TopologicalSpace X] [ConnectedSpace X]
    [LinearOrder Y] [TopologicalSpace Y] [OrderTopology Y]
    (f : X → Y) (hf : Continuous f) (a b : X) (r : Y)
    (hr : r ∈ Set.uIcc (f a) (f b)) :
    ∃ c : X, f c = r := by
  rcases Set.mem_uIcc.mp hr with hr | hr
  · simpa only [Set.mem_range] using intermediate_value_univ a b hf hr
  · simpa only [Set.mem_range] using intermediate_value_univ b a hf hr
