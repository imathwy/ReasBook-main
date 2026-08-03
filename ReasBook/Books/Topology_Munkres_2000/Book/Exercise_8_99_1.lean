module

public import Topology_Munkres_2000.Book.Definition_29_1.LocalCompactness
public import Topology_Munkres_2000.Book.Exercise_4_99_2.LocallyMetrizable
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

universe u v

namespace ChartedSpace

/-- Exercise 8.99.1 (1). A charted space modeled on a locally compact space is weakly
locally compact. -/
theorem weaklyLocallyCompactSpace (H : Type u) (M : Type v) [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M] [LocallyCompactSpace H] :
    WeaklyLocallyCompactSpace M := by
  -- Mathlib's chart theorem supplies the stronger local compactness structure on `M`.
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- Forgetting the separation component gives the required compact neighborhood at every point.
  infer_instance

/-- Exercise 8.99.1 (2). A charted space modeled on a metrizable space is locally
metrizable. -/
theorem locallyMetrizableSpace (H : Type u) (M : Type v) [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace.MetrizableSpace H] :
    LocallyMetrizableSpace M := by
  rw [locallyMetrizableSpace_iff]
  intro x
  -- The preferred chart source is a neighborhood of `x` in the ambient charted space.
  refine ⟨(chartAt H x).source, chart_source_mem_nhds H x, ?_⟩
  -- Its subtype topology is metrizable because it embeds into the metrizable model space.
  exact (Topology.IsEmbedding.subtypeVal.comp
    (chartAt H x).toHomeomorphSourceTarget.isEmbedding).metrizableSpace

end ChartedSpace
