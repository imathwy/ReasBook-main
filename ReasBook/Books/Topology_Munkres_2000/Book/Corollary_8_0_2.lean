module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Separation.Hausdorff

import Topology_Munkres_2000.Book.Exercise_36_1.Metrizable
import Topology_Munkres_2000.Book.Exercise_36_3.Instances
import Topology_Munkres_2000.Book.Theorem_50_3
import Topology_Munkres_2000.Book.Theorem_50_4

public section

universe u

/-- Corollary 8.0.2: Every compact Hausdorff `m`-manifold admits a topological embedding
into `EuclideanSpace ℝ (Fin (2 * m + 1))`. -/
theorem exists_embedding_euclidean_of_compact_manifold {m : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M] [T2Space M]
    [CompactSpace M] :
    ∃ f : M → EuclideanSpace ℝ (Fin (2 * m + 1)), Topology.IsEmbedding f := by
  -- This witness depends on the selected chart dimension and second-countability instance.
  -- Local instance justification (instance diamond): use the proof-local manifold structure.
  letI : TopologicalSpace.MetrizableSpace M :=
    ChartedSpace.metrizableSpace (EuclideanSpace ℝ (Fin m))
  exact existsEuclideanEmbedding_of_hasCoveringDimensionLE
    compactManifold_coveringDimension_le
