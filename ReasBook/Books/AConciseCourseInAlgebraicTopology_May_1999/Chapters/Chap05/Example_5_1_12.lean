import Mathlib.Topology.Sequences
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_10

universe u

variable {X : Type u} [TopologicalSpace X]

-- Semantic search hits: `FirstCountableTopology.frechetUrysohnSpace`,
-- `FrechetUrysohnSpace.to_sequentialSpace`, and the resulting
-- `[SequentialSpace X] -> [UCompactlyGeneratedSpace X]`. Local precedent packages the textbook
-- compactly generated notion as `CompactlyGeneratedWeakHausdorffSpace`.

/-- Example 5.1.12. Every weak Hausdorff space satisfying the first axiom of countability is
compactly generated. -/
instance instCompactlyGeneratedWeakHausdorffSpaceOfFirstCountable [WeaklyHausdorffSpace.{u, u} X]
    [FirstCountableTopology X] : CompactlyGeneratedWeakHausdorffSpace.{u, u} X := by
  infer_instance
