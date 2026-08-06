import Mathlib.Tactic.Recall
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Remark_6_2_4

open scoped ContinuousMap

universe u

variable {A X : Type u} [TopologicalSpace A] [TopologicalSpace X]

-- Semantic recall via `lean_leansearch`: `Topology.IsClosedEmbedding` is the canonical mathlib
-- owner for “inclusion with closed image,” and Chapter 6 already exports the source-facing
-- cofibration consequences as `IsCofibration.isClosedEmbedding` and `IsCofibration.isClosed_range`.

/- Problem 6.6.1. This is exactly the Chapter 6 closed-embedding consequence of cofibrations:
`IsCofibration.isClosedEmbedding` gives the closed-embedding statement, and
`IsCofibration.isClosed_range` records the resulting closed-image corollary. We therefore keep this
problem as a recall-only file rather than duplicating those theorem interfaces under new names. -/
recall IsCofibration.isClosedEmbedding
    {A X : Type u} [TopologicalSpace A] [TopologicalSpace X]
    [CompactlyGeneratedWeakHausdorffSpace A] [CompactlyGeneratedWeakHausdorffSpace X]
    {i : C(A, X)} :
      IsCofibration i → Topology.IsClosedEmbedding i

recall IsCofibration.isClosed_range
    {A X : Type u} [TopologicalSpace A] [TopologicalSpace X]
    [CompactlyGeneratedWeakHausdorffSpace A] [CompactlyGeneratedWeakHausdorffSpace X]
    {i : C(A, X)} :
      IsCofibration i → IsClosed (Set.range i)
