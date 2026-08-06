import Mathlib.Tactic.Recall
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_7

universe u v

-- Semantic search hits: `UCompactlyGeneratedSpace`, `CompactlyGeneratedSpace`,
-- `UCompactlyGeneratedSpace.isClosed`; local precedent: `IsCompactlyClosed.isClosed`.
/- Definition 5.1.9: the textbook notion of a k-space is formalized by
`UCompactlyGeneratedSpace.{v} X`. Together with `IsCompactlyClosed` from Definition 5.1.7,
this gives the textbook characterization that compactly closed subsets of `X` are exactly the
closed subsets. -/
recall UCompactlyGeneratedSpace (X : Type u) [TopologicalSpace X] : Prop

/- In a `UCompactlyGeneratedSpace.{v}`, compactly closed subsets of `X` are exactly the closed
subsets. -/
recall isCompactlyClosed_iff_isClosed {X : Type u} [TopologicalSpace X]
    [UCompactlyGeneratedSpace.{v} X] {A : Set X} :
    IsCompactlyClosed.{u, v} A ↔ IsClosed A
