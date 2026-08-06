import Mathlib.Tactic.Recall
import Mathlib.Topology.Category.CompactlyGenerated
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_10

universe u

-- The source-facing chapter owner for textbook compactly generated spaces is
-- `CompactlyGeneratedWeakHausdorffSpace`, while mathlib's canonical owner for k-ification is
-- `TopologicalSpace.compactlyGenerated`.

/- Convention 5.2.14: all subsequent spaces are assumed compactly generated in the textbook sense,
formalized here by `CompactlyGeneratedWeakHausdorffSpace X`. When a space-level construction is
formed in the ordinary category of spaces, its compactly generated replacement is obtained by
applying the k-ification `TopologicalSpace.compactlyGenerated X` from Construction 5.1.14. -/
recall CompactlyGeneratedWeakHausdorffSpace (X : Type u) [TopologicalSpace X] : Prop
recall TopologicalSpace.compactlyGenerated (X : Type u) [TopologicalSpace X] : TopologicalSpace X
