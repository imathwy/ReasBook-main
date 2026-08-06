import Mathlib.Topology.Compactness.LocallyCompact
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_10

universe u v

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Helper for Proposition 5.1.19: the ordinary product topology `X ×_c Y` is already
compactly generated when the left factor is locally compact and the right factor is compactly
generated weak Hausdorff. -/
lemma ordinaryProductTopology_uCompactlyGenerated
    [LocallyCompactSpace X] [CompactlyGeneratedWeakHausdorffSpace.{v, v} Y] :
    UCompactlyGeneratedSpace.{max u v} (X × Y) := sorry

end
