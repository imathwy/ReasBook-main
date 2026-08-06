import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_9

universe u v

-- Semantic search hits: `CompactlyGeneratedSpace`, `UCompactlyGeneratedSpace`; local precedent:
-- `WeaklyHausdorffSpace` from Definition 5.1.4. Since mathlib uses `CompactlyGeneratedSpace X`
-- for the k-space condition alone, the source-faithful owner here records the added weak
-- Hausdorff hypothesis explicitly.

/-- Definition 5.1.10. A topological space `X` is compactly generated in the textbook sense if it
is both weak Hausdorff and a k-space. Because mathlib already uses `CompactlyGeneratedSpace X`
for the k-space condition alone, this source-faithful owner packages the added
`WeaklyHausdorffSpace` hypothesis explicitly. -/
@[mk_iff compactlyGeneratedWeakHausdorffSpace_iff]
class CompactlyGeneratedWeakHausdorffSpace (X : Type u) [TopologicalSpace X] : Prop
    extends WeaklyHausdorffSpace.{u, v} X, UCompactlyGeneratedSpace.{v} X

/-- Weak Hausdorff k-spaces are compactly generated in the textbook sense of Definition 5.1.10. -/
instance instCompactlyGeneratedWeakHausdorffSpace
    (X : Type u) [TopologicalSpace X] [hwh : WeaklyHausdorffSpace.{u, v} X]
    [hcg : UCompactlyGeneratedSpace.{v} X] : CompactlyGeneratedWeakHausdorffSpace.{u, v} X where
  toWeaklyHausdorffSpace := hwh
  toUCompactlyGeneratedSpace := hcg
