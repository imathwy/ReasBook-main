import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Definition_5_1_10
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Problem_5_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Remark_5_2_13
import Books.AConciseCourseInAlgebraicTopology_May_1999.TopCat.Subspace

open CategoryTheory CategoryTheory.Limits

universe u

-- Semantic search hits: `uCompactlyGeneratedSpace_of_coinduced`,
-- `compactlyGeneratedSpace_of_coinduced`, `instUCompactlyGeneratedSpaceSum`; local Chapter 5
-- precedent: `CompactlyGeneratedWeakHausdorffSpace` from `Definition_5_1_10`. The pushout is
-- formalized on the canonical `TopCat` pushout object.

section

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Proposition 5.2.4. If `A` is a closed subspace of the weak Hausdorff space `X` and
`f : A → Y` is continuous into the weak Hausdorff space `Y`, then the pushout
`pushout (TopCat.ofHom f) (TopCat.subtypeInclusion A)` representing `Y ∪_f X` is
weak Hausdorff. This isolates the weak Hausdorff bridge needed by the general colimit argument for
compactly generated spaces. -/
instance pushout_weaklyHausdorffSpace_of_isClosed
    [WeaklyHausdorffSpace X] [WeaklyHausdorffSpace Y]
    (A : Set X) (hA : IsClosed A) (f : C(A, Y)) :
    WeaklyHausdorffSpace.{u, u}
      (pushout (TopCat.ofHom f) (TopCat.subtypeInclusion A) : TopCat) := by
  sorry

/-- Proposition 5.2.4. If `X` and `Y` are compactly generated in the textbook sense,
`A` is a closed subspace of `X`, and `f : A → Y` is continuous, then the pushout
`pushout (TopCat.ofHom f) (TopCat.subtypeInclusion A)` representing `Y ∪_f X` is
compactly generated in the same sense. This is the source-facing specialization of the Chapter 5
colimit closure result to a pushout along a closed subspace inclusion. -/
instance pushout_compactlyGeneratedWeakHausdorffSpace_of_isClosed
    [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    [CompactlyGeneratedWeakHausdorffSpace.{u, u} Y]
    (A : Set X) (hA : IsClosed A) (f : C(A, Y)) :
    CompactlyGeneratedWeakHausdorffSpace.{u, u}
      (pushout (TopCat.ofHom f) (TopCat.subtypeInclusion A) : TopCat) := by
  let _ : UCompactlyGeneratedSpace A := Subtype.uCompactlyGeneratedSpace hA
  let _ : CompactlyGeneratedWeakHausdorffSpace A :=
    instCompactlyGeneratedWeakHausdorffSpace A
  let _ :
      ∀ j,
        CompactlyGeneratedWeakHausdorffSpace.{u, u}
          ((span (TopCat.ofHom f) (TopCat.subtypeInclusion A)).obj j) :=
    fun j ↦
      match j with
      | WalkingSpan.zero => by
          change CompactlyGeneratedWeakHausdorffSpace.{u, u} A
          exact instCompactlyGeneratedWeakHausdorffSpace A
      | WalkingSpan.left => by
          change CompactlyGeneratedWeakHausdorffSpace.{u, u} Y
          exact ‹CompactlyGeneratedWeakHausdorffSpace Y›
      | WalkingSpan.right => by
          change CompactlyGeneratedWeakHausdorffSpace.{u, u} X
          exact ‹CompactlyGeneratedWeakHausdorffSpace X›
  let _ : WeaklyHausdorffSpace
      (colimit (span (TopCat.ofHom f) (TopCat.subtypeInclusion A)) : TopCat) := by
    simpa [pushout] using
      (pushout_weaklyHausdorffSpace_of_isClosed A hA f :
        WeaklyHausdorffSpace
          (pushout (TopCat.ofHom f) (TopCat.subtypeInclusion A) : TopCat))
  simpa [pushout] using
    (instCompactlyGeneratedWeakHausdorffSpaceColimitOfWeaklyHausdorff
        (span (TopCat.ofHom f) (TopCat.subtypeInclusion A)) :
      CompactlyGeneratedWeakHausdorffSpace.{u, u} (colimit (span (TopCat.ofHom f)
        (TopCat.subtypeInclusion A)) : TopCat))

end
