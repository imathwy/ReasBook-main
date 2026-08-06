import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Definition_1_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.ProofStep_2_7_9.IntersectionClosedSubcover

universe u v

open TopologicalSpace.IsOpenCover
open TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections
open unitInterval
open scoped IntersectionClosedSubcover

variable {ι : Type v} {X : Type u} [TopologicalSpace X]

/-- ProofStep 2.7.9 (1): every loop in the general cover case has image in a finite stage union
`U[O, S]` coming from a nonempty finite subcover `S` of `O` that is itself closed under nonempty
finite intersections. -/
-- Proof sketch: the unit interval is compact, so the image of a loop is compact. Specialize the
-- compact-parameter-space stage theorem to the path parameter `0 : I`.
theorem loop_image_subset_finite_union_of_intersection_closed_subcover
    (O : ι → TopologicalSpace.Opens X)
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : ClosedUnderNonemptyFiniteIntersections O)
    {x : X} (γ : Path x x) :
    ∃ S : IntersectionClosedSubcover O,
      Set.range γ ⊆ U[O, S] := by
  simpa using compact_image_subset_finite_intersection_closed_union 0 O hO hinter γ.toContinuousMap

/-- ProofStep 2.7.9 (2): every homotopy between loops in the general cover case has image in a
finite stage union `U[O, S]` coming from a nonempty finite subcover `S` of `O` that is itself
closed under nonempty finite intersections. -/
-- Proof sketch: the square `I × I` is compact, so the image of the homotopy is compact.
-- Specialize the compact-parameter-space stage theorem to the parameter `(0, 0) : I × I`.
theorem homotopy_image_subset_finite_union_of_intersection_closed_subcover
    (O : ι → TopologicalSpace.Opens X)
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : ClosedUnderNonemptyFiniteIntersections O)
    {x : X} {γ₀ γ₁ : Path x x} (H : Path.Homotopy γ₀ γ₁) :
    ∃ S : IntersectionClosedSubcover O,
      Set.range H ⊆ U[O, S] := by
  simpa using
    compact_image_subset_finite_intersection_closed_union (0, 0) O hO hinter H.toContinuousMap
