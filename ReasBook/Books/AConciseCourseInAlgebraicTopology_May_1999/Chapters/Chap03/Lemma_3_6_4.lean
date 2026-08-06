import Mathlib.CategoryTheory.Groupoid.VertexGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Construction_3_6_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory
open QuotientGroup

variable {B : Type u} [Groupoid.{v} B]

/-- Lemma 3.6.4 (1): the source-facing orbit covering `orbitSubgroupCovering b H : E(G/H) ⥤ B`
is a covering functor. -/
theorem orbitSubgroupCovering_isCovering
    (b : B) [IsConnected B] (H : O(End b)) :
    Functor.IsCovering (orbitSubgroupCovering b H) := by
  simpa [orbitSubgroupCovering] using
    orbitCategoryAssociatedAction_elements_isCovering b H

/-- Lemma 3.6.4 (2): at the canonical object `e = H`, a loop at `b` lies in the image subgroup
of the vertex group under the covering projection exactly when it lies in `H`. -/
theorem orbitSubgroupCovering_basepoint_mem_mapVertexGroup_range_iff_mem (b : B)
    (H : O(End b)) (γ : End b) :
    γ ∈ (Functor.mapVertexGroup
      (orbitSubgroupCovering b H) (orbitSubgroupCoveringBasepoint b H)).range ↔ γ ∈ H := by
  simpa [MonoidHom.mem_range, orbitSubgroupCoveringBasepoint] using
    (exists_orbitSubgroupCoveringHom_iff b H (𝟙 b) (𝟙 b) γ)
