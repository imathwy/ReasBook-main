import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.ManifoldBoundary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Instances.Real

open scoped Manifold

-- Semantic recall via `lean_leansearch`: `ROrientedManifold` is the Chapter 20 owner for
-- `R`-orientations on boundaryless manifolds. This item keeps the with-boundary owner on the
-- ambient manifold `M` itself and records the source-facing boundary-chart bridge from the ambient
-- atlas to the induced boundary orientation.

/-- An `R`-orientation of an `n`-manifold with boundary, modeled on `𝓡∂ n`, is an atlas of local
top-homology trivializations on `M` itself. This mirrors the boundaryless owner
`ROrientedManifold`, but keeps the half-space manifold structure on the ambient manifold. When the
canonical boundary manifold structure on `∂M` is available, the owner records for each ambient
orientation chart its induced boundary chart, so Proposition 21.4.2 can build the boundary
`ROrientedManifold` from the image boundary atlas rather than from an unconstrained stored witness.
-/
class ROrientedManifoldWithBoundary (R : outParam (Type _)) [CommRing R] (n : outParam ℕ)
    [NeZero n] (M : Type _) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    extends IsManifold (𝓡∂ n) ⊤ M where
  atlas : Set (LocalTopHomologyTrivialization R n M)
  cover : ∀ x : M, ∃ U ∈ atlas, x ∈ U.domain
  pairwise_compatible :
    ∀ {U V : LocalTopHomologyTrivialization R n M},
      U ∈ atlas → V ∈ atlas → U.OrientationCompatible V
  boundaryChart :
      LocalTopHomologyTrivialization R n M →
        LocalTopHomologyTrivialization R (n - 1) (manifoldBoundary n M)
  boundaryChart_domain :
    ∀ {U : LocalTopHomologyTrivialization R n M}, U ∈ atlas →
      (boundaryChart U).domain = Subtype.val ⁻¹' U.domain
  boundaryChart_compatible :
    ∀ {U V : LocalTopHomologyTrivialization R n M},
      U ∈ atlas → V ∈ atlas →
        (boundaryChart U).OrientationCompatible (boundaryChart V)
  boundary_isManifold
      [ChartedSpace (EuclideanSpace ℝ (Fin (n - 1))) (manifoldBoundary n M)]
      [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n - 1))) = n - 1)] :
      IsManifold (𝓡 (n - 1)) ⊤ (manifoldBoundary n M)

namespace ROrientedManifoldWithBoundary

section

variable {R : Type} [CommRing R]
variable {n : ℕ} [NeZero n]
variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]

/-- The atlas of an `R`-oriented manifold with boundary covers the ambient manifold. -/
theorem cover_apply {x : M} [h : ROrientedManifoldWithBoundary R n M] :
    ∃ U ∈ h.atlas, x ∈ U.domain :=
  h.cover x

/-- Charts in the atlas of an `R`-oriented manifold with boundary are pairwise compatible on
overlaps. -/
theorem atlas_pairwiseCompatible {U V : LocalTopHomologyTrivialization R n M}
    [h : ROrientedManifoldWithBoundary R n M] (hU : U ∈ h.atlas) (hV : V ∈ h.atlas) :
    U.OrientationCompatible V :=
  h.pairwise_compatible hU hV

/-- The boundary chart induced from an ambient orientation chart has domain equal to the boundary
part of the ambient chart domain. -/
theorem boundaryChart_domain_eq [h : ROrientedManifoldWithBoundary R n M]
    {U : LocalTopHomologyTrivialization R n M} (hU : U ∈ h.atlas) :
    (h.boundaryChart U).domain = Subtype.val ⁻¹' U.domain :=
  h.boundaryChart_domain hU

/-- The induced boundary atlas is the image of the ambient orientation atlas under
`ROrientedManifoldWithBoundary.boundaryChart`. -/
def boundaryAtlas [h : ROrientedManifoldWithBoundary R n M] :
    Set (LocalTopHomologyTrivialization R (n - 1) (manifoldBoundary n M)) :=
  h.boundaryChart '' h.atlas

/-- Membership in the induced boundary atlas means that the chart is the boundary chart attached to
some ambient orientation chart. -/
@[simp] theorem mem_boundaryAtlas_iff [h : ROrientedManifoldWithBoundary R n M]
    {V : LocalTopHomologyTrivialization R (n - 1) (manifoldBoundary n M)} :
    V ∈ boundaryAtlas ↔
      ∃ U ∈ h.atlas, h.boundaryChart U = V :=
  Iff.rfl

/-- Every ambient atlas chart contributes its induced boundary chart to the boundary atlas. -/
theorem boundaryChart_mem_boundaryAtlas [h : ROrientedManifoldWithBoundary R n M]
    {U : LocalTopHomologyTrivialization R n M} (hU : U ∈ h.atlas) :
    h.boundaryChart U ∈ boundaryAtlas :=
  ⟨U, hU, rfl⟩

/-- The induced boundary atlas covers `∂M`. -/
theorem boundaryAtlas_cover [h : ROrientedManifoldWithBoundary R n M] (x : manifoldBoundary n M) :
    ∃ V ∈ boundaryAtlas, x ∈ V.domain := by
  rcases h.cover x.1 with ⟨U, hU, hxU⟩
  refine ⟨h.boundaryChart U, boundaryChart_mem_boundaryAtlas hU, ?_⟩
  simpa [boundaryChart_domain_eq hU] using hxU

/-- Boundary charts induced from ambient orientation charts are pairwise compatible. -/
theorem boundaryAtlas_pairwiseCompatible [h : ROrientedManifoldWithBoundary R n M]
    {U V : LocalTopHomologyTrivialization R (n - 1) (manifoldBoundary n M)}
    (hU : U ∈ boundaryAtlas) (hV : V ∈ boundaryAtlas) :
    U.OrientationCompatible V := by
  rcases hU with ⟨U', hU', rfl⟩
  rcases hV with ⟨V', hV', rfl⟩
  exact h.boundaryChart_compatible hU' hV'

end

end ROrientedManifoldWithBoundary

section

variable {R : Type} [CommRing R]
variable {n : ℕ} [NeZero n]
variable {M : Type} [TopologicalSpace M] [CompactSpace M]
variable [ChartedSpace (EuclideanHalfSpace n) M]
variable [ROrientedManifoldWithBoundary R n M]

/-- The boundary of a compact `R`-oriented manifold with boundary is compact. -/
instance manifoldBoundaryCompactSpace : CompactSpace (manifoldBoundary n M) := by
  have hclosed : IsClosed (manifoldBoundary n M) := by
    simpa [manifoldBoundary] using
      (ModelWithCorners.isClosed_boundary (I := 𝓡∂ n) (n := ⊤) (M := M) (by simp))
  exact hclosed.isClosedEmbedding_subtypeVal.compactSpace

end

section

variable {R : Type} [CommRing R]
variable {n : ℕ} [NeZero n]
variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin (n - 1))) (manifoldBoundary n M)]
variable [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n - 1))) = n - 1)]

/-- Proposition 21.4.2. An `R`-orientation of `M` induces an `R`-orientation of `∂M`. In this
file, the ambient orientation is recorded by `ROrientedManifoldWithBoundary R n M`, and the
induced boundary orientation is built from the image boundary atlas
`ROrientedManifoldWithBoundary.boundaryAtlas`. -/
instance boundaryROrientedManifoldOfROrientedManifoldWithBoundary
    [h_oriented : ROrientedManifoldWithBoundary R n M] :
    ROrientedManifold R (𝓡 (n - 1)) (n - 1) (manifoldBoundary n M) :=
  { toIsManifold := h_oriented.boundary_isManifold
    atlas := ROrientedManifoldWithBoundary.boundaryAtlas
    cover := ROrientedManifoldWithBoundary.boundaryAtlas_cover
    pairwise_compatible :=
      ROrientedManifoldWithBoundary.boundaryAtlas_pairwiseCompatible }

/-- The canonical `R`-orientation induced on the boundary of an `R`-oriented manifold with
boundary. This is the term-level bridge to the instance
`boundaryROrientedManifoldOfROrientedManifoldWithBoundary`. -/
abbrev ROrientedManifoldWithBoundary.toBoundaryROrientedManifold
    (R : Type) [CommRing R] (n : ℕ) [NeZero n] (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M]
    [ROrientedManifoldWithBoundary R n M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n - 1))) (manifoldBoundary n M)]
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n - 1))) = n - 1)] :
    ROrientedManifold R (𝓡 (n - 1)) (n - 1) (manifoldBoundary n M) :=
  boundaryROrientedManifoldOfROrientedManifoldWithBoundary

/-- The canonical `R`-orientation induced on the boundary of an `(n + 1)`-dimensional
`R`-oriented manifold with boundary, stated in the source-facing successor form so the boundary
dimension is `n`. -/
abbrev ROrientedManifoldWithBoundary.toBoundaryROrientedManifoldSucc
    (R : Type) [CommRing R] (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [ROrientedManifoldWithBoundary R (n + 1) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) (manifoldBoundary (n + 1) M)]
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n)] :
    ROrientedManifold R (𝓡 n) n (manifoldBoundary (n + 1) M) :=
  by
    let _ :
        ChartedSpace (EuclideanSpace ℝ (Fin ((n + 1) - 1))) (manifoldBoundary (n + 1) M) := by
      change ChartedSpace (EuclideanSpace ℝ (Fin n)) (manifoldBoundary (n + 1) M)
      infer_instance
    let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin ((n + 1) - 1))) = (n + 1) - 1) := by
      change Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n)
      exact ⟨@finrank_euclideanSpace_fin ℝ _ n⟩
    simpa using
      (boundaryROrientedManifoldOfROrientedManifoldWithBoundary (R := R) (n := n + 1) (M := M))

end
