import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.RealProjectiveSpace
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.IntegralSingularHomology
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Problem_21_6_6

open scoped Manifold Topology
open Topology.IsEmbedding

noncomputable section

-- Chapter 13 already fixes `integralSingularHomology`, while Chapter 21 already fixes the
-- boundary owner `manifoldBoundary 3 M`, the orientability surface
-- `Nonempty (ROrientedManifoldWithBoundary ℤ 3 M)`, and the reusable sphere-component predicate
-- `boundaryComponentIsTwoSphere`.

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]

/-- The boundary component of `∂M` through `x` is homeomorphic to `RealProjectiveSpace 2`. -/
def boundaryComponentIsRealProjectivePlane (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] (x : manifoldBoundary 3 M) : Prop :=
  Nonempty ((connectedComponent x : Set (manifoldBoundary 3 M)) ≃ₜ RealProjectiveSpace 2)

namespace boundaryComponentIsRealProjectivePlane

/-- Rewriting a boundary-point `RealProjectiveSpace 2` component statement for an ambient point
`x ∈ ∂M` recovers the equivalent `connectedComponentIn` formulation. -/
theorem iff_connectedComponentIn (x : M) (hx : x ∈ manifoldBoundary 3 M) :
    boundaryComponentIsRealProjectivePlane M ⟨x, hx⟩ ↔
      Nonempty (connectedComponentIn (manifoldBoundary 3 M) x ≃ₜ RealProjectiveSpace 2) := by
  let xBoundary : manifoldBoundary 3 M := ⟨x, hx⟩
  let e : connectedComponent xBoundary ≃ₜ connectedComponentIn (manifoldBoundary 3 M) x :=
    (subtypeVal.homeomorphImage (connectedComponent xBoundary)).trans
      (Homeomorph.setCongr (connectedComponentIn_eq_image hx).symm)
  constructor
  · rintro ⟨h⟩
    exact ⟨e.symm.trans h⟩
  · rintro ⟨h⟩
    exact ⟨e.trans h⟩

end boundaryComponentIsRealProjectivePlane

/-- Problem 21.6.8. If a nonorientable `3`-manifold `M` has boundary with no components
homeomorphic to `S^2` or `RealProjectiveSpace 2`, then its first integral singular homology group
`H₁(M; ℤ)` is infinite. In this source-facing formalization, the Chapter 21 compact connected
manifold convention is made explicit by `[CompactSpace M]` and `[ConnectedSpace M]`,
nonorientability is recorded by the canonical with-boundary owner
`¬ Nonempty (ROrientedManifoldWithBoundary ℤ 3 M)`, and the boundary hypotheses are stated with
the reusable boundary-component predicates. -/
theorem firstIntegralSingularHomology_infinite_of_nonorientable_boundary
    [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
    [IsManifold (𝓡∂ 3) 3 M]
    (h_nonorientable : ¬ Nonempty (ROrientedManifoldWithBoundary ℤ 3 M))
    (h_noSphere : ∀ x : manifoldBoundary 3 M, ¬ boundaryComponentIsTwoSphere M x)
    (h_noProjectivePlane : ∀ x : manifoldBoundary 3 M,
      ¬ boundaryComponentIsRealProjectivePlane M x) :
    Infinite (integralSingularHomology 1 (TopCat.of M)) := by
  sorry
