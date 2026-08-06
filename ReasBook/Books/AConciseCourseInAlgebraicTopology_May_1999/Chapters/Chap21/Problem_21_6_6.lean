import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Category.TopCat.Sphere
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.IntegralSingularHomology
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Proposition_21_4_2

open scoped Manifold Topology
open Topology.IsEmbedding

noncomputable section

-- Chapter 13 already fixes `integralSingularHomology`, and Proposition 21.4.2 already fixes the
-- Chapter 21 boundary owner `manifoldBoundary 3 M` together with the canonical orientability owner
-- `ROrientedManifoldWithBoundary ℤ 3 M`.

/-- The boundary component of `∂M` through `x` is homeomorphic to `S^2`. -/
def boundaryComponentIsTwoSphere (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] (x : manifoldBoundary 3 M) : Prop :=
  Nonempty ((connectedComponent x : Set (manifoldBoundary 3 M)) ≃ₜ TopCat.sphere.{0} 2)

section

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]

/-- Rewriting a boundary-point `S^2` component statement for an ambient point `x ∈ ∂M` recovers
the equivalent `connectedComponentIn` formulation. -/
theorem boundaryComponentIsTwoSphere_iff_connectedComponentIn_homeomorphic_sphere
    (x : M) (hx : x ∈ manifoldBoundary 3 M) :
    boundaryComponentIsTwoSphere M ⟨x, hx⟩ ↔
      Nonempty (connectedComponentIn (manifoldBoundary 3 M) x ≃ₜ TopCat.sphere.{0} 2) := by
  let xBoundary : manifoldBoundary 3 M := ⟨x, hx⟩
  let e : connectedComponent xBoundary ≃ₜ connectedComponentIn (manifoldBoundary 3 M) x :=
    (subtypeVal.homeomorphImage (connectedComponent xBoundary)).trans
      (Homeomorph.setCongr (connectedComponentIn_eq_image hx).symm)
  constructor
  · rintro ⟨h⟩
    exact ⟨e.symm.trans h⟩
  · rintro ⟨h⟩
    exact ⟨e.trans h⟩

end

section

variable {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [CompactSpace M] [ConnectedSpace M]
variable [ChartedSpace (EuclideanHalfSpace 3) M]
variable [IsManifold (𝓡∂ 3) 3 M]

/-- Problem 21.6.6: if an orientable `3`-manifold `M` has `H₁(M; ℤ) = 0`, then `∂M` is a
disjoint union of `2`-spheres. Here orientability is expressed by the canonical Chapter 21
with-boundary owner `Nonempty (ROrientedManifoldWithBoundary ℤ 3 M)`, the compact connected
manifold convention is made explicit by `[CompactSpace M] [ConnectedSpace M]`, and the conclusion
is formalized by requiring each connected component of the boundary subtype `∂M` to be
homeomorphic to `TopCat.sphere 2`. -/
theorem boundaryComponent_homeomorphic_sphere_of_orientable_of_h1Zero
    (h_orientable : Nonempty (ROrientedManifoldWithBoundary ℤ 3 M))
    (hH1 : CategoryTheory.Limits.IsZero (integralSingularHomology 1 (TopCat.of M)))
    (x : manifoldBoundary 3 M) :
    boundaryComponentIsTwoSphere M x := by
  sorry

/-- Ambient-point version of Problem 21.6.6, restated with `connectedComponentIn` on the boundary
subset `∂M`. -/
theorem boundaryComponentIn_homeomorphic_sphere_of_orientable_of_h1Zero
    (h_orientable : Nonempty (ROrientedManifoldWithBoundary ℤ 3 M))
    (hH1 : CategoryTheory.Limits.IsZero (integralSingularHomology 1 (TopCat.of M)))
    (x : M) (hx : x ∈ manifoldBoundary 3 M) :
    Nonempty (connectedComponentIn (manifoldBoundary 3 M) x ≃ₜ TopCat.sphere.{0} 2) := by
  rw [← boundaryComponentIsTwoSphere_iff_connectedComponentIn_homeomorphic_sphere x hx]
  exact boundaryComponent_homeomorphic_sphere_of_orientable_of_h1Zero h_orientable hH1 ⟨x, hx⟩

end
