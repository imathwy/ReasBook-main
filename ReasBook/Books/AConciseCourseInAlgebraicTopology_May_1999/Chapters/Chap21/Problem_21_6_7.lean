import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Problem_21_6_6

open scoped Manifold Topology

noncomputable section

-- Chapter 13 already fixes `integralSingularHomology`, and Proposition 21.4.2 already fixes the
-- Chapter 21 boundary owner `manifoldBoundary 3 M` together with the canonical orientability
-- surface `Nonempty (ROrientedManifoldWithBoundary ℤ 3 M)`.

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]

/-- If an orientable compact connected `3`-manifold with boundary has nonempty boundary and no
boundary component homeomorphic to `S^2`, then `H₁(M; ℤ)` is not zero. This is the reusable
contrapositive form of Problem 21.6.6. -/
theorem firstIntegralSingularHomology_not_isZero_of_orientable_boundary
    [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
    [IsManifold (𝓡∂ 3) 3 M]
    (h_orientable : Nonempty (ROrientedManifoldWithBoundary ℤ 3 M))
    (h_boundary : Set.Nonempty (manifoldBoundary 3 M))
    (h_noSphere : ∀ x : manifoldBoundary 3 M, ¬ boundaryComponentIsTwoSphere M x) :
    ¬ CategoryTheory.Limits.IsZero (integralSingularHomology 1 (TopCat.of M)) := by
  intro hH1
  rcases h_boundary with ⟨x, hx⟩
  exact h_noSphere ⟨x, hx⟩
    (boundaryComponent_homeomorphic_sphere_of_orientable_of_h1Zero h_orientable hH1 ⟨x, hx⟩)

/-- Problem 21.6.7. If an orientable `3`-manifold `M` has nonempty boundary and no boundary
component homeomorphic to `S^2`, then its first integral singular homology group `H₁(M; ℤ)` is
infinite. In this source-facing formalization, the Chapter 21 compact connected manifold
convention is made explicit by `[CompactSpace M]` and `[ConnectedSpace M]`, and orientability is
recorded by the canonical owner `Nonempty (ROrientedManifoldWithBoundary ℤ 3 M)`. The boundary
hypothesis is stated with the reusable predicate `boundaryComponentIsTwoSphere`. -/
theorem firstIntegralSingularHomology_infinite_of_orientable_boundary
    [T2Space M] [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
    [IsManifold (𝓡∂ 3) 3 M]
    (h_orientable : Nonempty (ROrientedManifoldWithBoundary ℤ 3 M))
    (h_boundary : Set.Nonempty (manifoldBoundary 3 M))
    (h_noSphere : ∀ x : manifoldBoundary 3 M, ¬ boundaryComponentIsTwoSphere M x) :
    Infinite (integralSingularHomology 1 (TopCat.of M)) := by
  have h_nonzero :
      ¬ CategoryTheory.Limits.IsZero (integralSingularHomology 1 (TopCat.of M)) :=
    firstIntegralSingularHomology_not_isZero_of_orientable_boundary
      h_orientable h_boundary h_noSphere
  sorry
