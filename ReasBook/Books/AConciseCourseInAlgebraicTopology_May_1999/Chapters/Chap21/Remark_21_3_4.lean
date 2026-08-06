import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Proposition_21_3_2

open scoped Manifold

noncomputable section

-- Semantic recall via `lean_leansearch`: no canonical theorem for the homological constraints
-- inherited by the boundary of a compact odd-dimensional manifold with boundary surfaced in the
-- current environment. Chapter 21 already exposes the concrete Euler-characteristic identity
-- `manifoldEulerCharacteristic_boundary_eq_two_mul_of_oddDimension`, so this remark is recorded
-- through that proposition, with the parity statement below kept only as a companion corollary.

section

/- Remark 21.3.4. Boundary manifolds inherit homological constraints from the relative duality of
the bounding manifold. In this chapter, Proposition 21.3.2 records one concrete such consequence
through the identity
`manifoldEulerCharacteristic K ((modelWithCornersEuclideanHalfSpace (2 * m + 1)).boundary W) =
  2 * manifoldEulerCharacteristic K W`.

The theorem below is kept only as the corresponding parity corollary, not as the main labeled
surface of the remark. -/
#check manifoldEulerCharacteristic_boundary_eq_two_mul_of_oddDimension

/-- A parity consequence of Proposition 21.3.2 for a compact odd-dimensional manifold with
boundary. Here `∂W` is formalized by the Chapter 21 boundary owner
`manifoldBoundary (2 * m + 1) W`, and `χ(-)` is `manifoldEulerCharacteristic K (-)`. -/
theorem even_manifoldEulerCharacteristic_boundary_of_oddDimension
    (K : Type) [Field K] (m : ℕ)
    {W : Type} [TopologicalSpace W] [T2Space W] [SecondCountableTopology W]
    [ChartedSpace (EuclideanHalfSpace (2 * m + 1)) W] [CompactSpace W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (2 * m + 1)) (2 * m + 1) W] :
    Even (manifoldEulerCharacteristic K (manifoldBoundary (2 * m + 1) W)) := by
  rw [manifoldEulerCharacteristic_boundary_eq_two_mul_of_oddDimension K m]
  exact even_two_mul (manifoldEulerCharacteristic K W)

end
