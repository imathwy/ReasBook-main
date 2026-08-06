import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Proposition_21_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.ManifoldBoundary

open scoped Manifold

noncomputable section

-- Semantic recall via `lean_leansearch` did not surface a ready-made theorem for the Euler
-- characteristic of the boundary of a compact odd-dimensional manifold with boundary. This file
-- therefore uses the chapter-local owner `manifoldEulerCharacteristic` together with the
-- Chapter 21 boundary owner `manifoldBoundary n W`.

section

/-- Proposition 21.3.2. If `W` is a compact manifold with boundary of dimension `2 * m + 1`, then
the Euler characteristic of its boundary `∂W` is twice the Euler characteristic of `W`. In this
file, `∂W` is formalized by the Chapter 21 boundary owner
`manifoldBoundary (2 * m + 1) W`; for a chosen field `K`, `χ(-)` is formalized by
`manifoldEulerCharacteristic K (-)`. -/
theorem manifoldEulerCharacteristic_boundary_eq_two_mul_of_oddDimension
    (K : Type) [Field K] (m : ℕ)
    {W : Type} [TopologicalSpace W] [T2Space W] [SecondCountableTopology W]
    [ChartedSpace (EuclideanHalfSpace (2 * m + 1)) W] [CompactSpace W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (2 * m + 1)) (2 * m + 1) W] :
    manifoldEulerCharacteristic K (manifoldBoundary (2 * m + 1) W) =
      2 * manifoldEulerCharacteristic K W := sorry

end
