import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.ManifoldBoundary
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Proposition_21_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Proposition_21_3_2

open scoped Manifold

noncomputable section

-- This corollary is the parity split of two nearby Chapter 21 results: when `n` is even, apply
-- `manifoldEulerCharacteristic_boundary_eq_two_mul_of_oddDimension` to the ambient
-- `(n + 1)`-manifold;
-- when `n` is odd, view the boundary itself as a compact odd-dimensional manifold via the
-- Euclidean boundary-model bridge from `ManifoldBoundary` and apply
-- `manifoldEulerCharacteristic_eq_zero_of_oddDimension`.

/-- If a compact manifold-with-boundary has odd-dimensional boundary, then that boundary has Euler
characteristic zero. This applies `manifoldEulerCharacteristic_eq_zero_of_oddDimension` to the
canonical manifold structure on `∂[((2 * m + 1) + 1)] W`, that is, on the source-facing boundary
`∂W`. -/
theorem manifoldEulerCharacteristic_boundary_eq_zero_of_oddDimension
    (K : Type) [Field K] (m : ℕ)
    {W : Type} [TopologicalSpace W] [T2Space W] [SecondCountableTopology W]
    [ChartedSpace (EuclideanHalfSpace ((2 * m + 1) + 1)) W] [CompactSpace W]
    [IsManifold (𝓡∂ ((2 * m + 1) + 1)) ((2 * m + 1) + 1) W] :
    manifoldEulerCharacteristic K (∂[((2 * m + 1) + 1)] W) = 0 := by
  let n : ℕ := 2 * m + 1
  have h_boundaryAmbient :
      IsManifold (𝓡∂ (n + 1)) (((n : ℕ∞) + 1)) W := by
    simpa [n] using
      (‹IsManifold (𝓡∂ ((2 * m + 1) + 1)) ((2 * m + 1) + 1) W› :
        IsManifold (𝓡∂ ((2 * m + 1) + 1)) ((2 * m + 1) + 1) W)
  letI : IsManifold (𝓡∂ (n + 1)) (((n : ℕ∞) + 1)) W := h_boundaryAmbient
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = 2 * m + 1) := by
    refine ⟨?_⟩
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
    exact finrank_euclideanSpace_fin
  letI : CompactSpace (∂[n + 1] W) := ManifoldBoundary.boundaryCompactSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (∂[n + 1] W) :=
    ManifoldBoundary.boundaryEuclideanChartedSpace
  letI : IsManifold (𝓡 n) ⊤ (∂[n + 1] W) :=
    ManifoldBoundary.boundary_isManifold
  have h_zero : manifoldEulerCharacteristic K (∂[n + 1] W) = 0 := by
    exact manifoldEulerCharacteristic_eq_zero_of_oddDimension
      (K := K) (E := EuclideanSpace ℝ (Fin n)) (I := 𝓡 n)
      (M := ∂[n + 1] W) m
  simpa [n] using h_zero

/-- Corollary 21.3.3. If `M` is the boundary of a compact manifold, then `χ(M)` is even. Here the
boundary presentation is formalized by the scoped boundary notation `∂[n + 1] W` for the Chapter
21 boundary owner, written source-facing as `∂W` when the ambient dimension is clear, and `χ(-)`
is formalized by
`manifoldEulerCharacteristic K (-)`. -/
theorem even_manifoldEulerCharacteristic_boundary_of_compactManifold
    (K : Type) [Field K] (n : ℕ)
    {W : Type} [TopologicalSpace W] [T2Space W] [SecondCountableTopology W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] [CompactSpace W]
    [IsManifold (𝓡∂ (n + 1)) (n + 1) W] :
    Even (manifoldEulerCharacteristic K (∂[n + 1] W)) := by
  rcases Nat.even_or_odd (n + 1) with h_ambient_even | h_ambient_odd
  · have h_boundary_odd : Odd n := by
      exact Nat.not_even_iff_odd.1 (Nat.even_add_one.1 h_ambient_even)
    rcases h_boundary_odd with ⟨m, rfl⟩
    haveI : IsManifold (𝓡∂ ((2 * m + 1) + 1)) ((2 * m + 1) + 1) W := by
      simpa using
        (‹IsManifold (𝓡∂ ((2 * m + 1) + 1)) (((2 * m + 1 : ℕ∞) + 1)) W› :
          IsManifold (𝓡∂ ((2 * m + 1) + 1)) (((2 * m + 1 : ℕ∞) + 1)) W)
    rw [manifoldEulerCharacteristic_boundary_eq_zero_of_oddDimension K m]
    simp
  · rcases h_ambient_odd with ⟨m, hm⟩
    have hn : n = 2 * m := by
      omega
    subst n
    haveI : IsManifold (𝓡∂ (2 * m + 1)) (2 * (m : ℕ∞) + 1) W := by
      simpa using
        (‹IsManifold (𝓡∂ (2 * m + 1)) (2 * m + 1) W› :
          IsManifold (𝓡∂ (2 * m + 1)) (2 * m + 1) W)
    rw [manifoldEulerCharacteristic_boundary_eq_two_mul_of_oddDimension K m]
    exact even_two_mul (manifoldEulerCharacteristic K W)
