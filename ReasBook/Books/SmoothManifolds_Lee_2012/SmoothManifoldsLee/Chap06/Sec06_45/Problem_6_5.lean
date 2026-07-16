import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap06.Sec06_42.Proposition_6_25

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold NormalBundle

section TubularNeighborhoodClosestPoint

variable {n m : ℕ}
variable {M : Set (EuclideanSpace ℝ (Fin n))}
variable [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
variable [IsManifold (𝓡 m) ∞ M]
variable [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M]

-- Domain sampling pass:
-- * primary domain: embedded submanifolds, tubular neighborhoods, and minimizers of distance.
-- * relevant owner declarations checked before refinement:
--   `NM[n, m; M]`,
--   `NormalBundle.TubularNeighborhood`,
--   `NormalBundle.TubularNeighborhood.retraction`,
--   `embedded_submanifold_has_tubular_neighborhood`,
--   `IsMinOn`,
--   and `isMinOn_univ_iff`.
-- * source/core/bridge triage:
--   the source-facing content here is the closest-point characterization of the tubular
--   retraction; the core owners are `NormalBundle.TubularNeighborhood n m M` for the tubular data
--   and `IsMinOn` for the minimization statement; `isMinOn_univ_iff` is the thin bridge to the
--   textbook pointwise inequality on the subtype `M`.
/-- Problem 6-5: every embedded submanifold `M ⊆ ℝ^n` has a tubular neighborhood `T` such that the
retraction `r : T.neighborhood → M` from Proposition 6.25 picks out the unique point of `M`
closest to each point `y ∈ T.neighborhood`. Equivalently, for each `y : T.neighborhood`, a point
`x : M` minimizes the distance from `y` to `M` if and only if `x = r y`. -/
theorem embedded_submanifold_has_tubular_neighborhood_with_unique_closest_point_retraction :
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M]),
      letI := cs
      ∃ hs : IsManifold (𝓡 n) ∞ (NM[n, m; M]),
      letI := hs
        ∃ T : NormalBundle.TubularNeighborhood n m M,
          ∀ y : T.neighborhood, ∀ x : M,
            IsMinOn
                (fun z : M ↦
                  dist (y : EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin n)))
                Set.univ x ↔
              x = T.retraction y := sorry

end TubularNeighborhoodClosestPoint
