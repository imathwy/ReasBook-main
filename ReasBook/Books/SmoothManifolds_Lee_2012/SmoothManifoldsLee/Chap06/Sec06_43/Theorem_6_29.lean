import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap06.Sec06_43.Definition_6_43_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap06.Sec06_43.Theorem_6_26

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

-- Domain sampling pass:
-- * source-facing layer: smooth homotopies and their relative version on a closed subset.
-- * core/canonical owner in this chapter: `ContMDiffMap.SmoothHomotopy`, with the relative
--   relation `ContMDiffMap.SmoothlyHomotopicRel` derived from it.
-- * bridge/view owner: mathlib's `ContinuousMap.Homotopic` / `ContinuousMap.HomotopicRel` on the
--   underlying continuous maps.
-- Relevant declarations checked before refinement:
-- `ContMDiffMap.SmoothHomotopy`,
-- `ContMDiffMap.SmoothlyHomotopic`,
-- `ContinuousMap.HomotopyRel`,
-- `ContinuousMap.HomotopicRel`.

universe uN uM

section

variable {n m : ℕ}
variable {N : Type uN} [TopologicalSpace N] [SmoothManifoldWithBoundary n N]
variable {M : Type uM} [TopologicalSpace M] [TopologicalManifold m M]
  [IsManifold (𝓡 m) ∞ M]

/-- Theorem 6.29 (1). Suppose `N` is a smooth manifold with or without boundary, `M` is a smooth
manifold, and `F, G : N → M` are smooth maps. If `F` and `G` are homotopic, then they are
smoothly homotopic. -/
theorem smoothlyHomotopic_of_homotopic
    (F G : C^∞⟮leeBoundaryModelWithCorners n, N; 𝓡 m, M⟯)
    (hFG : (F : C(N, M)).Homotopic (G : C(N, M))) :
    ContMDiffMap.SmoothlyHomotopic F G := sorry

/-- Theorem 6.29 (2). If `F` and `G` are homotopic relative to a closed subset `A ⊆ N`, then
they are smoothly homotopic relative to `A`, i.e. they admit a smooth homotopy that is constant on
`A` throughout the interval. -/
theorem exists_smoothHomotopy_rel_of_homotopicRel
    (F G : C^∞⟮leeBoundaryModelWithCorners n, N; 𝓡 m, M⟯)
    {A : Set N} (hA : IsClosed A)
    (hFG : (F : C(N, M)).HomotopicRel (G : C(N, M)) A) :
    ContMDiffMap.SmoothlyHomotopicRel F G A := sorry

end
