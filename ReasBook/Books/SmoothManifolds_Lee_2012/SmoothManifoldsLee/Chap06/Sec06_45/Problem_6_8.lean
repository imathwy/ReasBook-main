import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap06.Sec06_43.Theorem_6_26

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

-- Domain sampling pass:
-- * primary domain: Whitney approximation and proper maps between smooth manifolds.
-- * source-facing layer: Problem 6-8 strengthens the chapter's Whitney approximation theorem by
--   requiring the approximating smooth map to remain proper.
-- * core/canonical owners reused here: `IsProperMap`, `ContMDiffMap`, and
--   `ContinuousMap.Homotopic`.
-- * primitive data: a continuous map `F : C(N, M)` together with `IsProperMap (F : N → M)`.
-- * derived API: the existence of a smooth map `G` homotopic to `F` that is again proper.

universe uN uM

section

variable {n m : ℕ}
variable {N : Type uN} [TopologicalSpace N] [SmoothManifoldWithBoundary n N]
variable {M : Type uM} [TopologicalSpace M] [TopologicalManifold m M]
  [IsManifold (𝓡 m) ∞ M]

/-- Problem 6-8: every proper continuous map between smooth manifolds is homotopic to a proper
smooth map. Here the source manifold may have boundary, as in Theorem 6.26, while the target is
a smooth manifold without boundary. -/
theorem exists_homotopic_to_proper_smooth_map_of_isProperMap
    (F : C(N, M)) (hFproper : IsProperMap (F : N → M)) :
    ∃ G : C^∞⟮leeBoundaryModelWithCorners n, N; 𝓡 m, M⟯,
      ContinuousMap.Homotopic F (G : C(N, M)) ∧ IsProperMap (G : N → M) := sorry

end
