import SmoothManifolds_Lee_2012.Chap04.Sec04_26.Proposition_4_41

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold

universe uM uMtilde uM'

section

variable {n : ℕ}
variable {M : Type uM} [TopologicalSpace M] [SmoothManifoldWithBoundary n M]
variable [ConnectedSpace M]

local notation "I" => leeBoundaryModelWithCorners n

-- Semantic Lean search tool unavailable in this environment (`lean_leansearch` not present in
-- tool discovery); verified directly against `Corollary_4_43.lean` and `Proposition_4_41.lean`.
/-- Exercise 4.45: every connected smooth manifold with boundary admits a universal smooth
covering map from a simply connected smooth manifold with boundary, and any other simply
connected smooth covering of the same base is diffeomorphic to it over the base. -/
theorem exists_universal_smooth_covering_manifold_with_boundary :
    ∃ (Mtilde : Type uMtilde) (_ : TopologicalSpace Mtilde)
      (_ : SmoothManifoldWithBoundary n Mtilde) (π : Mtilde → M),
      Manifold.IsUniversalSmoothCoveringMap I I π ∧
        ∀ {M' : Type uM'} [TopologicalSpace M'] [SmoothManifoldWithBoundary n M']
          (π' : M' → M),
          Manifold.IsUniversalSmoothCoveringMap I I π' →
            ∃ Φ : Diffeomorph I I Mtilde M' (⊤ : WithTop ℕ∞), π' ∘ Φ = π := sorry

end
