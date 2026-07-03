import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Topology.Covering.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_4_41 (from Chap04/Sec04_26) -/
open scoped Manifold ContDiff

universe u v

section

variable {n : ℕ} {M : Type u} {E : Type v}
variable [TopologicalSpace M] [SmoothManifoldWithBoundary n M]
variable [TopologicalSpace E] (π : E → M)

local notation "I" => leeBoundaryModelWithCorners n

namespace SmoothManifoldWithBoundary

variable {π : E → M}
variable [SmoothManifoldWithBoundary n E]

/-- A smooth map between smooth manifolds with boundary that is also a covering projection is a
smooth local diffeomorphism. This is the bridge from the source-facing structure on the total
space to the canonical local-diffeomorphism API used below. -/
theorem isLocalDiffeomorph (hπsmooth : ContMDiff I I ∞ π) (hπ : IsCoveringMap π) :
    IsLocalDiffeomorph I I ∞ π := by
  sorry

/-- If the covering projection is surjective, the induced smooth boundary covering is a smooth
covering map in Lee's sense. -/
theorem isSmoothCoveringMap (hπsmooth : ContMDiff I I ∞ π) (hπ : IsCoveringMap π)
    (h_surj : Function.Surjective π) :
    Manifold.IsSmoothCoveringMap I I π := by
  exact ⟨hπ, h_surj, isLocalDiffeomorph hπsmooth hπ⟩

end SmoothManifoldWithBoundary

-- Proof sketch: In evenly covered neighborhoods, `π` is a local homeomorphism identifying the
-- lifted charts on `E` with the boundary charts on `M`. This preserves whether a chart point lies
-- in the frontier of the model boundary, so boundary points of `E` are exactly the points lying
-- over boundary points of `M`.
/-- Proposition 4.41 (2): For any lifted smooth manifold-with-boundary structure on the covering
space, the boundary of the total space is the preimage of the boundary of the base. -/
theorem preimage_boundary_eq_boundary_of_smooth_boundary_covering_structure
    [SmoothManifoldWithBoundary n E] (hπ : IsCoveringMap π) (hπsmooth : ContMDiff I I ∞ π) :
    π ⁻¹' (leeBoundaryModelWithCorners n).boundary M =
      (leeBoundaryModelWithCorners n).boundary E := by
  simpa using
    (SmoothManifoldWithBoundary.isLocalDiffeomorph hπsmooth hπ).preimage_boundary (by simp)

section Existence

variable [ConnectedSpace M]

/- A smooth manifold-with-boundary structure on the total space of a cover has the expected
boundary behavior if the covering projection becomes a smooth map for that structure. -/
-- Proof sketch: Use evenly covered neighborhoods in `M` and the preferred boundary charts on `M`
-- to pull back a `leeBoundaryModelWithCorners n`-charted atlas to `E`. The lifted charts are
-- smooth because a covering map is locally a homeomorphism, so the pulled-back atlas gives a
-- smooth manifold-with-boundary structure for which `π` is smooth.
/-- Proposition 4.41 (1): A topological covering of a connected smooth manifold with boundary,
with second-countable total space, admits a smooth manifold-with-boundary structure on the total
space for which the projection is a smooth covering map. -/
theorem exists_smooth_boundary_covering_structure
    [SecondCountableTopology E] (hπ : IsCoveringMap π) (h_surj : Function.Surjective π) :
    ∃ s : SmoothManifoldWithBoundary n E,
      let _ : SmoothManifoldWithBoundary n E := s
      Manifold.IsSmoothCoveringMap I I π := sorry

-- Proof sketch: Any two compatible smooth structures on `E` are locally obtained by pulling back
-- the same boundary charts on `M` through the same covering map. This determines the maximal smooth
-- atlas, not the concrete `ChartedSpace` owner data stored in a structure instance.
/-- Proposition 4.41 (3): The smooth manifold-with-boundary structure on the covering space is
unique in the sense of inducing a unique maximal smooth atlas. -/
theorem exists_unique_smooth_boundary_covering_structure
    [SecondCountableTopology E] (hπ : IsCoveringMap π) (h_surj : Function.Surjective π) :
    ∃ s : SmoothManifoldWithBoundary n E,
      let _ : SmoothManifoldWithBoundary n E := s
      Manifold.IsSmoothCoveringMap I I π ∧
        ∀ s' : SmoothManifoldWithBoundary n E,
          (let _ : SmoothManifoldWithBoundary n E := s'
           Manifold.IsSmoothCoveringMap I I π) →
            (let _ : SmoothManifoldWithBoundary n E := s
             IsManifold.maximalAtlas I ∞ E) =
            (let _ : SmoothManifoldWithBoundary n E := s'
             IsManifold.maximalAtlas I ∞ E) := sorry

end Existence
end
