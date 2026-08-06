import Mathlib.Geometry.Manifold.Instances.Real

-- Semantic recall via `lean_leansearch`: the source-facing owner for a topological manifold with
-- boundary is the charted-space structure with half-space charts,
-- `ChartedSpace (EuclideanHalfSpace n) M`. The corresponding half-space model `𝓡∂ n` then
-- supplies the canonical boundary-point predicate and boundary set, while any stronger `C^r`
-- structure is recorded separately by `IsManifold (𝓡∂ n) r M`.

open scoped Manifold

universe u

variable {m : ℕ}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (m + 1)) M]
variable {r : WithTop ℕ∞}

/- Definition 21.3.1. A manifold with boundary is first of all a space locally modeled on the
half-space `EuclideanHalfSpace (m + 1)`, formalized here by the charted-space owner
`ChartedSpace (EuclideanHalfSpace (m + 1)) M`. Relative to the canonical half-space model
`𝓡∂ (m + 1)`, boundary points are those satisfying `(𝓡∂ (m + 1)).IsBoundaryPoint`, and the
boundary itself is the set `(𝓡∂ (m + 1)).boundary M`. If one later equips this charted space with
`C^r` transition compatibility, the stronger smooth/analytic structure is recorded separately by
`IsManifold (𝓡∂ (m + 1)) r M`. The positive index `m + 1` is only the library mechanism that
supplies the required `NeZero` instance for the half-space model. The theorem
`frontier_range_modelWithCornersEuclideanHalfSpace` identifies the frontier of the model range
with the boundary hyperplane. -/
#check (ChartedSpace (EuclideanHalfSpace (m + 1)) M)
#check (IsManifold (𝓡∂ (m + 1)) r M : Prop)
#check ((𝓡∂ (m + 1)).IsBoundaryPoint : M → Prop)
#check ((𝓡∂ (m + 1)).boundary M : Set M)
#check frontier_range_modelWithCornersEuclideanHalfSpace (m + 1)
