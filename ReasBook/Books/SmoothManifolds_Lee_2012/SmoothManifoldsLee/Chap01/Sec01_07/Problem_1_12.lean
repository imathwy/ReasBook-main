import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Manifold

/- Problem 1-12 (source-facing via core/canonical owners): Lee asks for a proof of Proposition
1.45. The product manifold-with-boundary structure itself is the canonical `IsManifold.prod`
instance on `M × N`; when the left factor is boundaryless, the boundary formula is the canonical
`ModelWithCorners.boundary_of_boundaryless_left`. -/
section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
variable [IsManifold I (⊤ : WithTop ℕ∞) M] [IsManifold J (⊤ : WithTop ℕ∞) N]

variable [BoundarylessManifold I M]

/-- Problem 1-12: the canonical product smooth structure makes `M × N` into a smooth manifold
with boundary, and when the left factor is boundaryless its boundary is exactly `M × ∂N`. -/
theorem prod_boundaryless_left_isManifold_with_boundary :
    IsManifold (I.prod J) (⊤ : WithTop ℕ∞) (M × N) ∧
      (I.prod J).boundary (M × N) = (univ : Set M).prod (J.boundary N) := by
  constructor
  · -- The product smooth structure is the canonical manifold instance on `M × N`.
    infer_instance
  · -- Proposition 1.45 is exactly the boundary formula for a boundaryless left factor.
    exact ModelWithCorners.boundary_of_boundaryless_left

end
