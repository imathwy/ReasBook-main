import SmoothManifoldsLee.Chap03.Sec03_15.Proposition_3_15
import Mathlib.Geometry.Manifold.IsManifold.Basic

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold

universe uH uM

variable {n : ℕ}
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/- Definition 3.15-extra-2: the preferred coordinate basis at `p` is the chapter-level owner
`chart_coordinate_vectors_basis`, specialized to the preferred chart `chartAt H p`. -/
#check chart_coordinate_vectors_basis

/-- The preferred coordinate components of a tangent vector at `p`. -/
noncomputable def preferred_coordinate_components
    (p : M) (v : TangentSpace I p) : Fin n → ℝ :=
  (chart_coordinate_vectors_basis (chartAt H p) (IsManifold.chart_mem_maximalAtlas p) p
    (mem_chart_source H p)).repr v

/- The coordinate expansion of `v : TangentSpace I p` in preferred coordinates is the basis
representation for the canonical source-facing basis
`chart_coordinate_vectors_basis (chartAt H p) (IsManifold.chart_mem_maximalAtlas p) p
  (mem_chart_source H p)`. This keeps the preferred-coordinate API as derived data from the
chapter-level owner declaration rather than a parallel coordinate-trivialization wrapper. -/
