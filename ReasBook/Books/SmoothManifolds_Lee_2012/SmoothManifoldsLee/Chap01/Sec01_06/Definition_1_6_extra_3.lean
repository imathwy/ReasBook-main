import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Instances.Real

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Manifold Topology

section

universe uM

variable {n : ℕ} [NeZero n]
variable {M : Type uM} [TopologicalSpace M]

/-- Euclidean half-space inherits its metric structure from the ambient Euclidean space. -/
noncomputable instance : PseudoMetricSpace (EuclideanHalfSpace n) :=
  show PseudoMetricSpace { x : EuclideanSpace ℝ (Fin n) // 0 ≤ x 0 } from inferInstance

variable [ChartedSpace (EuclideanHalfSpace n) M]
variable [IsManifold (𝓡∂ n) (⊤ : WithTop ℕ∞) M]

/-- A smooth coordinate half-ball is the source of a smooth coordinate map whose image is an open
metric ball in the model half-space. -/
def IsSmoothCoordinateHalfBall (n : ℕ) [NeZero n] {M : Type uM} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : WithTop ℕ∞) M] (B : Set M) : Prop :=
  ∃ φ : OpenPartialHomeomorph M (EuclideanHalfSpace n),
    φ ∈ IsManifold.maximalAtlas (𝓡∂ n) (⊤ : WithTop ℕ∞) M ∧
      φ.source = B ∧
        ∃ r : ℝ, 0 < r ∧ φ.target = Metric.ball (0 : EuclideanHalfSpace n) r

/-- Definition 1.6-extra-3: a regular coordinate half-ball is a subset whose closure lies in the
source of a smooth coordinate map sending the subset to an open half-ball, its closure to the
corresponding closed half-ball, and the whole source to a larger open half-ball. -/
def IsRegularCoordinateHalfBall (n : ℕ) [NeZero n] {M : Type uM} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : WithTop ℕ∞) M] (B : Set M) : Prop :=
  ∃ chart : OpenPartialHomeomorph M (EuclideanHalfSpace n),
    chart ∈ IsManifold.maximalAtlas (𝓡∂ n) (⊤ : WithTop ℕ∞) M ∧
      closure B ⊆ chart.source ∧
        ∃ outerRadius innerRadius : ℝ,
          0 < innerRadius ∧
          innerRadius < outerRadius ∧
          chart '' B = Metric.ball (0 : EuclideanHalfSpace n) innerRadius ∧
          chart '' closure B = Metric.closedBall (0 : EuclideanHalfSpace n) innerRadius ∧
          chart.target = Metric.ball (0 : EuclideanHalfSpace n) outerRadius

/-- A regular coordinate half-ball sits inside a surrounding smooth coordinate half-ball. -/
-- Proof sketch: unpack the regular-coordinate-half-ball witness and use the same coordinate map,
-- with source `φ.source` and radius `r'`, to witness the surrounding smooth coordinate half-ball.
theorem IsRegularCoordinateHalfBall.exists_smoothCoordinateHalfBall_superset {B : Set M}
    (hB : IsRegularCoordinateHalfBall n B) :
    ∃ B' : Set M, IsSmoothCoordinateHalfBall n B' ∧ closure B ⊆ B' := sorry

end
