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
def IsSmoothCoordinateHalfBall (B : Set M) : Prop :=
  ∃ φ : OpenPartialHomeomorph M (EuclideanHalfSpace n),
    φ ∈ IsManifold.maximalAtlas (𝓡∂ n) (⊤ : WithTop ℕ∞) M ∧
      φ.source = B ∧
        ∃ r : ℝ, 0 < r ∧ φ.target = Metric.ball (0 : EuclideanHalfSpace n) r

/-- Definition 1.6-extra-3: a regular coordinate half-ball is a subset whose closure lies in the
source of a smooth coordinate map sending the subset to an open half-ball, its closure to the
corresponding closed half-ball, and the whole source to a larger open half-ball. -/
structure IsRegularCoordinateHalfBall (B : Set M) where
  chart : OpenPartialHomeomorph M (EuclideanHalfSpace n)
  mem_maximalAtlas : chart ∈ IsManifold.maximalAtlas (𝓡∂ n) (⊤ : WithTop ℕ∞) M
  closure_subset_source : closure B ⊆ chart.source
  outerRadius : ℝ
  innerRadius : ℝ
  innerRadius_pos : 0 < innerRadius
  innerRadius_lt_outerRadius : innerRadius < outerRadius
  image_eq_ball : chart '' B = Metric.ball (0 : EuclideanHalfSpace n) innerRadius
  image_closure_eq_closedBall :
    chart '' closure B = Metric.closedBall (0 : EuclideanHalfSpace n) innerRadius
  target_eq_ball : chart.target = Metric.ball (0 : EuclideanHalfSpace n) outerRadius

/-- A regular coordinate half-ball carries a distinguished coordinate chart. -/
instance {B : Set M} :
    CoeOut (@IsRegularCoordinateHalfBall n _ M _ _ B)
      (OpenPartialHomeomorph M (EuclideanHalfSpace n)) where
  coe hB := hB.chart

/-- A regular coordinate half-ball sits inside a surrounding smooth coordinate half-ball. -/
-- Proof sketch: unpack the regular-coordinate-half-ball witness and use the same coordinate map,
-- with source `φ.source` and radius `r'`, to witness the surrounding smooth coordinate half-ball.
theorem IsRegularCoordinateHalfBall.exists_smoothCoordinateHalfBall_superset {B : Set M}
    (hB : @IsRegularCoordinateHalfBall n _ M _ _ B) :
    ∃ B' : Set M, @IsSmoothCoordinateHalfBall n _ M _ _ B' ∧ closure B ⊆ B' := sorry

end
