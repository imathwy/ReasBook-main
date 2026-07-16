import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Instances.Real
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01.Definition_1_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set
open scoped Manifold Topology

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M]

/-- A smooth coordinate ball is the source of a smooth chart whose image is an open metric ball in
the model space. -/
def IsSmoothCoordinateBall (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M] (B : Set M) : Prop :=
  ∃ φ : OpenPartialHomeomorph M E,
    φ ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M ∧
      φ.source = B ∧ φ.IsCoordinateBall

/-- Definition 1.3-extra-1: a regular coordinate ball is a subset whose closure is contained in a
larger smooth chart whose image is a larger Euclidean ball and which sends the subset and its
closure to the corresponding concentric open and closed balls. -/
def IsRegularCoordinateBall (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M] (B : Set M) : Prop :=
  ∃ chart : OpenPartialHomeomorph M E,
    chart ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M ∧
      closure B ⊆ chart.source ∧
      ∃ r r' : ℝ,
        0 < r ∧
          r < r' ∧
          chart '' B = Metric.ball (0 : E) r ∧
          chart '' closure B = Metric.closedBall (0 : E) r ∧
          chart.target = Metric.ball (0 : E) r'

/-- A regular coordinate ball is contained in a surrounding smooth coordinate ball. -/
theorem IsRegularCoordinateBall.exists_smoothCoordinateBall_superset {B : Set M}
    (hB : IsRegularCoordinateBall E B) :
    ∃ B' : Set M, IsSmoothCoordinateBall E B' ∧ closure B ⊆ B' :=
  by
    rcases hB with ⟨chart, hchart, hclosure, r, r', hr, hr', -, -, htarget⟩
    refine ⟨chart.source, ⟨chart, hchart, rfl, ?_⟩, hclosure⟩
    exact chart.isCoordinateBall_of_target_eq_ball (0 : E) r' (lt_trans hr hr') htarget
