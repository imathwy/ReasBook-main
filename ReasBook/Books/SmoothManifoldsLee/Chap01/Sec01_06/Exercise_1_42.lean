import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic search note: `lean_leansearch` was unavailable here.
-- Local repo search reused the boundary-model basis pattern from Proposition 1.40.

universe u

open Set
open scoped Manifold

variable {n : ℕ} [NeZero n]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
variable [IsManifold (𝓡∂ n) (⊤ : WithTop ℕ∞) M]

/-- A regular coordinate ball is an open set whose image in a chart is a metric ball centered away
from the boundary hyperplane, with the corresponding closed ball still contained in the chart
target. -/
def IsRegularCoordinateBall (s : Set M) : Prop :=
  ∃ x : M, ∃ c : EuclideanSpace ℝ (Fin n), ∃ r : ℝ,
    0 < r ∧ r < c 0 ∧
      Metric.closedBall c r ⊆ (extChartAt (𝓡∂ n) x).target ∧
      s = (extChartAt (𝓡∂ n) x).symm '' Metric.ball c r

/-- A regular coordinate half-ball is an open set whose image in a chart is a metric ball in the
half-space centered on the boundary hyperplane, with the corresponding closed ball still contained
in the chart target. -/
def IsRegularCoordinateHalfBall (s : Set M) : Prop :=
  ∃ x : M, ∃ c : EuclideanSpace ℝ (Fin n), ∃ r : ℝ,
    0 < r ∧ c 0 = 0 ∧
      Metric.closedBall c r ∩ Set.range (𝓡∂ n) ⊆ (extChartAt (𝓡∂ n) x).target ∧
      s = (extChartAt (𝓡∂ n) x).symm '' (Metric.ball c r ∩ Set.range (𝓡∂ n))

-- Proof sketch: Unwind the definition, note that the metric ball is open and lies in the chart
-- target because it is contained in the corresponding closed ball, and then use that the inverse
-- of a chart is an open map on its target.
/-- Every regular coordinate ball is open. -/
theorem IsRegularCoordinateBall.isOpen {s : Set M}
    (hs : @IsRegularCoordinateBall n _ M _ _ s) :
    IsOpen s := sorry

-- Proof sketch: Unwind the definition, use that the metric ball in the half-space is open and is
-- contained in the chart target, and then apply the openness of the inverse chart on its target.
/-- Every regular coordinate half-ball is open. -/
theorem IsRegularCoordinateHalfBall.isOpen {s : Set M}
    (hs : @IsRegularCoordinateHalfBall n _ M _ _ s) : IsOpen s := sorry

/-- A topological basis whose members are regular coordinate balls or regular coordinate half-balls.
-/
class IsRegularCoordinateBallHalfBallBasis (b : Set (Set M)) : Prop where
  countable : b.Countable
  isTopologicalBasis : TopologicalSpace.IsTopologicalBasis b
  regular_or_half_ball :
    ∀ s ∈ b,
      @IsRegularCoordinateBall n _ M _ _ s ∨
        @IsRegularCoordinateHalfBall n _ M _ _ s

-- Proof sketch: Start from a countable basis on the manifold, refine each basis neighborhood
-- using a chart around a chosen point, and inside the chart choose from a countable family of
-- metric balls with rational data whose closed balls stay in the chart target; classify the chosen
-- ball according to whether its center lies in the interior of the half-space or on the boundary.
/-- Exercise 1.42: a second-countable charted space modeled on a Euclidean half-space admits a
countable basis consisting of regular coordinate balls and regular coordinate half-balls, hence so
does every smooth manifold with boundary. -/
theorem exists_countable_regular_coordinate_ball_half_ball_basis
    [SecondCountableTopology M] :
    ∃ b : Set (Set M), @IsRegularCoordinateBallHalfBallBasis n _ M _ _ b :=
  sorry
