import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01_05.Proposition_1_40
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01_06.Definition_1_6_extra_3

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic search note: `lean_leansearch` was unavailable here.
-- This exercise now reuses the earlier chapter owner `IsRegularCoordinateHalfBall` directly and
-- relates the new ball/half-ball statements to the boundary-model coordinate-ball API of
-- Proposition 1.40 instead of maintaining a parallel local vocabulary.

universe u

open Set
open scoped Manifold

variable {n : ℕ} [NeZero n]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
variable [IsManifold (𝓡∂ n) (⊤ : WithTop ℕ∞) M]

/-- A regular coordinate ball is a subset cut out inside a boundary chart by an open Euclidean ball
centered away from the boundary hyperplane, with the corresponding closed ball still contained in
the chart target. This is the ball analogue of Definition 1.6-extra-3's regular coordinate
half-balls. The ambient dimension `n` is explicit because it is not recoverable from `s : Set M`
alone. -/
def IsRegularCoordinateBall (n : ℕ) [NeZero n] {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : WithTop ℕ∞) M] (s : Set M) : Prop :=
  ∃ x : M, ∃ c : EuclideanSpace ℝ (Fin n), ∃ r : ℝ,
    0 < r ∧ r < c 0 ∧
      Metric.closedBall c r ⊆ (extChartAt (𝓡∂ n) x).target ∧
      s = (extChartAt (𝓡∂ n) x).symm '' Metric.ball c r

/-- A regular coordinate ball yields a boundary-model coordinate ball after restricting the witness
chart to the smaller ball. -/
theorem IsRegularCoordinateBall.isBoundaryModelCoordinateBall {s : Set M}
    (hs : IsRegularCoordinateBall n s) :
    IsBoundaryModelCoordinateBall n s := sorry

/-- A regular coordinate half-ball yields a boundary-model coordinate half-ball after restricting
its witnessing chart to the smaller half-ball. -/
theorem IsRegularCoordinateHalfBall.isBoundaryModelCoordinateHalfBall {s : Set M}
    (hs : IsRegularCoordinateHalfBall n s) :
    IsBoundaryModelCoordinateHalfBall n s := sorry

/-- Every regular coordinate ball is open. -/
theorem IsRegularCoordinateBall.isOpen {s : Set M} (hs : IsRegularCoordinateBall n s) :
    IsOpen s := sorry

/-- Every regular coordinate half-ball is open. -/
theorem IsRegularCoordinateHalfBall.isOpen {s : Set M}
    (hs : IsRegularCoordinateHalfBall n s) :
    IsOpen s := sorry

/-- A countable topological basis whose members are regular coordinate balls or regular coordinate
half-balls. -/
class IsRegularCoordinateBallHalfBallBasis (n : ℕ) [NeZero n] {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : WithTop ℕ∞) M] (b : Set (Set M)) : Prop where
  countable : b.Countable
  isTopologicalBasis : TopologicalSpace.IsTopologicalBasis b
  regular_or_half_ball :
    ∀ s ∈ b, IsRegularCoordinateBall n s ∨ IsRegularCoordinateHalfBall n s

-- Proof sketch: start from the countable precompact coordinate-ball/half-ball basis of
-- Proposition 1.40, then refine each basis neighborhood inside a smooth chart by choosing a
-- smaller rational ball centered either in the interior or on the boundary hyperplane.
/-- Exercise 1.42: a second-countable smooth manifold with boundary admits a countable basis
consisting of regular coordinate balls and regular coordinate half-balls. -/
theorem exists_countable_regular_coordinate_ball_half_ball_basis [SecondCountableTopology M] :
    ∃ b : Set (Set M), IsRegularCoordinateBallHalfBallBasis n b := sorry
