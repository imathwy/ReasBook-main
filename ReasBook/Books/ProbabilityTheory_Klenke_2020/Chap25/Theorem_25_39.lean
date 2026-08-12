import Mathlib
import ProbabilityTheory_Klenke_2020.Chap25.StandardBrownianMotionVector

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {d : ℕ}

local notation "State" => EuclideanSpace ℝ (Fin d)
local notation "VectorProcess" => NNReal → Ω → State

section BrownianRecurrenceTransience

variable {W : VectorProcess}
variable (hW : IsStandardBrownianMotionVector μ W)

-- Proof sketch: apply the Brownian hitting-probability formula for balls from the next theorem in
-- the chapter together with the strong Markov property at the exit times of larger balls. For
-- `d ≤ 2` the return probability to every smaller ball is `1`, so every neighborhood of `y` is
-- visited at arbitrarily large times almost surely.
/-- Theorem 25.39 (1): if `d ≤ 2`, then for every `y ∈ ℝ^d`, almost every `d`-dimensional
Brownian path has `y` as a cluster point along `t → ∞`; equivalently, every neighborhood of `y`
is visited at arbitrarily large times. This is the textbook recurrence statement
`liminf_{t→∞} ‖W_t - y‖ = 0` in canonical filter form. -/
theorem brownian_visits_every_ball_frequently_of_dimension_le_two
    (hd : d ≤ 2) (y : State) :
    ∀ᵐ ω ∂μ, MapClusterPt y atTop (fun t ↦ W t ω) := sorry

-- Proof sketch: use the preceding recurrent-ball-visiting statement on a countable basis of open
-- balls with rational centers and rational radii. A path that hits every such basis element has
-- dense range in `ℝ^d`.
/-- Theorem 25.39 (2): if `d ≤ 2`, then almost every sample path of the `d`-dimensional Brownian
motion has dense range in `ℝ^d`. -/
theorem brownian_denseRange_of_dimension_le_two
    (hd : d ≤ 2) :
    ∀ᵐ ω ∂μ, DenseRange (fun t ↦ W t ω) := sorry

-- Proof sketch: apply the same strong-Markov reduction to larger and larger spheres. For
-- `d > 2`, the probability of ever re-entering a fixed ball after reaching radius `R` is
-- `(s / R)^(d - 2)`, which tends to `0`; hence the path eventually leaves every bounded set and
-- its norm tends to infinity almost surely.
/-- Theorem 25.39 (3): if `d > 2`, then the norm of the `d`-dimensional Brownian motion tends to
`∞` almost surely. This is the textbook transience statement `‖W_t‖ → ∞` as `t → ∞`. -/
theorem brownian_norm_tendsto_atTop_of_dimension_gt_two
    (hd : 2 < d) :
    ∀ᵐ ω ∂μ, Tendsto (fun t ↦ ‖W t ω‖) atTop atTop := sorry

-- Proof sketch: fix `y ≠ 0` and combine transience with the ball-hitting formula centered at
-- `y`. In dimensions `d > 2`, the Brownian path hits every sufficiently small ball around `y`
-- with probability strictly less than `1`; iterating after large exit times shows that almost
-- surely the whole path stays outside some positive-radius ball around `y`.
/-- Theorem 25.39 (4): if `d > 2`, then for every nonzero `y ∈ ℝ^d`, the Brownian path stays at a
positive distance from `y` almost surely. This is the textbook clause
`inf {‖W_t - y‖ : t ≥ 0} > 0` written as the existence of a uniform positive lower bound on the
distance to `y`. -/
theorem brownian_avoids_nonzero_points_of_dimension_gt_two
    (hd : 2 < d) (y : State) (hy : y ≠ 0) :
    ∀ᵐ ω ∂μ, ∃ ε : ℝ, 0 < ε ∧ ∀ t : NNReal, ε ≤ dist (W t ω) y := sorry

end BrownianRecurrenceTransience

end ProbabilityTheory
