import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_41
import ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_39
import ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_40

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {d : ℕ}

local notation "State" => EuclideanSpace ℝ (Fin d)
local notation "VectorProcess" => NNReal → Ω → State

section BrownianPolarSets

variable (P : State → ProbabilityMeasure Ω) (W : VectorProcess)
variable (hW : ∀ x : State, IsBrownianMotionVectorStartedAt (P x) W x)

/- Proof sketch: if `A` is nonempty, choose `y ∈ A`. In dimension `1`, one-dimensional Brownian
motion started at `y` returns arbitrarily close to `y` at arbitrarily large times almost surely by
Theorem 25.39, so `A` cannot be polar. The empty set is polar by definition. -/
/-- Theorem 25.42 (1): if `d = 1`, then a set in `ℝ^d` is polar exactly when it is empty. -/
theorem isPolarSet_iff_eq_empty_of_dimension_one
    (hd : d = 1) (A : Set State) :
    IsPolarSet P W A ↔ A = ∅ := sorry

/- Proof sketch: translate the singleton to `{0}` and use the ball-hitting formula from
Theorem 25.40. For `x ≠ y`, the probability of ever hitting `{y}` is the limit of the ball-hit
probabilities as the radius tends to `0`, which is `0` in dimensions `d ≥ 2`. For `x = y`, use
the strong Markov property together with the fact that Brownian motion is almost surely away from
its starting point at each fixed positive time. -/
/-- Theorem 25.42 (2): if `d ≥ 2`, then every singleton `{y}` in `ℝ^d` is polar. -/
theorem isPolarSet_singleton_of_dimension_two_le
    (hd : 2 ≤ d) (y : State) :
    IsPolarSet P W {y} := sorry

end BrownianPolarSets

end ProbabilityTheory
