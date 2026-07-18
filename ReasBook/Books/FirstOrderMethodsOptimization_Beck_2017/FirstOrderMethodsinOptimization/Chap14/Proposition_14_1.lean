import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap14.Algorithm_14_8
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap14.Definition_14_4
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap14.Definition_14_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Proposition 14.1 is `source-facing`: it studies the distinguished line of coordinatewise minima
for the Chapter 14 counterexample objective. Domain sampling against the existing Chapter 14 API
identifies the following owner split.
- `source-facing`: Definition 14.4's real-valued owner
  `alternating_minimization_failure_ii_objective`;
- `core/canonical`: `is_coordinatewise_minimum` from Definition 14.2;
- `source-facing` companion owners: the pair section owners
  `two_block_alternating_minimization_x1_objective` and
  `two_block_alternating_minimization_x2_objective` from Algorithm 14.8;
- `bridge/view`: the canonical coercion `Function.toExtendedReal` from Definition 9.2; and
- `bridge/view`: `two_block_alternating_minimization_objective_blocks` and
  `two_block_alternating_minimization_state` from Algorithm 14.8.

Accordingly, the objective itself is not redefined here: the file reuses Definition 14.4's owner
through its canonical `EReal` view. The primitive data kept here are only the distinguished line
of counterexample points and the resulting minimizer statements on that fixed objective. The main
coordinatewise-minimality statement therefore uses the Chapter 14 owner
`is_coordinatewise_minimum` on the canonical two-block block-vector view, while the textbook pair
sections are kept only as a thin source-facing companion theorem. -/

local notation "F" => alternating_minimization_failure_ii_objective.toExtendedReal
local notation "g₀" => (0 : ℝ → EReal)
local notation "F₂" =>
  two_block_alternating_minimization_objective_blocks
    F
    g₀
    g₀

-- Proof sketch: the objective is nonnegative as a sum of absolute values, and it vanishes exactly
-- when the linear system `3 x₁ + 4 x₂ = 0` and `x₁ - 2 x₂ = 0` holds, whose unique solution is
-- `(0, 0)`.
/-- Proposition 14.1 (1): the counterexample objective has the origin as its unique global
minimizer. -/
theorem alternating_minimization_counterexample_unique_minimizer
    (x : ℝ × ℝ) :
    IsMinOn F Set.univ x ↔ x = 0 := sorry

/-- Proposition 14.1 (2): every point `(-4 * α, 3 * α)` on the distinguished line is a
coordinate-wise minimum of the counterexample objective in the Chapter 14 two-block owner sense. -/
theorem alternating_minimization_counterexample_is_coordinatewise_minimum
    (α : ℝ) :
    is_coordinatewise_minimum F₂ (two_block_alternating_minimization_state (-4 * α) (3 * α)) :=
  sorry

-- Proof sketch: unpack the owner statement above at the two blocks `0` and `1`, then simplify
-- the canonical block objectives with the two-block bridge lemmas from Algorithm 14.8.
/-- Source-facing companion to Proposition 14.1 (2): every point `(-4 * α, 3 * α)` on the
distinguished line lies in the effective domain and minimizes both textbook one-variable sections
of the counterexample objective. -/
theorem alternating_minimization_counterexample_coordinatewise_minimum
    (α : ℝ) :
    (-4 * α, 3 * α) ∈ effective_domain F ∧
      IsMinOn
        (two_block_alternating_minimization_x1_objective
          F
          g₀
          g₀
          (3 * α))
        Set.univ
        (-4 * α) ∧
      IsMinOn
        (two_block_alternating_minimization_x2_objective
          F
          g₀
          g₀
          (-4 * α))
        Set.univ
        (3 * α) := by
  let hcoord := alternating_minimization_counterexample_is_coordinatewise_minimum α
  refine ⟨?_, ?_, ?_⟩
  · simp [effective_domain, Function.toExtendedReal]
  · simpa using hcoord.isMinOn 0
  · simpa using hcoord.isMinOn 1
