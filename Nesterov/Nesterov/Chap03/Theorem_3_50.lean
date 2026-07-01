import Nesterov.Chap01.Definition_1_3_2
import Nesterov.Chap01.Theorem_1_3_9
import Nesterov.Chap03.Definition_3_64

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open EuclideanSpace
open scoped ConvexLipschitz

/- Primary domain: value-oracle lower bounds for constrained convex minimization on `ℓ∞`-balls.

Relevant owner-style declarations sampled before refinement:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3` for the primitive feasible-set
  and objective data of a constrained minimization problem;
- `SetConstrainedMinimizationProblem.optimalValue` and
  `SetConstrainedMinimizationProblem.IsApproximateMinimizer` in `Chap01/Definition_1_3_7` for the
  derived optimal-value and `ε`-accuracy API;
- `ConvexLipschitzOn` and the Lean notation `𝓕⁰⁰[M](Q)` for the textbook class
  `𝓕_M^{0,0}(Q)` in `Chap03/Definition_3_64`, the
  source-facing Chapter 3 owner of fixed-parameter convex Lipschitz objectives on a feasible set;
- `DeterministicValueOracleMethod` and
  `DeterministicValueOracleMethod.oracleTranscript` in `Chap01/Theorem_1_3_9`, the chapter owner
  for ordered deterministic value-oracle methods;
- `DeterministicValueOracleMethod.SolvesLinftyLipschitzProblemClassWithin` in
  `Chap01/Theorem_1_3_9`, the closest upstream owner-pattern for bounded-budget oracle
  correctness on a source-facing problem class;
- `linftyLipschitzClass` and `mem_linftyLipschitzClass_iff_lipschitzOnWith` in
  `Chap01/Definition_1_3_4`, the chapter owner and canonical bridge for `ℓ∞`-Lipschitz
  objectives;
- `EuclideanSpace.linftyClosedBall` in `Chap01/Definition_1_3_2` for the source-facing
  `ℓ∞`-ball owner built from the chapter's `ℓ∞` norm on `EuclideanSpace ℝ (Fin n)`.

Source/core/bridge triage:
- source-facing: the Theorem 3.50 problem-class predicate on
  `SetConstrainedMinimizationProblem`, adding the textbook `ℓ∞`-ball and Lipschitz/convex
  hypotheses without strengthening the source assumptions;
- core/canonical: `SetConstrainedMinimizationProblem`, the source-facing class
  `𝓕⁰⁰[M](B∞(0, R))`, its derived optimal-value and approximate-minimizer API, and
  `DeterministicValueOracleMethod`;
- bridge/view: the source-facing `EuclideanSpace.linftyClosedBall` owner from
  `Definition_1_3_2`, the Chapter 1 coordinate-transport bridge to `LipschitzOnWith`, and the
  canonical feasible-set-indexed method type `Set E → DeterministicValueOracleMethod E`, which
  reuses the Chapter 1 transcript recursion while exposing the constrained problem's feasible set
  to the algorithm.

Primitive data:
- for problems: only the feasible set and objective, owned by
  `SetConstrainedMinimizationProblem`;
- for algorithms: a feasible-set-indexed family `Set E → DeterministicValueOracleMethod E` of
  deterministic query and output rules, each already owned by
  `DeterministicValueOracleMethod`.

Derived API:
- `optimalValue` and `IsApproximateMinimizer` from the Chapter 1 owner abstraction;
- the source-facing Theorem 3.50 class predicate adding nonempty/convex and `Q ⊆ B∞(0, R)` to
  the Chapter 3 function-class owner `problem.objective ∈ 𝓕⁰⁰[M](B∞(0, R))`;
- the companion bridge
  `linftyClosedBall_lipschitz_iff_lipschitzOnWith_coordImage`, which recovers the canonical
  coordinate-transported `LipschitzOnWith` view without making it the main owner;
- the uniform-accuracy predicate phrased through the Chapter 1 derived API `queryAfter` and
  `outputAfter` after specializing the feasible-set-indexed owner at `problem.feasibleSet`. -/

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "coordEquiv" => EuclideanSpace.equiv (Fin n) ℝ

/-- On `B∞(0, R)`, the textbook `ℓ∞`-Lipschitz estimate is equivalent to the Chapter 1
coordinate-transported `LipschitzOnWith` bridge. The source-facing Theorem 3.50 class keeps the
`‖·‖∞` surface and uses this theorem only as a companion view. -/
theorem linftyClosedBall_lipschitz_iff_lipschitzOnWith_coordImage
    {f : E → ℝ} {R M : NNReal} :
    (∀ x ∈ linftyClosedBall R, ∀ y ∈ linftyClosedBall R,
      |f x - f y| ≤ (M : ℝ) * ‖x - y‖∞) ↔
      LipschitzOnWith M (f ∘ (EuclideanSpace.equiv (Fin n) ℝ).symm)
        (coordEquiv '' (linftyClosedBall R : Set E)) := by
  sorry

namespace SetConstrainedMinimizationProblem

/-- Theorem 3.50's constrained problem class is the Chapter 1 owner
`SetConstrainedMinimizationProblem` together with the textbook hypotheses that the feasible set is
nonempty and convex, lies in the ambient closed `ℓ∞`-ball `B∞(0, R)`, and belongs to the
source-facing Chapter 3 class `𝓕_{M}^{0,0}(B∞(0, R))`. The ball radius is carried on the canonical
nonnegative owner `R : NNReal`, rather than as a raw real plus a separate positivity guard. -/
def IsInLinftyConstrainedProblemClass
    (problem : SetConstrainedMinimizationProblem E) (R M : NNReal) : Prop :=
  problem.feasibleSet.Nonempty ∧
    Convex ℝ problem.feasibleSet ∧
    problem.feasibleSet ⊆ linftyClosedBall R ∧
    problem.objective ∈ 𝓕⁰⁰[M](linftyClosedBall R)

end SetConstrainedMinimizationProblem

namespace DeterministicValueOracleMethod

/-- A deterministic value-oracle method solves the constrained problem class from Theorem 3.50
within `T` calls when, for every admissible constrained problem, the feasible-set-specialized
method queries only inside `B∞(0, R)` and its transcript-based output is an `ε`-approximate
minimizer in the canonical Chapter 1 sense. -/
def SolvesLinftyConstrainedProblemClassWithin
    (method : Set E → DeterministicValueOracleMethod E)
    (R M : NNReal) (ε : ℝ) (T : ℕ) : Prop :=
  ∀ problem : SetConstrainedMinimizationProblem E,
    problem.IsInLinftyConstrainedProblemClass R M →
      let algorithm := method problem.feasibleSet
      (∀ t : ℕ, t < T → algorithm.queryAfter problem t ∈ linftyClosedBall R) ∧
        problem.IsApproximateMinimizer ε (algorithm.outputAfter problem T)

end DeterministicValueOracleMethod

/-- Theorem 3.50: if the target accuracy satisfies `0 < ε` and a feasible-set-aware deterministic
value-oracle method with at most `T` oracle calls uniformly guarantees, for every nonempty convex
`Q ⊆ B∞(0, R)` and every `f ∈ 𝓕_{M}^{0,0}(B∞(0, R))`, an `ε`-approximate minimizer of the induced
set-constrained problem, then the query budget satisfies the lower bound
`n * log (M R / (8 ε)) ≤ T`. -/
-- Proof sketch: specialize to the finite hard family `u ↦ f_u` on the uniform grid inside
-- `B∞(0, R)`, where `f_u(x) = M * ‖x - u‖∞` and `Q = B∞(0, R)`. A depth-`T` value-query
-- transcript leaves exponentially many candidate minimizers consistent with the observed values,
-- so if `T < n * log (M R / (8 ε))` then two separated hard instances remain indistinguishable.
-- Any single feasible output is therefore `ε`-suboptimal on at least one of them.
theorem value_oracle_query_lower_bound_of_uniform_epsilon_guarantee
    {R M : NNReal} {ε : ℝ} {T : ℕ}
    (method : Set E → DeterministicValueOracleMethod E)
    (hε : 0 < ε)
    (hmethod : DeterministicValueOracleMethod.SolvesLinftyConstrainedProblemClassWithin
      method R M ε T) :
    (n : ℝ) * Real.log ((M : ℝ) * R / (8 * ε)) ≤ (T : ℝ) := sorry

end
