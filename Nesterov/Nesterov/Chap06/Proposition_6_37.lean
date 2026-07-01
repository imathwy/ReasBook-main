import Nesterov.Chap01.Definition_1_3_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {X : Type u}

/-
Proposition 6.37 lies in the constrained minimization / approximate-solution domain.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner of a
  feasible set together with a real-valued objective;
- `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the canonical
  owner for constrained optimal values;
- `SetConstrainedMinimizationProblem.IsApproximateMinimizer` and
  `SetConstrainedMinimizationProblem.isApproximateMinimizer_iff` in
  `Chap01/Definition_1_3_7`, the canonical `ε`-suboptimality owner on a constrained problem;
- `PrimalConvexMinimizationProblem` in `Chap06/Definition_6_4`, which reuses the same owner
  abstraction and derives its optimization API through it.

Best owner abstraction:
- source-facing: Proposition 6.37's smoothing comparison theorem;
- core/canonical: `SetConstrainedMinimizationProblem.mk Q φ` together with its derived
  `optimalValue` and `IsApproximateMinimizer` API;
- bridge/view: the smoothing comparison, with the lower bound used globally on `Q` and the upper
  bound used only at the feasible comparison point `yBar`.

Primitive data:
- the feasible set `Q`;
- the original and smoothed objectives `φ` and `φμ`.
- the global lower smoothing estimate on `Q`;
- the upper smoothing estimate at `yBar`.

Derived API:
- `(SetConstrainedMinimizationProblem.mk Q φ).optimalValue`;
- `(SetConstrainedMinimizationProblem.mk Q φ).IsApproximateMinimizer ε yBar`;
- the corresponding smoothed-problem instances built from `φμ`.

This refinement removes the duplicate local owners `optimalValueOn` and
`IsEpsilonSolutionOn` and states the proposition directly with the Chapter 1 owner API.
-/

-- Proof sketch: use the upper smoothing bound at `yBar` to estimate `φ yBar` by
-- `φμ yBar + μ log n`, use the lower smoothing bound on `Q` to deduce
-- `((SetConstrainedMinimizationProblem.mk Q φμ).optimalValue :
--   EReal) ≤ (SetConstrainedMinimizationProblem.mk Q φ).optimalValue`,
-- and combine these with the assumed `ε / 2` smoothed approximate-minimizer property and the
-- budget bound `μ log n ≤ ε / 2`.
/-- Proposition 6.37: if `φμ` is a smoothing of `φ` on `Q` satisfying
`φμ(y) ≤ φ(y)` for every feasible `y` and `φ(yBar) ≤ φμ(yBar) + μ log n` at the feasible point
`yBar`, then any `ε / 2`-approximate minimizer of the smoothed problem is an `ε`-approximate
minimizer of the original problem whenever `μ log n ≤ ε / 2`. -/
theorem isApproximateMinimizer_of_smoothedObjective_suboptimality
    {Q : Set X} {φ φμ : X → ℝ} {n : ℕ} {μ ε : ℝ} {yBar : X}
    (happrox_lower : ∀ y ∈ Q, φμ y ≤ φ y)
    (happrox_upper : φ yBar ≤ φμ yBar + μ * Real.log (n : ℝ))
    (hsmoothed :
      (SetConstrainedMinimizationProblem.mk Q φμ).IsApproximateMinimizer (ε / 2) yBar)
    (hμ_budget : μ * Real.log (n : ℝ) ≤ ε / 2) :
    (SetConstrainedMinimizationProblem.mk Q φ).IsApproximateMinimizer ε yBar := sorry

-- Proof sketch: under `log n ≠ 0`, the special choice `μ = ε / (2 log n)` gives
-- `μ log n = ε / 2`, so the previous theorem applies directly.
/-- Choosing `μ = ε / (2 log n)` with `log n ≠ 0` forces the smoothing budget to equal `ε / 2`,
so if the lower smoothing estimate holds on `Q` and the upper estimate is available at `yBar`
with that specialized parameter, then an `ε / 2`-approximate minimizer of the smoothed problem is
already an `ε`-approximate minimizer of the original problem. -/
theorem isApproximateMinimizer_of_smoothedObjective_suboptimality_with_canonical_mu
    {Q : Set X} {φ φμ : X → ℝ} {n : ℕ} {ε : ℝ} {yBar : X}
    (hlogn : Real.log (n : ℝ) ≠ 0)
    (happrox_lower : ∀ y ∈ Q, φμ y ≤ φ y)
    (happrox_upper :
      φ yBar ≤ φμ yBar + (ε / (2 * Real.log (n : ℝ))) * Real.log (n : ℝ))
    (hsmoothed :
      (SetConstrainedMinimizationProblem.mk Q φμ).IsApproximateMinimizer (ε / 2) yBar) :
    (SetConstrainedMinimizationProblem.mk Q φ).IsApproximateMinimizer ε yBar := sorry

end
