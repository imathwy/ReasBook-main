import Mathlib
import Nesterov.Chap05.Definition_5_1_1
import Nesterov.Chap05.Example_5_1_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter
open scoped Topology

/- Example 5.1.5 lies in the scalar self-concordance / reciprocal-power barrier domain.

Sampled owner-style declarations:
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the Chapter 5 owner for self-concordance with
  constant `Mf`;
* `quadraticAffineObjective` from `Example_5_1_2`, the chapter source-facing owner for the
  quadratic term `(1 / 2) x^2`;
* `negLog_isStandardSelfConcordantOn` from `Example_5_1_3`, the scalar logarithmic barrier model
  for the `p → 0⁺` limit;
* `powerBarrier` from `Chap01/Proposition_1_10_17`, the earlier project owner for reciprocal-power
  barriers on strict constraint loci.

Source/core/bridge triage:
* source-facing: the scalar regularized power barrier family
  `x ↦ (1 / 2) x^2 + 1 / (p x^p) - 1 / p`;
* core/canonical: `IsSelfConcordantOnWith (Set.Ioi (0 : ℝ))`;
* bridge/view: the pointwise `p → 0⁺` limit to `x ↦ (1 / 2) x^2 - log x`.

Primitive data:
* the scalar parameter `p`.

Derived API:
* the evaluation formula for `regularizedPowerBarrier p`;
* the self-concordance statement with constant `1 + p / 2` on `(0, ∞)`;
* the pointwise limit as `p → 0⁺`.

There is no upstream owner for this exact regularized scalar family, so the local definition
remains the source-facing owner. The file is refined only to the canonical Chapter 5
self-concordance surface, and its quadratic core is reused directly from
`quadraticAffineObjective` rather than restated as a parallel local formula.
-/

/-- The regularized univariate power barrier `x ↦ (1 / 2) x^2 + 1 / (p x^p) - 1 / p`. -/
def regularizedPowerBarrier (p : ℝ) : ℝ → ℝ :=
  fun x ↦ quadraticAffineObjective 0 0 1 x + 1 / (p * Real.rpow x p) - 1 / p

-- Proof sketch: evaluate the quadratic owner with `quadraticAffineObjective_apply` and simplify in
-- the scalar Hilbert space `ℝ`.
/-- Evaluating `regularizedPowerBarrier p` returns the textbook formula for `f_p`. -/
@[simp]
theorem regularizedPowerBarrier_apply (p x : ℝ) :
    regularizedPowerBarrier p x =
      (1 / 2 : ℝ) * x ^ (2 : ℕ) + 1 / (p * Real.rpow x p) - 1 / p :=
  by
    rw [regularizedPowerBarrier, quadraticAffineObjective_apply]
    simp [pow_two]

-- Proof sketch: use the explicit derivative formulas from the textbook on `(0, ∞)`, verify the
-- Hessian positivity, and check the cubic self-concordance bound separately on `x ≥ 1` and on
-- `0 < x ≤ 1`; the larger of the two resulting constants is `1 + p / 2`.
/-- Example 5.1.5: for `p > 0`, the regularized power barrier
`f_p(x) = (1 / 2) x^2 + 1 / (p x^p) - 1 / p` is self-concordant on `(0, ∞)` with
self-concordance constant `M_f = 1 + p / 2`. -/
theorem regularizedPowerBarrier_isSelfConcordantOnWith
    {p : ℝ} (hp : 0 < p) :
    IsSelfConcordantOnWith (Set.Ioi (0 : ℝ)) (Real.toNNReal (1 + p / 2))
      (regularizedPowerBarrier p) := sorry

-- Proof sketch: rewrite
-- `1 / (p * x^p) - 1 / p = (((1 / x)^p) - 1) / p`, express `((1 / x)^p)` as
-- `exp (p * log (1 / x))`, and identify the right-hand derivative at `p = 0`.
/-- As `p → 0⁺`, the regularized power barrier converges pointwise on `(0, ∞)` to
`x ↦ (1 / 2) x^2 - log x`. -/
theorem tendsto_regularizedPowerBarrier_at_zero
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun p : ℝ ↦ regularizedPowerBarrier p x)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds ((1 / 2 : ℝ) * x ^ (2 : ℕ) - Real.log x)) := sorry
