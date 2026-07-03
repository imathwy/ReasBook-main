import LecturesConvexOptimization_Nesterov_2018.Chap04.Algorithm_4_2_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E]

section RestartedAcceleratedCubicNewton

/- Lemma 4.2.7 lies in the restarted accelerated cubic-Newton / normed-distance contraction
domain.

Sampled owner-style declarations:
* `acceleratedCubicNewtonRestartPeriod` in `Algorithm_4_2_3`, the chapter owner of the least
  natural restart length above the source lower bound `((24 e) / (σ₃ / L₃))^(1/3)`;
* `acceleratedCubicNewtonRestartPeriod_lower_bound` in `Algorithm_4_2_3`, the canonical theorem
  that the owner block length dominates the source threshold;
* `lower_bound_at_minimizer_of_uniformConvexOn` in `Theorem_4_2_1`, a nearby chapter result whose
  public statement is already minimized to the normed-space layer for inequalities involving only
  `‖x - y‖`;
* mathlib `NormedAddCommGroup`, the owner abstraction supplying the primitive `E`-side operations
  used here: subtraction and the norm `‖x - y‖`.

Best owner abstraction:
* source-facing: the contraction estimate under a cubic growth lower bound and a restart-gap upper
  bound;
* core/canonical: `acceleratedCubicNewtonRestartPeriod sigma3 L3` for the least admissible
  restart block length;
* bridge/view: the source threshold
  `acceleratedCubicNewtonRestartThreshold sigma3 L3` together with
  `acceleratedCubicNewtonRestartPeriod_lower_bound`, which recovers the textbook real lower bound.

Primitive data:
* the objective `f`;
* the restart orbit `y`;
* the reference minimizer `xStar`;
* the cubic-growth modulus `sigma3`;
* the Hessian-Lipschitz constant `L3`;
* the chosen restart length `m`;
* the normed additive group structure on `E`.

Derived API:
* the canonical restart block length `acceleratedCubicNewtonRestartPeriod sigma3 L3`;
* the pointwise restart-gap estimate at step `k`;
* the one-step contraction estimates for the cubic distance and the objective gap.

This file keeps the cubic-growth hypothesis source-facing, since no upstream owner with the same
interface already packages exactly that content. The block-length hypothesis is nonetheless
refined to the chapter owner `acceleratedCubicNewtonRestartPeriod sigma3 L3 ≤ m`, rather than
keeping the equivalent real threshold inequality as primitive public data. On the ambient `E`-side,
the statements only use subtraction and `‖·‖`, so `NormedAddCommGroup E` is the correct owner
layer; there is no inner-product or scalar action on `E` in the public API. -/

variable {f : E → ℝ} {y : ℕ → E} {xStar : E} {sigma3 : ℝ} {L3 : NNReal} {m : ℕ}

variable
  (hsigma3 : 0 < sigma3)
  (hcubic_growth :
    ∀ x : E,
      f x - f xStar ≥ (sigma3 / 3 : ℝ) * ‖x - xStar‖ ^ (3 : ℕ))
  (hrestart_gap :
    ∀ k : ℕ,
      f (y (k + 1)) - f xStar ≤
        (((8 : ℝ) * (L3 : ℝ)) / ((m : ℝ) * ((m : ℝ) + 1) * ((m : ℝ) + 2))) *
          ‖y k - xStar‖ ^ (3 : ℕ))
  (hm : acceleratedCubicNewtonRestartPeriod sigma3 L3 ≤ m)

-- Proof sketch: apply the cubic growth lower bound at `y (k + 1)` and combine it with the
-- restarted accelerated cubic-Newton estimate for `f (y (k + 1)) - f xStar`. The lower bound on
-- `m` supplied through `acceleratedCubicNewtonRestartPeriod sigma3 L3 ≤ m` and
-- `acceleratedCubicNewtonRestartPeriod_lower_bound` implies
-- `((8 : ℝ) * L3) / (m (m + 1) (m + 2)) ≤ sigma3 / (3 * e)`, so cancelling `sigma3 / 3 > 0`
-- yields the displayed contraction of the cubic distance.
/-- Lemma 4.2.7 (1): if `f` satisfies the global cubic growth bound
`f x - f xStar ≥ (sigma3 / 3) ‖x - xStar‖^3` with `sigma3 > 0`, if the restarted outer iterates
`y` satisfy
`f(y_{k+1}) - f(xStar) ≤ (8 L3 / (m (m + 1) (m + 2))) ‖y_k - xStar‖^3`,
and if `m` dominates the canonical restart period
`acceleratedCubicNewtonRestartPeriod sigma3 L3`, then each restart contracts the cubic distance to
`xStar` by the factor `e⁻¹`. -/
theorem restartedAcceleratedCubicNewton_normCube_succ_le_exp_neg_one_mul
    (k : ℕ) :
    ‖y (k + 1) - xStar‖ ^ (3 : ℕ) ≤
      (1 / Real.exp 1 : ℝ) * ‖y k - xStar‖ ^ (3 : ℕ) := sorry

-- Proof sketch: use the previous cubic-distance contraction together with the same cubic growth
-- lower bound applied at `y k` to rewrite `‖y k - xStar‖^3` in terms of the objective gap
-- `f (y k) - f xStar`. Substituting that bound into the upper estimate for
-- `f (y (k + 1)) - f xStar` gives the factor `1 / e`.
/-- Lemma 4.2.7 (2): under the same cubic growth, restart-gap, and canonical restart-period
hypotheses, the objective gaps along the restarted accelerated cubic-Newton iterates contract by
the factor `e⁻¹`. -/
theorem restartedAcceleratedCubicNewton_gap_succ_le_exp_neg_one_mul
    (k : ℕ) :
    f (y (k + 1)) - f xStar ≤
      (1 / Real.exp 1 : ℝ) * (f (y k) - f xStar) := sorry

end RestartedAcceleratedCubicNewton
