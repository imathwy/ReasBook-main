import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap05.Proposition_5_3_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient

/- Lemma 5.4.1.1 lies in the scalar self-concordant-barrier domain.

Relevant owner-style declarations sampled before refinement:
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for a
  `ν`-self-concordant barrier on a domain;
* `_root_.barrier_parameter_bound_iff_gradient_inner_sq_le` in `Proposition_5_3_3`, the
  canonical pointwise bridge turning the barrier inequality into a squared
  gradient / local-norm estimate;
* `IsBarrierFunctionOn` in `Chap01/Definition_1_10_18`, the canonical frontier-blow-up owner
  needed for the source-faithful lower bound `1 ≤ κ`;
* `gradient_eq_deriv'` in mathlib, the one-dimensional bridge from the Euclidean gradient to the
  usual derivative.

Best owner abstraction:
* source-facing: the scalar interval barrier statement itself, namely
  `1 ≤ κ ≤ ν` for `κ = sup_t (f'(t))^2 / f''(t)`;
* core/canonical: `IsSelfConcordantBarrierOnWith I ν f` together with
  `_root_.barrier_parameter_bound_iff_gradient_inner_sq_le`;
* bridge/view: the ratio supremum `κ`, derived from the barrier owner rather than introduced with
  separate frontier-growth data.

Primitive data:
* the interval domain `I = {t : ℝ | α < (t : WithBot ℝ) ∧ t < β}`;
* interval nonemptiness when the lower bound `1 ≤ κ` is asserted;
* the barrier owner `IsSelfConcordantBarrierOnWith I ν f`.

Derived API:
* the pointwise inequality `(f'(t))^2 ≤ ν ‖1‖[f; t]^2`, then its scalar second-derivative
  reformulation `(f'(t))^2 ≤ ν f''(t)`;
* the barrier-derived positivity bridge `0 < f''(t)` on the interval;
* the ratio owner `selfConcordantBarrierRatio α β f t` and its supremum
  `selfConcordantBarrierKappa α β f`;
* the canonical barrier-function owner on `closure I`, derived from the barrier owner together with
  interval nonemptiness;
* the supremum ratio bounds on `κ`, with Hessian positivity and frontier blow-up recovered from
  the owner hypotheses.
-/

section

variable {α : WithBot ℝ} {β : ℝ}

/-- The scalar open interval `(\alpha, \beta)` used in Lemma 5.4.1.1. The lower endpoint is
allowed to be `-∞`, matching the source half-line variants. -/
abbrev scalarBarrierInterval (α : WithBot ℝ) (β : ℝ) : Set ℝ :=
  {t : ℝ | α < (t : WithBot ℝ) ∧ t < β}

-- Proof sketch: specialize
-- `_root_.barrier_parameter_bound_iff_gradient_inner_sq_le` to the scalar
-- interval owner `hself` at the point `t` and to the direction `u = 1`. On `ℝ`, the gradient is
-- the ordinary derivative, and `hessianLocalNorm_def` together with `Real.sq_sqrt` rewrites
-- `‖1‖[f; t]^2` as the second derivative. The owner inequality therefore becomes
-- `(f'(t))^2 ≤ ν f''(t)`.
/-- The canonical scalar specialization of the barrier-parameter owner inequality:
for every `t ∈ (\alpha, \beta)`, a `ν`-self-concordant barrier satisfies
`(f'(t))^2 ≤ ν f''(t)`. This is the core owner statement behind the textbook ratio `κ`. -/
theorem selfConcordantBarrier_deriv_sq_le_parameter_mul_secondDeriv
    {ν : NNReal} {f : ℝ → ℝ}
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f)
    (t : scalarBarrierInterval α β) :
    deriv f t ^ (2 : ℕ) ≤ (ν : ℝ) * iteratedDeriv 2 f t := sorry

-- Proof sketch: the barrier owner supplies the Chapter 1 frontier-blow-up theorem on `closure I`,
-- and `I` contains no affine line because of the finite upper endpoint `β`. Applying the chapter
-- no-affine-line positivity bridge to the scalar direction `1` yields `0 < f''(t)` at every
-- interior point.
/-- On the scalar barrier interval `(\alpha, \beta)`, the second derivative is strictly positive.
This removes the implementation artifact of totalized real division from the source-facing ratio
`κ`. -/
theorem selfConcordantBarrier_secondDeriv_pos
    {ν : NNReal} {f : ℝ → ℝ}
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f)
    (t : scalarBarrierInterval α β) :
    0 < iteratedDeriv 2 f t := sorry

/-- The source-facing scalar barrier ratio at `t`, expressed through the canonical positive
second-derivative theorem supplied by the barrier owner. -/
def selfConcordantBarrierRatio
    (α : WithBot ℝ) (β : ℝ) (f : ℝ → ℝ) (t : scalarBarrierInterval α β) : ℝ :=
  deriv f t ^ (2 : ℕ) / iteratedDeriv 2 f t

/-- Expanding `selfConcordantBarrierRatio α β f t` recovers the textbook scalar formula
`(f'(t))^2 / f''(t)`. -/
@[simp] theorem selfConcordantBarrierRatio_def
    (f : ℝ → ℝ) (t : scalarBarrierInterval α β) :
    selfConcordantBarrierRatio α β f t =
      deriv f t ^ (2 : ℕ) / iteratedDeriv 2 f t :=
  rfl

/-- The source-facing scalar barrier ratio supremum
`κ = sup_{t ∈ (\alpha, \beta)} (f'(t))^2 / f''(t)`. Nonemptiness is only needed for the lower
bound theorem `1 ≤ κ`, not for the owner itself or the upper bound `κ ≤ ν`. -/
def selfConcordantBarrierKappa
    (α : WithBot ℝ) (β : ℝ) (f : ℝ → ℝ) : ℝ :=
  sSup (Set.range (selfConcordantBarrierRatio α β f))

-- Proof sketch: divide
-- `selfConcordantBarrier_deriv_sq_le_parameter_mul_secondDeriv hself t`
-- by the positive scalar `iteratedDeriv 2 f t`.
/-- Every scalar barrier ratio value is bounded above by the barrier parameter. -/
theorem selfConcordantBarrierRatio_le_parameter
    {ν : NNReal} {f : ℝ → ℝ}
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f)
    (t : scalarBarrierInterval α β) :
    selfConcordantBarrierRatio α β f t ≤ (ν : ℝ) := sorry

-- Proof sketch: `κ` is the least upper bound of the pointwise ratio owner
-- `selfConcordantBarrierRatio α β f`.
/-- For a scalar `ν`-self-concordant barrier on `(\alpha, \beta)`, the source-facing ratio
`κ = sup_t (f'(t))^2 / f''(t)` is bounded above by the barrier parameter. -/
theorem selfConcordantBarrierKappa_le_parameter
    {ν : NNReal} {f : ℝ → ℝ}
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f) :
    selfConcordantBarrierKappa α β f ≤ (ν : ℝ) := sorry

-- Proof sketch: from interval nonemptiness, the barrier owner `hself` canonically supplies the
-- frontier-blow-up owner on `closure I`. Combining that barrier growth with the one-dimensional
-- convexity/Hessian positivity consequences of `hself`, the auxiliary ratio owner
-- `selfConcordantBarrierRatio α β f` cannot stay below `1` everywhere, so its supremum is at
-- least `1`.
/-- If `(\alpha, \beta)` is nonempty and `f` is a scalar `ν`-self-concordant barrier on it, then
the source-facing ratio supremum satisfies `1 ≤ κ`.

The frontier-growth and positivity input are derived from the barrier owner rather than passed as
separate public hypotheses. -/
theorem one_le_selfConcordantBarrierKappa
    {ν : NNReal} {f : ℝ → ℝ}
    (hI : Set.Nonempty (scalarBarrierInterval α β))
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f) :
    1 ≤ selfConcordantBarrierKappa α β f := sorry

/-- Lemma 5.4.1.1: for a scalar `ν`-self-concordant barrier on `(\alpha, \beta)`,
the barrier parameter dominates `κ = sup_t (f'(t))^2 / f''(t)`, and for a nonempty interval this
supremum is at least `1`. Both assertions are expressed directly at the scalar barrier owner
surface. -/
theorem selfConcordantBarrier_one_le_kappa_and_kappa_le_parameter
    {ν : NNReal} {f : ℝ → ℝ}
    (hI : Set.Nonempty (scalarBarrierInterval α β))
    (hself : IsSelfConcordantBarrierOnWith (scalarBarrierInterval α β) ν f) :
    1 ≤ selfConcordantBarrierKappa α β f ∧
      selfConcordantBarrierKappa α β f ≤ (ν : ℝ) := sorry

end

end
