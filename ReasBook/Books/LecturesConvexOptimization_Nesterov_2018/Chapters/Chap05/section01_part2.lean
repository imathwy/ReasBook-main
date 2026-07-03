import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_5_1_4 (from Chap05) -/
open scoped Gradient HessianLocalNorm

noncomputable section

universe u

/- Theorem 5.1.4 lies in the Chapter 5 self-concordance / logarithmic-barrier domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the constant-bearing chapter owner for
  self-concordance on a domain;
* `IsSelfConcordantOnWith.hessian_isPositive` from `Definition_5_1_1`, the chapter bridge from
  self-concordance to the pointwise Hessian-positivity owner;
* `hessianLocalNorm` from `Definition_5_1_1`, the chapter owner for the Hessian-induced local
  norm used by later barrier-parameter APIs;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the barrier analogue used downstream;
* `hessian` from `Chap01/Definition_1_4_16`, the canonical second-order owner;
* `convexOn_iff_hessian_isPositive` from `Chap02/Theorem_2_4`, the local owner-level Hessian
  positivity criterion for convex `C²` data.

Source/core/bridge triage:
* source-facing: the logarithmic barrier `x ↦ -log (β - f x)`;
* core/canonical: `ContinuousLinearMap.IsPositive (hessian f x)` for the Hessian comparison
  clause, and `IsSelfConcordantOnWith dom Mf f` for the quantitative self-concordance clause;
* bridge/view: the textbook positivity estimate `0 < β - f x` on that strict sublevel set.

Primitive data:
* the function `f`;
* the threshold `β`;
* the ambient domain `dom`;
* the self-concordance owner `IsSelfConcordantOnWith dom Mf f`, which supplies the `C³`
  regularity and pointwise Hessian positivity needed for clauses (2) and (3).

Derived API:
* the strict sublevel set itself, expressed directly by the canonical set-builder rather than a
  second packaged owner;
* the barrier-gradient square estimate on the owner surface `‖h‖[sublevelLogBarrier f β; x]`,
  stated directly on `IsSelfConcordantOnWith dom Mf f` so that the required differential
  regularity remains explicit in the public API;
* the self-concordance constant formula, used directly in the main theorem rather than through a
  one-off wrapper.

This file therefore keeps the barrier as the source-facing owner and deletes the duplicate-wheel
derived wrappers around its natural domain and parameter formula. -/

variable {E : Type u}

/-- The logarithmic barrier associated with the strict sublevel set `{x | f x < β}` is
`x ↦ -log (β - f x)`. -/
def sublevelLogBarrier (f : E → ℝ) (β : ℝ) : E → ℝ :=
  fun x ↦ -Real.log (β - f x)

/-- Evaluating `sublevelLogBarrier f β` recovers the textbook formula `-log (β - f x)`. -/
@[simp]
theorem sublevelLogBarrier_apply (f : E → ℝ) (β : ℝ) (x : E) :
    sublevelLogBarrier f β x = -Real.log (β - f x) :=
  rfl

/-- Theorem 5.1.4 (1): on the strict sublevel set `{x | f x < β}`, the logarithmic barrier
`x ↦ -log (β - f x)` is well defined because its argument is positive. -/
-- Proof sketch: if `f x < β`, then `0 < β - f x`; this is exactly the positivity needed for
-- `Real.log (β - f x)`.
theorem sublevelLogBarrier_arg_pos_of_mem_domain
    (f : E → ℝ) (β : ℝ) {x : E} (hx : f x < β) :
    0 < β - f x := sorry

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section SublevelLogBarrier

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}

namespace IsSelfConcordantOnWith

/-- Theorem 5.1.4 (2): at every point of the strict sublevel set `{x | f x < β}` inside the
domain of a self-concordant function, the Hessian quadratic form of `x ↦ -log (β - f x)`
dominates the square of the gradient pairing. -/
-- Proof sketch: `hself.contDiffOn` supplies the second-order regularity needed to differentiate
-- `τ ↦ -log (β - f (x + τ • h))` twice, while `hself.hessian_isPositive hx` makes the Hessian
-- contribution nonnegative.
theorem sublevelLogBarrier_hessian_quadraticForm_ge_gradient_sq
    (hself : IsSelfConcordantOnWith dom Mf f) (β : ℝ) {x h : E}
    (hx : x ∈ dom) (hβ : f x < β) :
    inner ℝ h (hessian (sublevelLogBarrier f β) x h) ≥
      (inner ℝ (∇ (sublevelLogBarrier f β) x) h) ^ (2 : ℕ) := sorry

/-- Theorem 5.1.4 (2), owner-level bridge: for a self-concordant input, the square of the
gradient pairing of `x ↦ -log (β - f x)` is bounded by the square of the canonical Hessian local
norm. -/
theorem sublevelLogBarrier_gradient_inner_sq_le
    (hself : IsSelfConcordantOnWith dom Mf f) (β : ℝ) {x h : E}
    (hx : x ∈ dom) (hβ : f x < β) :
    (inner ℝ (∇ (sublevelLogBarrier f β) x) h) ^ (2 : ℕ) ≤
      ‖h‖[sublevelLogBarrier f β; x] ^ (2 : ℕ) := sorry

end IsSelfConcordantOnWith

/-- Theorem 5.1.4 (3): if `f` is bounded below on `dom` by `f*`, then the barrier
`x ↦ -log (β - f x)` is self-concordant on `{x ∈ dom | f x < β}` with constant
`sqrt (1 + M_f^2 * (β - f*))`. -/
-- Proof sketch: compute the third directional derivative of `x ↦ -log (β - f x)` and rewrite it
-- in terms of the Hessian quadratic form and gradient pairing of `f`. Use the self-concordance
-- inequality for `f`, the quadratic-form lower bound from the previous clause applied to the
-- pointwise Hessian-positivity owner furnished by `hself.hessian_isPositive hx`, and the estimate
-- `β - f x ≤ β - f*` coming from the lower bound hypothesis to obtain the stated constant; when
-- `β ≤ f*`, the strict sublevel domain is empty, so the same statement remains valid without a
-- separate positivity hypothesis on `β - f*`.
theorem sublevelLogBarrier_isSelfConcordantOnWith
    (hself : IsSelfConcordantOnWith dom Mf f) (β fStar : ℝ)
    (h_lower : ∀ ⦃x : E⦄, x ∈ dom → fStar ≤ f x) :
    IsSelfConcordantOnWith
      {x : E | x ∈ dom ∧ f x < β}
      (NNReal.sqrt (1 + Mf ^ (2 : ℕ) * Real.toNNReal (β - fStar)))
      (sublevelLogBarrier f β) := sorry

end SublevelLogBarrier

end

/-! ### Corollary_5_1_5 (from Chap05) -/
open scoped Gradient HessianLocalNorm DikinEllipsoidNotation

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Corollary 5.1.5 lies in the Chapter 5 self-concordance / Hessian-comparison domain.

Sampled owner declarations:
* `hessian` in `Chap01/Definition_1_4_16`, the canonical Hessian operator owner;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` in `Chap05/Definition_5_1_1`, the chapter owner
  for the local Hessian norm;
* `IsSelfConcordantOnWith` in `Chap05/Definition_5_1_1`, the quantitative self-concordance owner;
* `IsSelfConcordantOnWith.openDikinEllipsoid_inv_constant_subset` in `Chap05/Theorem_5_1_5`,
  which derives the domain membership of points satisfying the Dikin-radius hypothesis;
* `IsSelfConcordantOnWith.hessian_loewner_bounds_of_mem_openDikinEllipsoid` in
  `Chap05/Proposition_5_0_15`, the pointwise Hessian comparison theorem in the same domain.

Source/core/bridge triage:
* source-facing: the averaged Hessian along the segment from `x` to `y` and its two comparison
  inequalities;
* core/canonical: `hessian f z`, `‖u‖[f; x]`, the interval integral
  `∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))`, and `IsSelfConcordantOnWith dom Mf f`;
* bridge/view: the Dikin-radius hypothesis, which supplies both `0 < Mf` and the derived
  membership `y ∈ dom` needed for pointwise Hessian comparison along the segment.

Primitive data:
* a complete real inner-product space `E`;
* a domain `dom`, a function `f`, a self-concordance constant `Mf`, and points `x y : E`.

Derived API:
* the averaged Hessian integral `∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))`;
* the admissibility hypothesis `y ∈ W⁰[f; x](1 / (Mf : ℝ))`;
* the individual lower and upper Loewner bounds obtained by projecting the paired comparison.

This file keeps the averaged Hessian as a source-facing integral expression built directly from the
canonical Hessian owner. The primitive owner-level result is the paired Loewner comparison, in
the same shape as `hessian_loewner_bounds_of_mem_openDikinEllipsoid`; the one-sided inequalities
are then exposed as derived projections rather than as parallel primitive wrappers. -/

namespace IsSelfConcordantOnWith

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}

section

variable (hself : IsSelfConcordantOnWith dom Mf f) {x y : E} (hx : x ∈ dom)
variable (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ)))

-- Proof sketch: set `r := ‖y - x‖[f; x]` and
-- `G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))`. Apply the pointwise
-- self-concordant Hessian comparison along the segment `τ ↦ x + τ • (y - x)`, derive `0 < Mf`
-- and `y ∈ dom` from the Dikin-radius hypothesis via Theorem 5.1.5(1), then integrate the
-- resulting Loewner inequalities over `τ ∈ [0, 1]`. The scalar integrals are
-- `∫_0^1 (1 - τ M_f r)^2 dτ = 1 - M_f r + (M_f^2 r^2) / 3` and
-- `∫_0^1 (1 - τ M_f r)⁻² dτ = (1 - M_f r)⁻¹`.
/-- Corollary 5.1.5: if `f` is self-concordant on `dom` with positive parameter `M_f`, `x ∈ dom`,
and `y ∈ W⁰[f; x](1 / (Mf : ℝ))`, then the average Hessian along the segment from `x` to `y` lies
between the two explicit Loewner bounds built from `∇² f(x)`. In the source notation,
`r := ‖y - x‖_x` and `G := ∫_0^1 ∇² f(x + τ (y - x)) dτ`. The positivity of `M_f` and the
membership `y ∈ dom` are consequences of the displayed open-Dikin hypothesis. -/
theorem segmentAverageHessian_bounds
    :
    let r := ‖y - x‖[f; x]
    let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
    ((1 - (Mf : ℝ) * r + ((Mf : ℝ) ^ (2 : ℕ) * r ^ (2 : ℕ)) / 3) • hessian f x ≤ G) ∧
      (G ≤ (1 / (1 - (Mf : ℝ) * r)) • hessian f x) := sorry

/-- Corollary 5.1.5 (lower bound): if `f` is self-concordant on `dom` with positive parameter
`M_f`, `x ∈ dom`, and `y ∈ W⁰[f; x](1 / (Mf : ℝ))`, then the average Hessian along the segment
from `x` to `y` dominates the explicit lower Loewner bound built from `∇² f(x)`. The positivity
of `M_f` and the membership `y ∈ dom` are consequences of the displayed open-Dikin hypothesis. -/
theorem segmentAverageHessian_lower_bound
    :
    let r := ‖y - x‖[f; x]
    let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
    (1 - (Mf : ℝ) * r + ((Mf : ℝ) ^ (2 : ℕ) * r ^ (2 : ℕ)) / 3) • hessian f x ≤ G := by
  simpa using segmentAverageHessian_bounds.1

/-- Corollary 5.1.5 (upper bound): if `f` is self-concordant on `dom` with positive parameter
`M_f`, `x ∈ dom`, and `y ∈ W⁰[f; x](1 / (Mf : ℝ))`, then the average Hessian along the segment
from `x` to `y` is bounded above by the explicit Loewner bound built from `∇² f(x)`. The
positivity of `M_f` and the membership `y ∈ dom` are consequences of the displayed open-Dikin
hypothesis. -/
theorem segmentAverageHessian_upper_bound
    :
    let r := ‖y - x‖[f; x]
    let G := ∫ τ in (0 : ℝ)..1, hessian f (x + τ • (y - x))
    G ≤ (1 / (1 - (Mf : ℝ) * r)) • hessian f x := by
  simpa using segmentAverageHessian_bounds.2

end

end IsSelfConcordantOnWith

end

/-! ### Example_5_1_5 (from Chap05) -/
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

/-! ### Lemma_5_1_5 (from Chap05) -/
open scoped SelfConcordantAuxiliaryFunction

noncomputable section

/- Lemma 5.1.5 lies in the Chapter 5 self-concordant auxiliary-function domain.

Sampled owner-style declarations:
* `selfConcordantOmega` and the scoped notation `ω` from `Definition_5_0_21`, the chapter owner
  for the auxiliary function `t ↦ t - log (1 + t)`;
* `selfConcordantOmegaStar` and the scoped notation `ω_*` from `Definition_5_0_21`, the chapter
  owner for the auxiliary function `t ↦ -t - log (1 - t)`;
* `selfConcordantOmegaArg` and `selfConcordantOmegaStarArg` from `Definition_5_0_21`, the
  scaled-argument bridge constructors used elsewhere in Chapter 5 but not as the main scalar
  surface here;
* `selfConcordantOmega_apply` and `selfConcordantOmegaStar_apply`, the canonical owner-level
  evaluation lemmas recovering the textbook scalar formulas;
* `Real.log_le_sub_one_of_pos` in mathlib, the standard logarithmic comparison theorem underlying
  the elementary rational sandwich estimates.

Source/core/bridge triage:
* source-facing: the textbook rational lower and upper bounds for `ω` on `[0, ∞)` and for `ω_*`
  on `[0, 1)`;
* core/canonical: the Chapter 5 owners `ω` and `ω_*`;
* bridge/view: the subtype constructors `selfConcordantOmegaArg`,
  `selfConcordantOmegaStarArg`, and the subtype-level evaluation lemmas
  `selfConcordantOmega_apply`, `selfConcordantOmegaStar_apply`.

Primitive data:
* a real parameter `t` in the textbook domain (`0 ≤ t`, or `0 ≤ t < 1` for `ω_*`).

Derived API:
* the rational comparison statements, now stated directly against the canonical owners `ω` and
  `ω_*`, with the raw logarithmic formulas recovered by the existing evaluation lemmas.

This refinement keeps the source-facing inequalities unchanged while removing the duplicate raw
formula surface from the main declarations. -/

-- Proof sketch: use the elementary denominator comparison
-- `1 + (2 / 3) t ≤ 1 + t` for `t ≥ 0`, then divide the common numerator `t^2` by the
-- corresponding positive denominators.
/-- The simpler lower rational approximation with denominator `1 + t` is bounded above by the
intermediate lower bound with denominator `1 + (2 / 3) t`. -/
theorem selfConcordantOmega_simpleLowerBound_le_intermediate
    {t : ℝ} (ht : 0 ≤ t) :
    t ^ 2 / (2 * (1 + t)) ≤
      t ^ 2 / (2 * (1 + (2 / 3 : ℝ) * t)) := sorry

-- Proof sketch: compare `ω' (t) = t / (1 + t)` with the derivatives of
-- `t ↦ t^2 / (2 * (1 + (2 / 3) * t))` and `t ↦ t^2 / (2 + t)` on `[0, ∞)`, use that all three
-- functions vanish at `t = 0`, and integrate the derivative inequalities.
/-- Lemma 5.1.5: for `t ≥ 0`, the self-concordant auxiliary function
`ω(t)` lies between the rational bounds
`t² / (2 * (1 + (2 / 3) t))` and `t² / (2 + t)`. -/
theorem selfConcordantOmega_bounds
    {t : ℝ} (ht : 0 ≤ t) :
    let tω := selfConcordantOmegaArg 1 t (by
      have h : -1 < ((1 : NNReal) : ℝ) * t := neg_one_lt_mf_mul_of_nonneg ht
      simpa using h)
    t ^ 2 / (2 * (1 + (2 / 3 : ℝ) * t)) ≤ ω tω ∧
      ω tω ≤ t ^ 2 / (2 + t) := sorry

-- Proof sketch: compare `ω'_* (t) = t / (1 - t)` with the derivatives of
-- `t ↦ t^2 / (2 - t)` and `t ↦ t^2 / (2 * (1 - t))` on `[0, 1)`, note that all three functions
-- vanish at `t = 0`, and integrate the derivative inequalities along the interval.
/-- For `t ∈ [0, 1)`, the auxiliary function `ω_*(t)` is squeezed between
`t² / (2 - t)` and `t² / (2 * (1 - t))`. -/
theorem selfConcordantOmegaStar_bounds
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) :
    let τω := selfConcordantOmegaStarArg 1 τ (by simpa using hτ1)
    τ ^ 2 / (2 - τ) ≤ ω_* τω ∧
      ω_* τω ≤ τ ^ 2 / (2 * (1 - τ)) := sorry

end

/-! ### Theorem_5_1_5 (from Chap05) -/
noncomputable section

universe u

open scoped HessianLocalNorm DikinEllipsoidNotation

/-
Theorem 5.1.5 belongs to the self-concordance / Dikin-ellipsoid domain.

Sampled owner declarations:
* `hessianLocalNorm` in `Chap05/Definition_5_1_1`, the canonical local Hessian norm;
* `openDikinEllipsoid` together with the notation `W⁰[f; x](r)` in `Chap05/Definition_5_0_13`,
  the Chapter 5 owner for the open local-norm ball;
* `mem_openDikinEllipsoid_iff_hessian_quadratic_lt_sq` in `Chap05/Definition_5_0_14`, the
  textbook quadratic bridge for the same Dikin geometry;
* `IsSelfConcordantOnWith` in `Chap05/Definition_5_1_1`, the chapter owner for quantitative
  self-concordance.

Best owner abstraction:
* source-facing: the open Dikin ellipsoid around `x`;
* core/canonical: `IsSelfConcordantOnWith dom Mf f` together with `‖u‖[f; x]`;
* bridge/view: the membership lemmas for `W⁰[f; x](r)` and its Hessian-quadratic reformulation.

Primitive data:
* a complete real inner-product space `E`;
* a domain `dom`, a function `f`, a self-concordance constant `Mf`, and points `x y : E`.

Derived API:
* the open Dikin ellipsoid `W⁰[f; x](r)`;
* the local displacement norms `‖y - x‖[f; x]` and `‖y - x‖[f; y]`.

This file records the Dikin-ellipsoid and local-norm transport consequences directly as
owner-level methods in `IsSelfConcordantOnWith`, rather than keeping a parallel top-level wrapper
API. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace IsSelfConcordantOnWith

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}

-- Proof sketch: apply the Dikin ellipsoid inclusion theorem for self-concordant functions. The
-- center hypothesis `hx : x ∈ dom` supplies the standard Dikin radius `1 / M_f`; when `Mf = 0`,
-- that radius is `0`, so `W⁰[f; x](1 / M_f)` is empty and the inclusion is vacuous.
/-- Theorem 5.1.5 (1): if `f` is self-concordant on `dom` with parameter `M_f`, then for every
`x ∈ dom`, the open Dikin ellipsoid `W⁰[f; x](1 / M_f)` is contained in `dom`.
No separate positivity hypothesis on `M_f` is needed. -/
theorem openDikinEllipsoid_inv_constant_subset
    (hself : IsSelfConcordantOnWith dom Mf f) {x : E} (hx : x ∈ dom) :
    W⁰[f; x](1 / (Mf : ℝ)) ⊆ dom := sorry

-- Proof sketch: consider the displacement `h := y - x` and the associated univariate reciprocal
-- local-norm function `t ↦ 1 / ‖h‖_{x + t h}`. The self-concordance differential inequality
-- bounds its slope by `Mf`, and evaluating the resulting estimate between `t = 0` and `t = 1`
-- yields the lower bound after inversion; the same formula remains meaningful when `Mf = 0`.
/-- Theorem 5.1.5 (2): for `x, y ∈ dom`, the local norm of the displacement `y - x` at `y` is at
least `‖y - x‖_x / (1 + M_f ‖y - x‖_x)`. -/
theorem displacement_localNorm_lower_bound
    (hself : IsSelfConcordantOnWith dom Mf f) {x y : E} (hx : x ∈ dom) (hy : y ∈ dom) :
    ‖y - x‖[f; y] ≥ ‖y - x‖[f; x] / (1 + (Mf : ℝ) * ‖y - x‖[f; x]) := sorry

-- Proof sketch: use the same reciprocal local-norm function as in clause (2), but now combine
-- the self-concordance slope bound with the Dikin-radius hypothesis `y ∈ W⁰[f; x](1 / M_f)` to
-- obtain a positive lower bound for the reciprocal at `t = 1`; clause (1) turns that same
-- hypothesis into the derived domain membership `y ∈ dom`, and inverting gives the claimed upper
-- bound. The displayed Dikin-radius hypothesis already rules out the degenerate case `Mf = 0`.
/-- Theorem 5.1.5 (3): if `x ∈ dom` and `y` lies in the open Dikin ellipsoid
`W⁰[f; x](1 / M_f)`, then the local norm of the displacement `y - x` at `y` is at most
`‖y - x‖_x / (1 - M_f ‖y - x‖_x)`. The open-Dikin hypothesis itself excludes the
degenerate case `M_f = 0`, and the domain membership `y ∈ dom` is derived from clause `(1)`. -/
theorem displacement_localNorm_upper_bound
    (hself : IsSelfConcordantOnWith dom Mf f) {x y : E} (hx : x ∈ dom)
    (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    ‖y - x‖[f; y] ≤ ‖y - x‖[f; x] / (1 - (Mf : ℝ) * ‖y - x‖[f; x]) := sorry

end IsSelfConcordantOnWith

end

/-! ### Example_5_1_6 (from Chap05) -/
open scoped Gradient HessianLocalNorm

noncomputable section

universe u

/- Example 5.1.6 lies in the Chapter 5 self-concordance / strong-convexity / Hessian-Lipschitz
domain.

Sampled owner-style declarations:
* `StrongConvexOn`, the canonical owner for whole-space strong convexity;
* `HasLipschitzContinuousHessian` and the theorem-surface notation `f ∈ C22[L₃]` from
  `Definition_5_0_7`, the canonical chapter owner for whole-space Hessian-Lipschitz smoothness;
* `fderiv ℝ (hessian f) x u` from `Definition_5_0_8`, the canonical Chapter 5 owner for the
  directional derivative of the Hessian operator;
* `IsSelfConcordantOnWith.of_thirdDerivative_operator_le` from `Corollary_5_1_1`, the canonical
  owner-level bridge from the operator inequality to `IsSelfConcordantOnWith`;
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the stronger Chapter 5 owner that packages
  open-convex `C³` self-concordance data.

Source/core/bridge triage:
* source-facing: the Hessian-operator inequality
  `D³f(x)[u] ≤ (L₃ / (σ₂ * √σ₂)) ‖u‖_{∇² f(x)} ∇²f(x)` at a point `x`, obtained from
  `StrongConvexOn Set.univ σ2 f`, `f ∈ C22[L3]`, and the pointwise `C³` regularity needed to
  interpret `D³f(x)[u]`;
* core/canonical: `StrongConvexOn Set.univ σ2 f`, `f ∈ C22[L3]`, `fderiv ℝ (hessian f) x u`,
  `hessian f x`, and `‖u‖[f; x]`;
* bridge/view: `IsSelfConcordantOnWith.of_thirdDerivative_operator_le`, which converts this
  source-facing operator inequality into the Chapter 5 owner `IsSelfConcordantOnWith`.

Primitive data:
* the objective `f`;
* the strong-convexity parameter `σ₂`;
* the Hessian-Lipschitz constant `L₃`;
* the owner hypotheses `StrongConvexOn Set.univ σ2 f` and `f ∈ C22[L3]`;
* the pointwise regularity witness `ContDiffAt ℝ 3 f x`, needed to interpret the operator
  `fderiv ℝ (hessian f) x u` as the genuine third derivative `D³f(x)[u]`.

Derived API:
* the operator inequality
  `fderiv ℝ (hessian f) x u ≤
    ((L₃ / (σ₂ * √σ₂)) ‖u‖_{∇² f(x)}) • ∇² f(x)`;
* under the extra bridge hypothesis `ContDiff ℝ 3 f`, the Chapter 5 owner
  `IsSelfConcordantOnWith Set.univ
    (Real.toNNReal ((L3 : ℝ) / (2 * σ2 * Real.sqrt σ2))) f`.

This refinement keeps Example 5.1.6 itself at the source-facing `StrongConvexOn + C22[L₃]`
layer and exposes its main conclusion directly on the canonical Hessian owner
`fderiv ℝ (hessian f) x u`. The stronger global `C³` packaging into
`IsSelfConcordantOnWith` remains a separate bridge theorem obtained through
`IsSelfConcordantOnWith.of_thirdDerivative_operator_le`. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section

variable {f : E → ℝ} {σ2 : ℝ} {L3 : NNReal}

namespace StrongConvexOn

variable (hf_strong : StrongConvexOn Set.univ σ2 f) (hσ2 : 0 < σ2) (hf_hessian : f ∈ C22[L3])
include hf_strong hσ2 hf_hessian

-- Proof sketch: use `ContDiffAt ℝ 3 f x` to identify `fderiv ℝ (hessian f) x u` with the genuine
-- directional third derivative operator `D³f(x)[u]`. The `C22[L₃]` hypothesis gives the operator
-- norm bound `‖D³f(x)[u]‖ ≤ L₃ ‖u‖`, while strong convexity yields the Loewner lower bound
-- `σ₂ • 1 ≤ hessian f x`, hence `‖v‖ ≤ ‖v‖[f; x] / √σ₂` for every `v`. Applying this estimate to
-- both slots of the bilinear operator `D³f(x)[u]` gives
-- `D³f(x)[u] ≤ (L₃ / (σ₂ * √σ₂)) ‖u‖[f; x] • ∇²f(x)`.
/-- Example 5.1.6: if `f` is strongly convex on all of `E` with parameter `σ₂`, belongs to the
chapter smoothness class `C22[L₃]`, and is `C³` at `x`, then the directional derivative of its
Hessian satisfies the operator inequality
`D³f(x)[u] ≤ (L₃ / (σ₂ * √σ₂)) ‖u‖_{∇² f(x)} ∇²f(x)`. This keeps the example at the
source-facing operator layer used by Corollary 5.1.1. -/
theorem thirdDerivative_operator_le_of_mem_C22
    {x u : E} (h_contDiffAt : ContDiffAt ℝ 3 f x) :
    fderiv ℝ (hessian f) x u ≤
      (((L3 : ℝ) / (σ2 * Real.sqrt σ2)) * ‖u‖[f; x]) • hessian f x := sorry

-- Proof sketch: use `IsSelfConcordantOnWith.of_thirdDerivative_operator_le` with
-- `dom = Set.univ`.
-- The preceding theorem supplies the operator inequality with coefficient
-- `2 * (L₃ / (2 * σ₂ * √σ₂))`, while `hf_strong` gives convexity on `Set.univ` and the global
-- hypothesis `h_contDiff` provides the required `C³` regularity on `Set.univ`.
/-- Bridge theorem: adding the separate `C³` hypothesis upgrades the operator estimate from
Example 5.1.6 to the Chapter 5 owner `IsSelfConcordantOnWith`; the modulus is converted to the
owner `strongConvexSelfConcordanceConstant σ₂ L₃`. -/
theorem isSelfConcordantOnWith_of_mem_C22_contDiff
    (h_contDiff : ContDiff ℝ 3 f) :
    IsSelfConcordantOnWith Set.univ
      (strongConvexSelfConcordanceConstant σ2 L3) f := by
  refine IsSelfConcordantOnWith.of_thirdDerivative_operator_le isOpen_univ ?_ ?_ ?_
  · simpa using h_contDiff.contDiffOn
  · simpa [strongConvexOn_zero] using (hf_strong.mono hσ2.le : StrongConvexOn Set.univ 0 f)
  · intro x _hx u
    change fderiv ℝ (hessian f) x u ≤
      (2 * (strongConvexSelfConcordanceConstant σ2 L3 : ℝ) * ‖u‖[f; x]) •
        hessian f x
    have hthird :
        fderiv ℝ (hessian f) x u ≤
          (((L3 : ℝ) / (σ2 * Real.sqrt σ2)) * ‖u‖[f; x]) • hessian f x :=
      hf_strong.thirdDerivative_operator_le_of_mem_C22 hσ2 hf_hessian
        (show ContDiffAt ℝ 3 f x from h_contDiff.contDiffAt)
    rw [two_mul_coe_strongConvexSelfConcordanceConstant hσ2]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hthird

omit hf_strong hσ2 hf_hessian

end StrongConvexOn

end

/-! ### Lemma_5_1_6 (from Chap05) -/
open scoped ConvexAnalysis Gradient WithTopConvexAnalysis

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Lemma 5.1.6 lies in the chapter's Fenchel-duality / self-concordance domain.

Primary domain:
- Fenchel conjugates of `WithTop ℝ`-valued functions whose finite real part is self-concordant on
  its effective domain, with the closedness of its constrained epigraph supplied separately from
  the self-concordance owner.

Sampled owner declarations before refinement:
- `fenchelDual` / notation `f⋆` in `Chap05/Definition_5_0_27`, the source-facing Fenchel-dual
  owner;
- `IsSelfConcordantOn` in `Chap05/Definition_5_1_1`, the chapter owner for self-concordance on a
  domain;
- `HasPositiveDefiniteHessianOn` in `Chap05/Definition_5_0_23`, the chapter owner for positive
  definiteness of the Hessian on a domain;
- `IsSelfConcordantOn.hasPositiveDefiniteHessianOn_of_no_affine_line` in `Chap05/Theorem_5_1_6`,
  the canonical bridge from self-concordance plus closed constrained epigraph to positive
  definiteness of the Hessian;
- `IsMaxOn`, the canonical maximizer predicate for the Fenchel support functional
  `y ↦ ⟪s, y⟫ - f y`.

Best owner abstraction:
- source-facing: the self-concordant standing assumptions on the primal owner
  `f : E → WithTop ℝ` and the resulting properties of `f⋆`;
- core/canonical: `dom f`, `withTopRealPart f`, `dom (f⋆)`, `extendedRealRealPart (f⋆)`, and
  `effectiveEpigraph (f⋆)`;
- bridge/view: the gradient image `∇ (withTopRealPart f) '' dom f`.

Primitive data:
- the primal owner `f : E → WithTop ℝ`;
- closedness of the constrained epigraph of the finite real part `withTopRealPart f` on `dom f`;
- self-concordance of `withTopRealPart f` on `dom f`;
- the no-affine-line standing assumption used in the source discussion.

Derived API in this file:
- the singleton-subdifferential and gradient-recovery lemmas on `dom f`;
- existence of Fenchel-support maximizers on `dom f` for points of `dom (f⋆)`;
- the source-facing identity `dom (f⋆) = {∇ f(x) | x ∈ dom f}`;
- the source-level openness consequence for `dom (f⋆)`.
- the positive-definite Hessian owner `HasPositiveDefiniteHessianOn (dom f) (withTopRealPart f)`,
  derived internally from `hself`, the closed constrained epigraph hypothesis, and the
  no-affine-line hypothesis via
  `IsSelfConcordantOn.hasPositiveDefiniteHessianOn_of_no_affine_line`.

Closedness of `effectiveEpigraph (f⋆)` and convexity of `extendedRealRealPart (f⋆)` already
live as unconditional canonical owners in
`Chap06/Text_6_1_1_Conjugate_Closedness_and_Domain_Nonemptiness`;
they are reused directly rather than re-exported here under stronger self-concordant hypotheses.

This refinement deletes the local `IsLegendreFunction` wrapper introduced in the previous round.
The source item is not defining a new owner-level Legendre class; it is proving properties of the
canonical Fenchel dual under the chapter's standing self-concordant assumptions. The public API
therefore stays on the existing chapter owners `constrainedEpigraph`, `IsSelfConcordantOn`,
`HasPositiveDefiniteHessianOn`, `f⋆`, `dom`, and `effectiveEpigraph`, with the gradient-image
formula exposed as the bridge statement rather than as a replacement owner. -/

omit [CompleteSpace E] in
/-- A Fenchel-support maximizer yields the corresponding subgradient on the effective domain. -/
theorem subgradient_mem_subdifferential_of_fenchelSupport_isMaxOn
    {f : E → WithTop ℝ} {s x : E}
    (hx : x ∈ dom f)
    (hmax : IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x) :
    s ∈ ∂ f(x) := by
  refine mem_subdifferential_iff.2 ⟨hx, ?_⟩
  intro y hy
  have hsupport : inner ℝ s y - withTopRealPart f y ≤ inner ℝ s x - withTopRealPart f x :=
    hmax hy
  have hsupport' :
      withTopRealPart f x + inner ℝ s (y - x) ≤ withTopRealPart f y := by
    have hsupport'' :
        withTopRealPart f x + (inner ℝ s y - inner ℝ s x) ≤ withTopRealPart f y := by
      linarith
    simpa [inner_sub_right] using hsupport''
  rw [← coe_withTopRealPart hy, ← coe_withTopRealPart hx]
  exact_mod_cast hsupport'

section SelfConcordantPrimal

variable {f : E → WithTop ℝ}
variable (hself : IsSelfConcordantOn (dom f) (withTopRealPart f))

include hself

/-- For a self-concordant primal function, the subdifferential at a finite point is
the singleton consisting of the primal gradient. -/
theorem subdifferential_eq_singleton_gradient_of_selfConcordant
    {x : E} (hx : x ∈ dom f) :
    ∂ f(x) = {∇ (withTopRealPart f) x} := by
  rcases hself with ⟨Mf, hMf⟩
  have hxin : x ∈ interior (dom f) := by
    rwa [hMf.isOpen_domain.interior_eq]
  have hfd : DifferentiableAt ℝ (withTopRealPart f) x := by
    exact
      (hMf.contDiffOn.contDiffAt (hMf.isOpen_domain.mem_nhds hx)).differentiableAt
        (by norm_num)
  exact subdifferential_eq_singleton_gradient hMf.convexOn hxin hfd

/-- At a Fenchel-support maximizer of a self-concordant function, the primal
gradient recovers the dual slope. -/
theorem gradient_eq_of_fenchelSupport_isMaxOn
    {s x : E}
    (hx : x ∈ dom f)
    (hmax : IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x) :
    ∇ (withTopRealPart f) x = s := by
  have hsub : s ∈ ∂ f(x) :=
    subgradient_mem_subdifferential_of_fenchelSupport_isMaxOn hx hmax
  have hs_mem : s ∈ ({∇ (withTopRealPart f) x} : Set E) := by
    simpa [subdifferential_eq_singleton_gradient_of_selfConcordant hself hx] using hsub
  have hs : s = ∇ (withTopRealPart f) x := by
    simpa using hs_mem
  exact hs.symm

/-- Every gradient vector of the primal finite real part lies in the effective domain of the
Fenchel dual. -/
theorem image_gradient_subset_dom_fenchelDual_of_selfConcordant
    : ∇ (withTopRealPart f) '' dom f ⊆ dom (f⋆) := by
  rintro s ⟨x, hx, rfl⟩
  have hsingleton : ∂ f(x) = {∇ (withTopRealPart f) x} :=
    subdifferential_eq_singleton_gradient_of_selfConcordant hself hx
  have hgrad_mem : ∇ (withTopRealPart f) x ∈ ∂ f(x) := by
    simp [hsingleton]
  exact subdifferential_subset_dom_fenchelDual hgrad_mem

end SelfConcordantPrimal

section StandingAssumptions

variable {f : E → WithTop ℝ}
variable
  (hclosed :
    IsClosed (constrainedEpigraph (dom f) (fun y ↦ (withTopRealPart f y : WithTop ℝ))))
variable (hself : IsSelfConcordantOn (dom f) (withTopRealPart f))
variable
  (hnoAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ dom f)

include hclosed hself hnoAffineLine

/-- Under the standing assumptions of Section 5.1.5, every finite dual point admits a
Fenchel-support maximizer on the primal effective domain. -/
theorem exists_fenchelSupport_isMaxOn_of_mem_dom_fenchelDual
    {s : E} (hs : s ∈ dom (f⋆)) :
    ∃ x, x ∈ dom f ∧
      IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x := by
  letI : HasPositiveDefiniteHessianOn (dom f) (withTopRealPart f) :=
    IsSelfConcordantOn.hasPositiveDefiniteHessianOn_of_no_affine_line hself
      hclosed hnoAffineLine
  sorry

/-- Under the standing self-concordant hypotheses, every finite dual point belongs to the
gradient image of the primal effective domain. -/
theorem dom_fenchelDual_subset_image_gradient_of_selfConcordant
    : dom (f⋆) ⊆ ∇ (withTopRealPart f) '' dom f := by
  intro s hs
  obtain ⟨x, hx, hmax⟩ :=
    exists_fenchelSupport_isMaxOn_of_mem_dom_fenchelDual
      hclosed hself hnoAffineLine hs
  have hgrad :
      ∇ (withTopRealPart f) x = s :=
    gradient_eq_of_fenchelSupport_isMaxOn hself hx hmax
  refine ⟨x, hx, ?_⟩
  simpa using hgrad

/-- Lemma 5.1.6: under the standing self-concordant assumptions of Section 5.1.5, the effective
domain of the Fenchel dual is exactly the gradient image of the primal effective domain. -/
theorem dom_fenchelDual_eq_image_gradient_of_selfConcordant
    : dom (f⋆) = ∇ (withTopRealPart f) '' dom f := by
  refine Set.Subset.antisymm
    (dom_fenchelDual_subset_image_gradient_of_selfConcordant hclosed hself hnoAffineLine)
    (image_gradient_subset_dom_fenchelDual_of_selfConcordant hself)

/-- Under the standing self-concordant assumptions, the effective domain of the Fenchel dual is
open. -/
theorem isOpen_dom_fenchelDual_of_selfConcordant
    : IsOpen (dom (f⋆)) := by
  letI : HasPositiveDefiniteHessianOn (dom f) (withTopRealPart f) :=
    IsSelfConcordantOn.hasPositiveDefiniteHessianOn_of_no_affine_line hself
      hclosed hnoAffineLine
  sorry

end StandingAssumptions

end

/-! ### Theorem_5_1_6 (from Chap05) -/
noncomputable section

universe u

/-
Theorem 5.1.6 belongs to the Chapter 5 self-concordance / closed-convex domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantOn` from `Definition_5_1_1`, the source-facing qualitative owner when the
  value of the self-concordance constant is not part of the statement;
* `HasPositiveDefiniteHessianOn` from `Definition_5_0_23`, the chapter owner for pointwise
  Hessian positivity together with strict Hessian quadratic-form positivity on a domain;
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the quantitative owner used only after
  unpacking a witness from `IsSelfConcordantOn`;
* `hessian` from `Chap01/Definition_1_4_16`, the canonical second-order owner replacing the raw
  `fderiv ℝ (∇ f)` shell;
* `hessianLocalNorm` and `hessianLocalNorm_def` from `Definition_5_1_1`, the canonical bridge
  from the Hessian owner to the local norm;
* `constrainedEpigraph` from `Chap03/Definition_3_3`, the chapter owner for the source epigraph
  over a feasible domain, whose closedness supplies the missing hypothesis from the source
  theorem.

Source/core/bridge triage:
* source-facing: strict positivity of the Hessian quadratic form in every nonzero direction under
  qualitative self-concordance and the source no-affine-line hypothesis;
* core/canonical: `HasPositiveDefiniteHessianOn dom f`, the Hessian owner `hessian f x`, and the
  Chapter 3 constrained-epigraph owner on `dom`;
* bridge/view: pointwise positivity and strict local-norm positivity read canonically via
  `HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem`,
  `HasPositiveDefiniteHessianOn.posdef`, and `hessianLocalNorm_def`.

Primitive data:
* the ambient complete real inner-product space `E`;
* a domain `dom`, objective `f`, and the closed constrained epigraph
  `constrainedEpigraph dom (fun y ↦ (f y : WithTop ℝ))`;
* the no-affine-line hypothesis on `dom`.

Derived API:
* the chapter owner `HasPositiveDefiniteHessianOn dom f`.

This file keeps the numbered theorem source-facing, but its core output is now the chapter owner
`HasPositiveDefiniteHessianOn dom f`. Downstream pointwise Hessian and local-norm positivity are
read from that owner through `HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem`,
`HasPositiveDefiniteHessianOn.posdef`, and `hessianLocalNorm_def` instead of new local wrapper
theorems. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace IsSelfConcordantOn

variable {dom : Set E} {f : E → ℝ}

-- Proof sketch: if the Hessian quadratic form vanished at some `x ∈ dom` in a nonzero direction
-- `h`, then the restriction of `f` to the affine line `x + ℝ • h` would be locally affine at
-- `x`. Closedness of the constrained epigraph upgrades this local zero-curvature behavior to an
-- entire affine line in `dom`, contradicting the source hypothesis.
/-- Theorem 5.1.6: if `f` is self-concordant on `dom`, the constrained epigraph of `f` over
`dom` is closed, and `dom` contains no affine line, then the Hessian of `f` is positive definite
on `dom`. -/
theorem hasPositiveDefiniteHessianOn_of_no_affine_line
    (hself : IsSelfConcordantOn dom f)
    (hclosed : IsClosed (constrainedEpigraph dom (fun y ↦ (f y : WithTop ℝ))))
    (hnoAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ dom) :
    HasPositiveDefiniteHessianOn dom f := by
  rcases hself with ⟨Mf, hMf⟩
  letI := hMf
  refine ⟨?_, ?_⟩
  · intro x hx
    exact IsSelfConcordantOnWith.hessian_isPositive_of_mem Mf hx
  · intro x hx h hh
    sorry

end IsSelfConcordantOn

end

/-! ### Example_5_1_7 (from Chap05) -/
open scoped Gradient NewtonDecrement
open NewtonDecrement

noncomputable section

/- Example 5.1.7 lies in the scalar self-concordance / Newton-decrement domain.

Sampled owner-style declarations:
* `IsStandardSelfConcordantOn` from `Definition_5_1_1`, the Chapter 5 owner for standard
  self-concordance;
* `HasPositiveDefiniteHessianOn` from `Definition_5_0_23`, the chapter owner for domain-level
  positive-definite Hessians;
* `quadraticAffineObjective_isSelfConcordantOnWith_zero` from `Example_5_1_2`, the canonical
  affine-quadratic perturbation input, specialized here to zero quadratic part;
* `negLog_isStandardSelfConcordantOn` from `Example_5_1_3`, the canonical `-log` owner on
  `(0, ∞)`;
* `NewtonDecrement.ofPosDefMem` together with the notation `λ[f; x | hx]` from
  `Definition_5_0_24`, the canonical positive-definite-Hessian domain bridge and its
  source-facing theorem surface for Newton decrements.

Source/core/bridge triage:
* source-facing: the scalar barrier `x ↦ ε x - log x`;
* core/canonical: `IsStandardSelfConcordantOn (Set.Ioi (0 : ℝ))` and
  `newtonDecrement`;
* bridge/view: the explicit derivative formulas and the closed-form Newton-decrement evaluation.

Primitive data:
* the scalar perturbation parameter `ε`.

Derived API:
* the evaluation formula for `affinePerturbedLogBarrier`;
* the first- and second-derivative formulas on `(0, ∞)`;
* the standard self-concordance statement on `(0, ∞)`;
* positive definiteness of the scalar Hessian on `(0, ∞)`;
* Hessian nondegeneracy on `(0, ∞)`, derived from that owner;
* the explicit Newton-decrement formula `λ[affinePerturbedLogBarrier ε; x | hx] = |1 - ε x|`.

The source-facing barrier itself is not duplicated upstream, so it remains the owner in this file.
The Newton decrement is already owned by `newtonDecrement`, and this file uses the Chapter 5
source-facing notation `λ[f; x | hx]` on the theorem surface instead of restating the
self-concordance constant in a parallel local decrement view.
-/

/-- The affine perturbation `x ↦ ε x - log x` of the logarithmic barrier on `(0, ∞)`. -/
def affinePerturbedLogBarrier (ε : ℝ) : ℝ → ℝ :=
  fun x ↦ ε * x - Real.log x

/-- Evaluating `affinePerturbedLogBarrier ε` recovers the textbook formula `ε x - log x`. -/
-- Proof sketch: unfold `affinePerturbedLogBarrier`.
@[simp]
theorem affinePerturbedLogBarrier_apply (ε x : ℝ) :
    affinePerturbedLogBarrier ε x = ε * x - Real.log x :=
  rfl

-- Proof sketch: differentiate the affine term `x ↦ ε x` and the logarithmic term separately on
-- `(0, ∞)`, then combine the resulting scalar formulas.
/-- The first derivative of `x ↦ ε x - log x` on `(0, ∞)` is `ε - 1 / x`. -/
theorem deriv_affinePerturbedLogBarrier_on_Ioi (ε x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    deriv (affinePerturbedLogBarrier ε) x = ε - 1 / x := sorry

-- Proof sketch: differentiate `deriv_affinePerturbedLogBarrier_on_Ioi` once more on `(0, ∞)` and
-- simplify the rational expression.
/-- The second derivative of `x ↦ ε x - log x` on `(0, ∞)` is `1 / x^2`. -/
theorem secondDeriv_affinePerturbedLogBarrier_on_Ioi (ε x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    iteratedDeriv 2 (affinePerturbedLogBarrier ε) x = 1 / x ^ 2 := sorry

-- Proof sketch: write `affinePerturbedLogBarrier ε` as the sum of the affine function
-- `x ↦ ε x` and the standard self-concordant barrier `x ↦ -log x`; the affine term has vanishing
-- Hessian and third derivative, so the Chapter 5 additive owner preserves the
-- self-concordance constant `1`.
/-- Example 5.1.7: for every real parameter `ε`, the affine perturbation
`x ↦ ε x - log x` is standard self-concordant on `(0, ∞)`. -/
theorem affinePerturbedLogBarrier_isStandardSelfConcordantOn (ε : ℝ) :
    IsStandardSelfConcordantOn (Set.Ioi (0 : ℝ)) (affinePerturbedLogBarrier ε) := by
  have hadd :
      IsSelfConcordantOnWith (Set.Ioi (0 : ℝ)) 1
        (quadraticAffineObjective 0 ε (0 : ℝ →L[ℝ] ℝ) + fun x ↦ -Real.log x) := by
    simpa [Set.univ_inter] using
      (quadraticAffineObjective_isSelfConcordantOnWith_zero
        0 ε (0 : ℝ →L[ℝ] ℝ) ContinuousLinearMap.isPositive_zero).add
        negLog_isStandardSelfConcordantOn
  have hbarrier :
      affinePerturbedLogBarrier ε =
        quadraticAffineObjective 0 ε (0 : ℝ →L[ℝ] ℝ) + fun x ↦ -Real.log x := by
    funext x
    change
      ε * x - Real.log x =
        quadraticAffineObjective 0 ε (0 : ℝ →L[ℝ] ℝ) x + -Real.log x
    rw [sub_eq_add_neg]
    have hq :
        quadraticAffineObjective 0 ε (0 : ℝ →L[ℝ] ℝ) x = inner ℝ ε x := by
      exact (congrArg (fun f : ℝ → ℝ ↦ f x) (quadraticAffineObjective_zero_operator 0 ε)).trans
        (zero_add (inner ℝ ε x))
    have hinner : inner ℝ ε x = x * ε := RCLike.inner_apply ε x
    calc
      ε * x + -Real.log x = x * ε + -Real.log x := by ring
      _ = inner ℝ ε x + -Real.log x := by rw [hinner.symm]
      _ = quadraticAffineObjective 0 ε (0 : ℝ →L[ℝ] ℝ) x + -Real.log x := by rw [hq]
  simpa [IsStandardSelfConcordantOn, hbarrier] using hadd

attribute [instance] affinePerturbedLogBarrier_isStandardSelfConcordantOn

-- Proof sketch: on `(0, ∞)`, the scalar Hessian is `1 / x^2`, so every nonzero direction `u`
-- satisfies `⟪u, hessian f x u⟫ = (1 / x^2) * u^2 > 0`.
/-- On `(0, ∞)`, the Hessian of `x ↦ ε x - log x` is positive definite. -/
theorem affinePerturbedLogBarrier_hasPositiveDefiniteHessianOn
    (ε : ℝ) :
    HasPositiveDefiniteHessianOn (Set.Ioi (0 : ℝ)) (affinePerturbedLogBarrier ε) := by
  sorry

attribute [instance] affinePerturbedLogBarrier_hasPositiveDefiniteHessianOn

-- Proof sketch: substitute the first- and second-derivative formulas on `(0, ∞)` and simplify
-- using `x > 0`, so `sqrt (1 / x^2) = 1 / x`, and identify the scalar formula with the canonical
-- Chapter 5 positive-definite-Hessian Newton-decrement bridge.
/-- On `(0, ∞)`, the canonical Newton decrement of `x ↦ ε x - log x` is `|1 - ε x|`. -/
theorem affinePerturbedLogBarrierNewtonDecrement_eq_abs_one_sub_mul
    (ε x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    λ[affinePerturbedLogBarrier ε; x | hx] = |1 - ε * x| := sorry

-- Proof sketch: specialize
-- `affinePerturbedLogBarrierNewtonDecrement_eq_abs_one_sub_mul` to `ε = 0` and simplify.
/-- For `ε = 0`, the canonical Newton decrement of the logarithmic barrier is identically `1` on
`(0, ∞)`. -/
theorem affinePerturbedLogBarrierNewtonDecrement_zero_eq_one
    (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    λ[affinePerturbedLogBarrier 0; x | hx] = 1 := sorry

-- Proof sketch: evaluate the objective along a sequence `x_k → ∞` inside `(0, ∞)`; the
-- logarithmic term grows without bound, so the barrier values on the domain image tend to `-∞`.
/-- The pure logarithmic barrier `x ↦ -log x` is unbounded below on its natural domain `(0, ∞)`. -/
theorem affinePerturbedLogBarrier_zero_not_bddBelow :
    ¬ BddBelow (affinePerturbedLogBarrier 0 '' Set.Ioi (0 : ℝ)) := sorry

-- Proof sketch: the derivative vanishes exactly at `x = 1 / ε`, and the second derivative is
-- positive on `(0, ∞)`, so strict convexity identifies that stationary point as the global
-- minimizer over the domain.
/-- If `ε > 0`, then the global minimizer of `x ↦ ε x - log x` on `(0, ∞)` is `1 / ε`. -/
theorem isMinOn_affinePerturbedLogBarrier_inv
    {ε : ℝ} (hε : 0 < ε) :
    IsMinOn (affinePerturbedLogBarrier ε) (Set.Ioi (0 : ℝ)) (1 / ε) := sorry

end

/-! ### Lemma_5_1_7 (from Chap05) -/
open InnerProductSpace
open scoped ConvexAnalysis DikinEllipsoidNotation Gradient MatrixOrder WithTopConvexAnalysis

noncomputable section

universe u

/- Lemma 5.1.7 lies in the Chapter 5 Fenchel-conjugacy / self-concordant Hessian-comparison
domain.

Sampled owner-style declarations in this domain:
* `HessianDualLocalNorm.ofPosDefMem` in `Definition_5_0_20`, the chapter owner for the dual local
  norm `‖·‖*` attached to a positive-definite Hessian on a domain;
* `HessianDualLocalNorm.ofSelfConcordantMem` in `Definition_5_0_20`, the owner-layer bridge/view
  that reads the same owner
  under the standing primal self-concordant hypotheses of Section 5.1.5;
* `HasPositiveDefiniteHessianOn` in `Definition_5_0_23`, the canonical owner for positive-definite
  primal Hessians on a domain;
* `fenchelPrimalExtension` together with `F⋆`, `dom (F⋆)`, and
  `extendedRealRealPart (F⋆)` from `FenchelPrimalExtension` / `Theorem_5_1_17`, the canonical
  owner surface for the primal/dual pair;
* `IsSelfConcordantOnWith.hessian_loewner_bounds_of_mem_openDikinEllipsoid` in
  `Proposition_5_0_15`, the owner-level Hessian comparison theorem on a self-concordant domain.

Best owner abstraction:
* source-facing: the conjugate-induced primal Hessian comparison under the standing primal
  self-concordant hypotheses, with primitive smallness datum
  `d = ‖∇ f x - ∇ f y‖*[f; x]`;
* core/canonical: `F := fenchelPrimalExtension domain f`, the dual owner
  `extendedRealRealPart (F⋆)` on `dom (F⋆)`, the positive-definite-Hessian owner
  `HasPositiveDefiniteHessianOn domain f`, the dual local norm
  `HessianDualLocalNorm.ofPosDefMem f hx`, and the intrinsic Hessian owner `hessian f`;
* bridge/view: `HessianDualLocalNorm.ofSelfConcordantMem`, the owner-layer dual-local-norm bridge,
  the dual self-concordance owner on
  `extendedRealRealPart (F⋆)`, the dual open-Dikin condition, and the Euclidean matrix
  realization `∇² f`.

Primitive data:
* a domain `domain`, a real-valued primal function `f`, and points `x y ∈ domain`;
* self-concordance of `f` on `domain` with parameter `M_f`;
* closedness of the constrained epigraph of `f` over `domain`;
* the no-affine-line hypothesis on `domain`;
* the source-defined quantity
  `d = ‖∇ f x - ∇ f y‖*[f; x]` together with the smallness hypothesis `d < 1 / M_f`.

Derived API:
* `HessianDualLocalNorm.ofSelfConcordantMem`, which packages the derived dual local norm from the
  standing primal hypotheses;
* dual self-concordance of `extendedRealRealPart (F⋆)` and gradient-domain membership
  `∇ f x, ∇ f y ∈ dom (F⋆)` obtained from `Theorem_5_1_17` and `Lemma_5_1_6`;
* the dual open-Dikin reformulation of the `d`-smallness condition;
* the Loewner-order comparison of `hessian f x` and `hessian f y`;
* the Euclidean matrix comparison as a thin view theorem.

Source/core/bridge triage:
* source-facing: the conjugate-induced Hessian comparison stated with the dual local norm `d` and
  the standing primal hypotheses of Section 5.1.5;
* core/canonical: `fenchelPrimalExtension domain f`, `extendedRealRealPart (F⋆)`,
  `HasPositiveDefiniteHessianOn domain f`, `HessianDualLocalNorm.ofPosDefMem`, and `hessian`;
* bridge/view: `HessianDualLocalNorm.ofSelfConcordantMem`, the dual-owner comparison theorem,
  the dual open-Dikin reformulation, and the Euclidean matrix theorem.

The previous version made a dual-owner bridge theorem the main public entry and thereby dropped
nonredundant primal assumptions still needed by the inverse-Hessian conjugacy bridge in this
project. This refinement restores the source-facing main theorem on the standing primal
self-concordant hypotheses, keeps the source quantity `d` on the theorem surface via the
owner-layer bridge `HessianDualLocalNorm.ofSelfConcordantMem`, and keeps the dual-owner
comparison only as internal bridge data. -/

section OwnerLevel

variable {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable [FiniteDimensional ℝ X]

variable {domain : Set X} {Mf : NNReal} {f : X → ℝ} {x y : X}

local notation "F" => fenchelPrimalExtension domain f

local instance finiteDimensionalComplete : CompleteSpace X := FiniteDimensional.complete ℝ X

-- Proof sketch: let
-- `d := HessianDualLocalNorm.ofPosDefMem f hx ((toDual ℝ X) (∇ f x - ∇ f y))`. The identity
-- `∇² (extendedRealRealPart (F⋆)) (∇ f x) = (hessian f x)⁻¹` from Fenchel conjugacy identifies
-- `d` with the local norm of the dual displacement `∇ f x - ∇ f y` for the dual objective
-- `extendedRealRealPart (F⋆)` at `∇ f x`, provided `∇ f x ∈ dom (F⋆)`. The smallness hypothesis
-- `d < 1 / M_f` is therefore exactly the dual Dikin condition needed to apply the canonical
-- Hessian comparison theorem on the self-concordant dual owner `extendedRealRealPart (F⋆)`.
-- The extra bridge hypothesis `∇ f y ∈ dom (F⋆)` is then what lets the inverse-Hessian transfer
-- identify the dual Hessian at the endpoint `∇ f y` with `(hessian f y)⁻¹`. Transporting that
-- dual comparison back across inversion yields the displayed primal Loewner-order bounds.
private theorem dualRealPart_hessian_loewner_bounds
    [HasPositiveDefiniteHessianOn domain f]
    (hdual : IsSelfConcordantOnWith (dom (F⋆)) Mf (extendedRealRealPart (F⋆)))
    (hx : x ∈ domain) (hy : y ∈ domain)
    (hgradx : ∇ f x ∈ dom (F⋆)) (hgrady : ∇ f y ∈ dom (F⋆))
    (d : ℝ)
    (hd : d = HessianDualLocalNorm.ofPosDefMem f hx ((toDual ℝ X) (∇ f x - ∇ f y)))
    (hd_lt : d < 1 / (Mf : ℝ)) :
    ((1 - (Mf : ℝ) * d) ^ (2 : ℕ)) • hessian f x ≤ hessian f y ∧
      hessian f y ≤ ((1 - (Mf : ℝ) * d) ^ (2 : ℕ))⁻¹ • hessian f x := by
  let _ := hdual
  sorry

-- Proof sketch: derive the positive-definite-Hessian owner on `domain` from the standing primal
-- assumptions via `IsSelfConcordantOn.hasPositiveDefiniteHessianOn_of_no_affine_line`, derive dual
-- self-concordance of `extendedRealRealPart (F⋆)` via
-- `fenchelPrimalExtension_dualRealPart_isSelfConcordantOnWith`, and derive
-- `∇ f x, ∇ f y ∈ dom (F⋆)` from the chapter owner bridge
-- `image_gradient_subset_dom_fenchelDual_of_selfConcordant`. Then apply the internal bridge
-- theorem `dualRealPart_hessian_loewner_bounds`. The dual-open-Dikin hypothesis and the
-- dual-owner theorem are both bridge/view forms; the main public entry keeps the source-defined
-- quantity `d` and the standing primal hypotheses on the theorem surface, using the canonical
-- self-concordant/vector bridge notation `‖u‖*[f; x]` for the dual local norm of a displacement.
section SelfConcordantSurface

variable [IsSelfConcordantOnWith domain Mf f]
variable
    (hclosed :
      IsClosed (constrainedEpigraph domain (fun z ↦ (f z : WithTop ℝ))))
    (hnoAffineLine : ∀ ⦃z h : X⦄, h ≠ 0 → ¬ ∀ τ : ℝ, z + τ • h ∈ domain)
    {x : X} (hx : x ∈ domain)

local notation:max "‖" u "‖*[" f "; " x "]" =>
  HessianDualLocalNorm.ofSelfConcordantMemVec Mf f hclosed hnoAffineLine x hx u

/-- Lemma 5.1.7, source-facing form: let `F := fenchelPrimalExtension domain f`. Assume `f` is
self-concordant on `domain` with parameter `M_f`, the constrained epigraph of `f` over `domain`
is closed, and `domain` contains no affine line. For `x, y ∈ domain`, let
`d := ‖∇ f x - ∇ f y‖*[f; x]`. If `d < 1 / M_f`, then the primal Hessians at `x` and `y`
satisfy the standard Loewner-order
comparison with factor `(1 - M_f d)^2`. -/
theorem hessian_loewner_bounds_of_fenchelDual_selfConcordant
    (hclosed :
      IsClosed (constrainedEpigraph domain (fun z ↦ (f z : WithTop ℝ))))
    (hnoAffineLine : ∀ ⦃z h : X⦄, h ≠ 0 → ¬ ∀ τ : ℝ, z + τ • h ∈ domain)
    (hx : x ∈ domain) (hy : y ∈ domain)
    (hd_lt : ‖∇ f x - ∇ f y‖*[f; x] < 1 / (Mf : ℝ)) :
    let d := ‖∇ f x - ∇ f y‖*[f; x]
    ((1 - (Mf : ℝ) * d) ^ (2 : ℕ)) • hessian f x ≤ hessian f y ∧
      hessian f y ≤ ((1 - (Mf : ℝ) * d) ^ (2 : ℕ))⁻¹ • hessian f x := by
  sorry

-- Proof sketch: the dual-open-Dikin hypothesis is exactly the bridge/view reformulation of the
-- source quantity `d` in the main theorem. After deriving the standing dual-owner data from the
-- primal hypotheses as above, apply the same internal bridge theorem
-- `dualRealPart_hessian_loewner_bounds`.
/-- Bridge/view corollary to Lemma 5.1.7: under the same standing primal self-concordant
hypotheses, if `∇ f y` lies in the dual open Dikin ellipsoid of `extendedRealRealPart (F⋆)`
centered at `∇ f x` with radius `r < 1 / M_f`, then the same Hessian comparison follows. -/
theorem hessian_loewner_bounds_of_fenchelDual_selfConcordant_of_mem_dualOpenDikinEllipsoid
    (hclosed :
      IsClosed (constrainedEpigraph domain (fun z ↦ (f z : WithTop ℝ))))
    (hnoAffineLine : ∀ ⦃z h : X⦄, h ≠ 0 → ¬ ∀ τ : ℝ, z + τ • h ∈ domain)
    {r : ℝ} (hx : x ∈ domain) (hy : y ∈ domain) (hr : r < 1 / (Mf : ℝ))
    (hgrad : ∇ f y ∈ W⁰[extendedRealRealPart (F⋆); ∇ f x](r)) :
    ((1 - (Mf : ℝ) * r) ^ (2 : ℕ)) • hessian f x ≤ hessian f y ∧
      hessian f y ≤ ((1 - (Mf : ℝ) * r) ^ (2 : ℕ))⁻¹ • hessian f x := by
  sorry

end SelfConcordantSurface

end OwnerLevel

section EuclideanBridge

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

variable {domain : Set E} {Mf : NNReal} {f : E → ℝ} {x y : E}

local notation "F" => fenchelPrimalExtension domain f

section SelfConcordantSurface

variable [IsSelfConcordantOnWith domain Mf f]
variable
    (hclosed :
      IsClosed (constrainedEpigraph domain (fun z ↦ (f z : WithTop ℝ))))
    (hnoAffineLine : ∀ ⦃z h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, z + τ • h ∈ domain)
    {x : E} (hx : x ∈ domain)

local notation:max "‖" u "‖*[" f "; " x "]" =>
  HessianDualLocalNorm.ofSelfConcordantMemVec Mf f hclosed hnoAffineLine x hx u

-- Proof sketch: apply the source-facing owner theorem
-- `hessian_loewner_bounds_of_fenchelDual_selfConcordant` and then transport the intrinsic
-- operator inequalities through the Euclidean identification `hessianMatrix_toEuclideanLin`.
/-- Euclidean matrix view of Lemma 5.1.7: under the same standing primal self-concordant
hypotheses, let
`d := ‖∇ f x - ∇ f y‖*[f; x]`. If `d < 1 / M_f`, the
conjugate-induced Hessian comparison becomes the
standard matrix Loewner comparison between `∇² f x` and `∇² f y`. -/
theorem conjugate_selfConcordant_hessianMatrix_comparison
    (hclosed :
      IsClosed (constrainedEpigraph domain (fun z ↦ (f z : WithTop ℝ))))
    (hnoAffineLine : ∀ ⦃z h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, z + τ • h ∈ domain)
    (hx : x ∈ domain) (hy : y ∈ domain)
    (hd_lt : ‖∇ f x - ∇ f y‖*[f; x] < 1 / (Mf : ℝ)) :
    let d := ‖∇ f x - ∇ f y‖*[f; x]
    (((1 - (Mf : ℝ) * d) ^ (2 : ℕ)) • ∇² f x ≤ ∇² f y) ∧
      (∇² f y ≤ ((1 - (Mf : ℝ) * d) ^ (2 : ℕ))⁻¹ • ∇² f x) := by
  sorry

end SelfConcordantSurface

end EuclideanBridge

end

/-! ### Theorem_5_1_7 (from Chap05) -/
open scoped Gradient HessianLocalNorm DikinEllipsoidNotation

noncomputable section

universe u

/-
Theorem 5.1.7 lies in the Chapter 5 self-concordance / Hessian-comparison domain.

Sampled owner-style declarations in this domain:
* `hessian` from `Chap01/Definition_1_4_16`, the canonical second-order owner replacing the raw
  `fderiv ℝ (∇ f)` surface;
* `thirdDirectionalDerivative` from `Chap05/Definition_5_0_10`, the source-facing Chapter 5 owner
  for the cubic derivative `D³f(x)[u,u,u]`;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` from `Definition_5_1_1`, the chapter owner for
  the Hessian local norm;
* `openDikinEllipsoid` together with the notation `W⁰[f; x](r)` and
  `mem_openDikinEllipsoid_iff` from `Definition_5_0_13`, the owner and bridge for the
  Dikin-radius hypothesis `y ∈ W⁰[f; x](1 / M_f)`;
* `selfConcordant_diagonal_bound_iff_trilinear_bound` from `Lemma_5_1_2`, the canonical bridge
  from the Chapter 5 cubic owner surface to the full trilinear third-derivative estimate;
* `selfConcordant_iff_thirdDerivative_operator_le` from `Corollary_5_1_1`, the operator-level
  bridge from the same cubic owner surface to a Hessian differential inequality;
* `IsSelfConcordantOnWith.hessian_loewner_bounds_of_mem_openDikinEllipsoid` from
  `Proposition_5_0_15`, the stronger operator-level comparison theorem under the bundled owner
  `IsSelfConcordantOnWith dom Mf f`.

Source/core/bridge triage:
* source-facing: the segment-local Hessian operator comparison at `x` and `y`;
* core/canonical: `hessian f z`, `‖u‖[f; z]`, and `W⁰[f; x](r)`;
* bridge/view: `mem_openDikinEllipsoid_iff`, the scalarized quadratic-form inequalities obtained
  by testing the operator bounds on a direction `h`, and the stronger bundled-owner Loewner
  comparison from `Proposition_5_0_15`.

Primitive data:
* an open set `dom` containing the segment from `x` to `y`;
* `C³` regularity of `f` on `dom`;
* pointwise positivity of the Hessian along the segment from `x` to `y`;
* the Chapter 5 diagonal cubic bound on `thirdDirectionalDerivative f z u` along that segment;
* the Dikin-radius membership of `y`.

Derived API:
* the lower and upper Loewner-order comparison of the endpoint Hessians;
* the quadratic-form inequalities obtained from that operator comparison by evaluating on a
  direction `h`.

This theorem remains source-facing because the sampled bundled owner
`IsSelfConcordantOnWith dom Mf f` from `Definition_5_1_1` would strengthen the assumptions to a
global convex-domain self-concordance hypothesis. The refinement therefore keeps the original
segment-local semantics but moves the main public surface from the quadratic-form bridge to the
canonical Hessian owner already used by `hessianLocalNorm`, `openDikinEllipsoid`, and the nearby
Loewner-order API. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: for each fixed direction `h`, scalarize the Hessian operator along the segment by
-- `ψ_h(t) = inner ℝ h (hessian f (x + t • (y - x)) h)`. The diagonal Chapter 5 cubic bound on
-- `thirdDirectionalDerivative` converts, via the standard local bridge to the Hessian
-- differential inequality, into control of `|ψ_h'(t)|` by the local norm of `y - x` at the
-- intermediate point times `ψ_h(t)`. Use the Dikin-radius hypothesis
-- `y ∈ W⁰[f; x](1 / M_f)` together with the standard local norm comparison along
-- the segment to obtain
-- `|ψ_h'(t)| ≤ 2 M_f r / (1 - t M_f r) * ψ_h(t)`, integrate the differential inequality for
-- `log ψ_h(t)`, and then reassemble the resulting pointwise quadratic-form bounds into the
-- Loewner-order comparison of the endpoint Hessians. The Dikin-radius hypothesis already rules
-- out the degenerate `Mf = 0` case, since then `W⁰[f; x](1 / (Mf : ℝ))` is empty.
/-- Theorem 5.1.7: if `f` is `C³` on an open set containing the segment from `x` to `y`, its
third directional derivative satisfies the Chapter 5 local-norm bound with constant `M_f` along
that segment, the Hessian is positive along the segment, and `y ∈ W⁰[f; x](1 / M_f)`, then with
`r = ‖y - x‖[f; x]` the Hessians at `x` and `y` satisfy the Loewner-order bounds
`(1 - M_f r)^2 • ∇²f(x) ≤ ∇²f(y) ≤ (1 - M_f r)⁻² • ∇²f(x)`. -/
theorem hessian_loewner_bounds_along_segment
    {dom : Set E} {Mf : NNReal} {f : E → ℝ} {x y : E}
    (hdom_open : IsOpen dom)
    (hcont : ContDiffOn ℝ 3 f dom)
    (hsegment : segment ℝ x y ⊆ dom)
    (hpsd : ∀ ⦃z : E⦄, z ∈ segment ℝ x y → (hessian f z).IsPositive)
    (hthird : ∀ ⦃z : E⦄ (hz : z ∈ segment ℝ x y) (u : E),
      |thirdDirectionalDerivative f z u| ≤
        2 * (Mf : ℝ) * ‖u‖[f; z] ^ (3 : ℕ))
    (hy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    let r := ‖y - x‖[f; x]
    ((1 - (Mf : ℝ) * r) ^ (2 : ℕ)) • hessian f x ≤ hessian f y ∧
      hessian f y ≤ ((1 - (Mf : ℝ) * r) ^ (2 : ℕ))⁻¹ • hessian f x := sorry

end

/-! ### Theorem_5_1_8 (from Chap05) -/
open scoped DikinEllipsoidNotation Gradient HessianLocalNorm SelfConcordantAuxiliaryFunction

noncomputable section

universe u

/- Theorem 5.1.8 lies in the Chapter 5 self-concordant Hessian-comparison domain.

Sampled owner declarations in this domain:
* `hessian` from `Chap01/Definition_1_4_16`, the canonical second-order owner;
* `hessianLocalNorm` and the notation `‖u‖[f; x]` from `Definition_5_1_1`, the chapter owner for
  the Hessian local norm;
* `hessian_loewner_bounds_along_segment` from `Theorem_5_1_7`, the segment-local Hessian
  comparison theorem stated directly in Loewner order;
* `IsSelfConcordantOnWith.hessian_loewner_bounds_of_mem_openDikinEllipsoid` from
  `Proposition_5_0_15`, the bundled-owner Dikin-ellipsoid version of the same owner-level
  comparison.

Source/core/bridge triage:
* source-facing: the gradient-pairing and lower Taylor bounds between two fixed points;
* core/canonical: the Loewner-order comparison on `hessian f _`;
* bridge/view: the scalar local norm `‖y - x‖[f; x]` appearing only in the comparison factor and
  in the final bound.

Primitive data:
* a `C²` function on a set containing the segment from `x` to `y`;
* positivity of the base Hessian `hessian f x`, so the Chapter 5 local norm at `x` is a genuine
  Hessian norm;
* a lower Loewner-order comparison of the Hessian along that segment.

Derived API:
* the lower bound for the gradient pairing;
* the affine lower Taylor bound with remainder `ω`.

This file stays source-facing, but its primitive Hessian hypothesis now uses the owner
`hessian f _` directly instead of the derived scalarized quadratic-form surface. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ} {x y : E}
variable (hcont : ContDiffOn ℝ 2 f dom)
variable (hsegment : segment ℝ x y ⊆ dom)
variable (hHessPos : (hessian f x).IsPositive)
variable
  (hloewnerLower :
    ∀ ⦃z : E⦄, z ∈ segment ℝ x y →
      (1 / (1 + (Mf : ℝ) * ‖z - x‖[f; x]) ^ (2 : ℕ)) • hessian f x ≤ hessian f z)

include hcont hsegment hHessPos hloewnerLower

-- Proof sketch: integrate the Loewner-order Hessian comparison along the segment
-- `y_τ = x + τ • (y - x)`. The base-point positivity hypothesis makes `‖y - x‖[f; x]` a genuine
-- Hessian norm, and `hloewnerLower` transports that positivity along the segment. The
-- fundamental theorem
-- of calculus gives
-- `∇ f(y) - ∇ f(x) = ∫₀¹ ∇² f(y_τ) (y - x) dτ`, and evaluating `hloewnerLower` on the
-- direction `y - x`
-- yields the scalar lower bound `r² / (1 + τ M_f r)^2` for the integrand, where
-- `r = hessianLocalNorm f x (y - x)`. Evaluating the integral gives the stated denominator
-- `1 + M_f r`.
/-- Theorem 5.1.8 (1): if a `C²` function has positive base Hessian `∇² f(x)` and along the
segment from `x` to `y` satisfies the lower Loewner-order Hessian comparison
`∇² f(z) ≽ (1 + M_f ‖z - x‖_x)⁻² ∇² f(x)`, then the gradient increment paired with `y - x`
is bounded below by `‖y - x‖_x² / (1 + M_f ‖y - x‖_x)`. -/
theorem gradient_difference_inner_ge_hessianLocalNorm_sq_div :
    let r := ‖y - x‖[f; x]
    inner ℝ (∇ f y - ∇ f x) (y - x) ≥
      r ^ (2 : ℕ) / (1 + (Mf : ℝ) * r) := sorry

-- Proof sketch: write
-- `f y - f x - ⟪∇ f(x), y - x⟫ = ∫₀¹ ⟪∇ f(y_τ) - ∇ f(x), y - x⟫ dτ`
-- along the segment `y_τ = x + τ • (y - x)`, then apply clause (1) to each pair `(x, y_τ)`.
-- This gives the integrand lower bound `τ r² / (1 + τ M_f r)`, where
-- `r = hessianLocalNorm f x (y - x)`. Evaluating the integral yields
-- `(1 / M_f²) * ω(M_f r)` when `M_f > 0`, and its limiting value `(1 / 2) r²` when `M_f = 0`.
/-- Theorem 5.1.8 (2): under the same owner-level Hessian comparison along the segment from `x`
to `y` and the same base-Hessian positivity hypothesis at `x`, the function value at `y` admits
the affine lower Taylor bound at `x` with remainder
`M_f⁻² ω(M_f ‖y - x‖_x)`, interpreted as `(1 / 2) ‖y - x‖_x²` when `M_f = 0`. -/
theorem taylor_lower_bound_of_hessian_loewner_lower :
    let r := ‖y - x‖[f; x]
    let tω := selfConcordantOmegaArg Mf r (by
      exact neg_one_lt_mf_mul_of_nonneg (by
        simpa [r] using hessianLocalNorm_nonneg f x (y - x)))
    f y ≥
      f x + inner ℝ (∇ f x) (y - x) +
        if hMf : Mf = 0 then
          r ^ (2 : ℕ) / 2
        else
          (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω := sorry

end

namespace IsSelfConcordantOnWith

section

variable {dom : Set E} {Mf : NNReal} {f : E → ℝ}

-- Proof sketch: derive `y ∈ dom` from the Dikin-step hypothesis via
-- `openDikinEllipsoid_inv_constant_subset`, use convexity of `dom` to place the whole segment
-- from `x` to `y` inside `dom`, and apply
-- `hessian_loewner_bounds_of_mem_openDikinEllipsoid` pointwise to the intermediate points
-- `x + τ • (y - x)` to recover the lower segment-wise Loewner hypothesis required by the
-- source-facing Theorem 5.1.8. The two displayed estimates then follow by the local theorems
-- `gradient_difference_inner_ge_hessianLocalNorm_sq_div` and
-- `taylor_lower_bound_of_hessian_loewner_lower`.
/-- Under the Chapter 5 owner `IsSelfConcordantOnWith dom Mf f`, every admissible Dikin step
`y ∈ W⁰[f; x](1 / (Mf : ℝ))` satisfies both lower bounds from Theorem 5.1.8: the gradient pairing
dominates `‖y - x‖_x² / (1 + M_f ‖y - x‖_x)`, and the function value dominates the affine Taylor
approximation at `x` with the explicit self-concordant remainder `ω`. This is the canonical
owner-level bridge from self-concordance to the source-facing lower estimates. -/
theorem gradient_difference_inner_and_taylor_lower_bounds_of_mem_openDikinEllipsoid
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x y : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    let r := ‖y - x‖[f; x]
    let tω := selfConcordantOmegaArg Mf r (by
      exact neg_one_lt_mf_mul_of_nonneg (by
        simpa [r] using hessianLocalNorm_nonneg f x (y - x)))
    inner ℝ (∇ f y - ∇ f x) (y - x) ≥
        r ^ (2 : ℕ) / (1 + (Mf : ℝ) * r) ∧
      f y ≥
        f x + inner ℝ (∇ f x) (y - x) +
          if hMf : Mf = 0 then
            r ^ (2 : ℕ) / 2
          else
            (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω := sorry

-- Proof sketch: project the first component of the owner-level conjunction above.
/-- The owner-level gradient-pairing lower bound derived from `IsSelfConcordantOnWith dom Mf f`
and the admissible Dikin-step hypothesis. -/
theorem gradient_difference_inner_ge_hessianLocalNorm_sq_div_of_mem_openDikinEllipsoid
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x y : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    inner ℝ (∇ f y - ∇ f x) (y - x) ≥
      ‖y - x‖[f; x] ^ (2 : ℕ) / (1 + (Mf : ℝ) * ‖y - x‖[f; x]) := by
  simpa using
    (gradient_difference_inner_and_taylor_lower_bounds_of_mem_openDikinEllipsoid hself hx hxy).1

-- Proof sketch: project the second component of the owner-level conjunction above.
/-- The owner-level Taylor lower bound with remainder `ω`, derived from
`IsSelfConcordantOnWith dom Mf f` and the admissible Dikin-step hypothesis. -/
theorem taylor_lower_bound_with_selfConcordantOmega_of_mem_openDikinEllipsoid
    (hself : IsSelfConcordantOnWith dom Mf f)
    {x y : E} (hx : x ∈ dom) (hxy : y ∈ W⁰[f; x](1 / (Mf : ℝ))) :
    let r := ‖y - x‖[f; x]
    let tω := selfConcordantOmegaArg Mf r (by
      exact neg_one_lt_mf_mul_of_nonneg (by
        simpa [r] using hessianLocalNorm_nonneg f x (y - x)))
    f y ≥
      f x + inner ℝ (∇ f x) (y - x) +
        if hMf : Mf = 0 then
          r ^ (2 : ℕ) / 2
        else
          (1 / (Mf : ℝ) ^ (2 : ℕ)) * ω tω := by
  simpa using
    (gradient_difference_inner_and_taylor_lower_bounds_of_mem_openDikinEllipsoid hself hx hxy).2

end

end IsSelfConcordantOnWith

end
