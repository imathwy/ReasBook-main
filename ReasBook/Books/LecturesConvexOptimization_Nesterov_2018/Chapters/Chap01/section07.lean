import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_1_7_3 (from Chap01) -/
noncomputable section

open NewtonSystem

/- Example 1.7.3 lives in the Chapter 1 Newton-system domain.

Primary domain:
* scalar Newton iteration for the equation `φ(t) = t / √(1 + t²)`

Sampled owner-style declarations:
* `NewtonSystem.step`
* `NewtonSystem.orbit`
* `NewtonSystem.step_scalar_def`

Source/core/bridge triage:
* source-facing: the specific scalar map `newtonUnivariateRootFunction` and the convergence,
  periodicity, and divergence statements of Example 1.7.3
* core/canonical: the admissible-point Newton owner API from `Algorithm_1_7_1`
* bridge/view: the scalar step formula `NewtonSystem.step_scalar_def`

Primitive data:
* the scalar map `newtonUnivariateRootFunction`
* the pointwise derivative-nonvanishing proof needed to place scalar points in the owner
  admissible domain

Derived API:
* the public scalar bridge `newtonUnivariateRootAdmissiblePoint` into the owner admissible domain
* the scalar Newton update `newtonUnivariateRootStep` and its canonical orbit
  `newtonUnivariateRootOrbit`, both obtained from the owner Newton constructions

This file therefore keeps the source-facing scalar example and its asymptotic theorems, but it
reuses the chapter owner step/orbit API directly. The only extra public declarations are the thin
scalar bridge names needed to keep the theorem surface free of private implementation scaffolding.
-/

/-- The scalar equation map `φ(t) = t / √(1 + t²)` used in the Newton root-finding example. -/
def newtonUnivariateRootFunction (t : ℝ) : ℝ :=
  t / Real.sqrt (1 + t ^ (2 : ℕ))

/-- Helper for Example 1.7.3: the square-root denominator has derivative `t / √(1 + t²)`. -/
private theorem hasDerivAt_sqrt_one_add_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Real.sqrt (1 + y ^ (2 : ℕ)))
      (x / Real.sqrt (1 + x ^ (2 : ℕ))) x := by
  -- Differentiate the inner quadratic first, then pass through `Real.sqrt`.
  have h_inner : HasDerivAt (fun y : ℝ ↦ 1 + y ^ (2 : ℕ)) (2 * x) x := by
    simpa [pow_two, two_mul, add_comm, add_left_comm, add_assoc] using
      (((hasDerivAt_id x).pow 2).const_add 1)
  have hx : (1 + x ^ (2 : ℕ)) ≠ 0 := by
    nlinarith
  -- The square-root simplification uses that `1 + x²` is strictly positive.
  convert h_inner.sqrt hx using 1
  field_simp [hx]

/-- Helper for Example 1.7.3: the quotient `t / √(1 + t²)` has derivative
`((√(1 + t²))⁻¹)^3`. -/
private theorem hasDerivAt_newtonUnivariateRootFunction (x : ℝ) :
    HasDerivAt newtonUnivariateRootFunction
      ((Real.sqrt (1 + x ^ (2 : ℕ)))⁻¹ ^ (3 : ℕ)) x := by
  -- Differentiate the quotient `x / √(1 + x²)` using the previous square-root derivative.
  have hsqrt := hasDerivAt_sqrt_one_add_sq x
  have hx0 : Real.sqrt (1 + x ^ (2 : ℕ)) ≠ 0 := by
    exact (Real.sqrt_ne_zero (show 0 ≤ 1 + x ^ (2 : ℕ) by positivity)).2 (by nlinarith)
  have hdiv := (hasDerivAt_id x).div hsqrt hx0
  -- After clearing denominators, only the identity `(√(1 + x²))² = 1 + x²` remains.
  convert hdiv using 1
  · field_simp [hx0]
    simp only [id_eq]
    rw [Real.sq_sqrt (show 0 ≤ 1 + x ^ (2 : ℕ) by positivity)]
    ring_nf

/-- The derivative of `t ↦ t / √(1 + t²)` is `1 / (√(1 + t²))^3`. -/
-- Proof sketch: differentiate the quotient `t / √(1 + t²)` using the chain rule for
-- `t ↦ √(1 + t²)` and simplify the resulting expression.
theorem deriv_newtonUnivariateRootFunction (t : ℝ) :
    deriv newtonUnivariateRootFunction t =
      1 / (Real.sqrt (1 + t ^ (2 : ℕ)) ^ (3 : ℕ)) := by
  -- Convert the `HasDerivAt` formula into the surface derivative expression used later.
  simpa [one_div] using (hasDerivAt_newtonUnivariateRootFunction t).deriv

/-- The derivative of `newtonUnivariateRootFunction` never vanishes. -/
theorem deriv_newtonUnivariateRootFunction_ne_zero (t : ℝ) :
    deriv newtonUnivariateRootFunction t ≠ 0 := by
  rw [deriv_newtonUnivariateRootFunction]
  positivity

/- The scalar point `t` viewed in the canonical admissible Newton domain of
`newtonUnivariateRootFunction`. This is internal bridge data used to specialize the chapter owner
API to the source-facing scalar example. -/
private abbrev newtonUnivariateRootAdmissiblePoint (t : ℝ) :
    AdmissiblePoint newtonUnivariateRootFunction :=
  ⟨t, fderiv_det_ne_zero_of_deriv_ne_zero (deriv_newtonUnivariateRootFunction_ne_zero t)⟩

/-- The scalar Newton update for `newtonUnivariateRootFunction`, obtained from the owner Newton
step. -/
def newtonUnivariateRootStep (t : ℝ) : ℝ :=
  step newtonUnivariateRootFunction (newtonUnivariateRootAdmissiblePoint t)

/- Every Newton step for `newtonUnivariateRootFunction` stays in the canonical admissible
domain. This is internal bridge data needed to specialize `NewtonSystem.orbit` to the scalar
example. -/
private theorem newtonUnivariateRootStepPreservesAdmissibility :
    StepPreservesAdmissibility newtonUnivariateRootFunction := by
  intro t
  exact fderiv_det_ne_zero_of_deriv_ne_zero
    (deriv_newtonUnivariateRootFunction_ne_zero (step newtonUnivariateRootFunction t))

/-- The canonical Newton orbit for `newtonUnivariateRootFunction`, viewed as an ordinary scalar
iterate sequence. -/
def newtonUnivariateRootOrbit (t0 : ℝ) : ℕ → ℝ :=
  orbit newtonUnivariateRootFunction
    (newtonUnivariateRootAdmissiblePoint t0)
    newtonUnivariateRootStepPreservesAdmissibility

/-- The canonical Newton orbit for this scalar example agrees with ordinary iteration of the
scalar Newton update. -/
theorem newtonUnivariateRootIterates_eq_iterate (t0 : ℝ) (k : ℕ) :
    (newtonUnivariateRootOrbit t0) k = (newtonUnivariateRootStep^[k]) t0 := by
  induction k with
  | zero =>
      rfl
  | succ k hk =>
      have hpoint :
          orbitPoint newtonUnivariateRootFunction (newtonUnivariateRootAdmissiblePoint t0)
              newtonUnivariateRootStepPreservesAdmissibility k =
            newtonUnivariateRootAdmissiblePoint ((newtonUnivariateRootOrbit t0) k) := by
        apply Subtype.ext
        rfl
      rw [Function.iterate_succ_apply']
      rw [newtonUnivariateRootOrbit, orbit_succ newtonUnivariateRootFunction
        (newtonUnivariateRootAdmissiblePoint t0)
        newtonUnivariateRootStepPreservesAdmissibility k, hpoint, hk]
      rfl

/-- Newton's method for `newtonUnivariateRootFunction` reduces to the cubic map `t ↦ -t^3`. -/
-- Proof sketch: expand the scalar Newton update with `NewtonSystem.step_scalar_def`, substitute
-- the derivative formula from
-- `deriv_newtonUnivariateRootFunction`, and simplify the resulting quotient.
theorem newtonUnivariateRootStep_eq_neg_cube (t : ℝ) :
    newtonUnivariateRootStep t = -(t ^ (3 : ℕ)) := by
  -- Expand the Newton update into the textbook scalar formula.
  rw [newtonUnivariateRootStep,
    step_scalar_def newtonUnivariateRootFunction t (deriv_newtonUnivariateRootFunction_ne_zero t),
    newtonUnivariateRootFunction, deriv_newtonUnivariateRootFunction]
  let s : ℝ := Real.sqrt (1 + t ^ (2 : ℕ))
  have hs0 : s ≠ 0 := by
    dsimp [s]
    exact (Real.sqrt_ne_zero (show 0 ≤ 1 + t ^ (2 : ℕ) by positivity)).2 (by nlinarith)
  have hs_sq : s ^ (2 : ℕ) = 1 + t ^ (2 : ℕ) := by
    dsimp [s]
    simpa [pow_two] using (Real.sq_sqrt (show 0 ≤ 1 + t ^ (2 : ℕ) by positivity))
  -- Clearing the nonzero square-root denominator reduces the step to a polynomial identity.
  have hmain : t - (t / s) / (1 / s ^ (3 : ℕ)) = -(t ^ (3 : ℕ)) := by
    field_simp [hs0]
    rw [hs_sq]
    ring
  simpa [s] using hmain

/-- Helper for Example 1.7.3: taking absolute values turns the Newton step into the cubic map on
magnitudes. -/
lemma abs_newtonUnivariateRootStep_eq_abs_cube (t : ℝ) :
    |newtonUnivariateRootStep t| = |t| ^ (3 : ℕ) := by
  -- The sign disappears under absolute value, leaving a pure cubic growth law.
  rw [newtonUnivariateRootStep_eq_neg_cube, abs_neg, abs_pow]

/-- Helper for Example 1.7.3: the subsequence `3^k` tends to `+∞`. -/
lemma three_pow_tendsto_atTop :
    Filter.Tendsto (fun k : ℕ ↦ 3 ^ k) Filter.atTop Filter.atTop := by
  -- Compare `3^k` to the identity sequence using the standard lower bound `k < 3^k`.
  refine Filter.tendsto_atTop.mpr ?_
  intro n
  filter_upwards [Filter.eventually_ge_atTop n] with k hk
  exact le_trans hk (Nat.lt_pow_self (show 1 < 3 by decide)).le

/-- Example 1.7.3: for the Newton iteration associated to `φ(t) = t / √(1 + t²)`, the iterates
started from `t₀` satisfy `|t_k| = |t₀|^(3^k)`. Consequently the method converges cubically to
`0` on `|t₀| < 1`, is two-periodic at `t₀ = ±1`, and diverges in magnitude on `|t₀| > 1`. -/
-- Proof sketch: use `newtonUnivariateRootStep_eq_neg_cube` to rewrite the recursion as
-- `t_{k+1} = -t_k^3`, then take absolute values and iterate the identity `|t_{k+1}| = |t_k|^3`.
theorem abs_newtonUnivariateRootIterates_eq_abs_start_pow_three_pow (t0 : ℝ) (k : ℕ) :
    |(newtonUnivariateRootOrbit t0) k| = |t0| ^ (3 ^ k) := by
  induction k with
  | zero =>
      -- The zeroth iterate is the starting point, and `3^0 = 1`.
      rw [newtonUnivariateRootIterates_eq_iterate]
      simp
  | succ k hk =>
      -- One Newton step raises the current magnitude to the third power.
      rw [newtonUnivariateRootIterates_eq_iterate, Function.iterate_succ_apply',
        abs_newtonUnivariateRootStep_eq_abs_cube]
      rw [show |(newtonUnivariateRootStep^[k]) t0| = |t0| ^ (3 ^ k) by
        simpa [newtonUnivariateRootIterates_eq_iterate] using hk]
      calc
        (|t0| ^ (3 ^ k)) ^ (3 : ℕ) = |t0| ^ (3 ^ k * 3) := by rw [pow_mul]
        _ = |t0| ^ (3 ^ Nat.succ k) := by rw [Nat.pow_succ]

/-- If `|t₀| < 1`, the Newton iterates for `t / √(1 + t²)` converge to `0`. -/
-- Proof sketch: combine
-- `abs_newtonUnivariateRootIterates_eq_abs_start_pow_three_pow` with the fact that
-- `|t₀|^(3^k) → 0` for every real number of absolute value strictly less than `1`.
theorem newtonUnivariateRootIterates_tendsto_zero_of_abs_lt_one (t0 : ℝ)
    (ht0 : |t0| < 1) :
    Filter.Tendsto (newtonUnivariateRootOrbit t0) Filter.atTop (nhds 0) := by
  -- Move to absolute values and then use the explicit formula `|t_k| = |t0|^(3^k)`.
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hpow : Filter.Tendsto (fun n : ℕ ↦ |t0| ^ n) Filter.atTop (nhds 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg t0) ht0
  convert hpow.comp three_pow_tendsto_atTop using 1
  ext k
  simp [Function.comp, abs_newtonUnivariateRootIterates_eq_abs_start_pow_three_pow]

/-- If `|t₀| = 1`, then `t₀` is a periodic point of period `2` for the scalar Newton map attached
to `t / √(1 + t²)`. -/
-- Proof sketch: from `newtonUnivariateRootStep_eq_neg_cube` and `|t₀| = 1`, every iterate has
-- absolute value `1`, and the update reduces to multiplication by `-1`, yielding period `2`.
theorem newtonUnivariateRootStep_isPeriodicPt_of_abs_eq_one (t0 : ℝ)
    (ht0 : |t0| = 1) :
    Function.IsPeriodicPt newtonUnivariateRootStep 2 t0 := by
  -- Route correction: the `|t0| = 1` regime is best handled by the exact classification
  -- `t0 = 1 ∨ t0 = -1`, then computing two explicit Newton steps.
  have hcases : t0 = 1 ∨ t0 = -1 := by
    rwa [← abs_one, abs_eq_abs] at ht0
  rcases hcases with rfl | rfl
  · rw [Function.IsPeriodicPt, Function.IsFixedPt, Function.iterate_succ_apply', Function.iterate_one]
    norm_num [newtonUnivariateRootStep_eq_neg_cube]
  · rw [Function.IsPeriodicPt, Function.IsFixedPt, Function.iterate_succ_apply', Function.iterate_one]
    norm_num [newtonUnivariateRootStep_eq_neg_cube]

/-- Consequently, if `|t₀| = 1`, the Newton iterate sequence repeats with period `2`. -/
theorem newtonUnivariateRootIterates_two_periodic_of_abs_eq_one (t0 : ℝ)
    (ht0 : |t0| = 1) (k : ℕ) :
    (newtonUnivariateRootOrbit t0) (k + 2) = (newtonUnivariateRootOrbit t0) k := by
  have hk := (newtonUnivariateRootStep_isPeriodicPt_of_abs_eq_one t0 ht0).apply_iterate k
  rw [Function.IsPeriodicPt, Function.IsFixedPt, ← Function.iterate_add_apply] at hk
  rw [newtonUnivariateRootIterates_eq_iterate, newtonUnivariateRootIterates_eq_iterate]
  simpa [Nat.add_comm] using hk

/-- If `|t₀| > 1`, the absolute values of the Newton iterates for `t / √(1 + t²)` tend to
`+∞`, so the method diverges in magnitude. -/
-- Proof sketch: use
-- `abs_newtonUnivariateRootIterates_eq_abs_start_pow_three_pow`; when `|t₀| > 1`, the powers
-- `|t₀|^(3^k)` grow without bound.
theorem abs_newtonUnivariateRootIterates_tendsto_atTop_of_one_lt_abs (t0 : ℝ)
    (ht0 : 1 < |t0|) :
    Filter.Tendsto (fun k ↦ |(newtonUnivariateRootOrbit t0) k|)
      Filter.atTop Filter.atTop := by
  -- The explicit magnitude formula reduces divergence to the standard `r^n → +∞` fact for `r > 1`.
  have hpow : Filter.Tendsto (fun n : ℕ ↦ |t0| ^ n) Filter.atTop Filter.atTop := by
    exact tendsto_pow_atTop_atTop_of_one_lt ht0
  convert hpow.comp three_pow_tendsto_atTop using 1
  ext k
  simp [Function.comp, abs_newtonUnivariateRootIterates_eq_abs_start_pow_three_pow]

end

/-! ### Proposition_1_7_4 (from Chap01) -/
/- Proposition 1.7.4 lies in the chapter's scalar convergence-rate and complexity-threshold domain.

Primary domain:
* square-root decay bounds for real-valued error sequences

Sampled owner-style declarations:
* `sqrt_rate_complexity_bound`
* `exists_power_law_bound_of_sqrt_bound`
* `IsOptimizationErrorSequence.hasConvergenceRateOfOrder_of_sqrt_bound`
* `HasGeometricRateOfConvergence.complexity_bound`

Best owner abstraction:
* `sqrt_rate_complexity_bound` from `Definition_1_2_5.lean`

Primitive data:
* the sequence `r`
* the constant `c`
* the pointwise square-root estimate `r k ≤ c / Real.sqrt (k : ℝ)` on positive indices

Derived API:
* the explicit complexity threshold `(c / ε)^2`

Source/core/bridge triage:
* source-facing: the textbook square-root complexity threshold
* core/canonical: `sqrt_rate_complexity_bound`
* bridge/view: the pointwise square-root rate hypothesis

The former declaration in this file duplicated the owner theorem with exactly the same interface and
no extra mathematics. This recall file therefore keeps Proposition 1.7.4 machine-checkable as a
direct owner recall and introduces no parallel theorem name. -/

recall sqrt_rate_complexity_bound
    {r : ℕ → ℝ} {c ε : ℝ}
    (h : ∀ ⦃k : ℕ⦄, 0 < k → r k ≤ c / Real.sqrt (k : ℝ))
    (hε : 0 < ε)
    {k : ℕ} (hk : 0 < k)
    (hkComplexity : (c / ε) ^ (2 : ℕ) ≤ (k : ℝ)) :
    r k ≤ ε

/-! ### Proposition_1_7_5 (from Chap01) -/
/- Proposition 1.7.5 lies in the chapter's scalar convergence-rate and complexity-threshold
domain.

Primary domain:
* geometric decay bounds for real error sequences

Sampled owner-style declarations:
* `HasGeometricRateOfConvergence.complexity_bound`
* `sqrt_rate_complexity_bound`
* `le_of_complexity_bound_from_rate_estimate`
* `HasGeometricRateOfConvergence.le_target_of_iterationThreshold_le`

Best owner abstraction:
* `HasGeometricRateOfConvergence`, with `complexity_bound` as its canonical complexity-threshold
  projection

Primitive data:
* the sequence `r`
* the constants `q` and `c`
* the owner bound `HasGeometricRateOfConvergence r q c`

Derived API:
* the logarithmic threshold consequence `r k ≤ ε`

Source/core/bridge triage:
* source-facing: the textbook logarithmic threshold consequence
* core/canonical: `HasGeometricRateOfConvergence.complexity_bound`
* bridge/view: none beyond the owner theorem's direct closed-form threshold

The former file duplicated the owner theorem under a second public name and carried an unused
nonnegativity hypothesis. This recall file now reuses the canonical owner theorem directly. -/

namespace HasGeometricRateOfConvergence

recall complexity_bound
    {r : ℕ → ℝ} {q c ε : ℝ}
    (h : HasGeometricRateOfConvergence r q c)
    (hc : 0 < c) (hq₀ : 0 < q) (hq₁ : q ≤ 1) (hε : 0 < ε)
    {k : ℕ} (hkComplexity : Real.log (c / ε) / q ≤ (k : ℝ)) :
    r k ≤ ε

end HasGeometricRateOfConvergence

/-! ### Proposition_1_7_6 (from Chap01) -/
open HasEventuallySuperlinearErrorBound

variable {r : ℕ → ℝ} {c : ℝ}

/- Proposition 1.7.6 lies in the chapter's scalar superlinear-convergence domain.

Primary domain:
* quadratic tail estimates and logarithmic complexity thresholds for real error sequences

Relevant owner-style declarations sampled before refining:
* `HasEventuallySuperlinearErrorBound`
* `quadratic_tail_bound`
* `quadratic_tail_le_of_logb_bound`
* `HasSuperlinearRateOfConvergence` in `Definition_1_8_15.lean`

Best owner abstraction:
* `HasEventuallySuperlinearErrorBound r 0 c 0`

Primitive data:
* the sequence `r`
* the constant `c`
* the base index `K`
* the owner recurrence witness `HasEventuallySuperlinearErrorBound r 0 c 0`

Derived API:
* the quadratic tail estimate from `K`
* the logarithmic threshold consequence forcing `r (K + j) ≤ ε`

Source/core/bridge triage:
* source-facing: the explicit Proposition 1.7.6 tail and threshold consequences
* core/canonical: the owner-namespace theorems `quadratic_tail_bound` and
  `quadratic_tail_le_of_logb_bound`
* bridge/view: direct recall only; this file adds no extra mathematics beyond the owner
  hypotheses or their canonical local consequences

The former file kept standalone theorem names for owner-derived consequences. Those consequences
now live with the owner abstraction, and Proposition 1.7.6 reuses them directly. -/

#check (quadratic_tail_bound :
    HasEventuallySuperlinearErrorBound r 0 c 0 →
      (∀ k : ℕ, 0 ≤ r k) →
        0 < c →
          (k0 j : ℕ) → r (k0 + j) ≤ (1 / c) * (c * r k0) ^ (2 ^ j : ℕ))

#check (quadratic_tail_le_of_logb_bound :
    HasEventuallySuperlinearErrorBound r 0 c 0 →
      (∀ k : ℕ, 0 ≤ r k) →
        0 < c →
          (k0 j : ℕ) →
            (ε : ℝ) →
              0 < c * r k0 →
                c * r k0 < 1 →
                  ε ∈ Set.Ioo (0 : ℝ) (1 / c) →
                    Real.logb 2
                        (Real.log (1 / (c * ε)) / Real.log (1 / (c * r k0))) ≤ (j : ℝ) →
                      r (k0 + j) ≤ ε)

/-! ### Theorem_1_7_7 (from Chap01) -/
open scoped Gradient
open NewtonSystem (AdmissiblePoint)

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/- Theorem 1.7.7 is source-facing in the local quadratic-convergence theory of Newton's method
for smooth unconstrained optimization on a finite-dimensional real Hilbert space.

Source/core/bridge triage:
* source-facing: the locally well-defined recursive Newton orbit for the stationarity system
  `∇ f = 0`, together with its quadratic-convergence theorem
* core/canonical: the Chapter 1 Newton admissible domain `NewtonSystem.AdmissiblePoint (∇ f)` and
  the owner step `NewtonSystem.step (∇ f)`
* bridge/view: the local radius owner `localQuadraticNewtonRadius`; the recursive orbit in this
  file is the local source-facing specialization built from the owner step rather than from the
  stronger global-closure bridge `NewtonSystem.orbit`

Primary domain:
* local Newton convergence under a Hessian-Lipschitz hypothesis on a real Hilbert space

Sampled owner-style declarations:
* `NewtonSystem.AdmissiblePoint`
* `NewtonSystem.step`
* `HasLipschitzContinuousHessian`

Owner abstraction:
* the Chapter 1 Newton-step owner `NewtonSystem.step (∇ f)` on the admissible domain
  `NewtonSystem.AdmissiblePoint (∇ f)`

Primitive data:
* `f`, `xStar`, `x0`, `μ`, and `M`
* the owner hypothesis `f ∈ C22[M]`, i.e.
  `HasLipschitzContinuousHessian (M : NNReal) f`, the positive Hessian-Lipschitz constant
  encoded by `M : NNRealˣ`, stationarity, and Hessian-positivity hypotheses
* the source closed-ball hypothesis `‖x0 - xStar‖ ≤ localQuadraticNewtonRadius μ M`
* the recursively defined Newton orbit started at `x0`, with well-definedness derived locally
  from those hypotheses rather than packaged as primitive input data

Derived API:
* iteratewise Hessian nondegeneracy near `xStar`
* the recursive Newton orbit and its update rule
* closed-ball invariance and the quadratic one-step error estimate

This file therefore keeps the source-facing recursive Newton orbit and the resulting Chapter 1
local quadratic-convergence theorem. The positivity of the Hessian-Lipschitz constant is
internalized in the canonical parameter type `NNRealˣ`, so the public API carries no separate
proof-only binder `0 < M`; the ambient completeness assumption is inferred from finite
dimensionality and so is not exposed explicitly. -/

/-- The local convergence radius `2 μ / (3 M)` from Theorem 1.7.7, with positivity of `M`
encoded in `M : NNRealˣ`. -/
def localQuadraticNewtonRadius (μ : ℝ) (M : NNRealˣ) : ℝ :=
  2 * μ / (3 * (M : ℝ))

/-- Expanding `localQuadraticNewtonRadius μ M` gives the textbook formula `2 μ / (3 M)`. -/
theorem localQuadraticNewtonRadius_def (μ : ℝ) (M : NNRealˣ) :
    localQuadraticNewtonRadius μ M = 2 * μ / (3 * (M : ℝ)) :=
  rfl

section

variable {μ : ℝ} {M : NNRealˣ} {f : E → ℝ} {xStar x0 : E}

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 1.7.7: on a segment, the affine map `t ↦ x + t • d` has derivative `d`. -/
private theorem line_hasDerivAt (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate the scalar multiple and then translate by the base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const d).const_add x

/-- Helper for Theorem 1.7.7: a function in `C22[M]` has a continuous gradient field. -/
private theorem gradient_continuous (hf : f ∈ C22[M]) : Continuous (∇ f) := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfd : Continuous (fderiv ℝ f) := hf.contDiff.continuous_fderiv (by norm_num)
  -- The gradient is the Riesz image of the Fréchet derivative.
  simpa [gradient, D] using D.continuous.comp hfd

/-- Helper for Theorem 1.7.7: the derivative of the gradient is the Hessian. -/
private theorem gradient_hasFDerivAt (hf : f ∈ C22[M]) (x : E) :
    HasFDerivAt (∇ f) (hessian f x) x := by
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    have hfderiv : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
      (hf.contDiff.contDiffAt (x := x)).fderiv_right
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
    exact hfderiv.differentiableAt one_ne_zero
  have hgradDiff : DifferentiableAt ℝ (∇ f) x := by
    -- Rewrite the gradient through the Riesz map and compose differentiable maps.
    simpa [gradient, D] using D.differentiableAt.comp x hfdiff
  -- The derivative of the gradient is the Hessian by definition.
  simpa [hessian] using hgradDiff.hasFDerivAt

/-- Helper for Theorem 1.7.7: integrating the Hessian action along a segment recovers the
gradient increment. -/
private theorem segment_gradient_integral_eq
    (hf : f ∈ C22[M]) (x d : E) :
    ∇ f (x + d) - ∇ f x = ∫ t in 0..1, hessian f (x + t • d) d := by
  have hderiv :
      ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ ↦ ∇ f (x + s • d)) (hessian f (x + t • d) d) t := by
    intro t ht
    -- Differentiate the gradient after restricting it to the affine segment.
    simpa [Function.comp] using
      (gradient_hasFDerivAt (hf := hf) (x := x + t • d)).comp_hasDerivAt t
        (line_hasDerivAt x d t)
  have hcont :
      Continuous (fun t : ℝ ↦ hessian f (x + t • d) d) := by
    have hcontH : Continuous (fun t : ℝ ↦ hessian f (x + t • d)) :=
      (HasLipschitzContinuousHessian.lipschitz hf).continuous.comp
        (continuous_const.add (continuous_id.smul continuous_const))
    exact hcontH.clm_apply continuous_const
  have hint :
      IntervalIntegrable (fun t : ℝ ↦ hessian f (x + t • d) d) MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable 0 1
  -- Apply the fundamental theorem of calculus to the gradient restriction.
  symm
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- Helper for Theorem 1.7.7: the Hessian Lipschitz estimate controls the segment action
`(∇²f(x + t d) - ∇²f(x)) d`. -/
private theorem segment_hessian_action_bound
    (hf : f ∈ C22[M]) (x d : E) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖(hessian f (x + t • d) - hessian f x) d‖ ≤ (M : ℝ) * t * ‖d‖ ^ (2 : ℕ) := by
  have hnorm :
      ‖hessian f (x + t • d) - hessian f x‖ ≤ (M : ℝ) * ‖t • d‖ := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      HasLipschitzContinuousHessian.norm_sub_le hf (x + t • d) x
  -- Convert the operator-norm bound into the action bound on the displacement vector.
  calc
    ‖(hessian f (x + t • d) - hessian f x) d‖
      ≤ ‖hessian f (x + t • d) - hessian f x‖ * ‖d‖ := by
          exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((M : ℝ) * ‖t • d‖) * ‖d‖ := by
          gcongr
    _ = ((M : ℝ) * (t * ‖d‖)) * ‖d‖ := by
          rw [norm_smul, Real.norm_of_nonneg ht.1]
    _ = (M : ℝ) * t * ‖d‖ ^ (2 : ℕ) := by
          ring

/-- Helper for Theorem 1.7.7: the Hessian Lipschitz condition yields the first-order Taylor
remainder bound for the gradient. -/
private theorem gradient_deviation_le_local
    (hf : f ∈ C22[M]) (x y : E) :
    ‖∇ f y - ∇ f x - hessian f x (y - x)‖ ≤
      ((M : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  let d : E := y - x
  have hy : x + d = y := by
    simp [d]
  have hcontIntegrand :
      Continuous (fun t : ℝ ↦ (hessian f (x + t • d) - hessian f x) d) := by
    have hcontH : Continuous (fun t : ℝ ↦ hessian f (x + t • d) - hessian f x) :=
      ((HasLipschitzContinuousHessian.lipschitz hf).continuous.comp
        (continuous_const.add (continuous_id.smul continuous_const))).sub continuous_const
    exact hcontH.clm_apply continuous_const
  have hintIntegrand :
      IntervalIntegrable (fun t : ℝ ↦ (hessian f (x + t • d) - hessian f x) d)
        MeasureTheory.volume 0 1 :=
    hcontIntegrand.intervalIntegrable 0 1
  have hintBound :
      IntervalIntegrable (fun t : ℝ ↦ (M : ℝ) * t * ‖d‖ ^ (2 : ℕ))
        MeasureTheory.volume 0 1 :=
    ((continuous_const.mul continuous_id).mul continuous_const).intervalIntegrable 0 1
  have hmono :
      ∫ t in 0..1, ‖(hessian f (x + t • d) - hessian f x) d‖
        ≤ ∫ t in 0..1, (M : ℝ) * t * ‖d‖ ^ (2 : ℕ) := by
    -- Bound the integrand pointwise on the whole segment.
    refine intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
      hintIntegrand.norm hintBound ?_
    intro t ht
    exact segment_hessian_action_bound (hf := hf) (x := x) (d := d) ht
  have hrewrite :
      ∇ f y - ∇ f x - hessian f x d =
        ∫ t in 0..1, (hessian f (x + t • d) - hessian f x) d := by
    -- Rewrite the remainder as an integral of Hessian differences.
    rw [← hy, segment_gradient_integral_eq (hf := hf) (x := x) (d := d)]
    have hconst : ∫ t in 0..1, hessian f x d = hessian f x d := by
      simp
    rw [hconst.symm]
    have hintSegment :
        IntervalIntegrable (fun t : ℝ ↦ (hessian f (x + t • d)) d)
          MeasureTheory.volume 0 1 :=
      ((((HasLipschitzContinuousHessian.lipschitz hf).continuous.comp
          (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
        continuous_const).intervalIntegrable 0 1)
    have hsub0 :
        ∫ t in 0..1, (hessian f (x + t • d)) d - (hessian f x) d =
          (∫ t in 0..1, (hessian f (x + t • d)) d) - ∫ t in 0..1, (hessian f x) d := by
      simpa using
        (intervalIntegral.integral_sub
          (f := fun t : ℝ ↦ (hessian f (x + t • d)) d)
          (g := fun _ : ℝ ↦ (hessian f x) d)
          (μ := MeasureTheory.volume)
          hintSegment
          (continuous_const.intervalIntegrable 0 1))
    have hsub :
        (∫ t in 0..1, (hessian f (x + t • d)) d) - ∫ t in 0..1, (hessian f x) d =
          ∫ t in 0..1, (hessian f (x + t • d)) d - (hessian f x) d := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsub0.symm
    calc
      (∫ t in 0..1, (hessian f (x + t • d)) d) - ∫ t in 0..1, (hessian f x) d
        = ∫ t in 0..1, (hessian f (x + t • d)) d - (hessian f x) d := hsub
      _ = ∫ t in 0..1, (hessian f (x + t • d) - hessian f x) d := by
          refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro t ht
          simp
  -- Integrate the pointwise Hessian bound and compute `∫₀¹ t = 1 / 2`.
  calc
    ‖∇ f y - ∇ f x - hessian f x d‖
      = ‖∫ t in 0..1, (hessian f (x + t • d) - hessian f x) d‖ := by
          rw [hrewrite]
    _ ≤ ∫ t in 0..1, ‖(hessian f (x + t • d) - hessian f x) d‖ := by
          exact intervalIntegral.norm_integral_le_integral_norm
            (f := fun t : ℝ ↦ (hessian f (x + t • d) - hessian f x) d)
            (a := (0 : ℝ)) (b := 1) (show (0 : ℝ) ≤ 1 by norm_num)
    _ ≤ ∫ t in 0..1, (M : ℝ) * t * ‖d‖ ^ (2 : ℕ) := hmono
    _ = ((M : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
          calc
            ∫ t in 0..1, (M : ℝ) * t * ‖d‖ ^ (2 : ℕ)
              = ∫ t in 0..1, ((M : ℝ) * ‖d‖ ^ (2 : ℕ)) * t := by
                  congr with t
                  ring
            _ = ((M : ℝ) * ‖d‖ ^ (2 : ℕ)) * (1 / 2 : ℝ) := by
                  rw [intervalIntegral.integral_const_mul, integral_id]
                  norm_num
            _ = ((M : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
                  ring
    _ = ((M : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
          simp [d]

/-- Helper for Theorem 1.7.7: the Hessian Lipschitz bound implies the local Loewner comparison
`∇²f(xStar) - M ‖x - xStar‖ I ≤ ∇²f(x)`. -/
private theorem hessian_loewner_bounds_of_hessian_lipschitz_local
    (hf : f ∈ C22[M]) (x y : E) :
    let s : ℝ := (M : ℝ) * ‖y - x‖
    hessian f x - s • 1 ≤ hessian f y ∧
      hessian f y ≤ hessian f x + s • 1 := by
  let Δ : E →L[ℝ] E := hessian f y - hessian f x
  let s : ℝ := (M : ℝ) * ‖y - x‖
  have hΔ_symm : Δ.IsSymmetric := by
    dsimp [Δ]
    exact (fderiv_gradient_isSymmetric_of_contDiffAt
      (hf.contDiff.contDiffAt : ContDiffAt ℝ 2 f y)).sub
      (fderiv_gradient_isSymmetric_of_contDiffAt
        (hf.contDiff.contDiffAt : ContDiffAt ℝ 2 f x))
  have hΔ_norm : ‖Δ‖ ≤ s := by
    dsimp [Δ, s]
    exact HasLipschitzContinuousHessian.norm_sub_le hf y x
  have hquad_bound (u : E) :
      |inner ℝ (Δ u) u| ≤ s * ‖u‖ ^ (2 : ℕ) := by
    calc
      |inner ℝ (Δ u) u| ≤ ‖Δ u‖ * ‖u‖ := by
        simpa [real_inner_comm] using abs_real_inner_le_norm (Δ u) u
      _ ≤ (‖Δ‖ * ‖u‖) * ‖u‖ := by
        gcongr
        exact Δ.le_opNorm u
      _ = ‖Δ‖ * ‖u‖ ^ (2 : ℕ) := by ring
      _ ≤ s * ‖u‖ ^ (2 : ℕ) := by
        gcongr
  have hsI_symm : (s • (1 : E →L[ℝ] E)).IsSymmetric := by
    intro u v
    simp [real_inner_smul_left, real_inner_smul_right]
  have hupper_nonneg : 0 ≤ s • (1 : E →L[ℝ] E) - Δ := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff]
    constructor
    · exact hsI_symm.sub hΔ_symm
    · intro u
      have hu : inner ℝ (Δ u) u ≤ s * ‖u‖ ^ (2 : ℕ) := (abs_le.mp (hquad_bound u)).2
      have hrewrite :
          inner ℝ ((s • (1 : E →L[ℝ] E) - Δ) u) u =
            s * ‖u‖ ^ (2 : ℕ) - inner ℝ (Δ u) u := by
        simp [real_inner_smul_left, inner_sub_left]
      rw [hrewrite]
      linarith
  have hlower_nonneg : 0 ≤ s • (1 : E →L[ℝ] E) + Δ := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff]
    constructor
    · exact hsI_symm.add hΔ_symm
    · intro u
      have hu : -(s * ‖u‖ ^ (2 : ℕ)) ≤ inner ℝ (Δ u) u := (abs_le.mp (hquad_bound u)).1
      have hrewrite :
          inner ℝ ((s • (1 : E →L[ℝ] E) + Δ) u) u =
            s * ‖u‖ ^ (2 : ℕ) + inner ℝ (Δ u) u := by
        simp [real_inner_smul_left, inner_add_left]
      rw [hrewrite]
      linarith
  constructor
  · rw [ContinuousLinearMap.le_def]
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp <| by
      dsimp [Δ, s] at hlower_nonneg ⊢
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hlower_nonneg
  · rw [ContinuousLinearMap.le_def]
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp <| by
      dsimp [Δ, s] at hupper_nonneg ⊢
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hupper_nonneg

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Helper for Theorem 1.7.7: inside the local Newton ball, the scaled error term is bounded by
`2 μ / 3`. -/
private theorem localQuadraticNewton_scaled_error_le
    {x : E} (hx : ‖x - xStar‖ ≤ localQuadraticNewtonRadius μ M) :
    (M : ℝ) * ‖x - xStar‖ ≤ 2 * μ / 3 := by
  have hM_pos : 0 < (M : ℝ) := by
    have hnonneg : 0 ≤ (M : ℝ) := by
      positivity
    have hne : (M : ℝ) ≠ 0 := by
      exact_mod_cast M.ne_zero
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hscaled := mul_le_mul_of_nonneg_left hx hM_pos.le
  dsimp [localQuadraticNewtonRadius] at hscaled
  have hthreeM_ne : (3 : ℝ) * (M : ℝ) ≠ 0 := by
    positivity
  field_simp [hthreeM_ne] at hscaled
  linarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Helper for Theorem 1.7.7: the spectral margin `μ - M ‖x - x*‖` stays above `μ / 3` inside
`B(x*, 2 μ / (3 M))`. -/
private theorem localQuadraticNewton_margin_lower
    {x : E} (hx : ‖x - xStar‖ ≤ localQuadraticNewtonRadius μ M) :
    μ / 3 ≤ μ - (M : ℝ) * ‖x - xStar‖ := by
  -- Convert the ball constraint into the textbook `M ‖x - x*‖ ≤ 2 μ / 3` bound.
  have hscaled := localQuadraticNewton_scaled_error_le (μ := μ) (M := M) (xStar := xStar) hx
  linarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Helper for Theorem 1.7.7: the spectral margin in the denominator of the Newton estimate is
strictly positive on the local Newton ball. -/
private theorem localQuadraticNewton_margin_pos
    (hμ : 0 < μ) {x : E} (hx : ‖x - xStar‖ ≤ localQuadraticNewtonRadius μ M) :
    0 < μ - (M : ℝ) * ‖x - xStar‖ := by
  -- The explicit lower bound `μ / 3` gives the positivity needed for invertibility estimates.
  have hmargin : μ / 3 ≤ μ - (M : ℝ) * ‖x - xStar‖ :=
    localQuadraticNewton_margin_lower (μ := μ) (M := M) (xStar := xStar) hx
  have hthird_pos : 0 < μ / 3 := by
    positivity
  exact lt_of_lt_of_le hthird_pos hmargin

/-- Helper for Theorem 1.7.7: the Hessian at a point in the local Newton ball keeps the lower
Loewner bound `μ - M ‖x - x*‖`. -/
private theorem hessian_lower_shift_isPositive_of_mem_localQuadraticNewtonBall
    (hf : f ∈ C22[M])
    (hHstar : (fderiv ℝ (∇ f) xStar - μ • (1 : E →L[ℝ] E)).IsPositive)
    {x : E} :
    (hessian f x - (μ - (M : ℝ) * ‖x - xStar‖) • (1 : E →L[ℝ] E)).IsPositive := by
  let s : ℝ := (M : ℝ) * ‖x - xStar‖
  have hHstar' : (hessian f xStar - μ • (1 : E →L[ℝ] E)).IsPositive := by
    simpa [hessian] using hHstar
  have hloewner : hessian f xStar - s • (1 : E →L[ℝ] E) ≤ hessian f x := by
    -- The Hessian-Lipschitz comparison transports the lower bound from `xStar` to `x`.
    simpa [hessian, s, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (hessian_loewner_bounds_of_hessian_lipschitz_local (M := M) (f := f) hf xStar x).1
  rw [ContinuousLinearMap.le_def] at hloewner
  have hsum :
      (hessian f x - (μ - s) • (1 : E →L[ℝ] E)) =
        (hessian f x - (hessian f xStar - s • (1 : E →L[ℝ] E))) +
          (hessian f xStar - μ • (1 : E →L[ℝ] E)) := by
    ext u
    rw [sub_smul]
    abel_nf
  -- Split the shifted Hessian into the transported comparison term and the base-point positivity.
  rw [hsum]
  exact hloewner.add hHstar'

/-- A point in the local Newton ball has nondegenerate Hessian under the assumptions of
Theorem 1.7.7. -/
theorem hessian_det_ne_zero_of_mem_localQuadraticNewtonBall
    (hμ : 0 < μ) (hf : f ∈ C22[M])
    (hHstar : (fderiv ℝ (∇ f) xStar - μ • (1 : E →L[ℝ] E)).IsPositive)
    {x : E} (hx : ‖x - xStar‖ ≤ localQuadraticNewtonRadius μ M) :
    (fderiv ℝ (∇ f) x).det ≠ 0 := by
  let c : ℝ := μ - (M : ℝ) * ‖x - xStar‖
  have hc_pos : 0 < c :=
    localQuadraticNewton_margin_pos (μ := μ) (M := M) (xStar := xStar) hμ hx
  have hshift_pos :
      (hessian f x - c • (1 : E →L[ℝ] E)).IsPositive := by
    simpa [c] using
      hessian_lower_shift_isPositive_of_mem_localQuadraticNewtonBall
        (μ := μ) (M := M) (f := f) (xStar := xStar) hf hHstar
  rw [ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot]
  intro hker
  obtain ⟨u, hu_mem, hu_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hu_zero : hessian f x u = 0 := hu_mem
  have hquad_nonneg : c * ‖u‖ ^ (2 : ℕ) ≤ 0 := by
    -- A nonzero kernel vector would force the positive quadratic form to become strictly negative.
    simpa [c, hu_zero, inner_smul_left, inner_self_eq_norm_sq_to_K] using
      hshift_pos.inner_nonneg_left u
  have hnorm_pos : 0 < ‖u‖ ^ (2 : ℕ) := by
    positivity
  have hprod_pos : 0 < c * ‖u‖ ^ (2 : ℕ) := by
    positivity
  linarith

/- A point in the local Newton ball canonically defines an admissible point for the Newton
system `∇ f = 0`. This is internal bridge data from the source-facing ball description to the
owner Newton admissible domain. -/
private abbrev localQuadraticNewtonPoint
    (hμ : 0 < μ) (hf : f ∈ C22[M])
    (hHstar : (fderiv ℝ (∇ f) xStar - μ • (1 : E →L[ℝ] E)).IsPositive)
    {x : E} (hx : ‖x - xStar‖ ≤ localQuadraticNewtonRadius μ M) :
    AdmissiblePoint (∇ f) :=
  ⟨x, hessian_det_ne_zero_of_mem_localQuadraticNewtonBall hμ hf hHstar hx⟩

/-- Helper for Theorem 1.7.7: the inverse Hessian on the local Newton ball is controlled by the
reciprocal spectral margin `1 / (μ - M ‖x - x*‖)`. -/
private theorem inverse_hessian_apply_le_of_mem_localQuadraticNewtonBall
    (hμ : 0 < μ) (hf : f ∈ C22[M])
    (hHstar : (fderiv ℝ (∇ f) xStar - μ • (1 : E →L[ℝ] E)).IsPositive)
    {x : E} (hx : ‖x - xStar‖ ≤ localQuadraticNewtonRadius μ M) :
    let A := hessian f x
    let Ainv :=
      ((A.toContinuousLinearEquivOfDetNeZero
        (hessian_det_ne_zero_of_mem_localQuadraticNewtonBall hμ hf hHstar hx)).symm :
          E →L[ℝ] E)
    ∀ v : E, ‖Ainv v‖ ≤ (1 / (μ - (M : ℝ) * ‖x - xStar‖)) * ‖v‖ := by
  let c : ℝ := μ - (M : ℝ) * ‖x - xStar‖
  let A : E →L[ℝ] E := hessian f x
  let hA : A.det ≠ 0 := by
    simpa [A, hessian] using
      hessian_det_ne_zero_of_mem_localQuadraticNewtonBall
        (μ := μ) (M := M) (f := f) (xStar := xStar) hμ hf hHstar hx
  let Ainv : E →L[ℝ] E := ((A.toContinuousLinearEquivOfDetNeZero hA).symm : E →L[ℝ] E)
  have hc_pos : 0 < c :=
    localQuadraticNewton_margin_pos (μ := μ) (M := M) (xStar := xStar) hμ hx
  have hshift_pos : (A - c • (1 : E →L[ℝ] E)).IsPositive := by
    simpa [A, c] using
      hessian_lower_shift_isPositive_of_mem_localQuadraticNewtonBall
        (μ := μ) (M := M) (f := f) (xStar := xStar) hf hHstar
  have hlower (u : E) : c * ‖u‖ ≤ ‖A u‖ := by
    by_cases hu : u = 0
    · simp [hu]
    · have hquad_nonneg : 0 ≤ inner ℝ ((A - c • (1 : E →L[ℝ] E)) u) u :=
        hshift_pos.inner_nonneg_left u
      have hquad_le : c * ‖u‖ ^ (2 : ℕ) ≤ inner ℝ (A u) u := by
        have hrewrite :
            inner ℝ ((A - c • (1 : E →L[ℝ] E)) u) u =
              inner ℝ (A u) u - c * ‖u‖ ^ (2 : ℕ) := by
          simp [inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K]
        rw [hrewrite] at hquad_nonneg
        linarith
      have hcs : c * ‖u‖ ^ (2 : ℕ) ≤ ‖A u‖ * ‖u‖ := by
        have hinner_le : inner ℝ (A u) u ≤ ‖A u‖ * ‖u‖ := by
          exact le_trans (le_abs_self _) <| by
            simpa [real_inner_comm] using abs_real_inner_le_norm (A u) u
        calc
          c * ‖u‖ ^ (2 : ℕ) ≤ inner ℝ (A u) u := hquad_le
          _ ≤ ‖A u‖ * ‖u‖ := hinner_le
      have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
      have hcs' : c * ‖u‖ * ‖u‖ ≤ ‖A u‖ * ‖u‖ := by
        simpa [pow_two, mul_assoc] using hcs
      exact (mul_le_mul_iff_of_pos_right hu_norm_pos).mp hcs'
  dsimp
  intro v
  by_cases hv : v = 0
  · simp [hv]
  · have hmain := hlower (Ainv v)
    have happly : A (Ainv v) = v := by
      exact ContinuousLinearEquiv.apply_symm_apply (A.toContinuousLinearEquivOfDetNeZero hA) v
    rw [happly] at hmain
    have hdiv : ‖Ainv v‖ ≤ ‖v‖ / c := by
      refine (le_div_iff₀ hc_pos).2 ?_
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmain
    simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using hdiv

/-- A single Newton step from a point in the local Newton ball stays in that ball and satisfies
the quadratic error estimate from Theorem 1.7.7. -/
theorem newtonOptimization_step_mem_ball_and_quadratic_error_bound
    (hμ : 0 < μ) (hf : f ∈ C22[M]) (hgrad : ∇ f xStar = 0)
    (hHstar : (fderiv ℝ (∇ f) xStar - μ • (1 : E →L[ℝ] E)).IsPositive)
    {x : E}
    (hx : ‖x - xStar‖ ≤ localQuadraticNewtonRadius μ M) :
    ‖NewtonSystem.step (∇ f) (localQuadraticNewtonPoint hμ hf hHstar hx) - xStar‖ ≤
        localQuadraticNewtonRadius μ M ∧
      ‖NewtonSystem.step (∇ f) (localQuadraticNewtonPoint hμ hf hHstar hx) - xStar‖ ≤
        ((M : ℝ) * ‖x - xStar‖ ^ (2 : ℕ)) /
          (2 * (μ - (M : ℝ) * ‖x - xStar‖)) := by
  let e : E := x - xStar
  let A : E →L[ℝ] E := hessian f x
  let hA : A.det ≠ 0 := by
    simpa [A, hessian] using
      hessian_det_ne_zero_of_mem_localQuadraticNewtonBall
        (μ := μ) (M := M) (f := f) (xStar := xStar) hμ hf hHstar hx
  let Ainv : E →L[ℝ] E := ((A.toContinuousLinearEquivOfDetNeZero hA).symm : E →L[ℝ] E)
  let stepPoint : AdmissiblePoint (∇ f) := localQuadraticNewtonPoint hμ hf hHstar hx
  have hstep_eq :
      NewtonSystem.step (∇ f) stepPoint - xStar = Ainv (A e - ∇ f x) := by
    -- Rewrite the Newton correction as inverse Hessian applied to the gradient Taylor remainder.
    calc
      NewtonSystem.step (∇ f) stepPoint - xStar
          = (x - Ainv (∇ f x)) - xStar := by
              simp [NewtonSystem.step_def, stepPoint, A, Ainv, hessian]
      _ = e - Ainv (∇ f x) := by
            simp [e, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = Ainv (A e) - Ainv (∇ f x) := by
            rw [show Ainv (A e) = e by
              exact ContinuousLinearEquiv.symm_apply_apply
                (A.toContinuousLinearEquivOfDetNeZero hA) e]
      _ = Ainv (A e - ∇ f x) := by
            simp
  have hremainder_raw : ‖A e - ∇ f x‖ ≤ ((M : ℝ) / 2) * ‖xStar - x‖ ^ (2 : ℕ) := by
    -- The Chapter 1 gradient Taylor estimate is the source proof's `H_k` remainder bound.
    simpa [A, e, hgrad, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (gradient_deviation_le_local (M := M) (f := f) hf x xStar)
  have hremainder : ‖A e - ∇ f x‖ ≤ ((M : ℝ) / 2) * ‖e‖ ^ (2 : ℕ) := by
    calc
      ‖A e - ∇ f x‖ ≤ ((M : ℝ) / 2) * ‖xStar - x‖ ^ (2 : ℕ) := hremainder_raw
      _ = ((M : ℝ) / 2) * ‖e‖ ^ (2 : ℕ) := by
            rw [norm_sub_rev]
  have hAinv : ∀ v : E, ‖Ainv v‖ ≤ (1 / (μ - (M : ℝ) * ‖x - xStar‖)) * ‖v‖ := by
    simpa [A, Ainv] using
      inverse_hessian_apply_le_of_mem_localQuadraticNewtonBall
        (μ := μ) (M := M) (f := f) (xStar := xStar) hμ hf hHstar hx
  have hmargin_pos : 0 < μ - (M : ℝ) * ‖x - xStar‖ :=
    localQuadraticNewton_margin_pos (μ := μ) (M := M) (xStar := xStar) hμ hx
  have hquad :
      ‖NewtonSystem.step (∇ f) stepPoint - xStar‖ ≤
        ((M : ℝ) * ‖x - xStar‖ ^ (2 : ℕ)) /
          (2 * (μ - (M : ℝ) * ‖x - xStar‖)) := by
    rw [hstep_eq]
    calc
      ‖Ainv (A e - ∇ f x)‖
          ≤ (1 / (μ - (M : ℝ) * ‖x - xStar‖)) * ‖A e - ∇ f x‖ :=
            hAinv _
      _ ≤ (1 / (μ - (M : ℝ) * ‖x - xStar‖)) * (((M : ℝ) / 2) * ‖e‖ ^ (2 : ℕ)) := by
            gcongr
      _ = ((M : ℝ) * ‖x - xStar‖ ^ (2 : ℕ)) /
            (2 * (μ - (M : ℝ) * ‖x - xStar‖)) := by
            field_simp [hmargin_pos.ne']
            ring
  have hradius_sq :
      (M : ℝ) * ‖x - xStar‖ ^ (2 : ℕ) ≤
        (M : ℝ) * (localQuadraticNewtonRadius μ M) ^ (2 : ℕ) := by
    gcongr
  have hmargin_lower : μ / 3 ≤ μ - (M : ℝ) * ‖x - xStar‖ :=
    localQuadraticNewton_margin_lower (μ := μ) (M := M) (xStar := xStar) hx
  have hball : ‖NewtonSystem.step (∇ f) stepPoint - xStar‖ ≤ localQuadraticNewtonRadius μ M := by
    calc
      ‖NewtonSystem.step (∇ f) stepPoint - xStar‖
          ≤ ((M : ℝ) * ‖x - xStar‖ ^ (2 : ℕ)) /
              (2 * (μ - (M : ℝ) * ‖x - xStar‖)) := hquad
      _ ≤ ((M : ℝ) * (localQuadraticNewtonRadius μ M) ^ (2 : ℕ)) /
            (2 * (μ / 3)) := by
            have hden_comp : 2 * (μ / 3) ≤ 2 * (μ - (M : ℝ) * ‖x - xStar‖) := by
              gcongr
            refine (div_le_div_iff₀ ?_ ?_).2 ?_
            · positivity
            · positivity
            calc
              ((M : ℝ) * ‖x - xStar‖ ^ (2 : ℕ)) * (2 * (μ / 3))
                  ≤ ((M : ℝ) * (localQuadraticNewtonRadius μ M) ^ (2 : ℕ)) * (2 * (μ / 3)) := by
                    gcongr
              _ ≤ ((M : ℝ) * (localQuadraticNewtonRadius μ M) ^ (2 : ℕ)) *
                    (2 * (μ - (M : ℝ) * ‖x - xStar‖)) := by
                      gcongr
      _ = localQuadraticNewtonRadius μ M := by
            have hM_pos : (0 : ℝ) < (M : ℝ) := by
              have hnonneg : 0 ≤ (M : ℝ) := by
                positivity
              have hne : (M : ℝ) ≠ 0 := by
                exact_mod_cast M.ne_zero
              exact lt_of_le_of_ne hnonneg (Ne.symm hne)
            rw [localQuadraticNewtonRadius_def]
            field_simp [hM_pos.ne']
  exact ⟨hball, hquad⟩

private abbrev LocalQuadraticNewtonState (μ : ℝ) (M : NNRealˣ) (xStar : E) :=
  {x : E // ‖x - xStar‖ ≤ localQuadraticNewtonRadius μ M}

private def localQuadraticNewtonStateStep
    (hμ : 0 < μ) (hf : f ∈ C22[M]) (hgrad : ∇ f xStar = 0)
    (hHstar : (fderiv ℝ (∇ f) xStar - μ • (1 : E →L[ℝ] E)).IsPositive) :
    LocalQuadraticNewtonState μ M xStar → LocalQuadraticNewtonState μ M xStar :=
  fun x ↦
    let hstep :=
      newtonOptimization_step_mem_ball_and_quadratic_error_bound
        hμ hf hgrad hHstar x.property
    ⟨NewtonSystem.step (∇ f) (localQuadraticNewtonPoint hμ hf hHstar x.property), hstep.1⟩

private def localQuadraticNewtonStateOrbit
    (hμ : 0 < μ) (hf : f ∈ C22[M]) (hgrad : ∇ f xStar = 0)
    (hHstar : (fderiv ℝ (∇ f) xStar - μ • (1 : E →L[ℝ] E)).IsPositive)
    (hx0 : ‖x0 - xStar‖ ≤ localQuadraticNewtonRadius μ M) :
    ℕ → LocalQuadraticNewtonState μ M xStar :=
  fun k ↦
    ((localQuadraticNewtonStateStep hμ hf hgrad hHstar)^[k]
      ⟨x0, hx0⟩)

/-- Helper for Theorem 1.7.7: the recursive state orbit advances by one application of the local
Newton state step. -/
private theorem localQuadraticNewtonStateOrbit_succ
    (hμ : 0 < μ) (hf : f ∈ C22[M]) (hgrad : ∇ f xStar = 0)
    (hHstar : (fderiv ℝ (∇ f) xStar - μ • (1 : E →L[ℝ] E)).IsPositive)
    (hx0 : ‖x0 - xStar‖ ≤ localQuadraticNewtonRadius μ M) (k : ℕ) :
    localQuadraticNewtonStateOrbit hμ hf hgrad hHstar hx0 (k + 1) =
      localQuadraticNewtonStateStep hμ hf hgrad hHstar
        (localQuadraticNewtonStateOrbit hμ hf hgrad hHstar hx0 k) := by
  -- This is just the canonical `Function.iterate` successor rule.
  exact Function.iterate_succ_apply' _ k _

/-- Helper for Theorem 1.7.7: the source-facing local Newton method starts from the prescribed
initial point `x0`. -/
private theorem localQuadraticNewtonMethod_x_zero
    (hμ : 0 < μ) (hf : f ∈ C22[M]) (hgrad : ∇ f xStar = 0)
    (hHstar : (fderiv ℝ (∇ f) xStar - μ • (1 : E →L[ℝ] E)).IsPositive)
    (hx0 : ‖x0 - xStar‖ ≤ localQuadraticNewtonRadius μ M) :
    ((localQuadraticNewtonPoint hμ hf hHstar
      (localQuadraticNewtonStateOrbit hμ hf hgrad hHstar hx0 0).property :
        AdmissiblePoint (∇ f)) : E) = x0 := by
  rfl

/-- Helper for Theorem 1.7.7: the source-facing local Newton method satisfies the Newton update
at each successor step. -/
private theorem localQuadraticNewtonMethod_step_eq
    (hμ : 0 < μ) (hf : f ∈ C22[M]) (hgrad : ∇ f xStar = 0)
    (hHstar : (fderiv ℝ (∇ f) xStar - μ • (1 : E →L[ℝ] E)).IsPositive)
    (hx0 : ‖x0 - xStar‖ ≤ localQuadraticNewtonRadius μ M) (k : ℕ) :
    ((localQuadraticNewtonPoint hμ hf hHstar
      (localQuadraticNewtonStateOrbit hμ hf hgrad hHstar hx0 (k + 1)).property :
        AdmissiblePoint (∇ f)) : E) =
      NewtonSystem.step (∇ f)
        (localQuadraticNewtonPoint hμ hf hHstar
          (localQuadraticNewtonStateOrbit hμ hf hgrad hHstar hx0 k).property) := by
  -- Expand one state-orbit step and read off the first coordinate of the resulting subtype.
  rw [localQuadraticNewtonStateOrbit_succ hμ hf hgrad hHstar hx0 k]
  rfl

/- The source-facing local Newton method from Theorem 1.7.7, valued in the canonical owner
type `NewtonSystem.Method`. This is internal scaffolding for the public orbit API below. -/
private def localQuadraticNewtonMethod
    (hμ : 0 < μ) (hf : f ∈ C22[M]) (hgrad : ∇ f xStar = 0)
    (hHstar : (fderiv ℝ (∇ f) xStar - μ • (1 : E →L[ℝ] E)).IsPositive)
    (hx0 : ‖x0 - xStar‖ ≤ localQuadraticNewtonRadius μ M) :
    NewtonSystem.Method (∇ f) x0 where
  x k :=
    localQuadraticNewtonPoint hμ hf hHstar
      (localQuadraticNewtonStateOrbit hμ hf hgrad hHstar hx0 k).property
  x_zero := localQuadraticNewtonMethod_x_zero hμ hf hgrad hHstar hx0
  step_eq := localQuadraticNewtonMethod_step_eq hμ hf hgrad hHstar hx0

/-- The recursive Newton orbit from Theorem 1.7.7, started at `x0` and obtained as the
underlying trajectory of the canonical local Newton method. -/
abbrev localQuadraticNewtonOrbit
    (hμ : 0 < μ) (hf : f ∈ C22[M]) (hgrad : ∇ f xStar = 0)
    (hHstar : (fderiv ℝ (∇ f) xStar - μ • (1 : E →L[ℝ] E)).IsPositive)
    (hx0 : ‖x0 - xStar‖ ≤ localQuadraticNewtonRadius μ M) :
    ℕ → E :=
  localQuadraticNewtonMethod hμ hf hgrad hHstar hx0

/-- Every point of the recursive local Newton orbit stays in the closed ball from Theorem 1.7.7. -/
theorem localQuadraticNewtonOrbit_mem_ball
    (hμ : 0 < μ) (hf : f ∈ C22[M]) (hgrad : ∇ f xStar = 0)
    (hHstar : (fderiv ℝ (∇ f) xStar - μ • (1 : E →L[ℝ] E)).IsPositive)
    (hx0 : ‖x0 - xStar‖ ≤ localQuadraticNewtonRadius μ M) (k : ℕ) :
    ‖localQuadraticNewtonOrbit hμ hf hgrad hHstar hx0 k - xStar‖ ≤
      localQuadraticNewtonRadius μ M := by
  simpa [localQuadraticNewtonOrbit, localQuadraticNewtonMethod] using
    (localQuadraticNewtonStateOrbit hμ hf hgrad hHstar hx0 k).property

/-- Theorem 1.7.7: if `f : E → ℝ` has `M`-Lipschitz Hessian for a positive constant encoded by
`M : NNRealˣ`, `xStar` is critical, and the Hessian at `xStar` dominates `μ I`, then the
recursively defined Newton orbit for the stationarity system `∇ f = 0` started at an initial
point in the closed ball of radius `2 μ / (3 M)` around `xStar` is well defined, stays in that
closed ball, and satisfies the standard quadratic one-step error estimate. -/
-- Proof sketch: first show that every point in the local ball has nondegenerate Hessian. This
-- makes the Newton step well defined there, and the one-step estimate keeps the orbit inside the
-- same ball. Iterating that invariant yields the recursive orbit together with iteratewise
-- Hessian nondegeneracy and the quadratic error bound.
theorem newtonOptimizationIterates_mem_ball_and_quadratic_error_bound
    (hμ : 0 < μ) (hf : f ∈ C22[M]) (hgrad : ∇ f xStar = 0)
    (hHstar : (fderiv ℝ (∇ f) xStar - μ • (1 : E →L[ℝ] E)).IsPositive)
    (hx0 : ‖x0 - xStar‖ ≤ localQuadraticNewtonRadius μ M) :
    let traj :=
      localQuadraticNewtonOrbit hμ hf hgrad hHstar hx0
    (∀ k, ‖traj k - xStar‖ ≤ localQuadraticNewtonRadius μ M) ∧
      (∀ k, (fderiv ℝ (∇ f) (traj k)).det ≠ 0) ∧
      ∀ k,
        ‖traj (k + 1) - xStar‖ ≤
          ((M : ℝ) * ‖traj k - xStar‖ ^ (2 : ℕ)) /
            (2 * (μ - (M : ℝ) * ‖traj k - xStar‖)) := by
  let traj := localQuadraticNewtonOrbit hμ hf hgrad hHstar hx0
  refine ⟨?_, ?_, ?_⟩
  · intro k
    -- The recursive state orbit already stores the closed-ball invariant at every iterate.
    simpa [traj] using localQuadraticNewtonOrbit_mem_ball hμ hf hgrad hHstar hx0 k
  · intro k
    -- Apply the local Hessian nondegeneracy theorem to the `k`th orbit point.
    simpa [traj, hessian] using
      hessian_det_ne_zero_of_mem_localQuadraticNewtonBall
        (μ := μ) (M := M) (f := f) (xStar := xStar) hμ hf hHstar
        ((localQuadraticNewtonStateOrbit hμ hf hgrad hHstar hx0 k).property)
  · intro k
    have hstep :=
      newtonOptimization_step_mem_ball_and_quadratic_error_bound
        (μ := μ) (M := M) (f := f) (xStar := xStar) hμ hf hgrad hHstar
        ((localQuadraticNewtonStateOrbit hμ hf hgrad hHstar hx0 k).property)
    have hsucc :
        traj (k + 1) =
          NewtonSystem.step (∇ f)
            (localQuadraticNewtonPoint hμ hf hHstar
              (localQuadraticNewtonStateOrbit hμ hf hgrad hHstar hx0 k).property) := by
      simpa [traj, localQuadraticNewtonOrbit, localQuadraticNewtonMethod] using
        localQuadraticNewtonMethod_step_eq hμ hf hgrad hHstar hx0 k
    have hsucc' :
        NewtonSystem.step (∇ f)
            (localQuadraticNewtonPoint hμ hf hHstar
              (localQuadraticNewtonStateOrbit hμ hf hgrad hHstar hx0 k).property) =
          traj (k + 1) := by
      simpa using hsucc.symm
    -- Specialize the one-step estimate at the `k`th orbit point and rewrite the successor iterate.
    simpa [traj, localQuadraticNewtonOrbit, localQuadraticNewtonMethod, hsucc'] using hstep.2

end

end
