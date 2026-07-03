import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_1_6_10 (from Chap01) -/
noncomputable section

universe u

variable {α : Type u} {f : α → ℝ} {x0 : α} {gStar : ℕ → ℝ} {L ω fStar : ℝ}

/- Primary domain: square-root complexity bounds for real optimization-error quantities.

Source/core/bridge triage for Proposition 1.6.10:
* source-facing: the textbook stopping criterion for `g_N^*`
* core/canonical: `sqrt_rate_complexity_bound` from `Definition_1_2_5.lean`
* bridge/view: the concrete constant `Real.sqrt ((L * (f x0 - fStar)) / ω)` together with the
  shifted sequence view `k ↦ gStar (k - 1)`

Relevant owner-style declarations sampled before refining:
* `sqrt_rate_complexity_bound` in `Definition_1_2_5.lean`
* `HasConvergenceRateOfOrder` in `Definition_1_6_9.lean`
* `HasGeometricRateOfConvergence.complexity_bound` in `Definition_1_2_6.lean`
* `minGradientNormAlongIterates_le_sqrt` in `Theorem_1_6_8.lean`

Primitive data:
* the sequence `gStar`
* the concrete square-root constant `Real.sqrt ((L * (f x0 - fStar)) / ω)`
* the pointwise estimate at index `N`

Derived API:
* the source-facing `ε`-complexity conclusion, obtained by applying the owner theorem at the
  shifted index `N + 1` -/

/-- Proposition 1.6.10: if the textbook rate estimate
`g_N^* ≤ [ω⁻¹ L (f(x₀) - f^*)]^{1/2} / (N + 1)^{1/2}` holds and
`N + 1 ≥ L (f(x₀) - f^*) / (ω ε^2)`, then `g_N^* ≤ ε`. -/
-- Proof sketch: apply the assumed rate bound at the chosen index `N`, then use the lower bound on
-- `N + 1`; if `ω = 0` then the rate estimate already gives `g_N^* ≤ 0`, while in the `ω ≠ 0`
-- branch the threshold rewrites to the owner theorem's canonical `(c / ε)^2` form.
theorem le_of_complexity_bound_from_rate_estimate
    (hRate :
      ∀ N : ℕ,
        gStar N ≤
          Real.sqrt ((L * (f x0 - fStar)) / ω) / Real.sqrt ((N : ℝ) + 1))
    {N : ℕ} {ε : ℝ}
    (hε : 0 < ε)
    (hN : (L * (f x0 - fStar)) / (ω * ε ^ (2 : ℕ)) ≤ (N : ℝ) + 1) :
    gStar N ≤ ε := by
  let c : ℝ := Real.sqrt ((L * (f x0 - fStar)) / ω)
  let a : ℝ := (L * (f x0 - fStar)) / ω
  have hε_ne : ε ≠ 0 := ne_of_gt hε
  have hbound : ∀ ⦃k : ℕ⦄, 0 < k → gStar (k - 1) ≤ c / Real.sqrt (k : ℝ) := by
    intro k hk
    have hk' : (((k - 1 : ℕ) : ℝ) + 1) = k := by
      exact_mod_cast Nat.succ_pred_eq_of_pos hk
    simpa [c, hk'] using hRate (k - 1)
  have hcomplexity : (c / ε) ^ (2 : ℕ) ≤ ((N + 1 : ℕ) : ℝ) := by
    by_cases hω : ω = 0
    · have hc : c = 0 := by
        simp [c, hω]
      calc
        (c / ε) ^ (2 : ℕ) = 0 := by simp [hc]
        _ ≤ ((N + 1 : ℕ) : ℝ) := by positivity
    · have hN' : a / ε ^ (2 : ℕ) ≤ (N : ℝ) + 1 := by
        change ((L * (f x0 - fStar)) / ω) / ε ^ (2 : ℕ) ≤ (N : ℝ) + 1
        calc
          ((L * (f x0 - fStar)) / ω) / ε ^ (2 : ℕ) =
              (L * (f x0 - fStar)) / (ω * ε ^ (2 : ℕ)) := by
            field_simp [hω, hε_ne]
          _ ≤ (N : ℝ) + 1 := hN
      by_cases hrad : 0 ≤ a
      · have hsq : c ^ (2 : ℕ) = a := by
          simpa [a, c, pow_two] using Real.sq_sqrt hrad
        calc
          (c / ε) ^ (2 : ℕ) = c ^ (2 : ℕ) / ε ^ (2 : ℕ) := by
            field_simp [hε_ne]
          _ = a / ε ^ (2 : ℕ) := by rw [hsq]
          _ ≤ (N : ℝ) + 1 := hN'
          _ = ((N + 1 : ℕ) : ℝ) := by norm_num
      · have hc : c = 0 := by
          simpa [a, c] using Real.sqrt_eq_zero_of_nonpos (le_of_lt <| lt_of_not_ge hrad)
        calc
          (c / ε) ^ (2 : ℕ) = 0 := by simp [hc]
          _ ≤ ((N + 1 : ℕ) : ℝ) := by positivity
  simpa using sqrt_rate_complexity_bound hbound hε (Nat.succ_pos N) hcomplexity

end

/-! ### Example_1_6_11 (from Chap01) -/
open Filter
open scoped Gradient

noncomputable section

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "initialPoint" => EuclideanSpace.single 0 (1 : ℝ)

/- Primary domain:
* gradient-method dynamics for a concrete polynomial objective on `ℝ²`

Source/core/bridge triage:
* source-facing: the quartic objective and the convergence-to-a-saddle example
* core/canonical owners: `gradientMethod stepSize f x0`, `HasGradientAt f 0 xStar`, and
  `IsLocalMin f xStar`
* bridge/view: the later coordinate formulas for `∇ saddlePointConvergenceObjective` and its
  Hessian in `Proposition_1_6_12`

Relevant owner-style declarations sampled before refining:
* `gradientMethod` in `Algorithm_1_6_1.lean`
* `HasGradientAt f (0 : E) xBar` in `Definition_1_4_15.lean`
* `isLocalMin_hasGradientAt_zero_of_differentiableAt` in `Theorem_1_4_13.lean`
* `IsLocalMin` from mathlib

Primitive data:
* the quartic objective `saddlePointConvergenceObjective`

Derived API:
* the canonical start point and limit point of the example trajectory
* the stationary/local-minimum analysis, which is derived from the owner abstractions and
  developed later in `Proposition_1_6_12`

Example 1.6.11 itself therefore keeps only the source-facing quartic objective and the final
convergence statement, rather than a parallel local helper API for differentiability, stationarity,
and local minimality. -/

/-- The quartic example objective
`f(x₁, x₂) = (1 / 2) x₁² + (1 / 4) x₂⁴ - (1 / 2) x₂²`. -/
def saddlePointConvergenceObjective (x : E) : ℝ :=
  (1 / 2 : ℝ) * x 0 ^ 2 + (1 / 4 : ℝ) * x 1 ^ 4 - (1 / 2 : ℝ) * x 1 ^ 2

/-- Helper for Example 1.6.11: the quartic objective has gradient
`(x₁, x₂^3 - x₂)`. -/
private lemma saddlePointConvergenceObjective_hasGradientAt (x : E) :
    HasGradientAt saddlePointConvergenceObjective
      (EuclideanSpace.single 0 (x 0) + EuclideanSpace.single 1 (x 1 ^ 3 - x 1)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  change
    HasFDerivAt
      (fun y : E ↦
        (1 / 2 : ℝ) * y 0 ^ 2 + (1 / 4 : ℝ) * y 1 ^ 4 - (1 / 2 : ℝ) * y 1 ^ 2)
      ((InnerProductSpace.toDual ℝ E)
        (EuclideanSpace.single 0 (x 0) + EuclideanSpace.single 1 (x 1 ^ 3 - x 1)))
      x
  let proj0 : E →L[ℝ] ℝ := (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 : E →L[ℝ] ℝ)
  let proj1 : E →L[ℝ] ℝ := (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1 : E →L[ℝ] ℝ)
  have h0 : HasFDerivAt (fun y : E ↦ y 0) proj0 x := by
    simpa [proj0] using (PiLp.hasFDerivAt_apply 2 x 0)
  have h1 : HasFDerivAt (fun y : E ↦ y 1) proj1 x := by
    simpa [proj1] using (PiLp.hasFDerivAt_apply 2 x 1)
  -- Differentiate the coordinate monomials and scale them by the objective coefficients.
  have hsq0 :
      HasFDerivAt (fun y : E ↦ y 0 ^ 2) (((2 : ℝ) * x 0) • proj0) x := by
    simpa [two_nsmul, pow_succ, mul_comm, mul_left_comm, mul_assoc] using (h0.pow 2)
  have hpow4 :
      HasFDerivAt (fun y : E ↦ y 1 ^ 4) (((4 : ℝ) * x 1 ^ 3) • proj1) x := by
    simpa [pow_succ, pow_succ', mul_comm, mul_left_comm, mul_assoc] using (h1.pow 4)
  have hsq1 :
      HasFDerivAt (fun y : E ↦ y 1 ^ 2) (((2 : ℝ) * x 1) • proj1) x := by
    simpa [two_nsmul, pow_succ, mul_comm, mul_left_comm, mul_assoc] using (h1.pow 2)
  have hmain :
      HasFDerivAt
        (fun y : E ↦
          (1 / 2 : ℝ) * y 0 ^ 2 + (1 / 4 : ℝ) * y 1 ^ 4 - (1 / 2 : ℝ) * y 1 ^ 2)
        ((x 0) • proj0 + (x 1 ^ 3 - x 1) • proj1) x := by
    -- Assemble the Fréchet derivative from the three scalar polynomial pieces.
    simpa [sub_eq_add_neg, proj0, proj1, smul_add, add_smul, mul_smul, mul_assoc, mul_comm,
      mul_left_comm, add_comm, add_left_comm, add_assoc] using
      (hsq0.const_smul (1 / 2 : ℝ)).add
        ((hpow4.const_smul (1 / 4 : ℝ)).sub (hsq1.const_smul (1 / 2 : ℝ)))
  have hdual :
      (x 0) • proj0 + (x 1 ^ 3 - x 1) • proj1 =
        (InnerProductSpace.toDual ℝ E)
          (EuclideanSpace.single 0 (x 0) + EuclideanSpace.single 1 (x 1 ^ 3 - x 1)) := by
    -- The coordinate linear form is exactly the inner-product pairing with the gradient vector.
    ext y
    have hinner0 : inner ℝ (EuclideanSpace.single 0 (x 0)) y = (x 0) * y 0 := by
      simpa using (EuclideanSpace.inner_single_left 0 (x 0) y)
    have hinner1 :
        inner ℝ (EuclideanSpace.single 1 (x 1 ^ 3 - x 1)) y = (x 1 ^ 3 - x 1) * y 1 := by
      simpa using (EuclideanSpace.inner_single_left 1 (x 1 ^ 3 - x 1) y)
    rw [InnerProductSpace.toDual_apply_apply, inner_add_left, hinner0, hinner1]
    simp [proj0, proj1]
  exact hmain.congr_fderiv hdual

/-- Helper for Example 1.6.11: with unit steps, every iterate after the first one is the
origin. -/
private lemma unitStepGradientMethod_eq_origin_succ (k : ℕ) :
    gradientMethod (fun _ : ℕ ↦ (1 : ℝ))
      saddlePointConvergenceObjective initialPoint (k + 1) = (0 : E) := by
  induction k with
  | zero =>
      -- The first unit step subtracts the gradient `(1, 0)` from the start point `(1, 0)`.
      rw [gradientMethod_succ, gradientMethod_zero]
      have hgrad :
          ∇ saddlePointConvergenceObjective initialPoint = initialPoint := by
        have hgrad_raw :=
          (saddlePointConvergenceObjective_hasGradientAt initialPoint).gradient
        have hcoord0 :
            (∇ saddlePointConvergenceObjective initialPoint) (0 : Fin 2) = 1 := by
          simpa using congrArg (fun v : E ↦ v (0 : Fin 2)) hgrad_raw
        have hcoord1 :
            (∇ saddlePointConvergenceObjective initialPoint) (1 : Fin 2) = 0 := by
          simpa using congrArg (fun v : E ↦ v (1 : Fin 2)) hgrad_raw
        ext i
        fin_cases i <;> simp [hcoord0, hcoord1]
      rw [hgrad]
      ext i
      fin_cases i <;> simp
  | succ k hk =>
      -- Once the trajectory reaches the origin, the vanishing gradient keeps it there.
      rw [gradientMethod_succ, hk]
      have hgrad0 : ∇ saddlePointConvergenceObjective (0 : E) = 0 := by
        have hgrad_raw :=
          (saddlePointConvergenceObjective_hasGradientAt (0 : E)).gradient
        have hcoord0 :
            (∇ saddlePointConvergenceObjective (0 : E)) (0 : Fin 2) = 0 := by
          simpa using congrArg (fun v : E ↦ v (0 : Fin 2)) hgrad_raw
        have hcoord1 :
            (∇ saddlePointConvergenceObjective (0 : E)) (1 : Fin 2) = 0 := by
          simpa using congrArg (fun v : E ↦ v (1 : Fin 2)) hgrad_raw
        ext i
        fin_cases i <;> simp [hcoord0, hcoord1]
      simp [hgrad0]

/-- Helper for Example 1.6.11: along the vertical axis, the quartic objective becomes the scalar
polynomial `(1 / 4) t^4 - (1 / 2) t^2`. -/
private lemma saddlePointConvergenceObjective_axis_slice_eq (t : ℝ) :
    saddlePointConvergenceObjective (EuclideanSpace.single 1 t) =
      (1 / 4 : ℝ) * t ^ 4 - (1 / 2 : ℝ) * t ^ 2 := by
  -- Restricting to `(0, t)` kills the first-coordinate term.
  simp [saddlePointConvergenceObjective]

/-- Helper for Example 1.6.11: the vertical-axis slice is strictly below the origin value for
small positive `t`. -/
private lemma saddlePointConvergenceObjective_axis_slice_neg_of_pos_lt_one
    {t : ℝ} (hpos : 0 < t) (hone : t < 1) :
    saddlePointConvergenceObjective (EuclideanSpace.single 1 t) <
      saddlePointConvergenceObjective (0 : E) := by
  have ht_sq_pos : 0 < t ^ 2 := by
    positivity
  have ht_sq_lt_one : t ^ 2 < 1 := by
    nlinarith
  -- The scalar slice equals `t^2 ((1/4) t^2 - 1/2)`, which is negative when `0 < t < 1`.
  simp [saddlePointConvergenceObjective]
  nlinarith [ht_sq_pos, ht_sq_lt_one]

-- Proof sketch: along the trajectory started at `(1, 0)` with unit step size, the second
-- coordinate stays equal to `0` because the second gradient component is `x₂^3 - x₂`, while the
-- first coordinate is sent from `1` to `0` in one step and then remains there. This makes the
-- iterate sequence eventually constant at `(0, 0)`.
/-- Example 1.6.11 (1): for
`f(x₁, x₂) = (1 / 2) x₁² + (1 / 4) x₂⁴ - (1 / 2) x₂²`, the unit-step gradient method started at
`(1, 0)` converges to `(0, 0)`. -/
theorem saddlePointConvergenceObjective_unitStepGradientMethod_tendsto_origin :
    Tendsto
      (gradientMethod (fun _ : ℕ ↦ (1 : ℝ))
        saddlePointConvergenceObjective initialPoint)
      atTop (nhds (0 : E)) := by
  -- The trajectory is eventually constant because every iterate with index at least `1` is `0`.
  refine tendsto_atTop_of_eventually_const (i₀ := 1) ?_
  intro n hn
  rcases Nat.exists_eq_add_of_le hn with ⟨k, rfl⟩
  simpa [Nat.add_comm] using unitStepGradientMethod_eq_origin_succ k

-- Proof sketch: the polynomial objective has gradient `(x₁, x₂^3 - x₂)`, which vanishes at
-- `(0, 0)`.
/-- Example 1.6.11 (2): the limit point `(0, 0)` is a stationary point of
`saddlePointConvergenceObjective`. -/
theorem saddlePointConvergenceObjective_origin_is_stationary :
    HasGradientAt saddlePointConvergenceObjective 0 (0 : E) := by
  -- Evaluate the explicit gradient formula at the origin.
  convert saddlePointConvergenceObjective_hasGradientAt (0 : E) using 1
  ext i
  fin_cases i <;> simp

-- Proof sketch: compare the values of `saddlePointConvergenceObjective` along the line `(0, t)`
-- for small nonzero `t`, where the objective becomes negative.
/-- Example 1.6.11 (3): the stationary point `(0, 0)` is not a local minimum of
`saddlePointConvergenceObjective`. -/
theorem saddlePointConvergenceObjective_origin_is_not_localMin :
    ¬ IsLocalMin saddlePointConvergenceObjective (0 : E) := by
  intro hmin
  let g : ℝ → E := fun t ↦ t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
  have hmin' : IsLocalMin saddlePointConvergenceObjective (g 0) := by
    simpa [g] using hmin
  have hcont : ContinuousAt g 0 := by
    -- The vertical-axis parameterization is an affine continuous map.
    simpa [g] using
      ((continuous_id.smul continuous_const).continuousAt :
        ContinuousAt (fun t : ℝ ↦ t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) 0)
  have hg :
      ∀ t : ℝ, g t = EuclideanSpace.single (1 : Fin 2) t := by
    intro t
    ext i
    fin_cases i <;> simp [g]
  have hcomp :
      (saddlePointConvergenceObjective ∘ g) =
        fun t : ℝ ↦ saddlePointConvergenceObjective (EuclideanSpace.single (1 : Fin 2) t) := by
    funext t
    simp [Function.comp, hg t]
  have hslice :
      IsLocalMin
        (fun t : ℝ ↦ saddlePointConvergenceObjective (EuclideanSpace.single (1 : Fin 2) t))
        0 := by
    -- Any local minimum at the origin would restrict to a local minimum on the vertical axis.
    simpa [hcomp] using hmin'.comp_continuous hcont
  have hset :
      {t : ℝ |
          saddlePointConvergenceObjective (EuclideanSpace.single (1 : Fin 2) 0) ≤
            saddlePointConvergenceObjective (EuclideanSpace.single (1 : Fin 2) t)} ∈
        nhds (0 : ℝ) := by
    simpa [IsLocalMin, IsMinFilter] using hslice
  rcases Metric.mem_nhds_iff.mp hset with ⟨ε, hε, hεmem⟩
  let t : ℝ := min (ε / 2) (1 / 2)
  have ht_pos : 0 < t := by
    dsimp [t]
    have hε_half : 0 < ε / 2 := by
      positivity
    positivity
  have ht_lt_one : t < 1 := by
    have hhalf : (1 / 2 : ℝ) < 1 := by
      norm_num
    dsimp [t]
    exact (min_lt_iff.mpr (Or.inr hhalf))
  have ht_mem : t ∈ Metric.ball (0 : ℝ) ε := by
    have ht_lt_eps : t < ε := by
      dsimp [t]
      calc
        min (ε / 2) (1 / 2) ≤ ε / 2 := min_le_left _ _
        _ < ε := by
          nlinarith
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos ht_pos] using ht_lt_eps
  have hlocal :
      saddlePointConvergenceObjective (EuclideanSpace.single (1 : Fin 2) 0) ≤
        saddlePointConvergenceObjective (EuclideanSpace.single (1 : Fin 2) t) :=
    hεmem ht_mem
  have hstrict :
      saddlePointConvergenceObjective (EuclideanSpace.single (1 : Fin 2) t) <
        saddlePointConvergenceObjective (0 : E) :=
    saddlePointConvergenceObjective_axis_slice_neg_of_pos_lt_one ht_pos ht_lt_one
  -- The local-minimum inequality contradicts the explicit nearby point with strictly smaller value.
  simpa using (not_lt_of_ge hlocal) hstrict

-- Proof sketch: combine the three atomic clauses of Example 1.6.11.
/-- The unit-step quartic-example trajectory converges to a stationary point that is not a local
minimum. -/
theorem unitStepGradientMethod_converges_to_nonminimizing_stationary_point :
    Tendsto
      (gradientMethod (fun _ : ℕ ↦ (1 : ℝ))
        saddlePointConvergenceObjective initialPoint)
      atTop (nhds (0 : E)) ∧
      HasGradientAt saddlePointConvergenceObjective 0 (0 : E) ∧
      ¬ IsLocalMin saddlePointConvergenceObjective (0 : E) := by
  -- Combine the three source-facing clauses of Example 1.6.11.
  exact ⟨saddlePointConvergenceObjective_unitStepGradientMethod_tendsto_origin,
    saddlePointConvergenceObjective_origin_is_stationary,
    saddlePointConvergenceObjective_origin_is_not_localMin⟩

end

/-! ### Proposition_1_6_12 (from Chap01) -/
open Filter
open EuclideanSpace
open scoped Gradient

noncomputable section

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "leftPoint" => single 1 (-1 : ℝ)
local notation "rightPoint" => single 1 (1 : ℝ)
local notation "initialPoint" => single 0 (1 : ℝ)

/- Primary domain:
* gradient-method dynamics and second-order stationary-point analysis for a concrete polynomial
  objective on `ℝ²`

Sampled owner-style declarations:
* `gradientMethod` in `Algorithm_1_6_1.lean`
* `∇²` / `hessianMatrix` in `Definition_1_4_16.lean`
* `strict_local_minimizer_of_gradient_zero_of_hessian_posDef` in `Theorem_1_4_21.lean`
* `unitStepGradientMethod_converges_to_nonminimizing_stationary_point` in
  `Example_1_6_11.lean`

Source/core/bridge triage:
* source-facing: the explicit quartic formulas, stationary-point classification, the universal
  axis-invariance claim, and the corrected unit-step convergence to a nonminimizing stationary
  point
* core/canonical: `gradientMethod stepSize f x0`, `∇² f x`, `HasGradientAt f 0 xStar`,
  and `IsLocalMin f xStar`
* bridge/view: the coordinate formulas on `EuclideanSpace ℝ (Fin 2)` and the specializations of
  the second-order sufficient condition to `leftPoint` and `rightPoint`

Owner abstraction:
* the quartic objective `saddlePointConvergenceObjective` from `Example_1_6_11`, together with the
  canonical gradient-method and second-order owner API

Primitive data:
* the quartic objective `saddlePointConvergenceObjective`
* the canonical comparison points `0`, `single 1 (-1)`, and `single 1 1`

Derived API:
* the explicit gradient and Hessian matrix formulas
* the stationary-point description
* the left/right isolated-minimum statements, as source-facing specializations of
  `strict_local_minimizer_of_gradient_zero_of_hessian_posDef`
* the universal axis-invariance statement for trajectories started at `(1, 0)`
* the proposition-level unit-step convergence/nonminimality conclusion, reused directly from the
  owner theorem

This file therefore keeps the source-facing quartic companions and the universal trajectory
invariance claim, while the corrected constant-step convergence conclusion is reused from the
existing owner theorem rather than duplicated as a parallel local theorem. -/

/-- Helper for Proposition 1.6.12: the quartic objective has the explicit gradient witness
`(x₁, x₂^3 - x₂)`. -/
private lemma saddlePointConvergenceObjective_hasGradientAt (x : E) :
    HasGradientAt saddlePointConvergenceObjective
      (single 0 (x 0) + single 1 (x 1 ^ 3 - x 1)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  change
    HasFDerivAt
      (fun y : E ↦
        (1 / 2 : ℝ) * y 0 ^ 2 + (1 / 4 : ℝ) * y 1 ^ 4 - (1 / 2 : ℝ) * y 1 ^ 2)
      ((InnerProductSpace.toDual ℝ E)
        (single 0 (x 0) + single 1 (x 1 ^ 3 - x 1)))
      x
  let proj0 : E →L[ℝ] ℝ := (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 : E →L[ℝ] ℝ)
  let proj1 : E →L[ℝ] ℝ := (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1 : E →L[ℝ] ℝ)
  have h0 : HasFDerivAt (fun y : E ↦ y 0) proj0 x := by
    simpa [proj0] using (PiLp.hasFDerivAt_apply 2 x 0)
  have h1 : HasFDerivAt (fun y : E ↦ y 1) proj1 x := by
    simpa [proj1] using (PiLp.hasFDerivAt_apply 2 x 1)
  -- Differentiate the three scalar polynomial pieces coordinatewise.
  have hsq0 :
      HasFDerivAt (fun y : E ↦ y 0 ^ 2) (((2 : ℝ) * x 0) • proj0) x := by
    simpa [two_nsmul, pow_succ, mul_comm, mul_left_comm, mul_assoc] using (h0.pow 2)
  have hpow4 :
      HasFDerivAt (fun y : E ↦ y 1 ^ 4) (((4 : ℝ) * x 1 ^ 3) • proj1) x := by
    simpa [pow_succ, pow_succ', mul_comm, mul_left_comm, mul_assoc] using (h1.pow 4)
  have hsq1 :
      HasFDerivAt (fun y : E ↦ y 1 ^ 2) (((2 : ℝ) * x 1) • proj1) x := by
    simpa [two_nsmul, pow_succ, mul_comm, mul_left_comm, mul_assoc] using (h1.pow 2)
  have hmain :
      HasFDerivAt
        (fun y : E ↦
          (1 / 2 : ℝ) * y 0 ^ 2 + (1 / 4 : ℝ) * y 1 ^ 4 - (1 / 2 : ℝ) * y 1 ^ 2)
        ((x 0) • proj0 + (x 1 ^ 3 - x 1) • proj1) x := by
    -- Assemble the derivative from the quadratic and quartic coordinate terms.
    simpa [sub_eq_add_neg, proj0, proj1, smul_add, add_smul, mul_smul, mul_assoc, mul_comm,
      mul_left_comm, add_comm, add_left_comm, add_assoc] using
      (hsq0.const_smul (1 / 2 : ℝ)).add
        ((hpow4.const_smul (1 / 4 : ℝ)).sub (hsq1.const_smul (1 / 2 : ℝ)))
  have hdual :
      (x 0) • proj0 + (x 1 ^ 3 - x 1) • proj1 =
        (InnerProductSpace.toDual ℝ E)
          (single 0 (x 0) + single 1 (x 1 ^ 3 - x 1)) := by
    -- The coordinate linear form is the inner-product dual of the explicit gradient vector.
    ext y
    have hinner0 : inner ℝ (single 0 (x 0)) y = (x 0) * y 0 := by
      simpa using (EuclideanSpace.inner_single_left 0 (x 0) y)
    have hinner1 :
        inner ℝ (single 1 (x 1 ^ 3 - x 1)) y = (x 1 ^ 3 - x 1) * y 1 := by
      simpa using (EuclideanSpace.inner_single_left 1 (x 1 ^ 3 - x 1) y)
    rw [InnerProductSpace.toDual_apply_apply, inner_add_left, hinner0, hinner1]
    simp [proj0, proj1]
  exact hmain.congr_fderiv hdual

/-- Helper for Proposition 1.6.12: the explicit quartic gradient map has derivative given by the
diagonal matrix `diag(1, 3 x₂² - 1)`. -/
private lemma explicitQuarticGradient_hasFDerivAt (x : E) :
    HasFDerivAt
      (fun y : E ↦ single 0 (y 0) + single 1 (y 1 ^ 3 - y 1))
      (LinearMap.toContinuousLinearMap
        ((!![1, 0; 0, 3 * x 1 ^ 2 - 1] : Matrix (Fin 2) (Fin 2) ℝ).toEuclideanLin))
      x := by
  let proj0 : E →L[ℝ] ℝ := (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0 : E →L[ℝ] ℝ)
  let proj1 : E →L[ℝ] ℝ := (PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1 : E →L[ℝ] ℝ)
  have h0 : HasFDerivAt (fun y : E ↦ y 0) proj0 x := by
    simpa [proj0] using (PiLp.hasFDerivAt_apply 2 x 0)
  have h1 : HasFDerivAt (fun y : E ↦ y 1) proj1 x := by
    simpa [proj1] using (PiLp.hasFDerivAt_apply 2 x 1)
  -- The second coordinate differentiates to `3 x₂² - 1`.
  have hcube :
      HasFDerivAt (fun y : E ↦ y 1 ^ 3) (((3 : ℝ) * x 1 ^ 2) • proj1) x := by
    simpa [pow_succ, pow_succ', mul_comm, mul_left_comm, mul_assoc] using (h1.pow 3)
  have hcoord1 :
      HasFDerivAt (fun y : E ↦ y 1 ^ 3 - y 1) (((3 : ℝ) * x 1 ^ 2 - 1) • proj1) x := by
    simpa [sub_eq_add_neg, proj1, smul_add, add_smul, mul_smul, mul_assoc, mul_comm,
      mul_left_comm, add_comm, add_left_comm, add_assoc] using hcube.sub h1
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp]
  intro i
  fin_cases i
  · change HasFDerivWithinAt
        (fun y : E ↦ (single 0 (y 0) + single 1 (y 1 ^ 3 - y 1)).ofLp 0)
        ((PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 0).comp
          (LinearMap.toContinuousLinearMap
            ((!![1, 0; 0, 3 * x 1 ^ 2 - 1] : Matrix (Fin 2) (Fin 2) ℝ).toEuclideanLin)))
        Set.univ x
    have hfun0 :
        (fun y : E ↦ (single 0 (y 0) + single 1 (y 1 ^ 3 - y 1)).ofLp 0) =
          fun y : E ↦ y 0 := by
      funext y
      simp
    rw [hfun0]
    have hcomp0 :
        proj0.comp
          (LinearMap.toContinuousLinearMap
            ((!![1, 0; 0, 3 * x 1 ^ 2 - 1] : Matrix (Fin 2) (Fin 2) ℝ).toEuclideanLin)) =
          proj0 := by
      ext y
      simp [proj0, Matrix.toEuclideanLin, dotProduct, Fin.sum_univ_two]
    exact (h0.hasFDerivWithinAt).congr_fderiv hcomp0.symm
  · change HasFDerivWithinAt
        (fun y : E ↦ (single 0 (y 0) + single 1 (y 1 ^ 3 - y 1)).ofLp 1)
        ((PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) 1).comp
          (LinearMap.toContinuousLinearMap
            ((!![1, 0; 0, 3 * x 1 ^ 2 - 1] : Matrix (Fin 2) (Fin 2) ℝ).toEuclideanLin)))
        Set.univ x
    have hfun1 :
        (fun y : E ↦ (single 0 (y 0) + single 1 (y 1 ^ 3 - y 1)).ofLp 1) =
          fun y : E ↦ y 1 ^ 3 - y 1 := by
      funext y
      simp
    rw [hfun1]
    have hcomp1 :
        proj1.comp
          (LinearMap.toContinuousLinearMap
            ((!![1, 0; 0, 3 * x 1 ^ 2 - 1] : Matrix (Fin 2) (Fin 2) ℝ).toEuclideanLin)) =
          ((3 : ℝ) * x 1 ^ 2 - 1) • proj1 := by
      ext y
      simp [proj1, Matrix.toEuclideanLin, dotProduct, Fin.sum_univ_two]
    exact (hcoord1.hasFDerivWithinAt).congr_fderiv hcomp1.symm

/-- Helper for Proposition 1.6.12: the gradient map has derivative given by the explicit Hessian
matrix. -/
private lemma saddlePointConvergenceObjective_gradient_hasFDerivAt (x : E) :
    HasFDerivAt (∇ saddlePointConvergenceObjective)
      (LinearMap.toContinuousLinearMap
        ((!![1, 0; 0, 3 * x 1 ^ 2 - 1] : Matrix (Fin 2) (Fin 2) ℝ).toEuclideanLin))
      x := by
  have hfun :
      (∇ saddlePointConvergenceObjective) =
        (fun y : E ↦ single 0 (y 0) + single 1 (y 1 ^ 3 - y 1)) := by
    funext y
    exact (saddlePointConvergenceObjective_hasGradientAt y).gradient
  -- Rewrite to the explicit gradient map and differentiate that polynomial map directly.
  rw [hfun]
  exact explicitQuarticGradient_hasFDerivAt x

/-- Helper for Proposition 1.6.12: stationarity forces the scalar equations
`x₁ = 0` and `x₂^3 - x₂ = 0`. -/
private lemma quartic_stationary_coordinate_eq_zero {x : E}
    (h : HasGradientAt saddlePointConvergenceObjective 0 x) :
    x 0 = 0 ∧ x 1 ^ 3 - x 1 = 0 := by
  have hgrad : ∇ saddlePointConvergenceObjective x = 0 := h.gradient
  -- Read off the two scalar equations from the explicit gradient formula.
  have hcoord0 : x 0 = 0 := by
    have hexp0 : (∇ saddlePointConvergenceObjective x) 0 = x 0 := by
      simpa using congrArg (fun v : E ↦ v 0)
        ((saddlePointConvergenceObjective_hasGradientAt x).gradient)
    have hzero0 : (∇ saddlePointConvergenceObjective x) 0 = 0 := by
      simpa using congrArg (fun v : E ↦ v 0) hgrad
    exact hexp0.symm.trans hzero0
  have hcoord1 : x 1 ^ 3 - x 1 = 0 := by
    have hexp1 : (∇ saddlePointConvergenceObjective x) 1 = x 1 ^ 3 - x 1 := by
      simpa using congrArg (fun v : E ↦ v 1)
        ((saddlePointConvergenceObjective_hasGradientAt x).gradient)
    have hzero1 : (∇ saddlePointConvergenceObjective x) 1 = 0 := by
      simpa using congrArg (fun v : E ↦ v 1) hgrad
    exact hexp1.symm.trans hzero1
  exact ⟨hcoord0, hcoord1⟩

/-- Helper for Proposition 1.6.12: the side-point Hessian matrix `diag(1, 2)` is positive
definite. -/
private lemma quartic_side_hessian_posDef :
    ((!![1, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef) := by
  -- The matrix is diagonal with strictly positive diagonal entries.
  have hdiag :
      (!![1, 0; 0, 2] : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.diagonal ![1, 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  rw [hdiag]
  exact Matrix.PosDef.diagonal (n := Fin 2) (R := ℝ) (d := ![1, 2]) (by
    intro i
    fin_cases i <;> norm_num)

-- Proof sketch: differentiate the explicit polynomial formula for
-- `saddlePointConvergenceObjective` coordinatewise; the first coordinate contributes `x₁`, and
-- the second contributes `x₂^3 - x₂`.
/-- The quartic example objective has gradient `(x₁, x₂^3 - x₂)`. -/
theorem saddlePointConvergenceObjective_gradient_eq (x : E) :
    ∇ saddlePointConvergenceObjective x =
      single 0 (x 0) + single 1 (x 1 ^ 3 - x 1) := by
  -- The explicit gradient witness from the helper is the canonical gradient.
  exact (saddlePointConvergenceObjective_hasGradientAt x).gradient

-- Proof sketch: differentiate the explicit gradient formula
-- `x ↦ (x 0, x 1 ^ 3 - x 1)` once more; this yields the diagonal matrix with entries
-- `1` and `3 x₂² - 1`.
/-- The Hessian of the quartic example objective is the diagonal matrix
`diag(1, 3 x₂² - 1)`. -/
theorem saddlePointConvergenceObjective_hessian_eq (x : E) :
    ∇² saddlePointConvergenceObjective x =
      !![1, 0; 0, 3 * x 1 ^ 2 - 1] := by
  apply Matrix.toEuclideanLin.injective
  have hgrad :
      fderiv ℝ (∇ saddlePointConvergenceObjective) x =
        LinearMap.toContinuousLinearMap
          ((!![1, 0; 0, 3 * x 1 ^ 2 - 1] : Matrix (Fin 2) (Fin 2) ℝ).toEuclideanLin) := by
    exact (saddlePointConvergenceObjective_gradient_hasFDerivAt x).fderiv
  -- Compare the Hessian operator with the derivative of the explicit gradient map.
  calc
    (∇² saddlePointConvergenceObjective x).toEuclideanLin =
        hessian saddlePointConvergenceObjective x := by
      simpa using hessianMatrix_toEuclideanLin saddlePointConvergenceObjective x
    _ = ((!![1, 0; 0, 3 * x 1 ^ 2 - 1] : Matrix (Fin 2) (Fin 2) ℝ).toEuclideanLin) := by
      simpa [hessian] using congrArg ContinuousLinearMap.toLinearMap hgrad

-- Proof sketch: the quartic polynomial is differentiable everywhere, so the owner stationary
-- condition `HasGradientAt saddlePointConvergenceObjective 0 x` is equivalent to
-- `∇ saddlePointConvergenceObjective x = 0`. Combine this with
-- `saddlePointConvergenceObjective_gradient_eq`, solve
-- `x₁ = 0` and `x₂^3 - x₂ = x₂ (x₂^2 - 1) = 0`, and identify the resulting three points with the
-- canonical points `0`, `single 1 (-1)`, and `single 1 1`.
/-- The stationary points of the quartic example objective are exactly `(0, 0)`, `(0, -1)`, and
`(0, 1)`. -/
theorem saddlePointConvergenceObjective_stationary_iff (x : E) :
    HasGradientAt saddlePointConvergenceObjective 0 x ↔
      x = 0 ∨ x = leftPoint ∨ x = rightPoint := by
  constructor
  · intro h
    obtain ⟨hx0, hx1⟩ := quartic_stationary_coordinate_eq_zero h
    have hfactor : x 1 * (x 1 ^ 2 - 1) = 0 := by
      nlinarith [hx1]
    rcases mul_eq_zero.mp hfactor with hx1zero | hsq
    · -- The vanishing second coordinate identifies the origin.
      left
      ext i
      fin_cases i <;> simp [hx0, hx1zero]
    · have hsquare : x 1 ^ 2 = 1 := by
        linarith
      have hsign : x 1 = 1 ∨ x 1 = -1 := by
        have hsquare' : x 1 ^ 2 = (1 : ℝ) ^ 2 := by
          simpa using hsquare
        simpa using (sq_eq_sq_iff_eq_or_eq_neg.mp hsquare')
      rcases hsign with hx1one | hx1neg
      · right
        right
        ext i
        fin_cases i <;> simp [hx0, hx1one]
      · right
        left
        ext i
        fin_cases i <;> simp [hx0, hx1neg]
  · intro hx
    rcases hx with rfl | rfl | rfl
    · -- The explicit gradient formula vanishes at the origin.
      convert saddlePointConvergenceObjective_hasGradientAt (0 : E) using 1
      ext i
      fin_cases i <;> simp
    · -- The explicit gradient formula vanishes at `(0, -1)`.
      convert saddlePointConvergenceObjective_hasGradientAt leftPoint using 1
      ext i
      fin_cases i <;> norm_num
    · -- The explicit gradient formula vanishes at `(0, 1)`.
      convert saddlePointConvergenceObjective_hasGradientAt rightPoint using 1
      ext i
      fin_cases i <;> norm_num

-- Proof sketch: evaluate the Hessian matrix at `(0, -1)` to obtain `diag(1, 2)`, verify positive
-- definiteness, and apply
-- `strict_local_minimizer_of_gradient_zero_of_hessian_posDef`, whose conclusion already has the
-- metric-radius shape below.
/-- The point `(0, -1)` is an isolated local minimum of the quartic example objective. -/
theorem leftPoint_isolatedLocalMin :
    ∃ ε > 0, ∀ ⦃y : E⦄,
      y ≠ leftPoint →
        dist y leftPoint < ε →
          saddlePointConvergenceObjective leftPoint <
            saddlePointConvergenceObjective y := by
  have hstationary : HasGradientAt saddlePointConvergenceObjective 0 leftPoint := by
    exact (saddlePointConvergenceObjective_stationary_iff leftPoint).mpr (Or.inr (Or.inl rfl))
  have hgradDiff : DifferentiableAt ℝ (∇ saddlePointConvergenceObjective) leftPoint := by
    exact (saddlePointConvergenceObjective_gradient_hasFDerivAt leftPoint).differentiableAt
  have hH : (∇² saddlePointConvergenceObjective leftPoint).PosDef := by
    -- The Hessian at the left side point is exactly `diag(1, 2)`.
    have hhess : ∇² saddlePointConvergenceObjective leftPoint = !![1, 0; 0, 2] := by
      rw [saddlePointConvergenceObjective_hessian_eq]
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num
    rw [hhess]
    exact quartic_side_hessian_posDef
  simpa using
    strict_local_minimizer_of_gradient_zero_of_hessian_posDef hstationary hgradDiff hH

-- Proof sketch: evaluate the Hessian matrix at `(0, 1)` to obtain `diag(1, 2)`, verify positive
-- definiteness, and apply
-- `strict_local_minimizer_of_gradient_zero_of_hessian_posDef`, whose conclusion already has the
-- metric-radius shape below.
/-- The point `(0, 1)` is an isolated local minimum of the quartic example objective. -/
theorem rightPoint_isolatedLocalMin :
    ∃ ε > 0, ∀ ⦃y : E⦄,
      y ≠ rightPoint →
        dist y rightPoint < ε →
          saddlePointConvergenceObjective rightPoint <
            saddlePointConvergenceObjective y := by
  have hstationary : HasGradientAt saddlePointConvergenceObjective 0 rightPoint := by
    exact (saddlePointConvergenceObjective_stationary_iff rightPoint).mpr (Or.inr (Or.inr rfl))
  have hgradDiff : DifferentiableAt ℝ (∇ saddlePointConvergenceObjective) rightPoint := by
    exact (saddlePointConvergenceObjective_gradient_hasFDerivAt rightPoint).differentiableAt
  have hH : (∇² saddlePointConvergenceObjective rightPoint).PosDef := by
    -- The Hessian at the right side point is again `diag(1, 2)`.
    have hhess : ∇² saddlePointConvergenceObjective rightPoint = !![1, 0; 0, 2] := by
      rw [saddlePointConvergenceObjective_hessian_eq]
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num
    rw [hhess]
    exact quartic_side_hessian_posDef
  simpa using
    strict_local_minimizer_of_gradient_zero_of_hessian_posDef hstationary hgradDiff hH

-- Proof sketch: use the recurrence together with
-- `saddlePointConvergenceObjective_gradient_eq`. If the second coordinate of `x k` is `0`, then
-- the second coordinate of the gradient also vanishes, so the update preserves the value `0`.
-- Apply this to the owner trajectory `gradientMethod stepSize saddlePointConvergenceObjective
-- initialPoint`, whose start point and update are canonical.
/-- Proposition 1.6.12 (1): every quartic-example gradient trajectory started at `(1, 0)` stays
on the horizontal axis `x₂ = 0`. -/
theorem quarticGradientMethod_axisInvariant
    (stepSize : ℕ → ℝ) (k : ℕ) :
    (gradientMethod stepSize saddlePointConvergenceObjective
      initialPoint k) 1 = 0 := by
  induction k with
  | zero =>
      -- The prescribed initial point is `(1, 0)`.
      norm_num
  | succ k hk =>
      let xk := gradientMethod stepSize saddlePointConvergenceObjective initialPoint k
      have hgradcoord : (∇ saddlePointConvergenceObjective xk) 1 = 0 := by
        -- On the axis `x₂ = 0`, the second gradient component vanishes as well.
        have := congrArg (fun v : E ↦ v 1) (saddlePointConvergenceObjective_gradient_eq xk)
        have hexp1 : (∇ saddlePointConvergenceObjective xk) 1 = xk 1 ^ 3 - xk 1 := by
          simpa using this
        have hxk1 : xk 1 = 0 := by
          simpa [xk] using hk
        have hcoord_rhs : xk 1 ^ 3 - xk 1 = 0 := by
          simp [hxk1]
        exact hexp1.trans hcoord_rhs
      rw [gradientMethod_succ]
      -- The update subtracts a multiple of the zero second gradient component.
      change xk 1 - stepSize k * (∇ saddlePointConvergenceObjective xk) 1 = 0
      rw [hk, hgradcoord]
      ring

/- Proposition 1.6.12 has two source-facing layers in this formalization:
the universal horizontal-axis invariance of trajectories started at `(1, 0)`, and the corrected
unit-step convergence-to-a-nonminimizing-stationary-point conclusion from
`Example_1_6_11`. The latter is reused through the owner theorem
`unitStepGradientMethod_converges_to_nonminimizing_stationary_point`, so the proposition keeps
that second clause as a direct owner recall rather than a duplicate local theorem. -/
/- Proposition 1.6.12 (2): for the constant unit-step schedule, the quartic-example trajectory
started at `(1, 0)` converges to `(0, 0)`, and this limit point is stationary but not a local
minimum for `saddlePointConvergenceObjective`. -/
recall unitStepGradientMethod_converges_to_nonminimizing_stationary_point :
    Tendsto
      (gradientMethod (fun _ : ℕ ↦ (1 : ℝ))
        saddlePointConvergenceObjective initialPoint)
      atTop (nhds (0 : E)) ∧
      HasGradientAt saddlePointConvergenceObjective 0 (0 : E) ∧
      ¬ IsLocalMin saddlePointConvergenceObjective (0 : E)

end

/-! ### Proposition_1_6_13 (from Chap01) -/
noncomputable section

open HasGeometricRateOfConvergence

universe u v

variable {𝕜 : Type u} {E : Type v} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-
Primary domain:
* norm decay for linear iterations on normed spaces

Sampled owner-style declarations:
* `HasGeometricRateOfConvergence` and
  `HasGeometricRateOfConvergence.of_step_bound` in `Definition_1_2_6.lean`
* `ContinuousLinearMap.le_opNorm` in mathlib
* `constrainedMinimizationInternalGap_hasGeometricRateOfConvergence` in
  `Chap02/Proposition_2_30.lean`

Source/core/bridge triage:
* source-facing: the linear recurrence `a (k + 1) = A k (a k)` together with the operator-norm
  bound `‖A k‖ ≤ 1 - q`
* core/canonical: the owner statement `HasGeometricRateOfConvergence`
* bridge/view: the scalar one-step estimate obtained from `ContinuousLinearMap.le_opNorm`

Owner abstraction:
* `HasGeometricRateOfConvergence`; the linear-algebra hypotheses only serve to produce its
  one-step bound

Primitive data:
* the trajectory `a`
* the step maps `A`
* the recurrence `a (k + 1) = A k (a k)`
* the operator-norm bound `‖A k‖ ≤ 1 - q`

Derived API:
* the scalar inequality `‖a (k + 1)‖ ≤ (1 - q) * ‖a k‖`
* the resulting owner geometric-rate statement
* under the extra textbook hypothesis `0 < q < 1`, the corollary
  `HasGeometricRateOfConvergence.tendsto_zero`
-/

/-- Proposition 1.6.13: if `a_{k+1} = A_k a_k` and each step operator has operator norm at most
`1 - q`, then the norm sequence satisfies the owner geometric-rate statement with constant
`‖a_0‖`. The textbook positivity hypothesis `0 < q < 1` is only needed later for the convergence
corollary `HasGeometricRateOfConvergence.tendsto_zero`.

The source specializes this to `ℝⁿ`; the proof only uses the normed-space operator estimate
`ContinuousLinearMap.le_opNorm`. -/
-- Proof sketch: use the recurrence together with the submultiplicative estimate
-- `‖A_k a_k‖ ≤ ‖A_k‖ ‖a_k‖` to get `‖a (k + 1)‖ ≤ (1 - q) ‖a_k‖`. Iterating yields the
-- geometric bound recorded by `HasGeometricRateOfConvergence`.
theorem linear_iteration_contraction_estimate
    (q : ℝ) (A : ℕ → E →L[𝕜] E) (a : ℕ → E)
    (ha : ∀ k : ℕ, a (k + 1) = A k (a k))
    (hA : ∀ k : ℕ, ‖A k‖ ≤ 1 - q) :
    HasGeometricRateOfConvergence (fun k : ℕ ↦ ‖a k‖) q ‖a 0‖ := by
  have hq₁ : q ≤ 1 := by
    have hnorm_nonneg : 0 ≤ ‖A 0‖ := norm_nonneg _
    linarith [hA 0, hnorm_nonneg]
  refine of_step_bound hq₁ le_rfl ?_
  intro k
  calc
    ‖a (k + 1)‖ = ‖A k (a k)‖ := by rw [ha k]
    _ ≤ ‖A k‖ * ‖a k‖ := (A k).le_opNorm (a k)
    _ ≤ (1 - q) * ‖a k‖ := by
      exact mul_le_mul_of_nonneg_right (hA k) (norm_nonneg _)

end

/-! ### Proposition_1_6_13 (from Items/Chap01) -/
noncomputable section

open Filter HasGeometricRateOfConvergence
open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

local notation "Euclid" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Proposition 1.6.13 lies in the finite-dimensional linear-iteration / geometric-convergence
domain.

Relevant owner-style declarations sampled before refining:
* `linear_iteration_contraction_estimate` in `LecturesConvexOptimization_Nesterov_2018/Chap01/Proposition_1_6_13.lean`, the
  chapter owner theorem for norm decay of linear iterations on normed spaces;
* `Matrix.toEuclideanCLM`, the canonical bridge from a matrix to the continuous linear map used by
  that owner theorem;
* `Matrix.l2_opNorm_toEuclideanCLM`, identifying the matrix `L²` operator norm with the norm of
  that bridge;
* `HasGeometricRateOfConvergence.tendsto_zero`, the canonical convergence-to-zero consequence of
  the owner bound.

Best owner abstraction:
* the chapter owner theorem `linear_iteration_contraction_estimate`

Primitive data:
* the matrix sequence `A`
* the trajectory `a`
* the recurrence `a (k + 1) = (A k).toEuclideanLin (a k)`
* the uniform norm bound `‖A k‖ ≤ 1 - q`

Derived API:
* the geometric norm estimate
* the convergence-to-zero consequence for `0 < q < 1`

Source/core/bridge triage:
* source-facing: the matrix recurrence in `ℝⁿ`
* core/canonical: `linear_iteration_contraction_estimate`
* bridge/view: `Matrix.toEuclideanCLM` and `Matrix.l2_opNorm_toEuclideanCLM`

This item therefore reuses the chapter owner theorem directly and keeps only the concrete
matrix-specialized bridge statements, rather than maintaining a parallel local proof of the same
geometric-decay owner result. -/

/- The chapter owner theorem is the canonical normed-space statement behind the matrix
specialization used here. -/
recall linear_iteration_contraction_estimate
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    (q : ℝ) (A : ℕ → E →L[𝕜] E) (a : ℕ → E)
    (ha : ∀ k : ℕ, a (k + 1) = A k (a k))
    (hA : ∀ k : ℕ, ‖A k‖ ≤ 1 - q) :
    HasGeometricRateOfConvergence (fun k : ℕ ↦ ‖a k‖) q ‖a 0‖

/-- The matrix recurrence in Proposition 1.6.13 is the Euclidean-space specialization of the
chapter owner theorem `linear_iteration_contraction_estimate`. -/
theorem norm_linear_iteration_hasGeometricRate
    {q : ℝ}
    (A : ℕ → Mat)
    (a : ℕ → Euclid)
    (ha : ∀ k : ℕ, a (k + 1) = (A k).toEuclideanLin (a k))
    (hA : ∀ k : ℕ, ‖A k‖ ≤ 1 - q) :
    HasGeometricRateOfConvergence (fun k : ℕ ↦ ‖a k‖) q ‖a 0‖ := by
  let e : Mat ≃⋆ₐ[ℝ] (Euclid →L[ℝ] Euclid) := Matrix.toEuclideanCLM
  let T : ℕ → Euclid →L[ℝ] Euclid := fun k ↦ e (A k)
  have hrec : ∀ k : ℕ, a (k + 1) = T k (a k) := fun k ↦ by
    simpa [T] using ha k
  have hT : ∀ k : ℕ, ‖T k‖ ≤ 1 - q := fun k ↦ by
    simpa [T, Matrix.l2_opNorm_toEuclideanCLM] using hA k
  exact linear_iteration_contraction_estimate q T a hrec hT

/-- Proposition 1.6.13: if a sequence in `ℝⁿ` satisfies the linear recurrence
`a_{k+1} = A_k a_k` and every matrix `A_k` has Euclidean operator norm at most `1 - q`, then the
iterates satisfy the geometric contraction estimate
`‖a_k‖ ≤ (1 - q)^k ‖a_0‖`. -/
theorem norm_linear_iteration_le_geometric_decay
    {q : ℝ}
    (A : ℕ → Mat)
    (a : ℕ → Euclid)
    (ha : ∀ k : ℕ, a (k + 1) = (A k).toEuclideanLin (a k))
    (hA : ∀ k : ℕ, ‖A k‖ ≤ 1 - q)
    (k : ℕ) :
    ‖a k‖ ≤ (1 - q) ^ k * ‖a 0‖ := by
  simpa [mul_comm] using (norm_linear_iteration_hasGeometricRate A a ha hA) k

/-- The norm sequence of a uniformly contractive linear iteration converges to `0`. -/
theorem norm_linear_iteration_tendsto_zero
    {q : ℝ}
    (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (A : ℕ → Mat)
    (a : ℕ → Euclid)
    (ha : ∀ k : ℕ, a (k + 1) = (A k).toEuclideanLin (a k))
    (hA : ∀ k : ℕ, ‖A k‖ ≤ 1 - q) :
    Tendsto (fun k : ℕ ↦ ‖a k‖) atTop (nhds 0) := by
  have hgeom := norm_linear_iteration_hasGeometricRate A a ha hA
  exact hgeom.tendsto_zero (fun _ ↦ norm_nonneg _) (norm_nonneg _) hq.1 hq.2

end

/-! ### Theorem_1_6_14 (from Chap01) -/
noncomputable section

/- Primary domain:
* scalar one-step contraction factors and radius recurrences for locally optimal gradient steps

Relevant owner-style declarations sampled before refining:
* `IsMinOn` in mathlib, the canonical owner predicate for an attained minimizer of a real-valued
  function on a set
* `HasGeometricRateOfConvergence` and
  `HasGeometricRateOfConvergence.of_step_bound` in `Definition_1_2_6.lean`
* `gradientMethod_dist_le_optimal_geometric_rate` in `Chap02/Theorem_2_17.lean`, the later
  owner-style optimal constant-step result
* the schedule type `(ℕ → ℝ)` recalled in `Definition_1_6_2.lean`

Source/core/bridge triage:
* source-facing: the step-dependent coefficients `a_k(h)` and `b_k(h)`, the optimal-step
  minimizer condition, the strict radius invariance, and the displayed recurrences and bounds
* core/canonical: `IsMinOn` for `h_k^*` and `HasGeometricRateOfConvergence` for the transformed
  gap sequence
* bridge/view: the radius owner `localGradientRadius μ M = 2 * μ / M`, the scaled radius
  `a_k = (M / (L + μ)) r_k`, and the gap ratio `r_k / ((2 * μ / M) - r_k)`

Best owner abstraction:
* `IsMinOn` for the source minimizer `h_k^*`, paired with `HasGeometricRateOfConvergence` for the
  intrinsic gap-ratio sequence

Primitive data:
* the radius sequence `r`
* the step schedule `h`
* the parameters `μ`, `L`, and the positive radius/Lipschitz datum `M : NNRealˣ`
* the initial source bound `0 < r_0 < localGradientRadius μ M`
* nonnegativity of the radius sequence, from which positivity of later radii is derived under
  the optimal-step hypotheses
* the one-step estimate
  `r_{k+1} ≤ max { a_k(h_k), b_k(h_k) } * r_k`

Derived API:
* `h_k^* = 2 / (L + μ)`
* strict invariance `r_{k+1} < r_k < localGradientRadius μ M`
* positivity of every later radius, obtained from the initial positivity and nonnegativity data
* the explicit radius recurrence
* the scaled recurrence for `a_k = (M / (L + μ)) r_k`
* the owner geometric-rate statement for the gap ratio
* the displayed bounds `(1.2.31)` and `(1.2.32)`

This file keeps those textbook scalar expressions as local notation inside the theorem layer,
uses `IsMinOn` only for the source minimizer layer, and lets the downstream recurrence lemmas
consume the derived textbook identity `h_k = 2 / (L + μ)` rather than repeating the minimizer
witness. The bridge to `HasGeometricRateOfConvergence` remains public instead of a private
helper. The positive denominator datum is carried canonically by `M : NNRealˣ` and the owner
`localGradientRadius`, rather than being recovered only from side inequalities. -/

section

variable {r h : ℕ → ℝ} {μ L : ℝ} {M : NNRealˣ}

/-- The local radius `2 * μ / M` from Theorem 1.6.14, with positivity of `M` encoded in
`M : NNRealˣ`. -/
def localGradientRadius (μ : ℝ) (M : NNRealˣ) : ℝ :=
  2 * μ / (M : ℝ)

/-- Expanding `localGradientRadius μ M` gives the textbook radius `2 * μ / M`. -/
theorem localGradientRadius_def (μ : ℝ) (M : NNRealˣ) :
    localGradientRadius μ M = 2 * μ / (M : ℝ) :=
  rfl

local notation "radius" => localGradientRadius μ M
local notation "step" => (2 / (L + μ) : ℝ)
local notation "q" => (2 * μ / (L + μ) : ℝ)
local notation "positiveSteps" => Set.Ioi (0 : ℝ)
local notation "aCoeff" =>
  fun k hStep ↦ 1 - hStep * (μ - (M : ℝ) * r k / 2)
local notation "bCoeff" =>
  fun k hStep ↦ hStep * (L + (M : ℝ) * r k / 2) - 1
local notation "bound" =>
  fun k hStep ↦ max (aCoeff k hStep) (bCoeff k hStep)
local notation "scaled" => fun k ↦ ((M : ℝ) / (L + μ)) * r k
local notation "gap" => fun k ↦ r k / (radius - r k)

/-- Helper for Theorem 1.6.14: the two affine radius factors cross exactly at the textbook step
`2 / (L + μ)`. -/
lemma localGradient_aCoeff_eq_bCoeff_iff
    (hLμ : 0 < L + μ) {k : ℕ} {hStep : ℝ} :
    aCoeff k hStep = bCoeff k hStep ↔ hStep = step := by
  constructor
  · intro hEq
    -- The shared `M r_k / 2` terms cancel, leaving a scalar linear equation in `hStep`.
    have hmul : hStep * (L + μ) = 2 := by
      linarith
    apply (eq_div_iff hLμ.ne').2
    linarith
  · intro hStep_eq
    subst hStep
    -- Substituting the textbook step makes the two branches coincide.
    field_simp [hLμ.ne']
    ring_nf

/-- Helper for Theorem 1.6.14: evaluating the maximum branch at the textbook step gives the
common affine value `((L - μ) + M r_k) / (L + μ)`. -/
lemma localGradient_bound_at_step
    (hLμ : 0 < L + μ) (k : ℕ) :
    bound k step = ((L - μ) + (M : ℝ) * r k) / (L + μ) := by
  have hcross : aCoeff k step = bCoeff k step :=
    (localGradient_aCoeff_eq_bCoeff_iff (r := r) (μ := μ) (L := L) (M := M) hLμ).2 rfl
  -- At the crossing point the maximum collapses to either branch.
  change max (aCoeff k step) (bCoeff k step) = ((L - μ) + (M : ℝ) * r k) / (L + μ)
  rw [max_eq_left hcross.ge]
  field_simp [hLμ.ne']
  ring_nf

/-- If `0 ≤ r_k < 2 * μ / M` and `h_k^*` minimizes `max {a_k(h), b_k(h)}` over positive
step sizes, then `h_k^* = 2 / (L + μ)`. -/
theorem localGradientRadiusBound_optimalStep_eq
    (hμ : 0 < μ) (hμL : μ ≤ L)
    {k : ℕ} {hStar : ℝ}
    (hrk_nonneg : 0 ≤ r k) (hrk_lt : r k < radius)
    (hopt : IsMinOn (bound k) positiveSteps hStar) :
    hStar = step := by
  have hLμ : 0 < L + μ := by
    nlinarith [hμ, hμL]
  have hM : 0 < (M : ℝ) := by
    exact_mod_cast (show 0 < (M : NNReal) from by
      exact pos_iff_ne_zero.mpr (Units.ne_zero M))
  have hslope_left : 0 < μ - (M : ℝ) * r k / 2 := by
    -- The source radius constraint makes the decreasing branch genuinely decreasing.
    unfold localGradientRadius at hrk_lt
    have hrk_mul : r k * (M : ℝ) < 2 * μ := by
      exact (lt_div_iff₀ hM).mp hrk_lt
    nlinarith [hrk_mul]
  have hstep_pos : 0 < step := by
    positivity
  have hcross : aCoeff k step = bCoeff k step :=
    (localGradient_aCoeff_eq_bCoeff_iff (r := r) (μ := μ) (L := L) (M := M) hLμ).2 rfl
  have hmin := isMinOn_iff.mp hopt
  have hstep_mem : step ∈ positiveSteps := by
    change 0 < step
    exact hstep_pos
  have hstep_le : bound k hStar ≤ bound k step := by
    exact hmin step hstep_mem
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hbranch_lt : bCoeff k hStar < aCoeff k hStar := by
      have : hStar * (L + μ) < 2 := by
        nlinarith [hlt, hLμ]
      linarith
    have hbound_star : bound k hStar = aCoeff k hStar := by
      change max (aCoeff k hStar) (bCoeff k hStar) = aCoeff k hStar
      rw [max_eq_left hbranch_lt.le]
    have hbound_step : bound k step = aCoeff k step := by
      change max (aCoeff k step) (bCoeff k step) = aCoeff k step
      rw [max_eq_left hcross.ge]
    have hbetter : aCoeff k step < aCoeff k hStar := by
      -- Left of the crossing, the maximum is the decreasing branch.
      nlinarith [hlt, hslope_left]
    have : bound k step < bound k hStar := by
      simpa [hbound_star, hbound_step] using hbetter
    exact not_lt_of_ge hstep_le this
  · have hbranch_gt : aCoeff k hStar < bCoeff k hStar := by
      have : 2 < hStar * (L + μ) := by
        nlinarith [hgt, hLμ]
      linarith
    have hbound_star : bound k hStar = bCoeff k hStar := by
      change max (aCoeff k hStar) (bCoeff k hStar) = bCoeff k hStar
      rw [max_eq_right hbranch_gt.le]
    have hbound_step : bound k step = bCoeff k step := by
      change max (aCoeff k step) (bCoeff k step) = bCoeff k step
      rw [max_eq_right hcross.le]
    have hbetter : bCoeff k step < bCoeff k hStar := by
      -- Right of the crossing, the maximum is the increasing branch.
      have hslope_right : 0 < L + (M : ℝ) * r k / 2 := by
        nlinarith [hμ, hμL, hrk_nonneg]
      nlinarith [hgt, hslope_right]
    have : bound k step < bound k hStar := by
      simpa [hbound_star, hbound_step] using hbetter
    exact not_lt_of_ge hstep_le this

section Recurrence

variable (hμ : 0 < μ) (hμL : μ ≤ L)
variable (hstep : ∀ k : ℕ, h k = step)
variable (hrec : ∀ k : ℕ, r (k + 1) ≤ bound k (h k) * r k)

/-- Under `0 < μ` and `μ ≤ L`, so that `L + μ > 0`, once the step schedule is identified with
the textbook value `h_k = 2 / (L + μ)`, the source radius estimate becomes
`r_{k+1} ≤ ((L - μ) r_k + M r_k^2) / (L + μ)`. -/
theorem localGradientRadius_recurrence_of_optimal_step
    (k : ℕ) :
    r (k + 1) ≤ ((L - μ) * r k + (M : ℝ) * r k ^ (2 : ℕ)) / (L + μ) := sorry

/-- Under `0 < μ` and `μ ≤ L`, so that the scaling by `L + μ` is nondegenerate, for the scaled
radii `a_k = (M / (L + μ)) r_k`, substituting the textbook step `h_k = 2 / (L + μ)` turns the
source recurrence into
`a_{k+1} ≤ (1 - q + a_k) a_k` with `q = 2 * μ / (L + μ)`. -/
theorem localGradientScaledRadius_recurrence_of_optimal_step
    (k : ℕ) :
    scaled (k + 1) ≤ (1 - q + scaled k) * scaled k := sorry

end Recurrence

section OptimalStep

variable (hμ : 0 < μ) (hμL : μ ≤ L)
variable (hr0 : 0 < r 0 ∧ r 0 < radius)
variable (hr_nonneg : ∀ k : ℕ, 0 ≤ r k)
variable (hopt : ∀ k : ℕ, IsMinOn (bound k) positiveSteps (h k))
variable (hrec : ∀ k : ℕ, r (k + 1) ≤ bound k (h k) * r k)

/-- If the sequence `r` is nonnegative, `0 < r_0 < 2 * μ / M`, and each `h_k` is the source
minimizer `h_k^*`, then the optimal-step identity `h_k = 2 / (L + μ)` propagates along the
radius-invariant region `r_k < 2 * μ / M`. -/
theorem localGradientRadius_strict_decay_of_optimal_step
    (k : ℕ) :
    h k = step ∧ r k < radius := sorry

/-- Helper for Theorem 1.6.14: under the optimal-step schedule, the gap ratio contracts by the
factor `1 / (1 + q)` in one step. -/
lemma localGradientGap_step_bound_of_optimal_step
    (k : ℕ) :
    gap (k + 1) ≤ gap k / (1 + q) := sorry

/-- The owner geometric-rate statement for the gap ratio
`r_k / ((2 * μ / M) - r_k)` under the source optimal-step choice, with positivity of each radius
derived from `0 < r_0 < 2 * μ / M`, nonnegativity, and the strict-decay layer above. -/
theorem localGradientGap_hasGeometricRate_of_optimal_step
    :
    HasGeometricRateOfConvergence gap (q / (1 + q)) (gap 0) := sorry

-- Proof sketch: combine the geometric-rate statement for `gap k = r k / (radius - r k)` with
-- the algebraic identity `radius / r k - 1 = 1 / gap k`, then rewrite the textbook recurrence
-- into the displayed reciprocal-gap inequality.
/-- Theorem 1.6.14 (1): if each `h_k` is the source minimizer `h_k^*` of
`max {a_k(h), b_k(h)}`, the radius sequence is nonnegative, and `0 < r_0 < 2 * μ / M`, then
the reciprocal-gap estimate `(1.2.31)` holds:
`radius / r_k - 1 ≥ (1 + q)^k (radius / r_0 - 1)`. -/
theorem localGradientScaledRadius_reciprocal_gap_lower_bound_of_optimal_step
    (k : ℕ) :
    radius / r k - 1 ≥ (1 + q) ^ k * (radius / r 0 - 1) := by
    -- TODO: The current formal hypotheses allow `r (k + 1) = 0` because `hrec` is only an
    -- upper bound. Then `radius / r (k + 1) - 1 = -1` in Lean, so the displayed reciprocal-gap
    -- inequality is false without an additional positivity or exact-recurrence assumption.
    sorry

-- Proof sketch: start from the reciprocal-gap estimate `(1.2.31)` and solve the resulting
-- inequality for `r k`. Multiplying by `M / (L + μ)` rewrites the bound in terms of
-- `scaled k = (M / (L + μ)) r k`.
/-- Theorem 1.6.14 (2): under the same optimal-step hypotheses, the scaled radii satisfy the
first explicit upper bound from `(1.2.32)`:
`a_k ≤ (q r_0) / (r_0 + (1 + q)^k (radius - r_0))`. -/
theorem localGradientScaledRadius_first_upper_bound_of_optimal_step
    (k : ℕ) :
    scaled k ≤ (q * r 0) / (r 0 + (1 + q) ^ k * (radius - r 0)) := sorry

-- Proof sketch: derive the first bound in `(1.2.32)` from `(1.2.31)`, then bound the
-- denominator below by `(radius - r 0) * (1 + q)^k` to obtain the geometric upper estimate.
/-- Theorem 1.6.14 (3): under the same optimal-step hypotheses, the scaled radii satisfy the
second explicit upper bound from `(1.2.32)`:
`a_k ≤ ((q r_0) / (radius - r_0)) (1 / (1 + q))^k`. -/
theorem localGradientScaledRadius_second_upper_bound_of_optimal_step
    (k : ℕ) :
    scaled k ≤ ((q * r 0) / (radius - r 0)) * (1 / (1 + q)) ^ k := sorry

end OptimalStep

end

end

/-! ### Theorem_1_6_15 (from Chap01) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section

variable {μ L : ℝ} {M : NNRealˣ}
variable {f : E → ℝ} {xStar x0 : E}

/- Primary domain: local linear convergence of the gradient method on a real Hilbert space near a
nondegenerate critical point with Lipschitz-continuous Hessian.

Owner declarations sampled before refining:
* `HasLipschitzContinuousHessian` in `Chap04/Definition_4_2_7`, written in Chapter 1 surface
  syntax as `f ∈ C22[M]`
* `HasLipschitzContinuousHessian.gradient_deviation_le` in `Lemma_1_5_11.lean`
* `gradientMethod` in `Algorithm_1_6_1.lean`
* `HasGeometricRateOfConvergence` in `Definition_1_2_6.lean`
* `localGradientRadius` and `localGradientGap_hasGeometricRate_of_optimal_step` in
  `Theorem_1_6_14.lean`, the scalar recurrence layer behind the local rate estimate

Source/core/bridge triage:
* source-facing: the local linear-rate theorem below
* core/canonical: `HasLipschitzContinuousHessian`, `gradientMethod`, and
  `HasGeometricRateOfConvergence`
* bridge/view: the intrinsic closed ball `Q = Metric.closedBall xStar radius`, where
  `radius = localGradientRadius μ M`, together with the Hessian quadratic bounds at `xStar` and
  the scalar local recurrence for the gradient-method distance sequence

Primitive data:
* `f`, `xStar`, `x0`
* the parameters `μ`, `L`, and the Hessian-Lipschitz datum `M`
* the Chapter 1 second-order owner hypothesis `f ∈ C22[(M : NNReal)]`
* the lower/upper quadratic bounds for the owner Hessian `hessian f xStar`
* the critical-point condition `∇ f xStar = 0`

Derived API:
* the intrinsic radius owner `localGradientRadius μ M`
* the constant-step trajectory `traj`
* the geometric-rate estimate for `k ↦ ‖traj k - xStar‖`
* any needed comparison between `μ` and `L`

No parallel local first-order wrapper is introduced here. The theorem is stated directly on the
Chapter 1 Hessian-Lipschitz owner `f ∈ C22[(M : NNReal)]`; the local ball is expressed through the
radius owner `localGradientRadius μ M`, and any induced strong-convex/smooth estimates are
derived consequences rather than primitive public data. -/

local notation "radius" => localGradientRadius μ M
local notation "step" => 2 / (L + μ)
local notation "rate" => (2 * μ) / (L + 3 * μ)
local notation "traj" => gradientMethod (fun _ : ℕ ↦ step) f x0

/-- Theorem 1.6.15: if `f` has `M`-Lipschitz Hessian, the Hessian at the stationary point `xStar`
has quadratic form bounded between `μ` and `L`, and the initial point lies in the intrinsic ball
of radius `localGradientRadius μ M` around `xStar`, then the fixed-step gradient method with
step size `2 / (L + μ)` satisfies the stated geometric error bound with rate parameter
`2 * μ / (L + 3 * μ)`. -/
-- Proof sketch: apply the Chapter 1 owner estimate `hf.gradient_deviation_le` on the ball
-- centered at `xStar` to compare `∇ f x` with the linearized model
-- `hessian f xStar (x - xStar)`.
-- The Hessian bounds at `xStar` supply the source local coefficients `μ - (M / 2) r_k` and
-- `L + (M / 2) r_k` for the distance sequence `r_k = ‖x_k - xStar‖`, while `hf` keeps `M`
-- tied to the genuine Hessian-Lipschitz datum. Any comparison between `μ` and `L` needed by the
-- scalar recurrence is derived internally from these Hessian bounds rather than stored as extra
-- public data, and the initial-radius hypothesis `h0` yields `0 < μ` because `M : NNRealˣ`
-- already forces `0 < (M : ℝ)`. The scalar recurrence layer from
-- `Theorem_1_6_14` uses the optimal constant step `2 / (L + μ)` and then yields the announced
-- geometric estimate with rate parameter `2 * μ / (L + 3 * μ)`.
theorem gradient_descent_local_linear_rate
    (hf : f ∈ C22[(M : NNReal)])
    (hess_lower : ∀ z : E, μ * ‖z‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f xStar z) z)
    (hess_upper : ∀ z : E, inner ℝ (hessian f xStar z) z ≤ L * ‖z‖ ^ (2 : ℕ))
    (hgradStar : ∇ f xStar = 0)
    (h0 : ‖x0 - xStar‖ < radius) :
    HasGeometricRateOfConvergence
      (fun k : ℕ ↦ ‖traj k - xStar‖)
      rate
      (radius * ‖x0 - xStar‖ / (radius - ‖x0 - xStar‖)) := sorry

end

end
