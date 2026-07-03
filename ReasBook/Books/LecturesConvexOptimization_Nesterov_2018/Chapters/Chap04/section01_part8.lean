import Mathlib
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Order.Filter.Extr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Recall
import Mathlib.Tactic.Ring

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_4_1_6 (from Chap04) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 4.1.6 lies in the Chapter 4 cubic-regularization / gradient-domination rate domain.

Sampled owner declarations:
* `CubicRegularizationMethod` in `Algorithm_4_1_5`, the source-facing owner for the iterate
  sequence, regularization schedule, and accepted-step relation;
* `GradientDominatedOn` and `GradientDominatedOn.UsesConstant` in `Definition_4_1_9`, the chapter
  owner and witness predicate for the minimizer and gradient-domination constant;
* `RegularizedNewton.acceptedParameters` in `Definition_4_1_16`, the fixed-iterate owner behind
  method `(4.1.16)` already reused by `CubicRegularizationMethod`;
* `cubic_newton_objective_drop_ge_half_sqrt_conditionNumber_mul_next_gap` in `Text_4_2_10`, the
  nearby chapter pattern where a source-facing rate theorem is driven by a one-step
  `‖∇ f‖^(3/2)` decrease hypothesis rather than lower-level step internals.

Best owner abstraction:
* source-facing: the two phase estimates from Theorem 4.1.6 for a cubic-regularization method
  applied to a degree-one gradient-dominated objective;
* core/canonical: `CubicRegularizationMethod`, `GradientDominatedOn 1 Set.univ f`, and the
  witness package `GradientDominatedOn.UsesConstant (p := 1) (𝓕 := Set.univ) (f := f) xStar τf`;
* bridge/view: the scalar textbook threshold `hatω`, together with the source-level one-step
  gradient-`3/2` descent inequality for the method.

Primitive data:
* the objective `f`;
* the cubic-regularization method `method`;
* the minimizer witness `xStar` and domination constant `τf`;
* the source-facing one-step descent inequality
  `f(x_k) - f(x_{k+1}) ≥ c ‖∇ f(x_{k+1})‖^(3/2)`.

Derived API:
* the scalar threshold `hatω`;
* the large-gap logarithmic contraction estimate;
* the small-gap inverse-square estimate.

This refinement keeps the source-facing rate statements, reuses the existing chapter owners for the
algorithm and domination data, and removes the lower-level residual inequality from the public API
in favor of the textbook one-step gradient-`3/2` decrease hypothesis already matching the source
statement layer.
-/

/-- The threshold `hatω = (18 / L0^2) τf^3 (L + L0)^3` appearing in the two-phase convergence
estimate for cubic regularization of a degree-one gradient-dominated function. -/
abbrev gradientDominatedCubicHatOmega
    (L L0 τf : ℝ) : ℝ :=
  (18 / L0 ^ (2 : ℕ)) * τf ^ (3 : ℕ) * (L + L0) ^ (3 : ℕ)

/-- Expanding `gradientDominatedCubicHatOmega L L0 τf` recovers the textbook
formula for `hatω`. -/
@[simp]
theorem gradientDominatedCubicHatOmega_def
    (L L0 τf : ℝ) :
    gradientDominatedCubicHatOmega L L0 τf =
      (18 / L0 ^ (2 : ℕ)) * τf ^ (3 : ℕ) * (L + L0) ^ (3 : ℕ) :=
  rfl

section GradientDominatedCubicRegularization

variable {f : E → ℝ} {stepMap : ℝ → E → E} {L0 L τf : ℝ} {x0 : E}

variable
  (method :
    CubicRegularizationMethod
      f
      stepMap
      L0 L x0)

variable (xStar : E)
local notation "Δ" => fun k : ℕ ↦ f (method k) - f xStar
local notation "κ" =>
  (L0 / (3 * Real.sqrt 2 * Real.rpow (L + L0) (3 / 2 : ℝ)) : ℝ)
local notation "ω̂" => gradientDominatedCubicHatOmega L L0 τf
variable
  (hgradientDominated :
    GradientDominatedOn.UsesConstant 1 Set.univ f xStar τf)
  (hdescent :
    ∀ k : ℕ,
      f (method k) - f (method (k + 1)) ≥
        κ * Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ))

/-- Helper for Theorem 4.1.6: the scalar threshold `hatω` matches the squared cubic-descent
coefficient exactly. -/
lemma gradient_dominated_cubic_hatOmega_coefficient
    (hL0 : 0 < L0) (hLsum_pos : 0 < L + L0) :
    κ ^ (2 : ℕ) * ω̂ = τf ^ (3 : ℕ) := by
  -- Clear the textbook constants once so the main recurrence can use a clean normalized form.
  have hsqrt2 : (Real.sqrt 2 : ℝ) ^ (2 : ℕ) = 2 := by
    simp [pow_two]
  have hrpow :
      Real.rpow (L + L0) (3 / 2 : ℝ) ^ (2 : ℕ) = (L + L0) ^ (3 : ℕ) := by
    calc
      Real.rpow (L + L0) (3 / 2 : ℝ) ^ (2 : ℕ)
          = Real.rpow (L + L0) ((3 / 2 : ℝ) + (3 / 2 : ℝ)) := by
              rw [pow_two]
              symm
              exact Real.rpow_add hLsum_pos (3 / 2 : ℝ) (3 / 2 : ℝ)
      _ = (L + L0) ^ (3 : ℕ) := by
            norm_num
  have hrpow' :
      Real.rpow (L0 + L) (3 / 2 : ℝ) ^ (2 : ℕ) = (L + L0) ^ (3 : ℕ) := by
    simpa [add_comm] using hrpow
  field_simp [gradientDominatedCubicHatOmega, hL0.ne', hLsum_pos.ne']
  ring_nf
  rw [hsqrt2, hrpow]
  ring_nf

/-- Helper for Theorem 4.1.6: squaring a nonnegative `3/2`-power recovers the cubic power. -/
lemma gradient_dominated_cubic_rpow_three_halves_sq {x : ℝ} (hx : 0 ≤ x) :
    (Real.rpow x (3 / 2 : ℝ)) ^ (2 : ℕ) = x ^ (3 : ℕ) := by
  -- Rewrite `x^(3/2)` as `x * sqrt x`, then square that expression.
  rw [pow_two]
  by_cases hzero : x = 0
  · simp [hzero]
  · have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hzero)
    have hrpow : Real.rpow x (3 / 2 : ℝ) = x * Real.sqrt x := by
      rw [Real.sqrt_eq_rpow]
      calc
        x ^ (3 / 2 : ℝ) = x ^ ((1 : ℝ) + (1 / 2 : ℝ)) := by
            norm_num
        _ = x ^ (1 : ℝ) * x ^ (1 / 2 : ℝ) := by
              rw [Real.rpow_add hx_pos]
        _ = x * x ^ (1 / 2 : ℝ) := by
              rw [Real.rpow_one]
    rw [hrpow]
    nlinarith [Real.sq_sqrt hx]

/-- Helper for Theorem 4.1.6: the minimizer witness makes every objective gap along the method
nonnegative. -/
lemma gradient_dominated_cubic_gap_nonneg
    (hgradientDominated :
      GradientDominatedOn.UsesConstant 1 Set.univ f xStar τf)
    (k : ℕ) :
    0 ≤ Δ k := by
  -- Expand `xStar ∈ argmin[univ] f` to the minimizing inequality at the current iterate.
  rcases mem_constrainedArgmin_iff.mp
      (GradientDominatedOn.UsesConstant.mem_argmin hgradientDominated) with
    ⟨_, hxStar_min⟩
  exact sub_nonneg.mpr ((isMinOn_iff.mp hxStar_min) (method k) (by simp))

/-- Helper for Theorem 4.1.6: the normalized `hatω` term is dominated by the cubic descent term
coming from the gradient lower bound. -/
lemma gradient_dominated_cubic_normalized_term_le_descent_term
    (hgradientDominated :
      GradientDominatedOn.UsesConstant 1 Set.univ f xStar τf)
    (k : ℕ) :
    ω̂ * Real.rpow (Δ (k + 1) / ω̂) (3 / 2 : ℝ) ≤
      κ * Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ) := by
  -- Compare squares: the gap bound gives `Δ^3 ≤ τf^3 ‖∇f‖^3`, and the coefficient identity turns
  -- `τf^3` into `κ^2 hatω`.
  have hω_pos : 0 < ω̂ := by
    have hLsum_pos : 0 < L + L0 := by
      linarith [CubicRegularizationMethod.L0_pos method, CubicRegularizationMethod.L0_le_L method]
    have hτf_pos : 0 < τf := GradientDominatedOn.UsesConstant.pos hgradientDominated
    dsimp [gradientDominatedCubicHatOmega]
    have hL0sq_pos : 0 < L0 ^ (2 : ℕ) := pow_pos (CubicRegularizationMethod.L0_pos method) 2
    have hτf3_pos : 0 < τf ^ (3 : ℕ) := pow_pos hτf_pos 3
    have hLsum3_pos : 0 < (L + L0) ^ (3 : ℕ) := pow_pos hLsum_pos 3
    positivity
  have hΔ_nonneg : 0 ≤ Δ (k + 1) := gradient_dominated_cubic_gap_nonneg
      (method := method) (xStar := xStar) hgradientDominated (k + 1)
  have hg_nonneg : 0 ≤ ‖∇ f (method (k + 1))‖ := by
    positivity
  have hκ_nonneg : 0 ≤ κ := by
    have hLsum_pos : 0 < L + L0 := by
      linarith [CubicRegularizationMethod.L0_pos method, CubicRegularizationMethod.L0_le_L method]
    have hden_pos :
        0 < 3 * Real.sqrt 2 * Real.rpow (L + L0) (3 / 2 : ℝ) := by
      have hsqrt2_pos : 0 < Real.sqrt 2 := by
        positivity
      have hrpow_pos : 0 < Real.rpow (L + L0) (3 / 2 : ℝ) :=
        Real.rpow_pos_of_pos hLsum_pos (3 / 2 : ℝ)
      positivity
    exact div_nonneg (CubicRegularizationMethod.L0_pos method).le hden_pos.le
  have hbound : Δ (k + 1) ≤ τf * ‖∇ f (method (k + 1))‖ := by
    -- On `Set.univ`, the within-gradient is the ambient gradient.
    simpa [gradientWithin, gradient, fderivWithin_univ, Real.rpow_natCast] using
      (GradientDominatedOn.UsesConstant.bound
        (p := 1) (𝓕 := Set.univ) (f := f) (xStar := xStar) (τf := τf)
        hgradientDominated (x := method (k + 1)) (by simp))
  have hleft_nonneg :
      0 ≤ ω̂ * Real.rpow (Δ (k + 1) / ω̂) (3 / 2 : ℝ) := by
    exact mul_nonneg hω_pos.le (Real.rpow_nonneg (by positivity) _)
  have hright_nonneg :
      0 ≤ κ * Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ) := by
    exact mul_nonneg hκ_nonneg (Real.rpow_nonneg hg_nonneg _)
  have hleft_sq :
      (ω̂ * Real.rpow (Δ (k + 1) / ω̂) (3 / 2 : ℝ)) ^ (2 : ℕ) =
        Δ (k + 1) ^ (3 : ℕ) / ω̂ := by
    have hdiv_nonneg : 0 ≤ Δ (k + 1) / ω̂ := by
      positivity
    rw [mul_pow, gradient_dominated_cubic_rpow_three_halves_sq hdiv_nonneg]
    field_simp [hω_pos.ne']
  have hright_sq :
      (κ * Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ)) ^ (2 : ℕ) =
        κ ^ (2 : ℕ) * ‖∇ f (method (k + 1))‖ ^ (3 : ℕ) := by
    rw [mul_pow, gradient_dominated_cubic_rpow_three_halves_sq hg_nonneg]
  have hcube :
      Δ (k + 1) ^ (3 : ℕ) ≤ τf ^ (3 : ℕ) * ‖∇ f (method (k + 1))‖ ^ (3 : ℕ) := by
    have hcube' :
        Δ (k + 1) ^ (3 : ℕ) ≤
          (τf * ‖∇ f (method (k + 1))‖) ^ (3 : ℕ) :=
      pow_le_pow_left₀ hΔ_nonneg hbound 3
    simpa [mul_pow] using hcube'
  have hsq :
      (ω̂ * Real.rpow (Δ (k + 1) / ω̂) (3 / 2 : ℝ)) ^ (2 : ℕ) ≤
        (κ * Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ)) ^ (2 : ℕ) := by
    rw [hleft_sq, hright_sq]
    have h1 :
        Δ (k + 1) ^ (3 : ℕ) / ω̂ ≤
          (τf ^ (3 : ℕ) * ‖∇ f (method (k + 1))‖ ^ (3 : ℕ)) / ω̂ :=
      div_le_div_of_nonneg_right hcube hω_pos.le
    have h2 :
        (τf ^ (3 : ℕ) * ‖∇ f (method (k + 1))‖ ^ (3 : ℕ)) / ω̂ =
          κ ^ (2 : ℕ) * ‖∇ f (method (k + 1))‖ ^ (3 : ℕ) := by
      have hLsum_pos : 0 < L + L0 := by
        linarith [CubicRegularizationMethod.L0_pos method, CubicRegularizationMethod.L0_le_L method]
      rw [← gradient_dominated_cubic_hatOmega_coefficient
        (L0 := L0) (L := L) (τf := τf)
        (hL0 := CubicRegularizationMethod.L0_pos method) (hLsum_pos := hLsum_pos)]
      field_simp [hω_pos.ne', (GradientDominatedOn.UsesConstant.pos hgradientDominated).ne']
    exact h1.trans_eq h2
  exact (sq_le_sq₀ hleft_nonneg hright_nonneg).mp hsq

/-- Helper for Theorem 4.1.6: the normalized gaps satisfy the scalar source recurrence
`δ_k - δ_{k+1} ≥ δ_{k+1}^{3/2}`. -/
lemma gradient_dominated_cubic_normalized_gap_step
    (hgradientDominated :
      GradientDominatedOn.UsesConstant 1 Set.univ f xStar τf)
    (hdescent :
      ∀ k : ℕ,
        f (method k) - f (method (k + 1)) ≥
          κ * Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ))
    (k : ℕ) :
    let δ : ℕ → ℝ := fun i ↦ Δ i / ω̂
    δ k - δ (k + 1) ≥ Real.rpow (δ (k + 1)) (3 / 2 : ℝ) := by
  -- Route correction: use the next-gap recurrence from the source proof, not a same-index
  -- recurrence. This is the scalar invariant that drives both phases.
  let δ : ℕ → ℝ := fun i ↦ Δ i / ω̂
  have hω_pos : 0 < ω̂ := by
    have hLsum_pos : 0 < L + L0 := by
      linarith [CubicRegularizationMethod.L0_pos method, CubicRegularizationMethod.L0_le_L method]
    have hτf_pos : 0 < τf := GradientDominatedOn.UsesConstant.pos hgradientDominated
    dsimp [gradientDominatedCubicHatOmega]
    have hL0sq_pos : 0 < L0 ^ (2 : ℕ) := pow_pos (CubicRegularizationMethod.L0_pos method) 2
    have hτf3_pos : 0 < τf ^ (3 : ℕ) := pow_pos hτf_pos 3
    have hLsum3_pos : 0 < (L + L0) ^ (3 : ℕ) := pow_pos hLsum_pos 3
    positivity
  have hmain :
      ω̂ * Real.rpow (Δ (k + 1) / ω̂) (3 / 2 : ℝ) ≤ Δ k - Δ (k + 1) := by
    have hleft :=
      gradient_dominated_cubic_normalized_term_le_descent_term
        (method := method) (xStar := xStar) hgradientDominated k
    have hright :
        κ * Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ) ≤ Δ k - Δ (k + 1) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hdescent k
    exact le_trans hleft hright
  have hrewrite :
      Δ k / ω̂ - Δ (k + 1) / ω̂ = (Δ k - Δ (k + 1)) / ω̂ := by
    field_simp [hω_pos.ne']
  -- Divide the unnormalized inequality by the positive threshold `hatω`.
  have hdiv0 :
      Real.rpow (Δ (k + 1) / ω̂) (3 / 2 : ℝ) * ω̂ ≤ Δ k - Δ (k + 1) := by
    simpa [mul_comm] using hmain
  have hdiv :
      Real.rpow (Δ (k + 1) / ω̂) (3 / 2 : ℝ) ≤ (Δ k - Δ (k + 1)) / ω̂ := by
    exact (le_div_iff₀ hω_pos).2 hdiv0
  simpa [δ, hrewrite] using hdiv

/-- Helper for Theorem 4.1.6: once the next normalized gap is at least `1`, one recurrence step
contracts its logarithm by the factor `2/3`. -/
lemma log_step_le_two_thirds_of_previous {a b : ℝ}
    (hb : 1 ≤ b)
    (hstep : a - b ≥ Real.rpow b (3 / 2 : ℝ)) :
    Real.log b ≤ (2 / 3 : ℝ) * Real.log a := by
  -- The recurrence implies `a ≥ b^(3/2)`, so taking logs gives the desired factor.
  have hb_pos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hrpow_le : Real.rpow b (3 / 2 : ℝ) ≤ a := by
    have hsum : b + Real.rpow b (3 / 2 : ℝ) ≤ a := by
      linarith
    linarith [Real.rpow_nonneg hb_pos.le (3 / 2 : ℝ)]
  have hlog : (3 / 2 : ℝ) * Real.log b ≤ Real.log a := by
    rw [← Real.log_rpow hb_pos (3 / 2 : ℝ)]
    exact Real.log_le_log (Real.rpow_pos_of_pos hb_pos (3 / 2 : ℝ)) hrpow_le
  nlinarith

/-- Helper for Theorem 4.1.6: a nonnegative sequence satisfying the source recurrence inherits the
geometric logarithmic contraction of part (1). -/
lemma gradient_dominated_cubic_log_gap_le_geometric_of_step
    {δ : ℕ → ℝ}
    (hδ_nonneg : ∀ k, 0 ≤ δ k)
    (hstep : ∀ k, δ k - δ (k + 1) ≥ Real.rpow (δ (k + 1)) (3 / 2 : ℝ))
    (h0 : 1 ≤ δ 0) :
    ∀ k : ℕ, Real.log (δ k) ≤ (2 / 3 : ℝ) ^ k * Real.log (δ 0) := by
  -- Split into the small-gap branch, where the logarithm is already nonpositive, and the
  -- large-gap branch, where the scalar log-step lemma applies.
  have hlog0_nonneg : 0 ≤ Real.log (δ 0) := by
    simpa [Real.log_one] using (Real.log_le_log zero_lt_one h0)
  intro k
  induction k with
  | zero =>
      simp
  | succ k hk =>
      by_cases hnext_pos : 0 < δ (k + 1)
      · by_cases hsmall : δ (k + 1) ≤ 1
        · have hlog_nonpos : Real.log (δ (k + 1)) ≤ 0 := by
            simpa [Real.log_one] using (Real.log_le_log hnext_pos hsmall)
          have hrhs_nonneg : 0 ≤ (2 / 3 : ℝ) ^ (k + 1) * Real.log (δ 0) := by
            positivity
          linarith
        · have hbig : 1 < δ (k + 1) := lt_of_not_ge hsmall
          have hstep_log :
              Real.log (δ (k + 1)) ≤ (2 / 3 : ℝ) * Real.log (δ k) := by
            exact log_step_le_two_thirds_of_previous hbig.le (hstep k)
          calc
            Real.log (δ (k + 1)) ≤ (2 / 3 : ℝ) * Real.log (δ k) := hstep_log
            _ ≤ (2 / 3 : ℝ) * ((2 / 3 : ℝ) ^ k * Real.log (δ 0)) := by
                  nlinarith [hk]
            _ = (2 / 3 : ℝ) ^ (k + 1) * Real.log (δ 0) := by
                  rw [pow_succ]
                  ring
      · have hnext_eq : δ (k + 1) = 0 := by
          linarith [hδ_nonneg (k + 1)]
        have hrhs_nonneg : 0 ≤ (2 / 3 : ℝ) ^ (k + 1) * Real.log (δ 0) := by
          positivity
        simp [hnext_eq, hrhs_nonneg]

/-- Helper for Theorem 4.1.6: one recurrence step in the small-gap regime increases the reciprocal
square root by at least the source constant `1 / (2 + 3B/2)`. -/
lemma reciprocal_sqrt_increment_ge_small_gap_constant
    {a b B : ℝ} (hb_pos : 0 < b)
    (hstep : a - b ≥ Real.rpow b (3 / 2 : ℝ))
    (hbB : b ≤ B ^ (2 : ℕ)) (hB : 0 ≤ B) :
    1 / Real.sqrt b - 1 / Real.sqrt a ≥ 1 / (2 + (3 / 2 : ℝ) * B) := by
  -- Rationalize the exact reciprocal difference, then bound `sqrt (1 + s)` by `1 + s / 2`.
  have hb_nonneg : 0 ≤ b := hb_pos.le
  have hrpow : Real.rpow b (3 / 2 : ℝ) = b * Real.sqrt b := by
    rw [Real.sqrt_eq_rpow]
    calc
      b ^ (3 / 2 : ℝ) = b ^ ((1 : ℝ) + (1 / 2 : ℝ)) := by
          norm_num
      _ = b ^ (1 : ℝ) * b ^ (1 / 2 : ℝ) := by
            rw [Real.rpow_add hb_pos]
      _ = b * b ^ (1 / 2 : ℝ) := by
            rw [Real.rpow_one]
  have hstep' : b + Real.rpow b (3 / 2 : ℝ) ≤ a := by
    linarith
  have ha_lower : b * (1 + Real.sqrt b) ≤ a := by
    calc
      b * (1 + Real.sqrt b) = b + b * Real.sqrt b := by
          ring
      _ = b + Real.rpow b (3 / 2 : ℝ) := by
            rw [hrpow]
      _ ≤ a := hstep'
  have ha_pos : 0 < a := by
    have : 0 < b * (1 + Real.sqrt b) := by
      positivity
    linarith
  have hroot : Real.sqrt (b * (1 + Real.sqrt b)) ≤ Real.sqrt a :=
    Real.sqrt_le_sqrt ha_lower
  have hsqrt_mul :
      Real.sqrt (b * (1 + Real.sqrt b)) = Real.sqrt b * Real.sqrt (1 + Real.sqrt b) := by
    rw [Real.sqrt_mul hb_nonneg]
  have hsqrt_mul_le : Real.sqrt b * Real.sqrt (1 + Real.sqrt b) ≤ Real.sqrt a := by
    simpa [hsqrt_mul] using hroot
  have hrecip_le :
      1 / Real.sqrt a ≤ 1 / (Real.sqrt b * Real.sqrt (1 + Real.sqrt b)) := by
    exact (one_div_le_one_div (Real.sqrt_pos.mpr ha_pos) (by positivity)).2 hsqrt_mul_le
  have hmain :
      1 / Real.sqrt b - 1 / Real.sqrt a ≥
        1 / Real.sqrt b - 1 / (Real.sqrt b * Real.sqrt (1 + Real.sqrt b)) := by
    linarith
  have hid :
      1 / Real.sqrt b - 1 / (Real.sqrt b * Real.sqrt (1 + Real.sqrt b)) =
        1 / (Real.sqrt (1 + Real.sqrt b) * (1 + Real.sqrt (1 + Real.sqrt b))) := by
    have hsq : Real.sqrt (1 + Real.sqrt b) ^ (2 : ℕ) = 1 + Real.sqrt b := by
      exact Real.sq_sqrt (by positivity)
    field_simp [hb_pos.ne']
    nlinarith [hsq]
  have hsqrtB : Real.sqrt b ≤ B := by
    rw [Real.sqrt_le_iff]
    exact ⟨hB, by simpa using hbB⟩
  have hsqrt_one : Real.sqrt (1 + Real.sqrt b) ≤ 1 + Real.sqrt b / 2 := by
    have : -(1 : ℝ) ≤ Real.sqrt b := by
      nlinarith [Real.sqrt_nonneg b]
    exact Real.sqrt_one_add_le this
  have hrewrite :
      Real.sqrt (1 + Real.sqrt b) * (1 + Real.sqrt (1 + Real.sqrt b)) =
        1 + Real.sqrt b + Real.sqrt (1 + Real.sqrt b) := by
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 1 + Real.sqrt b)]
  have hden :
      Real.sqrt (1 + Real.sqrt b) * (1 + Real.sqrt (1 + Real.sqrt b)) ≤
        2 + (3 / 2 : ℝ) * B := by
    rw [hrewrite]
    nlinarith
  have hden_pos :
      0 < Real.sqrt (1 + Real.sqrt b) * (1 + Real.sqrt (1 + Real.sqrt b)) := by
    positivity
  have hpos_rhs : 0 < 2 + (3 / 2 : ℝ) * B := by
    positivity
  have htarget :
      1 / (2 + (3 / 2 : ℝ) * B) ≤
        1 / (Real.sqrt (1 + Real.sqrt b) * (1 + Real.sqrt (1 + Real.sqrt b))) := by
    exact (one_div_le_one_div hpos_rhs hden_pos).2 hden
  rw [hid] at hmain
  linarith

/-- Helper for Theorem 4.1.6: the source recurrence makes the normalized sequence monotone. -/
lemma gradient_dominated_cubic_step_nonincreasing
    {δ : ℕ → ℝ}
    (hδ_nonneg : ∀ k, 0 ≤ δ k)
    (hstep : ∀ k, δ k - δ (k + 1) ≥ Real.rpow (δ (k + 1)) (3 / 2 : ℝ)) :
    ∀ k, δ (k + 1) ≤ δ k := by
  -- The recurrence lower-bounds the drop by a nonnegative quantity.
  intro k
  have hnonneg : 0 ≤ Real.rpow (δ (k + 1)) (3 / 2 : ℝ) :=
    Real.rpow_nonneg (hδ_nonneg (k + 1)) _
  linarith [hstep k]

/-- Helper for Theorem 4.1.6: every normalized gap stays below the initial one. -/
lemma gradient_dominated_cubic_step_le_initial
    {δ : ℕ → ℝ}
    (hδ_nonneg : ∀ k, 0 ≤ δ k)
    (hstep : ∀ k, δ k - δ (k + 1) ≥ Real.rpow (δ (k + 1)) (3 / 2 : ℝ)) :
    ∀ k, δ k ≤ δ 0 := by
  -- Iterate monotonicity to compare every later index with `δ 0`.
  intro k
  induction k with
  | zero =>
      simp
  | succ k hk =>
      exact le_trans (gradient_dominated_cubic_step_nonincreasing hδ_nonneg hstep k) hk

/-- Helper for Theorem 4.1.6: under the small-gap initial condition, each normalized gap is either
already zero or has the reciprocal lower bound used in part (2). -/
lemma gradient_dominated_cubic_reciprocal_or_zero
    {δ : ℕ → ℝ} {γ : ℝ}
    (hδ_nonneg : ∀ k, 0 ≤ δ k)
    (hstep : ∀ k, δ k - δ (k + 1) ≥ Real.rpow (δ (k + 1)) (3 / 2 : ℝ))
    (hγ : 1 < γ) (h0 : δ 0 ≤ γ ^ (2 : ℕ)) :
    ∀ k : ℕ,
      δ k = 0 ∨
        1 / Real.sqrt (δ k) ≥ 1 / γ + (k : ℝ) / (2 + (3 / 2 : ℝ) * γ) := by
  -- Sum the one-step reciprocal increment, while keeping a separate zero-gap branch to avoid
  -- dividing by `sqrt 0`.
  have hγ_pos : 0 < γ := lt_trans zero_lt_one hγ
  have hγ_nonneg : 0 ≤ γ := hγ_pos.le
  intro k
  induction k with
  | zero =>
      by_cases hzero : δ 0 = 0
      · exact Or.inl hzero
      · have hpos : 0 < δ 0 := lt_of_le_of_ne (hδ_nonneg 0) (Ne.symm hzero)
        have hsqrt_le : Real.sqrt (δ 0) ≤ γ := by
          rw [Real.sqrt_le_iff]
          exact ⟨hγ_nonneg, by simpa using h0⟩
        have hrecip : 1 / γ ≤ 1 / Real.sqrt (δ 0) := by
          exact (one_div_le_one_div hγ_pos (Real.sqrt_pos.mpr hpos)).2 hsqrt_le
        right
        simpa using hrecip
  | succ k hk =>
      rcases hk with hzero | hrecip
      · have hnext_nonneg : 0 ≤ δ (k + 1) := hδ_nonneg (k + 1)
        have hstepk := hstep k
        have hnext_eq : δ (k + 1) = 0 := by
          rw [hzero] at hstepk
          have : 0 ≤ Real.rpow (δ (k + 1)) (3 / 2 : ℝ) :=
            Real.rpow_nonneg hnext_nonneg _
          linarith
        exact Or.inl hnext_eq
      · by_cases hnext_zero : δ (k + 1) = 0
        · exact Or.inl hnext_zero
        · have hnext_pos : 0 < δ (k + 1) := lt_of_le_of_ne (hδ_nonneg (k + 1)) (Ne.symm hnext_zero)
          have hnext_le_gamma_sq : δ (k + 1) ≤ γ ^ (2 : ℕ) := by
            exact le_trans (gradient_dominated_cubic_step_le_initial hδ_nonneg hstep (k + 1)) h0
          have hincr :=
            reciprocal_sqrt_increment_ge_small_gap_constant
              hnext_pos (hstep k) hnext_le_gamma_sq hγ_nonneg
          right
          have hsucc :
              1 / γ + ((k + 1 : ℕ) : ℝ) / (2 + (3 / 2 : ℝ) * γ) =
                (1 / γ + (k : ℝ) / (2 + (3 / 2 : ℝ) * γ)) +
                  1 / (2 + (3 / 2 : ℝ) * γ) := by
            norm_num [Nat.cast_add]
            ring
          rw [hsucc]
          linarith

/-- Helper for Theorem 4.1.6: a reciprocal-square-root lower bound converts into the exact
inverse-square upper bound from part (2). -/
lemma inverse_square_of_reciprocal_nat
    {δ γ : ℝ} (k : ℕ) (hδ_pos : 0 < δ) (hγ : 0 < γ)
    (hrecip :
      1 / Real.sqrt δ ≥ 1 / γ + (k : ℝ) / (2 + (3 / 2 : ℝ) * γ)) :
    δ ≤
      γ ^ (2 : ℕ) * (2 + (3 / 2 : ℝ) * γ) ^ (2 : ℕ) /
        (2 + ((k : ℝ) + 3 / 2) * γ) ^ (2 : ℕ) := by
  -- Rewrite the reciprocal lower bound as a bound on `sqrt δ`, square it, and clear the
  -- denominator algebraically.
  let C : ℝ := 2 + (3 / 2 : ℝ) * γ
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  have hmul : (1 / γ + (k : ℝ) / C) * Real.sqrt δ ≤ 1 := by
    have htmp := mul_le_mul_of_nonneg_right hrecip (Real.sqrt_nonneg δ)
    have hsqrt : Real.sqrt δ * (1 / Real.sqrt δ) = 1 := by
      field_simp [Real.sqrt_pos.mpr hδ_pos]
    nlinarith [hsqrt]
  have hsq' : ((1 / γ + (k : ℝ) / C) * Real.sqrt δ) ^ (2 : ℕ) ≤ 1 := by
    have hnonneg : 0 ≤ (1 / γ + (k : ℝ) / C) * Real.sqrt δ := by
      positivity
    simpa using pow_le_pow_left₀ hnonneg hmul 2
  have hsqmul : (1 / γ + (k : ℝ) / C) ^ (2 : ℕ) * δ ≤ 1 := by
    have hsqrt_sq : Real.sqrt δ ^ (2 : ℕ) = δ := Real.sq_sqrt hδ_pos.le
    nlinarith [hsq', hsqrt_sq]
  have hAeq : 1 / γ + (k : ℝ) / C = (C + (k : ℝ) * γ) / (γ * C) := by
    dsimp [C]
    field_simp [hγ.ne']
  rw [hAeq] at hsqmul
  have hmul_pos : 0 < γ * C := by
    positivity
  have hcore : (C + (k : ℝ) * γ) ^ (2 : ℕ) * δ ≤ γ ^ (2 : ℕ) * C ^ (2 : ℕ) := by
    field_simp [hmul_pos.ne'] at hsqmul
    nlinarith
  have hden_eq : C + (k : ℝ) * γ = 2 + ((k : ℝ) + 3 / 2) * γ := by
    dsimp [C]
    ring
  have htarget : δ ≤ γ ^ (2 : ℕ) * C ^ (2 : ℕ) / (C + (k : ℝ) * γ) ^ (2 : ℕ) := by
    refine (le_div_iff₀ (by positivity)).2 ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcore
  simpa [C, hden_eq] using htarget

-- Proof sketch: combine the assumed one-step estimate
-- `f(x_k) - f(x_{k+1}) ≥ κ ‖∇ f(x_{k+1})‖^(3/2)` with the degree-one
-- gradient-domination inequality to obtain the scalar
-- recurrence `δ_k - δ_{k+1} ≥ δ_{k+1}^{3/2}` for the normalized gaps `δ_k = Δ k / hatω`. Then
-- use
-- `log δ_k ≥ (3 / 2) log δ_{k+1}` and iterate to get the geometric decay of the logarithm.
/-- Theorem 4.1.6 (1): if the initial objective gap is at least `hatω`, then the normalized
suboptimality logarithm along the cubic-regularized Newton iterates contracts by the factor
`(2 / 3)^k`. -/
theorem gradientDominated_cubicRegularization_log_gap_le_geometric
    (hgap0 : ω̂ ≤ Δ 0) :
    ∀ k : ℕ,
      Real.log (Δ k / ω̂) ≤ (2 / 3 : ℝ) ^ k * Real.log (Δ 0 / ω̂) := by
  -- TODO: the intended proof is already reduced to the scalar helper lemmas above, but the main
  -- declaration header does not include the essential assumptions `hgradientDominated` and
  -- `hdescent`, so those hypotheses are unavailable inside this theorem body.
  sorry

-- Proof sketch: derive the same scalar recurrence
-- `δ_k - δ_{k+1} ≥ δ_{k+1}^{3/2}`, then derive the reciprocal estimate
-- `1 / sqrt δ_{k+1} - 1 / sqrt δ_k ≥ 1 / (2 + (3 / 2) * sqrt δ_0)` under the small-gap
-- hypothesis `δ_0 ≤ γ^2`. Summing this inequality yields
-- `1 / sqrt δ_k ≥ 1 / γ + k / (2 + (3 / 2) * γ)`, which rearranges to the displayed
-- inverse-square bound for `Δ k`.
/-- Theorem 4.1.6 (2): if the initial objective gap is at most `γ^2 hatω` for some `γ > 1`,
then every cubic-regularized Newton iterate satisfies the inverse-square upper bound from
equation `(4.1.36)`. -/
theorem gradientDominated_cubicRegularization_gap_le_inverse_square
    {γ : ℝ} (hγ : 1 < γ)
    (hgap0 : Δ 0 ≤ γ ^ (2 : ℕ) * ω̂) :
    ∀ k : ℕ,
      Δ k ≤
        ω̂ *
          (γ ^ (2 : ℕ) * (2 + (3 / 2 : ℝ) * γ) ^ (2 : ℕ) /
            (2 + ((k : ℝ) + 3 / 2) * γ) ^ (2 : ℕ)) := by
  -- TODO: the intended proof is already reduced to the reciprocal-square-root helper lemmas
  -- above, but the main declaration header omits the essential assumptions
  -- `hgradientDominated` and `hdescent`, so the source-faithful closure cannot be attached here
  -- without repairing the theorem statement.
  sorry

end GradientDominatedCubicRegularization

end

/-! ### Definition_4_1_7 (from Chap04) -/
open scoped ConstrainedArgmin

noncomputable section

variable {E : Type*} [AddCommMonoid E] [Module ℝ E]

/- Definition 4.1.7 lies in the unconstrained star-convex optimization domain over a real module.

Sampled owner-style declarations:
* `IsMinOn` and `isMinOn_univ_iff`, the canonical mathlib owner for whole-space minimizers;
* `argmin[Q]` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project owner
  for minimizer sets on a feasible set, specialized here to `Q = Set.univ`;
* mathlib `StarConvex ℝ x s`, the ambient owner pattern for star-shaped geometry of sets;
* `StarConvexWithRespectToOn` in `Theorem_4_1_4`, the chapter bridge owner for the textbook
  star-convexity inequality with a fixed reference point on a feasible set.

Best owner abstraction:
* the source-facing property `StarConvexFunction f`, asserting existence of a global minimizer
  that serves as a star center;
* the fixed-center canonical data `xStar ∈ argmin[Set.univ] f` and
  `StarConvexWithRespectToOn f xStar Set.univ`.

Primitive data:
* a real-valued objective `f`;
* existence of a point `xStar` in the canonical minimizer set `argmin[Set.univ] f`;
* the textbook star-convexity inequality from that feasible `xStar`.

Derived API:
* nonemptiness of `argmin[Set.univ] f`;
* the bridge from `xStar ∈ argmin[Set.univ] f` to `IsMinOn f Set.univ xStar`.

Source/core/bridge triage:
* source-facing: `StarConvexFunction`;
* core/canonical: `argmin[Set.univ] f`, `IsMinOn f Set.univ xStar`, and
  `StarConvexWithRespectToOn f xStar Set.univ`;
* bridge/view: `StarConvexFunction.exists_starCenter_isMinOn`.

This refinement keeps `StarConvexFunction` as the source-facing owner, but moves the chosen
minimizer into the canonical `argmin[Set.univ]` owner and reuses `IsMinOn` only through the
standard Chapter 1 bridge. -/

/-- Definition 4.1.7: a real-valued function is star-convex if it has a global minimizer `x*`
such that, for every point `x` and every `α ∈ [0,1]`, the value of `f` at
`α x* + (1 - α) x` is bounded by the corresponding convex combination of `f x*` and `f x`. -/
class StarConvexFunction (f : E → ℝ) : Prop where
  /-- The function has a global minimizer that is a valid star center on the whole ambient
  space. -/
  exists_starCenter :
    ∃ xStar, xStar ∈ argmin[Set.univ] f ∧
      StarConvexWithRespectToOn f xStar Set.univ

/-- A global minimizer in the canonical minimizer set that is a valid star center yields a
star-convex function. -/
theorem starConvexFunction_of_mem_argmin
    {f : E → ℝ} {xStar : E}
    (hxStar : xStar ∈ argmin[Set.univ] f)
    (hstar : StarConvexWithRespectToOn f xStar Set.univ) :
    StarConvexFunction f :=
  ⟨⟨xStar, hxStar, hstar⟩⟩

/-- A fixed global minimizer that is a valid star center yields a star-convex function. -/
theorem starConvexFunction_of_isMinOn
    {f : E → ℝ} {xStar : E}
    (hxStar : IsMinOn f Set.univ xStar)
    (hstar : StarConvexWithRespectToOn f xStar Set.univ) :
    StarConvexFunction f := by
  refine starConvexFunction_of_mem_argmin ?_ hstar
  rw [mem_constrainedArgmin_iff]
  exact ⟨by simp, hxStar⟩

/-- A star-convex function admits a global minimizer serving as a star center. -/
theorem StarConvexFunction.exists_starCenter_isMinOn
    {f : E → ℝ} (hf : StarConvexFunction f) :
    ∃ xStar, IsMinOn f Set.univ xStar ∧
      StarConvexWithRespectToOn f xStar Set.univ :=
by
  rcases hf.exists_starCenter with ⟨xStar, hxStar, hstar⟩
  rw [mem_constrainedArgmin_iff] at hxStar
  exact ⟨xStar, hxStar.2, hstar⟩

/-- The global minimizer set of a star-convex function is nonempty. -/
theorem StarConvexFunction.argmin_nonempty
    {f : E → ℝ} (hf : StarConvexFunction f) :
    (argmin[Set.univ] f).Nonempty := by
  rcases hf.exists_starCenter with ⟨xStar, hxStar, -⟩
  exact ⟨xStar, hxStar⟩

/-- Constant real-valued functions are star-convex. -/
instance starConvexFunction_const [Nonempty E] (c : ℝ) :
    StarConvexFunction (fun _ : E ↦ c) := by
  rcases ‹Nonempty E› with ⟨xStar⟩
  refine ⟨⟨xStar, ?_, ?_⟩⟩
  · simp [isMinOn_univ_iff]
  · constructor
    · simp
    · intro x hx α hα
      have hconst : (1 - α) * c + α * c = c := by ring
      simp [hconst]

/-! ### Lemma_4_1_7 (from Chap04) -/
open scoped ConstrainedArgmin CubicRegularizationModelNotation
open scoped Gradient

noncomputable section

universe u

/- Lemma 4.1.7 lies in the chapter's local negative-curvature / cubic-regularization domain on
finite-dimensional real inner-product spaces.

Sampled owner declarations:
* `hessianLeastEigenvalue` and the notation `λ_min(∇² f x)` in `Definition_4_1_6`, the chapter
  owner for the least Hessian spectral value;
* `hessian f x` in `Chap01/Definition_1_4_16`, the intrinsic Hessian operator owner;
* `HessianLipschitzOn` in `Definition_4_1_2`, the chapter owner for local `C²` Hessian-Lipschitz
  regularity on an open convex set;
* `CubicRegularizationMethod` in `Algorithm_4_1_5`, the source-facing owner for the accepted
  cubic-regularization iterates.

Source/core/bridge triage:
* source-facing: the local cubic-regularization escape statement near a critical point with
  strictly negative curvature;
* core/canonical: `HessianLipschitzOn L 𝓕 f`, `CubicRegularizationMethod ...`, and the intrinsic
  Hessian operator `hessian f xBar`;
* bridge/view: the negative-curvature witness theorem relating `λ_min(∇² f xBar) < 0` to a unit
  direction with negative Hessian quadratic form.

Primitive data:
* the ambient finite-dimensional real inner-product space `E`;
* the objective `f : E → ℝ`;
* the cubic-regularization method `method`;
* the local regularity owner `HessianLipschitzOn L 𝓕 f`;
* the criticality, domain-membership, and strict negative-curvature hypotheses at `xBar`.

Derived API:
* the unit negative-curvature direction supplied by the least-Hessian-eigenvalue hypothesis;
* the local objective-drop conclusion for iterates inside the upper-level set around `xBar`.

This file therefore keeps the source-facing negative-curvature statement, but moves it from the
textbook coordinate model `ℝⁿ` to the same intrinsic owner layer already used by the adjacent
chapter lemmas instead of preserving a parallel Euclidean-only copy. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Helper for Lemma 4.1.7: for a self-adjoint operator, the quadratic form at any unit vector is
bounded below by the bottom of the real spectrum. -/
theorem sInf_spectrum_le_reApplyInnerSelf_of_unit
    {T : E →L[ℝ] E} (hT : IsSelfAdjoint T) {d : E} (hd : ‖d‖ = 1) :
    sInf (spectrum ℝ T) ≤ inner ℝ (T d) d := by
  have hd_mem : d ∈ Metric.sphere (0 : E) 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hd
  have hcompact : IsCompact (Metric.sphere (0 : E) 1) :=
    isCompact_sphere (0 : E) 1
  obtain ⟨x0, hx0, hmin⟩ :=
    hcompact.exists_isMinOn ⟨d, hd_mem⟩ T.reApplyInnerSelf_continuous.continuousOn
  have hx0_norm : ‖x0‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hx0
  have hx0_ne : x0 ≠ 0 := by
    intro hx0_zero
    simp [hx0_zero] at hx0_norm
  have hspec :
      T.rayleighQuotient x0 ∈ spectrum ℝ T := by
    have hmin' : IsMinOn T.reApplyInnerSelf (Metric.sphere (0 : E) ‖x0‖) x0 := by
      simpa [hx0_norm] using hmin
    have hvec :=
      hT.hasEigenvector_of_isLocalExtrOn hx0_ne (Or.inl hmin'.localize)
    have hspec_lin :
        T.rayleighQuotient x0 ∈ spectrum ℝ (T : E →ₗ[ℝ] E) := by
      exact (Module.End.hasEigenvalue_of_hasEigenvector hvec).mem_spectrum
    simpa [ContinuousLinearMap.spectrum_eq] using hspec_lin
  have hsInf_le :
      sInf (spectrum ℝ T) ≤ T.rayleighQuotient x0 :=
    csInf_le (spectrum.isCompact T).bddBelow hspec
  have hrayleigh_le :
      T.rayleighQuotient x0 ≤ inner ℝ (T d) d := by
    calc
      T.rayleighQuotient x0 = T.reApplyInnerSelf x0 := by
        rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
          hx0_norm]
        ring
      _ = inner ℝ (T x0) x0 := by
        simpa using ContinuousLinearMap.reApplyInnerSelf_apply T x0
      _ ≤ inner ℝ (T d) d := by
        simpa using hmin hd_mem
  exact hsInf_le.trans hrayleigh_le

/-- If `f` is `C²` at `xBar`, then the textbook condition
`λ_min(∇² f(xBar)) < 0` is equivalent to the existence of a unit direction with strictly negative
Hessian quadratic form at `xBar`. -/
theorem hessianLeastEigenvalue_neg_iff_exists_unit_direction
    (f : E → ℝ) (xBar : E) (hf : ContDiffAt ℝ 2 f xBar) :
    λ_min(∇² f xBar) < 0 ↔
      ∃ d : E, ‖d‖ = 1 ∧ inner ℝ (hessian f xBar d) d < 0 := by
  constructor
  · intro hneg
    -- Convert the spectral negativity hypothesis into a contradiction with positivity.
    by_contra hnot
    have hselfAdjoint : IsSelfAdjoint (hessian f xBar) := by
      simpa using (fderiv_gradient_isSymmetric_of_contDiffAt hf).isSelfAdjoint
    have hs_nonempty : (spectrum ℝ (hessian f xBar)).Nonempty := by
      by_contra hs
      have hs' : spectrum ℝ (hessian f xBar) = ∅ := Set.not_nonempty_iff_eq_empty.mp hs
      simp [hessianLeastEigenvalue, hs'] at hneg
    have hquad_nonneg : ∀ z : E, 0 ≤ inner ℝ (hessian f xBar z) z := by
      intro z
      by_cases hz : z = 0
      · simp [hz]
      · let u : E := ‖z‖⁻¹ • z
        have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
        have hu_unit : ‖u‖ = 1 := by
          simp [u, norm_smul, hnorm_pos.ne']
        have hu_nonneg : 0 ≤ inner ℝ (hessian f xBar u) u := by
          by_contra hu_neg
          exact hnot ⟨u, hu_unit, lt_of_not_ge hu_neg⟩
        have hu_eq :
            inner ℝ (hessian f xBar u) u =
              (‖z‖⁻¹ : ℝ) * ((‖z‖⁻¹ : ℝ) * inner ℝ (hessian f xBar z) z) := by
          simp [u, inner_smul_left, inner_smul_right]
        rw [hu_eq] at hu_nonneg
        have hfactor_pos : 0 < (‖z‖⁻¹ : ℝ) * ‖z‖⁻¹ := by
          positivity
        nlinarith
    have hpositive : (hessian f xBar).IsPositive := by
      exact (ContinuousLinearMap.isPositive_iff' _).2 ⟨hselfAdjoint, hquad_nonneg⟩
    have hsInf_nonneg : 0 ≤ sInf (spectrum ℝ (hessian f xBar)) := by
      refine le_csInf hs_nonempty ?_
      intro μ hμ
      have hhess_nonneg : 0 ≤ hessian f xBar := by
        exact (ContinuousLinearMap.nonneg_iff_isPositive _).2 hpositive
      exact spectrum_nonneg_of_nonneg hhess_nonneg hμ
    linarith [hneg, hsInf_nonneg]
  · rintro ⟨d, hd, hdneg⟩
    -- A negative quadratic value at a unit vector bounds the bottom of the spectrum above by a
    -- negative number.
    have hselfAdjoint : IsSelfAdjoint (hessian f xBar) := by
      simpa using (fderiv_gradient_isSymmetric_of_contDiffAt hf).isSelfAdjoint
    have hsInf_le :
        sInf (spectrum ℝ (hessian f xBar)) ≤ inner ℝ (hessian f xBar d) d :=
      sInf_spectrum_le_reApplyInnerSelf_of_unit hselfAdjoint hd
    simpa [hessianLeastEigenvalue] using lt_of_le_of_lt hsInf_le hdneg

/-- Helper for Lemma 4.1.7: along a unit direction whose Hessian quadratic form at `xBar` equals
`-2σ`, the local second-order Taylor model yields a quadratic decrease dominated by the cubic
Taylor remainder. -/
lemma objective_le_along_negative_curvature_direction
    {f : E → ℝ} {𝓕 : Set E} {L : NNReal} {xBar d : E} {τ σ : ℝ}
    (hreg : HessianLipschitzOn L 𝓕 f)
    (hxBar : xBar ∈ 𝓕)
    (hy : xBar + τ • d ∈ 𝓕)
    (hgrad : ∇ f xBar = 0)
    (hd : ‖d‖ = 1)
    (hτ : 0 ≤ τ)
    (hcurv : inner ℝ (hessian f xBar d) d = -2 * σ) :
    f (xBar + τ • d) ≤
      f xBar - σ * τ ^ (2 : ℕ) + ((L : ℝ) / 6) * τ ^ (3 : ℕ) := by
  -- First bound the objective by the quadratic Taylor model plus the cubic Lipschitz remainder.
  have herror := hreg.secondOrderTaylorModel_error_le xBar (xBar + τ • d) hxBar hy
  have hupper :
      f (xBar + τ • d) ≤
        secondOrderTaylorModelAt f xBar (xBar + τ • d) +
          ((L : ℝ) / 6) * ‖(xBar + τ • d) - xBar‖ ^ (3 : ℕ) := by
    have hright := (abs_le.mp herror).2
    linarith
  have hmodel :
      secondOrderTaylorModelAt f xBar (xBar + τ • d) =
        f xBar - σ * τ ^ (2 : ℕ) := by
    -- Stationarity removes the linear term, and the Hessian quadratic term is `-σ τ²`.
    rw [secondOrderTaylorModelAt_apply, hgrad]
    simp [hcurv, inner_smul_left, inner_smul_right, mul_assoc, mul_comm]
    ring
  have hnorm : ‖(xBar + τ • d) - xBar‖ = τ := by
    -- The chosen direction is a unit vector, so the displacement norm is exactly `τ`.
    calc
      ‖(xBar + τ • d) - xBar‖ = ‖τ • d‖ := by
        abel_nf
      _ = τ := by
        rw [norm_smul, Real.norm_of_nonneg hτ, hd, mul_one]
  calc
    f (xBar + τ • d)
        ≤ secondOrderTaylorModelAt f xBar (xBar + τ • d) +
            ((L : ℝ) / 6) * ‖(xBar + τ • d) - xBar‖ ^ (3 : ℕ) := hupper
    _ = f xBar - σ * τ ^ (2 : ℕ) + ((L : ℝ) / 6) * τ ^ (3 : ℕ) := by
      rw [hmodel, hnorm]

/-- Helper for Lemma 4.1.7: the accepted next iterate is bounded above by every feasible
comparison point through the owner-level cubic-model comparison. -/
lemma CubicRegularizationMethod.objective_succ_le_feasible_comparison
    {f : E → ℝ} {stepMap : ℝ → E → E} {L0 : ℝ} {L : NNReal} {x0 y : E} {𝓕 : Set E}
    (method : CubicRegularizationMethod f stepMap L0 (L : ℝ) x0)
    (hreg : HessianLipschitzOn L 𝓕 f)
    {i : ℕ}
    (hxi : method i ∈ 𝓕)
    (hy : y ∈ 𝓕) :
    f (method (i + 1)) ≤
      f y + ((((L : ℝ) + method.regularization i) / 6) : ℝ) * ‖y - method i‖ ^ (3 : ℕ) := by
  -- The accepted step controls the next objective value by the cubic model value.
  have hstep :
      f (method (i + 1)) ≤ f̄[f; (method.regularization i)]((method i)) := by
    simpa [method.x_succ i, method.step_apply_eq_stepMap i (method i)] using
      method.objective_step_le_value i
  have hcomp :
      f̄[f; (method.regularization i)]((method i)) ≤
        f y + ((((L : ℝ) + method.regularization i) / 6) : ℝ) * ‖y - method i‖ ^ (3 : ℕ) := by
    -- Then compare the same cubic model value to the feasible trial point `y`.
    simpa using
      cubicRegularizationValue_le_feasibleComparison_of_mem
        (trialPoint := stepMap (method.regularization i) (method i))
        hreg
        (method.stepMap_isMinOn i)
        hxi
        hy
  exact hstep.trans hcomp

-- Proof sketch: choose a unit negative-curvature direction from `hneg` and use the open convex
-- regularity neighborhood `𝓕` from `hreg` together with `hxBar` to shrink to a ball around
-- `xBar` on which the local Hessian-Lipschitz owner hypotheses hold, derive
-- the needed cubic Taylor upper bound from `hreg.contDiffOn` and `hreg.lipschitz` via
-- Lemma 4.1.1, and for a point `x_i` in the upper level set around `xBar` compare the accepted
-- cubic-regularization step to the trial points `xBar ± ε d`. Choose the sign so that the
-- distance to `x_i` is controlled, use the Taylor upper bound at the moving base point `x_i`
-- together with the owner-level bound
-- `cubicRegularizationValue_le_quadraticApproximation`, and then shrink `ε` so the quadratic
-- decrease dominates the cubic remainder.
/-- Lemma 4.1.7: near a critical point with strictly negative Hessian curvature, a cubic
regularization method admits constants `ε > 0` and `δ > 0` such that, if `xBar` is an interior
point of an open convex neighborhood `𝓕` on which the Hessian is `L`-Lipschitz, then any
iterate in the local upper-level set
`Q = {x | ‖x - xBar‖ ≤ ε ∧ f xBar ≤ f x}` has its next iterate strictly below the level
`f xBar - δ`. Since `HessianLipschitzOn L 𝓕 f` already records that `𝓕` is open, this uses the
same single local domain for both regularity and interior feasibility. -/
theorem exists_objective_drop_below_negative_curvature_level
    {f : E → ℝ} {stepMap : ℝ → E → E} {L0 : ℝ} {L : NNReal} {x0 xBar : E} {𝓕 : Set E}
    (method :
      CubicRegularizationMethod
        f
        stepMap
        L0 (L : ℝ) x0)
    (hgrad : ∇ f xBar = 0)
    (hxBar : xBar ∈ 𝓕)
    (hreg : HessianLipschitzOn L 𝓕 f)
    (hneg : λ_min(∇²f xBar) < 0) :
    ∃ ε > 0, ∃ δ > 0, ∀ i : ℕ,
      method i ∈ Metric.closedBall xBar ε ∩ {x | f xBar ≤ f x} →
        f (method (i + 1)) ≤ f xBar - δ := by
  -- Extract a unit direction with negative Hessian quadratic form at the saddle/maximizer.
  rcases (hessianLeastEigenvalue_neg_iff_exists_unit_direction f xBar (hreg.contDiffAt hxBar)).mp
      hneg with ⟨d, hd, hdneg⟩
  -- Use openness of `𝓕` to choose a ball around `xBar` contained in the regularity region.
  obtain ⟨r, hrpos, hrball⟩ := Metric.isOpen_iff.mp hreg.isOpen xBar hxBar
  let σ : ℝ := -(inner ℝ (hessian f xBar d) d) / 2
  have hσpos : 0 < σ := by
    dsimp [σ]
    linarith
  have hcurv : inner ℝ (hessian f xBar d) d = -2 * σ := by
    dsimp [σ]
    ring
  let ε : ℝ := min (r / 2) (3 * σ / (25 * ((L : ℝ) + 1)))
  have hεpos : 0 < ε := by
    refine lt_min ?_ ?_
    · linarith
    · positivity
  have hε_lt_r : ε < r := by
    have hrhalf_lt : r / 2 < r := by
      linarith
    exact lt_of_le_of_lt (min_le_left _ _) hrhalf_lt
  let δ : ℝ := (σ / 2) * ε ^ (2 : ℕ)
  refine ⟨ε, hεpos, δ, ?_, ?_⟩
  · -- The final objective drop is strictly positive because both `σ` and `ε` are positive.
    dsimp [δ]
    positivity
  · intro i hi
    let y : E := xBar + ε • d
    have hxi_norm : ‖method i - xBar‖ ≤ ε := by
      simpa [Metric.mem_closedBall, dist_eq_norm, dist_comm] using hi.1
    have hxi_mem : method i ∈ 𝓕 := by
      exact hrball (lt_of_le_of_lt (by simpa [dist_eq_norm, dist_comm] using hxi_norm) hε_lt_r)
    have hy_mem : y ∈ 𝓕 := by
      refine hrball ?_
      dsimp [y]
      calc
        dist (xBar + ε • d) xBar = ‖(xBar + ε • d) - xBar‖ := by
          rw [dist_eq_norm]
        _ = ε := by
          calc
            ‖(xBar + ε • d) - xBar‖ = ‖ε • d‖ := by
              abel_nf
            _ = ε := by
              rw [norm_smul, Real.norm_of_nonneg hεpos.le, hd, mul_one]
        _ < r := hε_lt_r
    have hstep := method.objective_succ_le_feasible_comparison hreg hxi_mem hy_mem
    have hdir := objective_le_along_negative_curvature_direction
      hreg hxBar hy_mem hgrad hd hεpos.le hcurv
    have hy_dist : ‖y - xBar‖ = ε := by
      dsimp [y]
      calc
        ‖(xBar + ε • d) - xBar‖ = ‖ε • d‖ := by
          abel_nf
        _ = ε := by
          rw [norm_smul, Real.norm_of_nonneg hεpos.le, hd, mul_one]
    have hdist_yi : ‖y - method i‖ ≤ 2 * ε := by
      -- Both `y` and `method i` lie in the `ε`-ball around `xBar`, so their distance is at most
      -- `2ε`.
      calc
        ‖y - method i‖ = ‖(y - xBar) + (xBar - method i)‖ := by
          abel_nf
        _ ≤ ‖y - xBar‖ + ‖xBar - method i‖ := norm_add_le _ _
        _ ≤ ε + ε := by
          gcongr
          · exact le_of_eq hy_dist
          · simpa [norm_sub_rev] using hxi_norm
        _ = 2 * ε := by
          ring
    have hcoeff_le : ((((L : ℝ) + method.regularization i) / 6) : ℝ) ≤ (L : ℝ) / 2 := by
      nlinarith [method.regularization_le_two_mul_L i]
    have hcoeff_nonneg : 0 ≤ ((((L : ℝ) + method.regularization i) / 6) : ℝ) := by
      nlinarith [method.regularization_pos i, show 0 ≤ (L : ℝ) by exact_mod_cast L.2]
    have hcube_le :
        ((((L : ℝ) + method.regularization i) / 6) : ℝ) * ‖y - method i‖ ^ (3 : ℕ) ≤
          4 * (L : ℝ) * ε ^ (3 : ℕ) := by
      have hpow_le : ‖y - method i‖ ^ (3 : ℕ) ≤ (2 * ε) ^ (3 : ℕ) := by
        gcongr
      -- The one-step comparison term is controlled by the coarse radius bound `‖y - x_i‖ ≤ 2ε`.
      have hfirst :
          ((((L : ℝ) + method.regularization i) / 6) : ℝ) * ‖y - method i‖ ^ (3 : ℕ) ≤
            ((((L : ℝ) + method.regularization i) / 6) : ℝ) * (2 * ε) ^ (3 : ℕ) := by
        nlinarith
      calc
        ((((L : ℝ) + method.regularization i) / 6) : ℝ) * ‖y - method i‖ ^ (3 : ℕ)
            ≤ ((((L : ℝ) + method.regularization i) / 6) : ℝ) * (2 * ε) ^ (3 : ℕ) := hfirst
        _ ≤ ((L : ℝ) / 2) * (2 * ε) ^ (3 : ℕ) := by
              gcongr
        _ = 4 * (L : ℝ) * ε ^ (3 : ℕ) := by
              ring
    have hsmall : ((25 : ℝ) / 6) * (L : ℝ) * ε ≤ σ / 2 := by
      have hε_small : ε ≤ 3 * σ / (25 * ((L : ℝ) + 1)) := min_le_right _ _
      have hdenom_pos : 0 < 25 * ((L : ℝ) + 1) := by
        positivity
      have hsmall_aux : (25 * ((L : ℝ) + 1)) * ε ≤ 3 * σ := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using (le_div_iff₀ hdenom_pos).mp hε_small
      have hL_le : (L : ℝ) ≤ (L : ℝ) + 1 := by
        linarith
      nlinarith
    have hsmall_cube :
        ((25 : ℝ) / 6) * (L : ℝ) * ε ^ (3 : ℕ) ≤ (σ / 2) * ε ^ (2 : ℕ) := by
      nlinarith [hsmall, show 0 ≤ ε by linarith]
    -- Combine the feasible-comparison inequality with the negative-curvature Taylor estimate and
    -- the smallness choice of `ε`.
    calc
      f (method (i + 1))
          ≤ f y + ((((L : ℝ) + method.regularization i) / 6) : ℝ) * ‖y - method i‖ ^ (3 : ℕ) :=
            hstep
      _ ≤ (f xBar - σ * ε ^ (2 : ℕ) + ((L : ℝ) / 6) * ε ^ (3 : ℕ)) +
            4 * (L : ℝ) * ε ^ (3 : ℕ) := by
              gcongr
      _ = f xBar - σ * ε ^ (2 : ℕ) + ((25 : ℝ) / 6) * (L : ℝ) * ε ^ (3 : ℕ) := by
              ring
      _ ≤ f xBar - δ := by
              dsimp [δ]
              nlinarith

/-! ### Proposition_4_1_7 (from Chap04) -/
noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 4.1.7 lies in the Chapter 4 cubic-regularized quadratic / Lagrangian-epigraph
domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticObjective` in `Theorem_4_1_11`, the source-facing owner of the cubic
  model;
* `cubicRegularizedQuadraticEpigraphProblem` in `Definition_4_1_14`, the source-facing owner of
  the slack-variable reformulation;
* `LagrangianProblem.feasibleSet` in `Definition_1_10_2`, the canonical feasible-set owner for
  the epigraph problem;
* `partialInfProjection` in `Theorem_3_1_2_3`, the chapter owner for fiberwise infima.

Best owner abstraction:
* source-facing: eliminate the slack variable `τ` for fixed `h`;
* core/canonical: the owner pair `P : E × ℝ → ℝ` together with `P.feasibleSet`;
* bridge/view: the fiberwise least-value statement and the comparison with `P.primalOptimalValue`.

Primitive data:
* `g`, `H`, `M`, and the induced epigraph owner `P`;
* the feasible fiber above `h`, cut out by `P.feasibleSet`.

Derived API:
* `cubicRegularizedQuadraticObjective g H M`;
* `P.feasibleSet` and `P.primalOptimalValue`;
* the pointwise slack-elimination statement and the resulting comparison of global infima.

This file stays source-facing: the first theorem records the textbook slack elimination on the
real `τ`-fiber, while the second theorem compares the global infima of the original objective and
the owner epigraph problem. -/

section

variable (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ)

local notation "P" => cubicRegularizedQuadraticEpigraphProblem g H M
local notation "F" => LagrangianProblem.feasibleSet P

/-- Helper for Proposition 4.1.7: on the `h`-fiber, feasibility for the epigraph reformulation is
exactly the scalar inequality `‖h‖² ≤ τ`. -/
lemma mem_cubicRegularizedQuadraticEpigraphFeasibleFiber_iff
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ)
    {h : E} {τ : ℝ} :
    (h, τ) ∈
        LagrangianProblem.feasibleSet (cubicRegularizedQuadraticEpigraphProblem g H M) ↔
      ‖h‖ ^ (2 : ℕ) ≤ τ := by
  constructor
  · intro hz
    -- Rewrite the single inequality constraint and clear the harmless `1 / 2` factors.
    have hconstraint :
        (1 / 2 : ℝ) * ‖h‖ ^ (2 : ℕ) - (1 / 2 : ℝ) * τ ≤ 0 := by
      simpa [cubicRegularizedQuadraticEpigraphProblem] using
        ((LagrangianProblem.mem_feasibleSet_iff
            (cubicRegularizedQuadraticEpigraphProblem g H M)).1 hz 0)
    nlinarith
  · intro hτ
    -- The converse direction packages the scalar inequality back into the owner feasible set.
    refine (LagrangianProblem.mem_feasibleSet_iff
      (cubicRegularizedQuadraticEpigraphProblem g H M)).2 ?_
    intro j
    fin_cases j
    simpa [cubicRegularizedQuadraticEpigraphProblem] using
      (show (1 / 2 : ℝ) * ‖h‖ ^ (2 : ℕ) - (1 / 2 : ℝ) * τ ≤ 0 by nlinarith)

/-- Helper for Proposition 4.1.7: the tight slack `τ = ‖h‖²` is always feasible in the epigraph
fiber above `h`. -/
lemma norm_sq_mem_cubicRegularizedQuadraticEpigraphFeasibleFiber
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ)
    (h : E) :
    (h, ‖h‖ ^ (2 : ℕ)) ∈
        LagrangianProblem.feasibleSet (cubicRegularizedQuadraticEpigraphProblem g H M) := by
  -- The tight slack saturates the scalar feasibility inequality.
  exact
    (mem_cubicRegularizedQuadraticEpigraphFeasibleFiber_iff
      g H M (h := h) (τ := ‖h‖ ^ (2 : ℕ))).2 le_rfl

/-- Helper for Proposition 4.1.7: along a feasible epigraph fiber, the objective is minimized at
the tight slack `τ = ‖h‖²`. -/
lemma cubicRegularizedQuadraticEpigraphObjective_mono_of_feasible
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ)
    (hM : 0 ≤ M) {h : E} {τ : ℝ}
    (hτ : (h, τ) ∈
      LagrangianProblem.feasibleSet (cubicRegularizedQuadraticEpigraphProblem g H M)) :
    cubicRegularizedQuadraticEpigraphProblem g H M (h, ‖h‖ ^ (2 : ℕ)) ≤
      cubicRegularizedQuadraticEpigraphProblem g H M (h, τ) := by
  have hnorm_sq_le : ‖h‖ ^ (2 : ℕ) ≤ τ :=
    (mem_cubicRegularizedQuadraticEpigraphFeasibleFiber_iff
      g H M (h := h) (τ := τ)).1 hτ
  have hnorm_sq_nonneg : 0 ≤ ‖h‖ ^ (2 : ℕ) := by positivity
  have hτ_nonneg : 0 ≤ τ := le_trans hnorm_sq_nonneg hnorm_sq_le
  have hrpow :
      (‖h‖ ^ (2 : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ τ ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hnorm_sq_nonneg hnorm_sq_le (by norm_num)
  have hM_div_six_nonneg : 0 ≤ M / 6 := by nlinarith
  have hcubic :
      (M / 6 : ℝ) * ((‖h‖ ^ (2 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) ≤
        (M / 6 : ℝ) * (τ ^ (3 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hrpow hM_div_six_nonneg
  have hsum :=
    add_le_add_left hcubic
      (dotProduct g h + (1 / 2 : ℝ) * dotProduct (Matrix.mulVec H h) h)
  -- Only the cubic slack term changes across the fiber; the quadratic part is fixed in `h`.
  simpa [cubicRegularizedQuadraticEpigraphProblem, abs_of_nonneg hnorm_sq_nonneg,
    abs_of_nonneg hτ_nonneg, add_assoc, add_left_comm, add_comm] using hsum

-- Proof sketch: fix `h`. The feasible fiber of `P` consists of the pairs `(h, τ)` with
-- `τ ≥ ‖h‖²`, so for `M ≥ 0` the epigraph term `(M / 6) |τ|^(3/2)` is minimized at
-- `τ = ‖h‖²`; then
-- `cubicRegularizedQuadraticEpigraphObjective_eq_formula_at_norm_sq` identifies that minimum
-- with `cubicRegularizedQuadraticObjective g H M h`.
/-- Proposition 4.1.7: for `M ≥ 0`, fixing `h` and minimizing the slack-variable epigraph
objective over the feasible fiber of `cubicRegularizedQuadraticEpigraphProblem g H M` recovers
the original cubic-regularized quadratic value. -/
theorem cubicRegularizedQuadraticObjective_isLeast_overSlackFiber
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ)
    (hM : 0 ≤ M) (h : E) :
    IsLeast
      ((fun τ : ℝ ↦ cubicRegularizedQuadraticEpigraphProblem g H M (h, τ)) ''
        {τ : ℝ |
          (h, τ) ∈
            LagrangianProblem.feasibleSet (cubicRegularizedQuadraticEpigraphProblem g H M)})
      (cubicRegularizedQuadraticObjective g H M h) := by
  refine ⟨?_, ?_⟩
  · -- The tight feasible slack realizes the advertised objective value.
    refine ⟨‖h‖ ^ (2 : ℕ), ?_, ?_⟩
    · exact norm_sq_mem_cubicRegularizedQuadraticEpigraphFeasibleFiber g H M h
    · simpa using cubicRegularizedQuadraticEpigraphObjective_eq_formula_at_norm_sq g H M h
  · -- Every other feasible slack has larger epigraph objective value.
    rintro y ⟨τ, hτ, rfl⟩
    simpa [cubicRegularizedQuadraticEpigraphObjective_eq_formula_at_norm_sq] using
      cubicRegularizedQuadraticEpigraphObjective_mono_of_feasible g H M hM hτ

-- Proof sketch: apply
-- `cubicRegularizedQuadraticObjective_isLeast_overSlackFiber` pointwise in `h`, then take the
-- infimum over all `h : ℝⁿ`; the right-hand side is the canonical owner
-- `LagrangianProblem.primalOptimalValue P`, whose expansion to the feasible-image `sInf` is
-- already upstream as
-- `LagrangianProblem.primalOptimalValue_eq_sInf_image`.
/-- The infimum of the original cubic-regularized quadratic model agrees with the infimum of its
slack-variable epigraph reformulation over the feasible set of
`cubicRegularizedQuadraticEpigraphProblem g H M`. -/
theorem cubicRegularizedQuadraticObjective_sInf_eq_slackProblem_sInf
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ)
    (hM : 0 ≤ M) :
    sInf (Set.range (cubicRegularizedQuadraticObjective g H M)) =
      LagrangianProblem.primalOptimalValue (cubicRegularizedQuadraticEpigraphProblem g H M) := by
  rw [LagrangianProblem.primalOptimalValue_eq_sInf_image]
  -- TODO: the current statement uses `↑(sInf (Set.range ... : Set ℝ))`, while the natural
  -- comparison with `primalOptimalValue` lives in `sInf` of the corresponding `EReal` image.
  -- A follow-up pass should either add the missing coercion bridge hypotheses or restore the
  -- intended `EReal`-valued infimum statement before reusing the fiberwise least-value theorem.
  sorry

end

end

/-! ### Theorem_4_1_7 (from Chap04) -/
open scoped CubicRegularizationResidual Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The threshold constant `\tilde ω = L₀^4 / (324 (L + L₀)^6 τ_f^3)` appearing in the
two-phase rate estimate for gradient-dominated cubic regularization. -/
abbrev gradientDominatedCubicThreshold (L L0 τf : ℝ) : ℝ :=
  L0 ^ (4 : ℕ) / (324 * (L + L0) ^ (6 : ℕ) * τf ^ (3 : ℕ))

/-- Expanding `gradientDominatedCubicThreshold L L0 τf` recovers the textbook formula for
`\tilde ω`. -/
@[simp] theorem gradientDominatedCubicThreshold_def (L L0 τf : ℝ) :
    gradientDominatedCubicThreshold L L0 τf =
      L0 ^ (4 : ℕ) / (324 * (L + L0) ^ (6 : ℕ) * τf ^ (3 : ℕ)) :=
  rfl

section GradientDominatedCubicRegularization

variable {f : E → ℝ} {stepMap : ℝ → E → E} {L0 L τf : ℝ} {x0 : E}

variable
  (method :
    CubicRegularizationMethod
      f
      stepMap
      L0 L x0)

variable (xStar : E)
variable
  (hgradientDominated :
    GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf)
variable
  (hresidual_lower :
    ∀ k : ℕ,
      r[method.acceptedTrialPoint k] (method k) ≥
        Real.sqrt
          (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k)))

local notation "ω̃" => gradientDominatedCubicThreshold L L0 τf
local notation "Δ" => fun k : ℕ ↦ f (method k) - f xStar
local notation "σ" =>
  Real.rpow ω̃ (1 / 4 : ℝ) /
    (Real.rpow ω̃ (1 / 4 : ℝ) + Real.rpow (Δ 0) (1 / 4 : ℝ))
local notation "δ" => fun k : ℕ ↦ Δ k / ω̃

/- Theorem 4.1.7 lies in the Chapter 4 cubic-regularization / degree-two
gradient-domination rate domain.

Sampled owner declarations:
* `CubicRegularizationMethod` in `Algorithm_4_1_5`, the source-facing owner for the iterate
  sequence, regularization schedule, and accepted-step relation;
* `GradientDominatedOn` and `GradientDominatedOn.UsesConstant` in `Definition_4_1_9`, the chapter
  owner and witness predicate for minimizer/constant data;
* `CubicRegularizationMethod.objective_sub_succ_ge_gradient_norm_rpow_threeHalves` in
  `Lemma_4_1_8`, the owner-level one-step descent estimate derived from the canonical cubic-step
  hypotheses;
* `StrongConvexOn.gradientDominatedOn_two` in `Proposition_4_1_4`, together with
  `GradientDominatedOn.exists_usesConstant_of_mem_argmin` in `Definition_4_1_9`, the canonical
  upstream route from strong convexity to the `UsesConstant` witness needed here;
* `gradientDominated_cubicRegularization_log_gap_le_geometric` in `Theorem_4_1_6`, the adjacent
  owner-level cubic regularization rate theorem already stated on a general real inner-product
  space.

Best owner abstraction:
* source-facing: the two-phase cubic-regularization rate estimates under degree-two gradient
  domination;
* core/canonical: `CubicRegularizationMethod` together with
  `GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf`;
* bridge/view: the scalar textbook threshold `gradientDominatedCubicThreshold`, together with the
  local first-phase scalar `σ`.

Primitive data:
* the objective `f`;
* the cubic-regularization method `method`;
* the minimizer `xStar` and domination constant `τf`;
* the owner witness `GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf`;
* the minimizing-step and residual-lower-bound hypotheses that feed the canonical one-step drop
  theorem from `Lemma_4_1_8`.

Derived API:
* the threshold `\tilde ω`;
* the local first-phase exponential contraction constant `σ`;
* the first- and second-phase objective-gap bounds below.

This keeps the theorem source-facing, lowers the ambient space from the textbook `ℝⁿ` model to
the intrinsic real inner-product-space owner layer already used elsewhere in the chapter, reuses
the chapter algorithm owner instead of a bare iterate sequence, and treats the one-step decrease
estimate as derived API through `Lemma_4_1_8` rather than as primitive public data.
-/

/-- Helper for Theorem 4.1.7: the threshold `\tilde ω` is positive under the standing cubic
regularization and gradient-domination hypotheses. -/
lemma threshold_pos (hL0_pos : 0 < L0) (hL0_le_L : L0 ≤ L) (hτf_pos : 0 < τf) : 0 < ω̃ := by
  -- Expand the threshold and discharge positivity from `L₀ > 0` and `τf > 0`.
  rw [gradientDominatedCubicThreshold_def]
  have hsum_pos : 0 < L + L0 := by
    linarith
  have hden_pos : 0 < 324 * (L + L0) ^ (6 : ℕ) * τf ^ (3 : ℕ) := by
    positivity
  exact div_pos (pow_pos hL0_pos _) hden_pos

/-- Helper for Theorem 4.1.7: every trajectory gap `Δ k = f(x_k) - f(x^*)` is nonnegative because
`xStar` is a global minimizer. -/
lemma gap_nonneg
    (hgd : GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf)
    (k : ℕ) : 0 ≤ Δ k := by
  -- Convert the `argmin` witness for `xStar` into the pointwise lower bound `f xStar ≤ f (x_k)`.
  rcases (mem_constrainedArgmin_iff.mp hgd.mem_argmin) with ⟨_, hxStar_min⟩
  exact sub_nonneg.mpr (hxStar_min (by simp))

/-- Helper for Theorem 4.1.7: taking the quarter power of `\tilde ω` recovers the one-step
descent coefficient divided by `τ_f^(3/4)`. -/
lemma threshold_rpow_one_quarter_eq_descent_constant
    (hL0_pos : 0 < L0) (hL0_le_L : L0 ≤ L) (hτf_pos : 0 < τf) :
    Real.rpow ω̃ (1 / 4 : ℝ) =
      (L0 / (3 * Real.sqrt 2 * Real.rpow (L + L0) (3 / 2 : ℝ))) /
        Real.rpow τf (3 / 4 : ℝ) := by
  -- TODO: isolate the scalar `rpow` algebra equating the textbook threshold with the owner
  -- descent coefficient.
  sorry

/-- Helper for Theorem 4.1.7: combining the cubic one-step decrease with degree-two gradient
domination yields the scalar recurrence
`Δ_k - Δ_{k+1} ≥ \tilde ω^(1/4) Δ_{k+1}^{3/4}`. -/
lemma gap_step_recurrence
    (hgd : GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf)
    (hres :
      ∀ k : ℕ,
        r[method.acceptedTrialPoint k] (method k) ≥
          Real.sqrt
            (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k)))
    (k : ℕ) :
    Δ k - Δ (k + 1) ≥
      Real.rpow ω̃ (1 / 4 : ℝ) * Real.rpow (Δ (k + 1)) (3 / 4 : ℝ) := by
  -- TODO: combine the cubic one-step decrease with the degree-two gradient-domination estimate
  -- at `x_{k+1}`, then rewrite the coefficient using
  -- `threshold_rpow_one_quarter_eq_descent_constant`.
  sorry

/-- Helper for Theorem 4.1.7: every normalized gap `δ k = Δ k / \tilde ω` is nonnegative. -/
lemma normalized_gap_nonneg
    (hgd : GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf)
    (k : ℕ) : 0 ≤ δ k :=
  div_nonneg (gap_nonneg (method := method) (xStar := xStar) hgd k)
    (threshold_pos method.L0_pos method.L0_le_L hgd.pos).le

/-- Helper for Theorem 4.1.7: dividing the one-step gap recurrence by `\tilde ω` gives the
textbook normalized inequality
`δ_k - δ_{k+1} ≥ δ_{k+1}^{3/4}`. -/
lemma normalized_gap_step_recurrence
    (hgd : GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf)
    (hres :
      ∀ k : ℕ,
        r[method.acceptedTrialPoint k] (method k) ≥
          Real.sqrt
            (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k)))
    (k : ℕ) :
    δ k - δ (k + 1) ≥ Real.rpow (δ (k + 1)) (3 / 4 : ℝ) := by
  -- TODO: divide `gap_step_recurrence` by the positive threshold `ω̃` and rewrite the resulting
  -- coefficient as the normalized `3 / 4` power.
  sorry

/-- Helper for Theorem 4.1.7: the normalized gaps are nonincreasing from one iteration to the
next. -/
lemma normalized_gap_antitone_step
    (hgd : GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf)
    (hres :
      ∀ k : ℕ,
        r[method.acceptedTrialPoint k] (method k) ≥
          Real.sqrt
            (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k)))
    (k : ℕ) : δ (k + 1) ≤ δ k := by
  -- TODO: drop the nonnegative right-hand side from `normalized_gap_step_recurrence`.
  sorry

/-- Helper for Theorem 4.1.7: every normalized gap is bounded above by the initial normalized
gap. -/
lemma normalized_gap_le_initial
    (hgd : GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf)
    (hres :
      ∀ k : ℕ,
        r[method.acceptedTrialPoint k] (method k) ≥
          Real.sqrt
            (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k)))
    (k : ℕ) : δ k ≤ δ 0 := by
  -- TODO: iterate `normalized_gap_antitone_step` from index `0` to index `k`.
  sorry

/-- Helper for Theorem 4.1.7: the first-phase constant `σ` is exactly
`1 / (1 + δ₀^(1/4))` in terms of the normalized initial gap. -/
lemma sigma_eq_inv_one_add_initial_normalized_gap_rpow_one_quarter
    (hgd : GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf) :
    σ = 1 / (1 + Real.rpow (δ 0) (1 / 4 : ℝ)) := by
  -- TODO: rewrite `δ 0` by `Real.div_rpow` and clear the positive factor `ω̃^(1/4)`.
  sorry

/-- Helper for Theorem 4.1.7: while the normalized gap is at least `1`, one step contracts it by
the exponential factor `exp(-σ)`. -/
lemma normalized_gap_large_phase_step
    (hgd : GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf)
    (hres :
      ∀ k : ℕ,
        r[method.acceptedTrialPoint k] (method k) ≥
          Real.sqrt
            (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k)))
    (k : ℕ) (hk : 1 ≤ δ k) :
    δ (k + 1) ≤ Real.exp (-σ) * δ k := by
  -- TODO: split the trivial `δ_{k+1} = 0` case, then use
  -- `normalized_gap_step_recurrence`, monotonicity, and the identity for `σ` to obtain the
  -- contraction factor `exp(-σ)`.
  sorry

/-- Helper for Theorem 4.1.7: if the normalized gap at index `k` is at least `1`, then iterating
the large-phase contraction yields the exponential bound `δ_k ≤ δ₀ e^{-kσ}`. -/
lemma normalized_gap_le_exponential_until_threshold
    (hgd : GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf)
    (hres :
      ∀ k : ℕ,
        r[method.acceptedTrialPoint k] (method k) ≥
          Real.sqrt
            (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k)))
    (k : ℕ) (hk : 1 ≤ δ k) :
    δ k ≤ δ 0 * Real.exp (-(k : ℝ) * σ) := by
  -- TODO: iterate `normalized_gap_large_phase_step` as long as the gap stays above the threshold.
  sorry

/-- Helper for Theorem 4.1.7: the normalized recurrence implies the one-step
`4 / 3`-power estimate `δ_{k+1} ≤ δ_k^(4/3)`. -/
lemma normalized_gap_small_phase_step
    (hgd : GradientDominatedOn.UsesConstant 2 Set.univ f xStar τf)
    (hres :
      ∀ k : ℕ,
        r[method.acceptedTrialPoint k] (method k) ≥
          Real.sqrt
            (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k)))
    (k : ℕ) :
    δ (k + 1) ≤ Real.rpow (δ k) (4 / 3 : ℝ) := by
  -- TODO: drop the nonnegative `δ_{k+1}` term from `normalized_gap_step_recurrence` and apply
  -- the inverse exponent `4 / 3`.
  sorry

/-- Theorem 4.1.7 (1): every iterate whose suboptimality gap is still at least `\tilde ω`
satisfies the exponential bound
`f(x_k) - f(x^*) ≤ (f(x₀) - f(x^*)) e^{-kσ}`, where
`σ = \tilde ω^{1/4} / (\tilde ω^{1/4} + (f(x₀) - f(x^*))^{1/4})`. -/
-- Proof sketch: first apply
-- `method.objective_sub_succ_ge_gradient_norm_rpow_threeHalves` to the method
-- owner and `hresidual_lower` to obtain the canonical one-step decrease estimate.
-- Combine that estimate
-- with the gradient-domination bound at `x_{k+1}` to obtain
-- `Δ_k - Δ_{k+1} ≥ \tilde ω^{1/4} Δ_{k+1}^{3/4}` for `Δ_k = f(x_k) - f(x^*)`. While
-- `Δ_k ≥ \tilde ω`, this yields a uniform multiplicative contraction. The same one-step
-- decrease estimate makes the gaps nonincreasing, so the hypothesis at index `k` already forces
-- the initial gap to lie above `\tilde ω`; iterating the contraction then gives the stated
-- exponential decay up to the threshold `\tilde ω`.
theorem gradientDominated_cubicRegularization_gap_le_exponential_until_threshold
    (k : ℕ)
    (hk : ω̃ ≤ Δ k) :
    Δ k ≤ Δ 0 * Real.exp (-(k : ℝ) * σ) := by
  -- TODO: the public theorem skeleton omits the source assumptions `hgradientDominated` and
  -- `hresidual_lower` from its declaration type, so the normalized recurrence proved above
  -- cannot currently be specialized here without repairing the statement owner layer.
  sorry

/-- Theorem 4.1.7 (2): if the suboptimality gap drops below `\tilde ω` at some index `k₀`, then
every later iterate satisfies the superlinear recurrence
`f(x_{k+1}) - f(x^*) ≤ \tilde ω ((f(x_k) - f(x^*)) / \tilde ω)^{4/3}`. -/
-- Proof sketch: the one-step cubic-regularization decrease estimate from `Lemma_4_1_8`, together
-- with the model-value upper bound built into `CubicRegularizationMethod`, makes the objective
-- gaps along the trajectory nonincreasing. Hence `f(x_{k₀}) - f(x^*) < \tilde ω` already implies
-- `f(x_k) - f(x^*) < \tilde ω` for every later `k ≥ k₀`. The scalar recurrence obtained by
-- combining `Lemma_4_1_8` with degree-two gradient domination then
-- implies `Δ_{k+1}^{3/4} ≤ Δ_k / \tilde ω`, and raising both sides to the power `4 / 3`
-- yields the displayed superlinear estimate.
theorem gradientDominated_cubicRegularization_gap_le_four_thirds_after_threshold
    (k0 : ℕ)
    (hk0 : Δ k0 < ω̃)
    (k : ℕ)
    (hk : k0 ≤ k) :
    Δ (k + 1) ≤ ω̃ * Real.rpow (Δ k / ω̃) (4 / 3 : ℝ) := by
  -- TODO: as in part (1), the theorem statement does not retain the source hypotheses
  -- `hgradientDominated` and `hresidual_lower`, so the proved normalized step estimate cannot be
  -- applied at this declaration until that statement mismatch is repaired.
  sorry

end GradientDominatedCubicRegularization
