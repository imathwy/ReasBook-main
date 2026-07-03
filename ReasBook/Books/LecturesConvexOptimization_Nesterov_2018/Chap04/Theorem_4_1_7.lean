import Mathlib
import Nesterov.Chap04.Lemma_4_1_8
import Nesterov.Chap04.Definition_4_1_9

-- Declarations for this item will be appended below by the statement pipeline.

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
