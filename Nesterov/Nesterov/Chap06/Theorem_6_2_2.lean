import Nesterov.Chap06.Algorithm_6_3
import Nesterov.Chap06.Definition_6_39
import Nesterov.Chap06.Theorem_6_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin

universe u v

section

variable
    {X : Type u} {U : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
    {Q₁ : Set X} {Q₂ : Set U}
    (hQ₁ : Convex ℝ Q₁) (hQ₂ : Convex ℝ Q₂)
    {A₀ : X →L[ℝ] StrongDual ℝ U}
    {hatf : X → ℝ} {hatφ : U → ℝ} {d₁ : X → ℝ} {d₂ : U → ℝ}
    (xμ : ℝ → U → X)
    (hxμ :
      ∀ μ : ℝ, ∀ u : U,
        xμ μ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A₀ hatf d₁ μ u))
    (uμ : ℝ → X → U)
    (huμ :
      ∀ μ : ℝ, ∀ x : X, x ∈ Q₁ →
        uμ μ x ∈ smoothedPrimalObjectiveArgmax A₀ Q₂ hatφ d₂ μ x)
    (x₀ : Q₂ → Q₁) (V : Q₂ → Q₂)
    {fμ₂ : ℝ → X → ℝ} {φμ₁ : ℝ → U → ℝ}
    {fμ₂_zero : ℝ → Q₁ → ℝ} {φ_zero : Q₂ → ℝ}
    {initialPrimalSmoothing initialDualSmoothing : ℝ}
    (initialState : Q₁ × Q₂)

/- Theorem 6.2.2 lies in the chapter's alternating excessive-gap recursion / rate domain.

Mandatory domain-style sampling before refinement:
- `algorithm_6_3_primal_smoothing` and `algorithm_6_3_dual_smoothing` in
  `Chap06/Algorithm_6_3`, the source-facing smoothing-parameter recursions of Algorithm 6.3;
- `alternatingExcessiveGapPrimalIterate` and `alternatingExcessiveGapDualIterate` in
  `Chap06/Algorithm_6_3`, the source-facing owners of the actual alternating recursion;
- `algorithm_6_3_iterates_satisfy_excessive_gap_condition` in `Chap06/Theorem_6_6`, the chapter
  owner propagating the excessive-gap certificate along the actual Algorithm 6.3 recursion;
- `satisfiesExcessiveGapCondition` in `Chap06/Theorem_6_4`, the chapter owner of the excessive-gap
  certificate;
- `raw_duality_gap_le_excessive_gap_budget` in `Chap06/Lemma_6_2_1`, the chapter owner turning an
  excessive-gap certificate into the textbook raw-gap budget estimate.

Best owner abstraction:
- source-facing: the actual Algorithm 6.3 smoothing and iterate sequences;
- core/canonical: `algorithm_6_3_iterates_satisfy_excessive_gap_condition`,
  `satisfiesExcessiveGapCondition`, and `raw_duality_gap_le_excessive_gap_budget`;
- bridge/view: the rate theorem below, which composes the canonical propagation result with the
  raw-gap budget estimate.

Primitive data:
- the feasible sets and the Chapter 6 even/odd update-owner data used by Algorithm 6.3;
- the initial smoothing parameters `μ₁,0`, `μ₂,0`;
- the feasible initial state, the canonical propagation hypotheses from `Theorem_6_6`, and the
  stagewise smoothing bounds.

Derived API:
- the stagewise excessive-gap certificate for the actual Algorithm 6.3 iterates;
- the duality-gap rate bound obtained from that certificate and the smoothing budget estimate.

The previous version still fed Theorem 6.2.2 through external smoothing sequences. This
refinement instead reuses the source-facing smoothing owners from `Algorithm_6_3`, so the rate
theorem now speaks directly about the chapter's actual recursion.
-/

local notation "μ₁" =>
  algorithm_6_3_primal_smoothing initialPrimalSmoothing

local notation "μ₂" =>
  algorithm_6_3_dual_smoothing initialDualSmoothing

local notation "x̄" =>
  alternatingExcessiveGapPrimalIterate
    hQ₁
    hQ₂
    xμ
    hxμ
    uμ
    huμ
    x₀
    V
    initialPrimalSmoothing
    initialDualSmoothing
    initialState

local notation "ū" =>
  alternatingExcessiveGapDualIterate
    hQ₁
    hQ₂
    xμ
    hxμ
    uμ
    huμ
    x₀
    V
    initialPrimalSmoothing
    initialDualSmoothing
    initialState

local notation "x̄ₑ" =>
  fun k ↦
    algorithm_6_3_even_primal_iterate
      hQ₁
      hQ₂
      xμ
      hxμ
      uμ
      huμ
      initialPrimalSmoothing
      initialDualSmoothing
      (x̄ k, ū k)
      k

local notation "ūₑ" =>
  fun k ↦
    algorithm_6_3_even_dual_iterate
      hQ₁
      hQ₂
      xμ
      hxμ
      uμ
      huμ
      initialPrimalSmoothing
      initialDualSmoothing
      (x̄ k, ū k)
      k

local notation "x̄ₒ" =>
  fun k ↦
    algorithm_6_3_odd_primal_iterate
      hQ₁
      hQ₂
      uμ
      huμ
      x₀
      initialDualSmoothing
      (x̄ k, ū k)
      k

local notation "ūₒ" =>
  fun k ↦
    algorithm_6_3_odd_dual_iterate
      hQ₂
      uμ
      huμ
      V
      initialDualSmoothing
      (x̄ k, ū k)
      k

/-- Theorem 6.2.2: if the Algorithm 6.3 iterates start from an excessive-gap pair and each even
and odd update satisfy the canonical propagation hypotheses of `Theorem_6_6`, then every iterate
pair `(x̄_k, ū_k)` of the feasible Algorithm 6.3 recursion satisfies the Chapter 6 excessive-gap
certificate; if the smoothing budget also obeys the chapter rate estimate, then the raw duality
gap satisfies the same rate bound. -/
-- Proof sketch: first propagate the excessive-gap certificate along the actual Algorithm 6.3
-- recursion by applying `algorithm_6_3_iterates_satisfy_excessive_gap_condition`; then combine
-- the stagewise smoothing estimates with the propagated certificate to bound the raw duality gap
-- by `μ₁,k D₁ + μ₂,k D₂`, and finally apply `hbudget`.
theorem algorithm_6_3_excessive_gap_and_duality_gap_rate
    {A : X →L[ℝ] U}
    {f : X → ℝ} {φ : U → ℝ} {D₁ D₂ : ℝ}
    (hzero :
      satisfiesExcessiveGapCondition
        Q₁
        Q₂
        (fμ₂ (μ₂ 0))
        (φμ₁ (μ₁ 0))
        (x̄ 0)
        (ū 0))
    (heven_step :
      ∀ k : ℕ, Even k →
        satisfiesExcessiveGapCondition
          Q₁
          Q₂
          (fμ₂ (μ₂ k))
          (φμ₁ (μ₁ k))
          (x̄ k)
          (ū k) →
        satisfiesExcessiveGapCondition
          Q₁
          Q₂
          (fμ₂ (μ₂ (k + 1)))
          (φμ₁ (μ₁ (k + 1)))
          (x̄ₑ k)
          (ūₑ k))
    (hodd_source :
      ∀ k : ℕ, Odd k →
        satisfiesExcessiveGapCondition
          Q₁
          Q₂
          (fμ₂ (μ₂ k))
          (φμ₁ (μ₁ k))
          (x̄ k)
          (ū k) →
        satisfiesExcessiveGapConditionWithMu1Zero
          (fμ₂_zero (μ₂ k))
          φ_zero
          (x̄ k)
          (ū k))
    (hodd_step :
      ∀ k : ℕ, Odd k →
        satisfiesExcessiveGapConditionWithMu1Zero
          (fμ₂_zero (μ₂ k))
          φ_zero
          (x̄ k)
          (ū k) →
        satisfiesExcessiveGapConditionWithMu1Zero
          (fμ₂_zero (μ₂ (k + 1)))
          φ_zero
          (x̄ₒ k)
          (ūₒ k))
    (hodd_target :
      ∀ k : ℕ, Odd k →
        satisfiesExcessiveGapConditionWithMu1Zero
          (fμ₂_zero (μ₂ (k + 1)))
          φ_zero
          (x̄ₒ k)
          (ūₒ k) →
        satisfiesExcessiveGapCondition
          Q₁
          Q₂
          (fμ₂ (μ₂ (k + 1)))
          (φμ₁ (μ₁ (k + 1)))
          (x̄ₒ k)
          (ūₒ k))
    (hfμ₂_lower :
      ∀ k : ℕ,
        f (x̄ k) - μ₂ k * D₂ ≤ fμ₂ (μ₂ k) (x̄ k))
    (hφμ₁_upper :
      ∀ k : ℕ,
        φμ₁ (μ₁ k) (ū k) ≤ φ (ū k) + μ₁ k * D₁)
    (hbudget :
      ∀ k : ℕ,
        μ₁ k * D₁ + μ₂ k * D₂ ≤
          (4 * ‖A‖ * Real.sqrt (D₁ * D₂)) / ((k : ℝ) + 1)) :
    ∀ k : ℕ,
      satisfiesExcessiveGapCondition
        Q₁
        Q₂
        (fμ₂ (μ₂ k))
        (φμ₁ (μ₁ k))
        (x̄ k)
        (ū k) ∧
      f (x̄ k) - φ (ū k) ≤
        (4 * ‖A‖ * Real.sqrt (D₁ * D₂)) / ((k : ℝ) + 1) := sorry

end
