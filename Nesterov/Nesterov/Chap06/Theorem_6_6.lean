import Nesterov.Chap06.Algorithm_6_3
import Nesterov.Chap06.Definition_6_39
import Nesterov.Chap06.Theorem_6_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin

universe u v

section

variable {X : Type u} {U : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable {Q₁ : Set X} {Q₂ : Set U}
variable (hQ₁ : Convex ℝ Q₁) (hQ₂ : Convex ℝ Q₂)
variable {A : X →L[ℝ] StrongDual ℝ U}
variable {hatf : X → ℝ} {hatφ : U → ℝ} {d₁ : X → ℝ} {d₂ : U → ℝ}
variable (xμ : ℝ → U → X)
variable
    (hxμ :
      ∀ μ : ℝ, ∀ u : U,
        xμ μ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ u))
variable (uμ : ℝ → X → U)
variable
    (huμ :
      ∀ μ : ℝ, ∀ x : X, x ∈ Q₁ →
        uμ μ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ x)
variable (x₀ : Q₂ → Q₁) (V : Q₂ → Q₂)
variable {fμ₂ : ℝ → X → ℝ} {φμ₁ : ℝ → U → ℝ}
variable {fμ₂_zero : ℝ → Q₁ → ℝ} {φ_zero : Q₂ → ℝ}
variable {initialPrimalSmoothing initialDualSmoothing : ℝ}
variable (initialState : Q₁ × Q₂)

/- Theorem 6.6 lies in the chapter's alternating excessive-gap propagation domain.

Primary mathematical domain:
- parity-split propagation of the Chapter 6 excessive-gap certificate along the iterates generated
  by Algorithm 6.3.

Sampled owner-style declarations:
- `algorithm_6_3_step_size` in `Chap06/Algorithm_6_3`, the Algorithm 6.3 owner of the step-size
  sequence `τ_k = 2 / (k + 3)`;
- `algorithm_6_3_primal_smoothing` and `algorithm_6_3_dual_smoothing` in
  `Chap06/Algorithm_6_3`, the source-facing owners of the smoothing recursions
  `μ₁,k`, `μ₂,k`;
- `alternatingExcessiveGapPrimalIterate` and `alternatingExcessiveGapDualIterate` in
  `Chap06/Algorithm_6_3`, the source-facing owners of the actual Algorithm 6.3 iterates;
- `satisfiesExcessiveGapCondition` in `Chap06/Theorem_6_4` and
  `satisfiesExcessiveGapConditionWithMu1Zero` in `Chap06/Definition_6_39`, the chapter owners of
  the two certificate layers used by the even and odd updates.

Best owner abstraction:
- source-facing: the actual Algorithm 6.3 iterate and smoothing sequences;
- core/canonical: the Algorithm 6.3 recursion lemmas from `Chap06/Algorithm_6_3` and the two
  Chapter 6 excessive-gap certificate predicates;
- bridge/view: the induction theorem below, which turns the one-step even and odd propagation
  rules into a certificate for every iterate.

Primitive data:
- the initial state `( \bar x₀, \bar u₀ )`;
- the initial smoothing parameters `μ₁,0`, `μ₂,0`;
- the Chapter 6 even and odd update-owner data;
- the stagewise even-step and odd-step certificate propagation rules.

Derived API:
- the general excessive-gap certificate for every iterate pair of Algorithm 6.3.

The previous version restated this theorem for arbitrary iterate and smoothing sequences satisfying
the same parity split and kept local duplicate certificate aliases. This file now consumes the
actual Algorithm 6.3 owners together with the chapter certificate owners directly, so the chapter
has one public recursion surface instead of generic duplicates.
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

-- Proof sketch: argue by induction on `k`. The base case is `hzero`. For the inductive step,
-- split into the parity of `k`. On even steps, use the canonical Algorithm 6.3 recurrence lemmas
-- for `x̄` and `ū`, then apply `heven_step`. On odd steps, pass from the general certificate to
-- the `μ₁ = 0` certificate via `hodd_source`, propagate it across the odd update with
-- `hodd_step`, rewrite the iterate `(k + 1)` using the canonical Algorithm 6.3 odd-step
-- recurrence lemmas, and return to the general certificate using `hodd_target`.
/-- Theorem 6.6: if the initial Algorithm 6.3 iterate pair satisfies the Chapter 6 excessive-gap
condition, if each even step preserves the general excessive-gap certificate, and if each odd step
passes through the `μ₁ = 0` excessive-gap certificate before returning to the general one, then
every Algorithm 6.3 iterate pair satisfies the general excessive-gap condition. -/
theorem algorithm_6_3_iterates_satisfy_excessive_gap_condition
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
    (k : ℕ) :
    satisfiesExcessiveGapCondition
      Q₁
      Q₂
      (fμ₂ (μ₂ k))
      (φμ₁ (μ₁ k))
      (x̄ k)
      (ū k) := sorry

end
