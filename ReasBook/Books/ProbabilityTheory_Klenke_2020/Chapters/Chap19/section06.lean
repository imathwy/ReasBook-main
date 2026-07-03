import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_19_6_1 (from Items/Chap19) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {Ξ : Type v} [MeasurableSpace Ξ]

/- Layering for Exercise 19.6.1:
- `source-facing`: a one-sided nearest-neighbor environment on `ℕ`, the blocked-at-zero
  transition matrix it determines, and the three sign-of-`E[log ρ₀]` state-classification
  conclusions for quenched realizations of that half-line walk.
- `core/canonical`: the Chapter 17 state predicates `IsTransientState`, `IsNullRecurrentState`,
  and `IsPositiveRecurrentState`.
- `bridge/view`: restriction of the two-sided Chapter 19 owner `RandomEnvironment` and
  `IsSolomonEnvironmentLaw` to the nonnegative half-line. -/

/-- A one-sided nearest-neighbor environment on `ℕ`, assigning to each site the probability of a
jump to the right. The complementary mass is the left-jump probability away from the boundary, and
at `0` it becomes the blocked self-loop mass. -/
structure HalfLineRandomEnvironment where
  /-- The probability of a jump from `n` to `n + 1`. -/
  rightJumpProb : ℕ → ℝ≥0
  /-- The right-jump probabilities are at most `1`. -/
  rightJumpProb_le_one : ∀ n : ℕ, rightJumpProb n ≤ 1

namespace HalfLineRandomEnvironment

/-- A one-sided environment is elliptic if every right-jump probability lies strictly between `0`
and `1`. -/
class IsElliptic (W : HalfLineRandomEnvironment) : Prop where
  pos_lt_one (n : ℕ) : 0 < W.rightJumpProb n ∧ W.rightJumpProb n < 1

/-- In an elliptic one-sided environment, every right-jump probability is positive. -/
theorem IsElliptic.pos {W : HalfLineRandomEnvironment} (hW : W.IsElliptic) (n : ℕ) :
    0 < W.rightJumpProb n :=
  (hW.pos_lt_one n).1

/-- In an elliptic one-sided environment, every right-jump probability is strictly less than `1`.
-/
theorem IsElliptic.lt_one {W : HalfLineRandomEnvironment} (hW : W.IsElliptic) (n : ℕ) :
    W.rightJumpProb n < 1 :=
  (hW.pos_lt_one n).2

end HalfLineRandomEnvironment

namespace RandomEnvironment

/-- Restrict a two-sided environment on `ℤ` to its nonnegative sites. This is the canonical bridge
from the Chapter 19 owner to the half-line owner used in Exercise 19.6.1. -/
def toHalfLine (W : RandomEnvironment) : HalfLineRandomEnvironment where
  rightJumpProb n := W.rightJumpProb n
  rightJumpProb_le_one n := W.rightJumpProb_le_one n

end RandomEnvironment

/-- The logarithmic local Solomon ratio `log ρ_n` for a sampled one-sided environment. -/
def halfLineRandomEnvironmentLogRatio (W : Ω → HalfLineRandomEnvironment) (n : ℕ) : Ω → ℝ :=
  fun ω ↦
    Real.log
      (((((1 : ℝ≥0) - ((W ω).rightJumpProb n)) / ((W ω).rightJumpProb n) : ℝ≥0) : ℝ))

scoped[ProbabilityTheory] notation "logρ₊[" W "](" n ")" => halfLineRandomEnvironmentLogRatio W n

/-- A Solomon environment law on the half-line is a random nearest-neighbor environment on `ℕ`
whose log-ratio field is i.i.d. and whose sampled environments are almost surely elliptic. -/
class IsHalfLineSolomonEnvironmentLaw (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → HalfLineRandomEnvironment) : Prop where
  ae_elliptic : ∀ᵐ ω ∂μ, (W ω).IsElliptic
  logRatio_iid : IsIID (fun n ↦ logρ₊[W](n)) μ

namespace IsHalfLineSolomonEnvironmentLaw

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → HalfLineRandomEnvironment}

/-- In a half-line Solomon environment law, the sampled environment is elliptic almost surely. -/
theorem ae_elliptic_at (hW : IsHalfLineSolomonEnvironmentLaw μ W) (n : ℕ) :
    ∀ᵐ ω ∂μ, 0 < (W ω).rightJumpProb n ∧ (W ω).rightJumpProb n < 1 :=
  hW.ae_elliptic.mono fun _ hω ↦ hω.pos_lt_one n

end IsHalfLineSolomonEnvironmentLaw

namespace IsSolomonEnvironmentLaw

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → RandomEnvironment}

/-- Restricting a two-sided Solomon environment law to the nonnegative half-line yields the
canonical one-sided law used in Exercise 19.6.1. -/
theorem toHalfLine (hW : IsSolomonEnvironmentLaw μ W) :
    IsHalfLineSolomonEnvironmentLaw μ (fun ω ↦ (W ω).toHalfLine) := sorry

end IsSolomonEnvironmentLaw

/-- The half-line RWRE transition matrix attached to a fixed environment `W`, with the boundary
attempt to jump left from `0` blocked so that the chain stays at `0`. -/
def blockedAtZeroRandomEnvironmentTransitionMatrix
    (W : HalfLineRandomEnvironment) : ℕ → ℕ → ℝ≥0∞
  | 0, m =>
      if m = 0 then (((1 : ℝ≥0) - W.rightJumpProb 0 : ℝ≥0) : ℝ≥0∞)
      else if m = 1 then W.rightJumpProb 0
      else 0
  | n + 1, m =>
      if m = n then (((1 : ℝ≥0) - W.rightJumpProb (n + 1) : ℝ≥0) : ℝ≥0∞)
      else if m = n + 2 then W.rightJumpProb (n + 1)
      else 0

/-- At `0`, the blocked half-line RWRE keeps the forbidden left-jump mass as a self-loop. -/
theorem blockedAtZeroRandomEnvironmentTransitionMatrix_zero_self (W : HalfLineRandomEnvironment) :
    blockedAtZeroRandomEnvironmentTransitionMatrix W 0 0 =
      (((1 : ℝ≥0) - W.rightJumpProb 0 : ℝ≥0) : ℝ≥0∞) := by
  simp [blockedAtZeroRandomEnvironmentTransitionMatrix]

/-- At `0`, the blocked half-line RWRE keeps the original right-jump probability. -/
theorem blockedAtZeroRandomEnvironmentTransitionMatrix_zero_one (W : HalfLineRandomEnvironment) :
    blockedAtZeroRandomEnvironmentTransitionMatrix W 0 1 = W.rightJumpProb 0 := by
  simp [blockedAtZeroRandomEnvironmentTransitionMatrix]

/-- Away from the boundary, the blocked half-line RWRE has the expected nearest-neighbor row. -/
theorem blockedAtZeroRandomEnvironmentTransitionMatrix_succ
    (W : HalfLineRandomEnvironment) (n m : ℕ) :
    blockedAtZeroRandomEnvironmentTransitionMatrix W (n + 1) m =
      if m = n then (((1 : ℝ≥0) - W.rightJumpProb (n + 1) : ℝ≥0) : ℝ≥0∞)
      else if m = n + 2 then W.rightJumpProb (n + 1)
      else 0 := rfl

/-- At an interior state `n + 1`, the blocked half-line RWRE jumps left to `n` with the owner
left-jump probability. -/
theorem blockedAtZeroRandomEnvironmentTransitionMatrix_left
    (W : HalfLineRandomEnvironment) (n : ℕ) :
    blockedAtZeroRandomEnvironmentTransitionMatrix W (n + 1) n =
      (((1 : ℝ≥0) - W.rightJumpProb (n + 1) : ℝ≥0) : ℝ≥0∞) := by
  simp [blockedAtZeroRandomEnvironmentTransitionMatrix]

/-- At an interior state `n + 1`, the blocked half-line RWRE jumps right to `n + 2` with the
owner right-jump probability. -/
theorem blockedAtZeroRandomEnvironmentTransitionMatrix_right
    (W : HalfLineRandomEnvironment) (n : ℕ) :
    blockedAtZeroRandomEnvironmentTransitionMatrix W (n + 1) (n + 2) =
      W.rightJumpProb (n + 1) := by
  simp [blockedAtZeroRandomEnvironmentTransitionMatrix]

-- Proof sketch: the boundary row is supported only at `0` and `1`. Every interior row `n + 1`
-- is supported only at `n` and `n + 2`, and those two masses add up to `1`.
/-- The blocked-at-zero half-line RWRE transition matrix is stochastic. -/
theorem blockedAtZeroRandomEnvironmentTransitionMatrix_isStochastic (W : HalfLineRandomEnvironment) :
    IsStochasticMatrix (blockedAtZeroRandomEnvironmentTransitionMatrix W) := by
  intro x
  classical
  cases x with
  | zero =>
      have hsupport :
          ∀ y ∉ ({0, 1} : Finset ℕ), blockedAtZeroRandomEnvironmentTransitionMatrix W 0 y = 0 := by
        intro y hy
        have hy_zero : y ≠ 0 := by
          intro h
          exact hy (by simp [h])
        have hy_one : y ≠ 1 := by
          intro h
          exact hy (by simp [h])
        simp [blockedAtZeroRandomEnvironmentTransitionMatrix, hy_zero, hy_one]
      rw [tsum_eq_sum hsupport]
      have hprob : (W.rightJumpProb 0 : ℝ≥0∞) ≤ 1 := by
        exact_mod_cast W.rightJumpProb_le_one 0
      simpa [blockedAtZeroRandomEnvironmentTransitionMatrix_zero_self,
        blockedAtZeroRandomEnvironmentTransitionMatrix_zero_one, add_comm] using
        add_tsub_cancel_of_le hprob
  | succ n =>
      have hsupport :
          ∀ y ∉ ({n, n + 2} : Finset ℕ),
            blockedAtZeroRandomEnvironmentTransitionMatrix W (n + 1) y = 0 := by
        intro y hy
        have hy_left : y ≠ n := by
          intro h
          exact hy (by simp [h])
        have hy_right : y ≠ n + 2 := by
          intro h
          exact hy (by simp [h])
        simp [blockedAtZeroRandomEnvironmentTransitionMatrix, hy_left, hy_right]
      rw [tsum_eq_sum hsupport]
      have hprob : (W.rightJumpProb (n + 1) : ℝ≥0∞) ≤ 1 := by
        exact_mod_cast W.rightJumpProb_le_one (n + 1)
      simpa [blockedAtZeroRandomEnvironmentTransitionMatrix_left,
        blockedAtZeroRandomEnvironmentTransitionMatrix_right, add_comm] using
        add_tsub_cancel_of_le hprob

/-- The discrete kernel attached to the blocked-at-zero half-line RWRE transition matrix is
Markov. -/
instance (W : HalfLineRandomEnvironment) :
    IsMarkovKernel (discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W)) :=
  discreteMatrixKernel_isMarkovKernel _
    (blockedAtZeroRandomEnvironmentTransitionMatrix_isStochastic W)

section

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → HalfLineRandomEnvironment}
variable {P : Ω → ℕ → ProbabilityMeasure Ξ} {X : Ω → ℕ → Ξ → ℕ}
variable (hW : IsHalfLineSolomonEnvironmentLaw μ W)
variable
  (hreal :
    ∀ ω,
      IsMarkovProcessRealization
        (fun n : ℕ ↦
          discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix (W ω)) ^ n)
        (P ω) (X ω))
variable (hlog : Integrable (logρ₊[W](0)) μ)

-- Proof sketch: this is the blocked-half-line analogue of the right-transient branch of
-- Theorem 19.35. Negative mean `E[log ρ₀]` yields almost-sure rightward drift, and blocking the
-- forbidden jump from `0` to `-1` does not create recurrent traps, so every state of the quenched
-- half-line chain is transient.
/-- Exercise 19.6.1 (1): for the half-line random walk in random environment with blocked boundary
at `0`, if
`E[log ρ₀] < 0` and `E[|log ρ₀|] < ∞`, then for almost every environment every state is
transient. -/
theorem ae_allStatesTransient_of_integral_logRatio_lt_zero_blockedAtZero
    (hmean : ∫ ω, logρ₊[W](0) ω ∂μ < 0) :
    ∀ᵐ ω ∂μ, ∀ x : ℕ, IsTransientState (P ω) (X ω) x := sorry

-- Proof sketch: at the critical value `E[log ρ₀] = 0`, the blocked walk remains recurrent but has
-- infinite expected return time; staying at `0` blocks escape to `-∞` without
-- creating a finite invariant law, so almost every quenched chain is null recurrent at every
-- state.
/-- Exercise 19.6.1 (2): for the half-line random walk in random environment with blocked boundary
at `0`, if
`E[log ρ₀] = 0` and `E[|log ρ₀|] < ∞`, then for almost every environment every state is null
recurrent. -/
theorem ae_allStatesNullRecurrent_of_integral_logRatio_eq_zero_blockedAtZero
    (hmean : ∫ ω, logρ₊[W](0) ω ∂μ = 0) :
    ∀ᵐ ω ∂μ, ∀ x : ℕ, IsNullRecurrentState (P ω) (X ω) x := sorry

-- Proof sketch: when `E[log ρ₀] > 0`, the half-line walk has leftward bias toward the boundary;
-- blocking at `0` traps that drift and yields finite return times, hence almost every quenched
-- half-line chain is positive recurrent.
/-- Exercise 19.6.1 (3): for the half-line random walk in random environment with blocked boundary
at `0`, if
`E[log ρ₀] > 0` and `E[|log ρ₀|] < ∞`, then for almost every environment every state is positive
recurrent. -/
theorem ae_allStatesPositiveRecurrent_of_integral_logRatio_gt_zero_blockedAtZero
    (hmean : 0 < ∫ ω, logρ₊[W](0) ω ∂μ) :
    ∀ᵐ ω ∂μ, ∀ x : ℕ, IsPositiveRecurrentState (P ω) (X ω) x := sorry

end

end ProbabilityTheory

/-! ### Theorem_19_6 (from Items/Chap19) -/
open MeasureTheory
open scoped ENNReal

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} {Ω : Type v} [MeasurableSpace Ω]

/-
Layering for Theorem 19.6:
- `source-facing`: `F_A` and `S_A`, the textbook first-hit probability of the killed chain and the
  corresponding positive-probability reachability set.
- `core/canonical`: `hittingAfter` for the first time the trajectory enters `insert y A`,
  `stoppedValue` for the state reached at that time, `IsHarmonicOutside` for harmonicity on
  `E \ A`, and `discreteMatrixKernel p` for the transition kernel of the discrete chain.
- `bridge/view`: the internal event that the first hit of `insert y A` occurs at the state `y`.
  For `y ∉ A` this is exactly the usual event `τ_y < τ_A`, while for `y ∈ A` it is the
  boundary-inclusive first-hit event `X_{τ_A} = y`.
-/

/-- The event that the trajectory `X` first hits `insert y A` at the state `y`, where the first
hit may occur at time `0`. For `y ∉ A`, this is the usual event `τ_y < τ_A`; for `y ∈ A`, it is
the event that the first hit of `A` occurs at `y`. -/
private def firstHitAtStateEvent (X : ℕ → Ω → E) (A : Set E) (y : E) : Set Ω :=
  {ω | hittingAfter X (insert y A) 0 ω < ⊤ ∧
      stoppedValue X (hittingAfter X (insert y A) 0) ω = y}

/-- The quantity `F_A x y` is the probability under `P x` that the first hit of `insert y A`
occurs at the state `y`, where the hit may occur at time `0`. Equivalently, for `y ∉ A` it is the
probability of the event `τ_y < τ_A`, while for `y ∈ A` it is the first-hit distribution of `A`
at the point `y`. -/
def F_A (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) (x y : E) : ℝ :=
  (P x : Measure Ω).real (firstHitAtStateEvent X A y)

/-- The set `S_A x` consists of states that can be reached from `x` with positive probability
as the first point where the trajectory enters `insert y A`; in particular it contains the
boundary points of `A` that occur with positive first-hit probability. -/
def S_A (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) (x : E) : Set E :=
  {y | 0 < F_A P X A x y}

-- Proof sketch: unfold `S_A`; membership is defined exactly by strict positivity of `F_A`.
/-- Membership in `S_A x` is equivalent to strict positivity of the first-hit probability
`F_A x y`. -/
theorem mem_S_A_iff
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E) (A : Set E) (x y : E) :
    y ∈ S_A P X A x ↔ 0 < F_A P X A x y :=
  Iff.rfl

section

variable {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
variable {A : Set E} {f : E → ℝ} {x₀ : E}

-- Proof sketch: pass from `hf` to the chain stopped on first entering `A`; iterating the stopped
-- transition operator expresses `f x₀` as an average of the values of `f` on states in
-- `S_A x₀`. If `f x₀` is already the greatest value attained on `S_A x₀`, every state with
-- positive first-hit probability from `x₀` must share the same value.
/-- Theorem 19.6 (1): (i) if a function harmonic on `E \ A` attains the supremum of its values on
`S_A(x₀)` at some `x₀ ∉ A`, then it is constant on `S_A(x₀)`. -/
theorem harmonicOn_compl_eq_on_S_A_of_isGreatest
    (hf : IsHarmonicOutside (discreteMatrixKernel p) A f) (hx₀ : x₀ ∉ A)
    (hmax : IsGreatest (f '' S_A P X A x₀) (f x₀)) :
    ∀ ⦃y : E⦄, y ∈ S_A P X A x₀ → f y = f x₀ := sorry

-- Proof sketch: the positivity assumption on `F_A` says that every `y ∉ A` belongs to
-- `S_A x₀`. Apply part (i) at the point where `f` attains its global supremum; since the global
-- supremum also bounds `f` on `S_A x₀`, the local maximum principle forces equality on all of
-- `E \ A`.
/-- Theorem 19.6 (2): (ii) if `F_A(x,y) > 0` for all `x, y ∈ E \ A` and `f` attains its global
supremum at some `x₀ ∉ A`, then `f` is constant on `E \ A`. -/
theorem harmonicOn_compl_eq_on_compl_of_F_A_pos_of_isGreatest
    (hf : IsHarmonicOutside (discreteMatrixKernel p) A f)
    (hFA : ∀ ⦃x y : E⦄, x ∉ A → y ∉ A → 0 < F_A P X A x y)
    (hx₀ : x₀ ∉ A) (hmax : IsGreatest (Set.range f) (f x₀)) :
    ∀ ⦃y : E⦄, y ∉ A → f x₀ = f y := sorry

end

end ProbabilityTheory
