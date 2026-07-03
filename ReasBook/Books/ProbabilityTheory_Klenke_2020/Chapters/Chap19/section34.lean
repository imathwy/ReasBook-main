import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_19_34 (from Items/Chap19) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- A one-dimensional nearest-neighbor environment on `ℤ`, assigning to each site the
probability of a jump to the right. The left-jump probability is then `1 - W.rightJumpProb x`. -/
structure RandomEnvironment where
  /-- The probability of a jump from `x` to `x + 1`. -/
  rightJumpProb : ℤ → ℝ≥0
  /-- The right-jump probabilities are at most `1`. -/
  rightJumpProb_le_one : ∀ x : ℤ, rightJumpProb x ≤ 1

/-- The one-step transition matrix on `ℤ` determined by the environment `W`: from `x` the walk
jumps to `x + 1` with probability `W.rightJumpProb x` and to `x - 1` with the complementary
probability. This is the source-facing discrete owner; `discreteMatrixKernel` is the canonical
kernel bridge attached to it. -/
def randomEnvironmentTransitionMatrix (W : RandomEnvironment) : ℤ → ℤ → ℝ≥0∞ :=
  fun x y ↦
    if y = x + 1 then W.rightJumpProb x
    else if y = x - 1 then (1 : ℝ≥0) - W.rightJumpProb x
    else 0

/-- Evaluating the RWRE transition matrix recovers the textbook nearest-neighbor step
probabilities. -/
theorem randomEnvironmentTransitionMatrix_apply (W : RandomEnvironment) (x y : ℤ) :
    randomEnvironmentTransitionMatrix W x y =
      if y = x + 1 then (W.rightJumpProb x : ℝ≥0∞)
      else if y = x - 1 then (((1 : ℝ≥0) - W.rightJumpProb x : ℝ≥0) : ℝ≥0∞)
      else 0 := rfl

-- Proof sketch: every row is supported on the two neighbors `x ± 1`, and those two masses add to
-- `1`.
/-- The RWRE transition matrix is stochastic. -/
theorem randomEnvironmentTransitionMatrix_isStochastic (W : RandomEnvironment) :
    IsStochasticMatrix (randomEnvironmentTransitionMatrix W) := by
  intro x
  classical
  have hsupport :
      ∀ y ∉ ({x + 1, x - 1} : Finset ℤ), randomEnvironmentTransitionMatrix W x y = 0 := by
    intro y hy
    have hy_right : y ≠ x + 1 := by
      intro h
      exact hy (by simp [h])
    have hy_left : y ≠ x - 1 := by
      intro h
      exact hy (by simp [h])
    simp [randomEnvironmentTransitionMatrix, hy_right, hy_left]
  rw [tsum_eq_sum hsupport]
  have hneq : x + 1 ≠ x - 1 := by omega
  have hneq' : x - 1 ≠ x + 1 := by omega
  have hprob : (W.rightJumpProb x : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast W.rightJumpProb_le_one x
  simpa [randomEnvironmentTransitionMatrix, hneq, hneq'] using add_tsub_cancel_of_le hprob

/-- The discrete kernel associated to `randomEnvironmentTransitionMatrix W` is Markov. -/
instance (W : RandomEnvironment) :
    IsMarkovKernel (discreteMatrixKernel (randomEnvironmentTransitionMatrix W)) :=
  discreteMatrixKernel_isMarkovKernel _ (randomEnvironmentTransitionMatrix_isStochastic W)

/-- At the right neighbor `x + 1`, the RWRE transition matrix has mass `W.rightJumpProb x`. -/
theorem randomEnvironmentTransitionMatrix_right (W : RandomEnvironment) (x : ℤ) :
    randomEnvironmentTransitionMatrix W x (x + 1) = W.rightJumpProb x := by
  simp [randomEnvironmentTransitionMatrix]

/-- At the left neighbor `x - 1`, the RWRE transition matrix has mass `1 - W.rightJumpProb x`. -/
theorem randomEnvironmentTransitionMatrix_left (W : RandomEnvironment) (x : ℤ) :
    randomEnvironmentTransitionMatrix W x (x - 1) = (1 : ℝ≥0) - W.rightJumpProb x := by
  have hneq : x - 1 ≠ x + 1 := by omega
  simp [randomEnvironmentTransitionMatrix, hneq]

namespace RandomEnvironment

/-- A one-dimensional environment is elliptic if every right-jump probability lies strictly
between `0` and `1`. -/
class IsElliptic (W : RandomEnvironment) : Prop where
  pos_lt_one (x : ℤ) : 0 < W.rightJumpProb x ∧ W.rightJumpProb x < 1

/-- In an elliptic environment, every right-jump probability is positive. -/
theorem IsElliptic.pos {W : RandomEnvironment} (hW : W.IsElliptic) (x : ℤ) :
    0 < W.rightJumpProb x :=
  (hW.pos_lt_one x).1

/-- In an elliptic environment, every right-jump probability is strictly less than `1`. -/
theorem IsElliptic.lt_one {W : RandomEnvironment} (hW : W.IsElliptic) (x : ℤ) :
    W.rightJumpProb x < 1 :=
  (hW.pos_lt_one x).2

end RandomEnvironment

/- Layering for Definition 19.34:
- `source-facing`: the nearest-neighbor transition matrix `randomEnvironmentTransitionMatrix W` on
  `ℤ` in the fixed environment `W`.
- `core/canonical`: the Chapter 17 discrete-time owner
  `IsMarkovProcessRealization
    (fun n ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X`.
- `bridge/view`: the canonical kernel bridge `discreteMatrixKernel
  (randomEnvironmentTransitionMatrix W)` and direct reuse of Theorem 17.11 for the one-step
  conditional-law criterion, together with the textbook initial-state and one-step joint-law
  consequences. -/

section

variable (W : RandomEnvironment) (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ)

/- Definition 19.34: a random walk in the random environment `W` is a discrete-time Markov
process realization whose one-step transition matrix is `randomEnvironmentTransitionMatrix W`,
equivalently whose one-step kernel is its canonical bridge
`discreteMatrixKernel (randomEnvironmentTransitionMatrix W)`. -/
#check
  IsMarkovProcessRealization
    (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n)
    P X

end

section

variable {W : RandomEnvironment} {P : ℤ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℤ}
variable [IsMarkovProcessRealization
  (fun n : ℕ ↦ discreteMatrixKernel (randomEnvironmentTransitionMatrix W) ^ n) P X]

-- Proof sketch: evaluate the `initial_eq` owner field at the singleton `{x}`.
/-- Under the canonical Chapter 17 RWRE owner, the walk started from `x` is almost surely at `x`
at time `0`. -/
theorem randomWalkInRandomEnvironment_start (x : ℤ) :
    (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1 := sorry

-- Proof sketch: combine the owner-level Markov property for the one-step kernel
-- `discreteMatrixKernel (randomEnvironmentTransitionMatrix W)` with the discrete singleton
-- evaluation formula `discreteMatrixKernel p y {z} = p y z`.
/-- Under the canonical Chapter 17 RWRE owner, the one-step joint law of `(X_n, X_{n+1})` is the
textbook transition weight `randomEnvironmentTransitionMatrix W y z` times the time-`n` marginal
at `y`. -/
theorem randomWalkInRandomEnvironment_transition
    (x : ℤ) (n : ℕ) (y z : ℤ) :
    (P x : Measure Ω) {ω | X n ω = y ∧ X (n + 1) ω = z} =
      randomEnvironmentTransitionMatrix W y z * (P x : Measure Ω) (X n ⁻¹' {y}) := sorry

end

end ProbabilityTheory
