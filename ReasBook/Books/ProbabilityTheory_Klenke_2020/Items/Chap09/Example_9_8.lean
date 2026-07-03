import Mathlib
import AchimKlenkeLean.Items.Chap05.Definition_5_33
import AchimKlenkeLean.Items.Chap09.Definition_9_7

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

open scoped BigOperators

universe u v w

variable {Ω : Type u}

/-- The random walk on `ℤ` associated with the increment sequence `ξ`, realized as the partial-sum
process `S_n = ξ₀ + ⋯ + ξ_{n-1}`. -/
def randomWalkProcess (ξ : ℕ → Ω → ℤ) : ℕ → Ω → ℤ :=
  fun n ω ↦ Finset.sum (Finset.range n) fun i ↦ ξ i ω

/-- The order-`k` linear filter associated with the coefficients `c₀, …, c_k`. -/
def movingAverageProcess (X : ℤ → Ω → ℝ) (c : ℕ → ℝ) (k : ℕ) : ℤ → Ω → ℝ :=
  fun n ω ↦ Finset.sum (Finset.range (k + 1)) fun i ↦ c i * X (n - i) ω

/-- The textbook moving-average weights are nonnegative and normalized to have total mass `1`. -/
def IsMovingAverageWeights (c : ℕ → ℝ) (k : ℕ) : Prop :=
  (∀ i ∈ Finset.range (k + 1), 0 ≤ c i) ∧
    Finset.sum (Finset.range (k + 1)) c = 1

/-- `Y` is the moving average of `X` with weights `c₀, …, c_k` if it is the corresponding finite
linear filter and the weights are nonnegative with sum `1`. -/
def IsMovingAverageOf (Y X : ℤ → Ω → ℝ) (c : ℕ → ℝ) (k : ℕ) : Prop :=
  Y = movingAverageProcess X c k ∧ IsMovingAverageWeights c k

-- Proof sketch: unfold `randomWalkProcess`; it is exactly the finite partial sum of the increment
-- sequence over `Finset.range n`.
/-- The random-walk process is given by the finite partial sums of the increment sequence. -/
theorem randomWalkProcess_apply (ξ : ℕ → Ω → ℤ) (n : ℕ) (ω : Ω) :
    randomWalkProcess ξ n ω = Finset.sum (Finset.range n) fun i ↦ ξ i ω := rfl

-- Proof sketch: unfold `movingAverageProcess`; it is exactly the finite weighted sum from the
-- textbook formula `Y_n = ∑_{i=0}^k c_i X_{n-i}`.
/-- The moving-average process is given by the finite weighted sum from the textbook formula. -/
theorem movingAverageProcess_apply (X : ℤ → Ω → ℝ) (c : ℕ → ℝ) (k : ℕ) (n : ℤ) (ω : Ω) :
    movingAverageProcess X c k n ω =
      Finset.sum (Finset.range (k + 1)) fun i ↦ c i * X (n - i) ω := rfl

-- Proof sketch: this is immediate from the definition of `IsMovingAverageOf`: when the weight
-- sequence is nonnegative and sums to `1`, the finite linear filter `movingAverageProcess X c k`
-- is precisely the textbook moving average of `X`.
/-- Example 9.8 (5): Item (iii). If the coefficients are nonnegative and sum to `1`, then the
finite linear filter `Y_n = ∑_{i=0}^k c_i X_{n-i}` is the moving average of `X` with weights
`c₀, …, c_k`. -/
theorem movingAverageProcess_isMovingAverageOf
    (X : ℤ → Ω → ℝ) (c : ℕ → ℝ) (k : ℕ) (hweights : IsMovingAverageWeights c k) :
    IsMovingAverageOf (movingAverageProcess X c k) X c k :=
  ⟨rfl, hweights⟩

variable [MeasurableSpace Ω]
variable {T : Type v} [AddSemigroup T] {E : Type w} [Sub E] [MeasurableSpace E]

/-- A process has stationary increment laws if translating both endpoints of an increment by the
same amount does not change its law. This is the `E`-valued bridge layer for the Chapter 9 owner
`HasStationaryIncrements`, which is specialized to real-valued processes. -/
def HasStationaryIncrementLaws
    (X : T → Ω → E) (μ : Measure Ω := by volume_tac) : Prop :=
  ∀ r s t,
    IdentDistrib
      (fun ω ↦ X ((s + t) + r) ω - X (t + r) ω)
      (fun ω ↦ X (s + r) ω - X r ω)
      μ μ

namespace HasStationaryIncrementLaws

variable {X : T → Ω → E} {μ : Measure Ω}

/-- A process with stationary increment laws has the same increment distribution after common time
translation. -/
theorem identDistrib_increment (hX : HasStationaryIncrementLaws X μ) (r s t : T) :
    IdentDistrib
      (fun ω ↦ X ((s + t) + r) ω - X (t + r) ω)
      (fun ω ↦ X (s + r) ω - X r ω)
      μ μ :=
  hX r s t

end HasStationaryIncrementLaws

-- Proof sketch: the local `E`-valued bridge is definitionally the same three-time translation
-- invariant increment-law predicate as the Chapter 9 real-valued owner.
/-- On real-valued processes, `HasStationaryIncrementLaws` is exactly the Chapter 9 owner
`HasStationaryIncrements`. -/
theorem hasStationaryIncrementLaws_iff_hasStationaryIncrements
    (X : T → Ω → ℝ) (μ : Measure Ω := by volume_tac) :
    HasStationaryIncrementLaws X μ ↔ HasStationaryIncrements X μ :=
  Iff.rfl

/-- A process has stationary independent increments if it has both independent increments and
stationary increment laws. -/
def HasStationaryIndependentIncrements {T : Type v} [Preorder T] [AddSemigroup T]
    {E : Type w} [Sub E] [MeasurableSpace E] (X : T → Ω → E)
    (μ : Measure Ω := by volume_tac) : Prop :=
  HasIndepIncrements X μ ∧ HasStationaryIncrementLaws X μ

-- Proof sketch: apply the owner abstraction `IsPoissonProcess`; independence is one of its
-- fields, and the increment law depends only on the interval length `t - s`, so translating the
-- interval does not change the law.
/-- Example 9.8 (1): Item (i). A Poisson process with intensity `θ` has stationary independent
increments. -/
theorem hasStationaryIndependentIncrements_of_poissonProcess
    {μ : Measure Ω} {θ : NNReal} {N : NNReal → Ω → ℕ}
    (hN : IsPoissonProcess θ μ N) :
    HasStationaryIndependentIncrements N μ := sorry

-- Proof sketch: the increments of the partial-sum process over disjoint time intervals are sums
-- over disjoint blocks of the i.i.d. increment sequence, so they are independent and depend in
-- law only on the block length.
/-- Example 9.8 (2): Item (i). The random walk on `ℤ`, realized as the partial-sum process of an
i.i.d. integer-valued increment sequence, has stationary independent increments. -/
theorem randomWalkProcess_hasStationaryIndependentIncrements
    (μ : Measure Ω) (ξ : ℕ → Ω → ℤ) (hξ_indep : iIndepFun ξ μ)
    (hξ_ident : ∀ m n : ℕ, IdentDistrib (ξ m) (ξ n) μ μ) :
    HasStationaryIndependentIncrements (randomWalkProcess ξ) μ := sorry

-- Proof sketch: for each finite family of times, the shifted family remains i.i.d. with the same
-- one-dimensional laws; therefore the corresponding finite-dimensional distributions agree.
/-- Example 9.8 (3): Item (ii). An i.i.d. process is stationary. -/
theorem isStationaryProcess_of_iIndepFun_identDistrib
    {T : Type v} [AddSemigroup T] {E : Type w} [MeasurableSpace E]
    (μ : Measure Ω) (X : T → Ω → E) (hX_indep : iIndepFun X μ)
    (hX_ident : ∀ s t : T, IdentDistrib (X s) (X t) μ μ) :
    IsStationaryProcess X μ := sorry

-- Proof sketch: a finite vector of moving-average coordinates is obtained from a finite vector of
-- coordinates of `X` by a fixed linear map depending only on the coefficients `c₀, …, c_k`; the
-- shift-invariance of the finite-dimensional laws of `X` is preserved by this map.
/-- Example 9.8 (4): Item (iii). A finite linear filter of a stationary real-valued process on
`ℤ` is stationary. -/
theorem movingAverageProcess_isStationary
    (μ : Measure Ω) (X : ℤ → Ω → ℝ) (c : ℕ → ℝ) (k : ℕ)
    (hX_stationary : IsStationaryProcess X μ) :
    IsStationaryProcess (movingAverageProcess X c k) μ := sorry
