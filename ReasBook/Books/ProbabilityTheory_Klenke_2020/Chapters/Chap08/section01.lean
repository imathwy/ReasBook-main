import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_8_1 (from Items/Chap08) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

private theorem ennreal_inv_three_six_mul_two_six :
    ((3 : ℝ≥0∞) / 6)⁻¹ * ((2 : ℝ≥0∞) / 6) = (2 : ℝ≥0∞) / 3 := by
  rw [show ((3 : ℝ≥0∞) / 6) = (((3 : NNReal) / 6 : NNReal) : ℝ≥0∞) by simp]
  rw [show ((2 : ℝ≥0∞) / 6) = (((2 : NNReal) / 6 : NNReal) : ℝ≥0∞) by simp]
  rw [show (((((3 : NNReal) / 6 : NNReal) : ℝ≥0∞))⁻¹) =
      ((((3 : NNReal) / 6 : NNReal)⁻¹ : NNReal) : ℝ≥0∞) by
      simpa using (ENNReal.coe_inv (by norm_num : ((3 : NNReal) / 6 : NNReal) ≠ 0)).symm]
  rw [show ((2 : ℝ≥0∞) / 3) = (((2 : NNReal) / 3 : NNReal) : ℝ≥0∞) by simp]
  exact_mod_cast
    (show (((3 : NNReal) / 6 : NNReal)⁻¹) * ((2 : NNReal) / 6 : NNReal) = (2 : NNReal) / 3 by
      apply NNReal.coe_inj.mp
      norm_num)

-- Proof sketch: rewrite the conditioned event with `ProbabilityTheory.cond_apply`, compute the
-- two relevant uniform probabilities with `ProbabilityTheory.uniformOn_apply_finset`, and finish
-- with the finite-cardinality ratio `((3/6)⁻¹ * (2/6) = 2/3)`.
/-- Example 8.1: For the uniform probability measure on the die faces `{1, \dots, 6}`, the
conditional probability that the outcome is odd, given that it is at most `3`, is `2/3`. -/
theorem die_uniform_conditional_probability_odd_given_le_three :
    (uniformOn (Set.Icc (1 : ℕ) 6))[({1, 3, 5} : Finset ℕ) | ({1, 2, 3} : Finset ℕ)] =
      (2 : ℝ≥0∞) / 3 := by
  simpa [Finset.coe_Icc] using
    (show (uniformOn (((Finset.Icc 1 6 : Finset ℕ) : Set ℕ)))[({1, 3, 5} : Finset ℕ) |
        ({1, 2, 3} : Finset ℕ)] = (2 : ℝ≥0∞) / 3 from by
      rw [cond_apply (show MeasurableSet ((({1, 2, 3} : Finset ℕ) : Set ℕ)) by simp)]
      rw [show ((({1, 2, 3} : Finset ℕ) : Set ℕ) ∩ (({1, 3, 5} : Finset ℕ) : Set ℕ)) =
          (({1, 3} : Finset ℕ) : Set ℕ) by
            ext n
            simp
            omega]
      rw [uniformOn_apply_finset, uniformOn_apply_finset]
      exact ennreal_inv_three_six_mul_two_six)

/-! ### Exercise_8_1_1 (from Items/Chap08) -/
open MeasureTheory ProbabilityTheory
open Set
open scoped ENNReal ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}

-- Proof sketch: for the forward implication, use `cdf_expMeasure_eq` to identify the survival
-- function of `expMeasure θ` as `exp (-θ t)` and then derive the multiplicative tail identity
-- `P[X > t + s] = P[X > t] * P[X > s]`. For the reverse implication, show that this tail identity
-- forces the survival function `t ↦ P {ω | t < X ω}` to solve the multiplicative Cauchy equation
-- on `ℝ≥0`; positivity and measurability then identify it with `exp (-θ t)` for some `θ > 0`,
-- yielding `HasLaw X (expMeasure θ) P`.
/-- Exercise 8.1.1: a strictly positive real random variable on a probability space is
exponentially distributed for some rate if and only if its tail probabilities are memoryless,
equivalently `P[X > t + s] = P[X > t] * P[X > s]` for all `s, t ≥ 0`. -/
theorem strictly_positive_has_exponential_law_iff_memoryless
    (hX_meas : Measurable X) (hX_pos : ∀ᵐ ω ∂P, 0 < X ω) :
    (∃ θ > 0, HasLaw X (expMeasure θ) P) ↔
      ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
        P (X ⁻¹' Ioi (t + s)) = P (X ⁻¹' Ioi t) * P (X ⁻¹' Ioi s) := sorry

-- Proof sketch: rewrite the law statement as the fixed-rate multiplicative tail identity
-- `P[X > t + s] = expMeasure θ (Ioi t) * P[X > s]`. This keeps the main characterization in
-- canonical `HasLaw`/measure form and avoids conditioning on null tail events.
/-- A strictly positive real random variable has law `expMeasure θ` with `θ > 0` exactly when its
tail probabilities satisfy the fixed-rate memoryless identity
`P[X > t + s] = expMeasure θ (Ioi t) * P[X > s]` for all `s, t ≥ 0`. -/
theorem hasLaw_expMeasure_iff_tail_eq_expMeasure_tail_mul_tail
    {θ : ℝ} (hθ : 0 < θ) (hX_meas : Measurable X) (hX_pos : ∀ᵐ ω ∂P, 0 < X ω) :
    HasLaw X (expMeasure θ) P ↔
      ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
        P (X ⁻¹' Ioi (t + s)) = expMeasure θ (Ioi t) * P (X ⁻¹' Ioi s) := sorry

-- Proof sketch: combine the canonical tail characterization with the explicit exponential tail
-- formula `expMeasure θ (Ioi t) = exp (-θ t)` for `t ≥ 0`, obtained from `cdf_expMeasure_eq`.
/-- A strictly positive real random variable has exponential law of rate `θ > 0` exactly when its
tail probabilities satisfy the explicit fixed-rate identity
`P[X > t + s] = exp (-θ t) * P[X > s]` for all `s, t ≥ 0`. -/
theorem hasLaw_expMeasure_iff_tail_eq_exp_mul_tail
    {θ : ℝ} (hθ : 0 < θ) (hX_meas : Measurable X) (hX_pos : ∀ᵐ ω ∂P, 0 < X ω) :
    HasLaw X (expMeasure θ) P ↔
      ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
        P (X ⁻¹' Ioi (t + s)) =
          ENNReal.ofReal (Real.exp (-(θ * t))) * P (X ⁻¹' Ioi s) := sorry

/-! ### Exercise_8_1_2 (from Items/Chap08) -/
noncomputable section

/-
The reduced absent-minded-passenger process is governed by the reserved seats that get taken by a
passenger forced to choose uniformly at random. Starting from the still-available seats
`{1} ∪ s`, a random choice of seat `1` ends the chain, while a random choice of `j ∈ s` records
that seat `j` was taken out of order and continues only with the larger reserved seats. The
smaller seat labels are no longer available, because their owners sit down deterministically
before the next random choice.
-/
private def absentMindedPassengerChosenSeatsFromRemaining : Finset ℕ → PMF (Finset ℕ)
  | s =>
      let choices := insert 1 s
      let p : PMF ℕ := PMF.uniformOfFinset choices (by simp [choices])
      p.bindOnSupport fun j hj ↦
        if h1 : j = 1 then
          PMF.pure ∅
        else
          PMF.map (insert j)
            (absentMindedPassengerChosenSeatsFromRemaining (s.filter fun m ↦ j < m))
termination_by s => s.card

decreasing_by
  have hj' : j ∈ insert 1 s := by
    simpa [p, choices] using hj
  have hjs : j ∈ s := by
    rcases Finset.mem_insert.mp hj' with h | h
    · contradiction
    · exact h
  have hproper : s.filter (fun m ↦ j < m) ⊂ s := by
    rw [Finset.filter_ssubset]
    exact ⟨j, hjs, by simp⟩
  exact Finset.card_lt_card hproper

/-- The absent-minded passenger model on `n` seats, recorded as the random finite set of reserved
seat labels in `{2, …, n}` that are taken by a random chooser before seat `1` is finally chosen.
For every `k ≥ 2`, passenger `k` gets their own seat exactly when `k` is absent from this set, and
the first passenger gets their own seat exactly when the set is empty. -/
noncomputable def absentMindedPassengerChosenSeats (n : ℕ) : PMF (Finset ℕ) :=
  absentMindedPassengerChosenSeatsFromRemaining (Finset.Icc 2 n)

/-- Predicate on the reduced absent-minded-passenger states saying that passenger `k` gets their
reserved seat. For `k = 1` this means that no later reserved seat is ever chosen out of order,
i.e. the recorded set is empty; for `k ≥ 2` it means that seat `k` is never chosen by a displaced
passenger. -/
def absentMindedPassengerGetsReservedSeat (k : ℕ) (chosen : Finset ℕ) : Prop :=
  if k = 1 then chosen = ∅ else k ∉ chosen

/-- The probability that passenger `k` gets their reserved seat in the absent-minded passenger
problem with `n` seats, defined from the actual reduced random process rather than by a closed
formula. -/
noncomputable def absentMindedPassengerReservedSeatProbability (n k : ℕ) : ℝ := by
  letI : MeasurableSpace (Finset ℕ) := ⊤
  exact ((absentMindedPassengerChosenSeats n).toMeasure
    {chosen | absentMindedPassengerGetsReservedSeat k chosen}).toReal

-- Proof sketch: in the reduced model, passenger `1` gets their own seat exactly when the random
-- chain stops immediately, i.e. when no seat in `{2, …, n}` is ever chosen. That happens iff the
-- initial uniform choice is seat `1`, which has probability `1 / n`.
/-- The absent-minded first passenger gets their reserved seat with probability `1 / n`. -/
theorem absentMindedPassenger_first_passenger_reservedSeatProbability (n : ℕ) (hn : 0 < n) :
    absentMindedPassengerReservedSeatProbability n 1 = (1 : ℝ) / n := sorry

-- Proof sketch: passenger `n` gets their own seat exactly when the reduced chain hits seat `1`
-- before it hits seat `n`; by symmetry of the two special terminal seats, these alternatives have
-- equal probability.
/-- Exercise 8.1.2 (1): In the absent-minded passenger problem with `n ≥ 2` seats, the last
passenger gets their reserved seat with probability `1 / 2`. -/
theorem absentMindedPassenger_last_passenger_reservedSeatProbability (n : ℕ) (hn : 2 ≤ n) :
    absentMindedPassengerReservedSeatProbability n n = (1 : ℝ) / 2 := sorry

-- Proof sketch: for `2 ≤ k ≤ n`, passenger `k` gets their own seat exactly when the reduced
-- random chain hits seat `1` before it hits seat `k`. Conditioning on the first time the chain
-- enters `{1, k, …, n}` yields the standard recursion and the closed form.
/-- Exercise 8.1.2 (2): For `2 ≤ k ≤ n`, the `k`th passenger gets their reserved seat with
probability `(n - k + 1) / (n - k + 2)`. -/
theorem absentMindedPassenger_kth_passenger_reservedSeatProbability
    {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    absentMindedPassengerReservedSeatProbability n k =
      (n - k + 1 : ℝ) / (n - k + 2 : ℝ) := sorry
