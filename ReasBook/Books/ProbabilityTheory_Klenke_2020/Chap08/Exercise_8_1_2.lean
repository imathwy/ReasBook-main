import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
