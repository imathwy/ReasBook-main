module

import Topology_Munkres_2000.Book.Theorem_8_4
public import Mathlib.Data.Nat.Fib.Basic

public section

/-- The Fibonacci recurrence, restricted to positive indices and written in the
source order. -/
theorem Nat.fib_add_two_pnat (n : ℕ+) :
    Nat.fib (n + 2) = Nat.fib (n + 1) + Nat.fib n := by
  -- Apply the usual natural-number recurrence and restore the source order.
  simpa only [PNat.add_coe, add_comm] using
    (Nat.fib_add_two (n := (n : ℕ)))

/-- Helper for Exercise 8.4: subtracting a smaller positive integer gives a
strictly smaller positive integer. -/
private lemma PNat.sub_lt_self_of_lt (i b : ℕ+) (h : b < i) :
    i - b < i := by
  -- Compare the difference with the result of adding back the subtracted term.
  calc
    i - b < i - b + b := PNat.lt_add_right (i - b) b
    _ = i := PNat.sub_add_of_lt h

/-- Helper for Exercise 8.4: an index above `1` is `2` or lies two steps after
another positive index. -/
private lemma PNat.eq_two_or_exists_eq_add_two_of_one_lt
    (i : ℕ+) (hi : 1 < i) :
    i = 2 ∨ ∃ n : ℕ+, i = n + 2 := by
  -- Separate the second index; every larger index has a positive two-step predecessor.
  by_cases h_two : i = 2
  · exact Or.inl h_two
  · right
    have h_two_lt : 2 < i := by
      have h_two_le : (2 : ℕ+) ≤ i := PNat.add_one_le_iff.mpr hi
      exact lt_of_le_of_ne h_two_le (Ne.symm h_two)
    exact ⟨i - 2, (PNat.sub_add_of_lt h_two_lt).symm⟩

/-- Helper for Exercise 8.4: the strict-history rule defining the positive
Fibonacci sequence. -/
private def positiveFibonacciStep
    {i : ℕ+} (hi : 1 < i) (history : Set.Iio i → ℕ) : ℕ :=
  if h_two : 2 < i then
    history ⟨i - 1, PNat.sub_lt_self_of_lt i 1 hi⟩ +
      history ⟨i - 2, PNat.sub_lt_self_of_lt i 2 h_two⟩
  else 1

/-- Helper for Exercise 8.4: the strict-history rule returns the second initial
Fibonacci value at index `2`. -/
private lemma positiveFibonacciStep_two
    (hi : (1 : ℕ+) < 2) (history : Set.Iio (2 : ℕ+) → ℕ) :
    positiveFibonacciStep hi history = 1 := by
  -- At index `2`, the recursive branch is unavailable.
  simp only [positiveFibonacciStep, lt_self_iff_false, ↓reduceDIte]

/-- Helper for Exercise 8.4: at index `n + 2`, the strict-history rule reads
the preceding two values. -/
private lemma positiveFibonacciStep_add_two
    (f : ℕ+ → ℕ) (n : ℕ+) (hi : 1 < n + 2) :
    positiveFibonacciStep hi ((Set.Iio (n + 2)).restrict f) =
      f (n + 1) + f n := by
  -- Select the recursive branch and normalize its two predecessor indices.
  have h_two_lt : (2 : ℕ+) < n + 2 := PNat.lt_add_left 2 n
  have h_sub_one : n + 2 - 1 = n + 1 := by
    have h_two_eq : (2 : ℕ+) = 1 + 1 := rfl
    rw [h_two_eq, ← add_assoc, PNat.add_sub]
  have h_sub_two : n + 2 - 2 = n := by
    exact PNat.add_sub
  simp only [positiveFibonacciStep, dif_pos h_two_lt, Set.restrict_apply]
  rw [h_sub_one, h_sub_two]

/-- Helper for Exercise 8.4: the abstract positive recursion formula is
equivalent to the two initial Fibonacci values and the displayed recurrence. -/
private lemma isPositiveRecursionFormula_positiveFibonacci_iff
    (f : ℕ+ → ℕ) :
    f.IsPositiveRecursionFormula 1 positiveFibonacciStep ↔
      f 1 = 1 ∧ f 2 = 1 ∧
        ∀ n : ℕ+, f (n + 2) = f (n + 1) + f n := by
  -- Read the initial and recursive equations from the abstract recursion predicate.
  constructor
  · intro hf
    have h_one_two : (1 : ℕ+) < 2 := by
      norm_num
    refine ⟨hf.eq_one, ?_, ?_⟩
    · calc
        f 2 = positiveFibonacciStep h_one_two ((Set.Iio 2).restrict f) :=
          hf.eq_of_one_lt 2 h_one_two
        _ = 1 := positiveFibonacciStep_two h_one_two ((Set.Iio 2).restrict f)
    · intro n
      have h_one_lt : (1 : ℕ+) < n + 2 := by
        exact h_one_two.trans (PNat.lt_add_left 2 n)
      calc
        f (n + 2) =
            positiveFibonacciStep h_one_lt ((Set.Iio (n + 2)).restrict f) :=
          hf.eq_of_one_lt (n + 2) h_one_lt
        _ = f (n + 1) + f n := positiveFibonacciStep_add_two f n h_one_lt
  · rintro ⟨h_one, h_two, h_rec⟩
    -- Decompose every later index into the second index or a two-step successor.
    apply Function.IsPositiveRecursionFormula.mk h_one
    intro i hi
    rcases PNat.eq_two_or_exists_eq_add_two_of_one_lt i hi with h_eq | ⟨n, h_eq⟩
    · subst i
      calc
        f 2 = 1 := h_two
        _ = positiveFibonacciStep hi ((Set.Iio 2).restrict f) :=
          (positiveFibonacciStep_two hi ((Set.Iio 2).restrict f)).symm
    · subst i
      calc
        f (n + 2) = f (n + 1) + f n := h_rec n
        _ = positiveFibonacciStep hi ((Set.Iio (n + 2)).restrict f) :=
          (positiveFibonacciStep_add_two f n hi).symm

/-- Exercise 8.4. A positive-indexed sequence with the Fibonacci initial values
and recurrence exists uniquely. -/
theorem existsUnique_positiveFibonacci :
    ∃! f : ℕ+ → ℕ,
      f 1 = 1 ∧ f 2 = 1 ∧
        ∀ n : ℕ+, f (n + 2) = f (n + 1) + f n := by
  -- Instantiate Theorem 8.4 and transport its property through the bridge lemma.
  obtain ⟨f, hf, h_unique⟩ :=
    existsUnique_positiveRecursive ℕ 1 positiveFibonacciStep
  refine ⟨f, (isPositiveRecursionFormula_positiveFibonacci_iff f).mp hf, ?_⟩
  intro g hg
  exact h_unique g ((isPositiveRecursionFormula_positiveFibonacci_iff g).mpr hg)

/-- A positive-indexed sequence with the Fibonacci initial values and recurrence
is the restriction of the canonical sequence `Nat.fib`. -/
theorem positiveFibonacci_eq_fib
    (f : ℕ+ → ℕ)
    (h_one : f 1 = 1)
    (h_two : f 2 = 1)
    (h_rec : ∀ n : ℕ+, f (n + 2) = f (n + 1) + f n) :
    f = fun n : ℕ+ ↦ Nat.fib n := by
  -- Compare both sequences with the unique sequence supplied by the exercise.
  obtain ⟨u, hu, h_unique⟩ := existsUnique_positiveFibonacci
  have h_f : f = u := h_unique f ⟨h_one, h_two, h_rec⟩
  have h_fib_property :
      (fun n : ℕ+ ↦ Nat.fib n) 1 = 1 ∧
        (fun n : ℕ+ ↦ Nat.fib n) 2 = 1 ∧
          ∀ n : ℕ+,
            (fun k : ℕ+ ↦ Nat.fib k) (n + 2) =
              (fun k : ℕ+ ↦ Nat.fib k) (n + 1) +
                (fun k : ℕ+ ↦ Nat.fib k) n := by
    -- The canonical natural-number Fibonacci sequence satisfies the same equations.
    refine ⟨Nat.fib_one, Nat.fib_two, ?_⟩
    intro n
    exact Nat.fib_add_two_pnat n
  have h_fib : (fun n : ℕ+ ↦ Nat.fib n) = u :=
    h_unique (fun n : ℕ+ ↦ Nat.fib n) h_fib_property
  exact h_f.trans h_fib.symm
