module

import Topology_Munkres_2000.Book.Theorem_8_4
public import Topology_Munkres_2000.Book.Exercise_4_6.PositivePowers

public section

open scoped Real

namespace Real

/-- Helper for Example 8.2: subtracting one from a positive integer greater
than one gives a strictly smaller positive integer. -/
private lemma positivePredecessor_lt (i : ℕ+) (hi : 1 < i) :
    i - 1 < i := by
  -- Compare the predecessor with its successor, then recover the original index.
  calc
    i - 1 < i - 1 + 1 := PNat.lt_succ_self _
    _ = i := PNat.sub_add_of_lt hi

/-- Helper for Example 8.2: the history rule evaluates the preceding value and
multiplies it by `a`. -/
private def positivePowStep (a : ℝ) {i : ℕ+} (hi : 1 < i)
    (f : Set.Iio i → ℝ) : ℝ :=
  f ⟨i - 1, positivePredecessor_lt i hi⟩ * a

/-- Helper for Example 8.2: the positive-power history rule exposes its
predecessor multiplication formula. -/
private lemma positivePowStep_apply (a : ℝ) (i : ℕ+) (hi : 1 < i)
    (f : Set.Iio i → ℝ) :
    positivePowStep a hi f =
      f ⟨i - 1, positivePredecessor_lt i hi⟩ * a := by
  -- Unfold the named history rule at the specified initial segment.
  rfl

/-- Helper for Example 8.2: the abstract positive recursion formula is
equivalent to the displayed predecessor recurrence for powers. -/
private lemma isPositiveRecursionFormula_iff_positivePowRecurrence
    (a : ℝ) (h : ℕ+ → ℝ) :
    h.IsPositiveRecursionFormula a (positivePowStep a) ↔
      h 1 = a ∧
        ∀ (i : ℕ+) (hi : 1 < i), h i = h (i - 1) * a := by
  -- Translate the initial-value and restricted-history equations componentwise.
  constructor
  · intro hh
    constructor
    · exact hh.eq_one
    · intro i hi
      rw [hh.eq_of_one_lt i hi, positivePowStep_apply]
      rfl
  · rintro ⟨h_one, h_later⟩
    apply Function.IsPositiveRecursionFormula.mk h_one
    intro i hi
    rw [positivePowStep_apply]
    exact h_later i hi

/-- Example 8.2 (1). For a real number `a`, there is a unique function on the
positive integers satisfying the recursive equations for positive powers. -/
theorem existsUnique_positivePow (a : ℝ) :
    ∃! h : ℕ+ → ℝ,
      h 1 = a ∧
        ∀ (i : ℕ+) (hi : 1 < i), h i = h (i - 1) * a := by
  -- Apply positive-integer recursion, then transport its property and uniqueness.
  obtain ⟨h, hh, h_unique⟩ :=
    existsUnique_positiveRecursive ℝ a (positivePowStep a)
  refine ⟨h, (isPositiveRecursionFormula_iff_positivePowRecurrence a h).mp hh, ?_⟩
  intro g hg
  exact h_unique g
    ((isPositiveRecursionFormula_iff_positivePowRecurrence a g).mpr hg)

/-- Helper for Example 8.2: canonical positive powers satisfy the initial value
and predecessor recurrence. -/
private lemma positivePow_satisfiesRecurrence (a : ℝ) :
    (fun i : ℕ+ ↦ a ^ i) 1 = a ∧
      ∀ (i : ℕ+) (hi : 1 < i),
        (fun j : ℕ+ ↦ a ^ j) i = (fun j : ℕ+ ↦ a ^ j) (i - 1) * a := by
  -- Use the computation rules for positive powers at one and at successors.
  constructor
  · exact positivePow_one a
  · intro i hi
    simpa only [PNat.sub_add_of_lt hi] using positivePow_succ a (i - 1)

/-- A function on the positive integers satisfies the recursive equations for
powers of `a` exactly when it is the canonical positive-power function. -/
theorem positivePow_iff (a : ℝ) (h : ℕ+ → ℝ) :
    (h 1 = a ∧
        ∀ (i : ℕ+) (hi : 1 < i), h i = h (i - 1) * a) ↔
      h = fun i : ℕ+ ↦ a ^ i := by
  -- Compare any recurrent function with the canonical powers through uniqueness.
  obtain ⟨u, hu, h_unique⟩ := existsUnique_positivePow a
  constructor
  · intro hh
    exact (h_unique h hh).trans
      (h_unique (fun i : ℕ+ ↦ a ^ i) (positivePow_satisfiesRecurrence a)).symm
  · intro hh
    rw [hh]
    exact positivePow_satisfiesRecurrence a

end Real
