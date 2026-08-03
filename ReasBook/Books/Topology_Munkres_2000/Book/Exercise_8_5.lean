module

import Topology_Munkres_2000.Book.Theorem_8_4
public import Mathlib.Analysis.Real.Sqrt

public section

/-- Helper for Exercise 8.5: subtracting one from a positive integer greater
than one gives a strictly smaller positive integer. -/
private lemma positivePredecessor_lt (i : ℕ+) (hi : 1 < i) :
    i - 1 < i := by
  -- Compare the predecessor with its successor, then recover the original index.
  calc
    i - 1 < i - 1 + 1 := PNat.lt_succ_self _
    _ = i := PNat.sub_add_of_lt hi

/-- Helper for Exercise 8.5: adding one to a positive real and taking its square
root remains strictly positive. -/
private lemma positiveRealSqrtAddOne_pos (x : {x : ℝ // 0 < x}) :
    0 < Real.sqrt ((x : ℝ) + 1) := by
  -- The radicand is positive, so the positive-square-root criterion applies.
  exact Real.sqrt_pos.2 (add_pos_of_pos_of_nonneg x.property zero_le_one)

/-- Helper for Exercise 8.5: the number `3` as an element of the positive-real
subtype. -/
private def positiveThree : {x : ℝ // 0 < x} :=
  ⟨3, zero_lt_three⟩

/-- Helper for Exercise 8.5: the history rule sending the preceding value to
the square root of that value plus one. -/
private noncomputable def positiveRealSqrtAddOneStep
    {i : ℕ+} (hi : 1 < i)
    (f : Set.Iio i → {x : ℝ // 0 < x}) : {x : ℝ // 0 < x} :=
  ⟨Real.sqrt ((f ⟨i - 1, positivePredecessor_lt i hi⟩ : ℝ) + 1),
    positiveRealSqrtAddOne_pos (f ⟨i - 1, positivePredecessor_lt i hi⟩)⟩

/-- Helper for Exercise 8.5: coercing the history step to `ℝ` exposes its
square-root formula. -/
private lemma positiveRealSqrtAddOneStep_apply
    (i : ℕ+) (hi : 1 < i)
    (f : Set.Iio i → {x : ℝ // 0 < x}) :
    (positiveRealSqrtAddOneStep hi f : ℝ) =
      Real.sqrt ((f ⟨i - 1, positivePredecessor_lt i hi⟩ : ℝ) + 1) := by
  -- The coercion is the value field of the defining subtype pair.
  rfl

/-- Helper for Exercise 8.5: the abstract positive recursion formula is
equivalent to the displayed real-valued square-root recurrence. -/
private lemma isPositiveRecursionFormula_iff_sqrtAddOne
    (h : ℕ+ → {x : ℝ // 0 < x}) :
    h.IsPositiveRecursionFormula positiveThree positiveRealSqrtAddOneStep ↔
      (h 1 : ℝ) = 3 ∧
        ∀ (i : ℕ+) (_hi : 1 < i),
          (h i : ℝ) = Real.sqrt ((h (i - 1) : ℝ) + 1) := by
  -- Translate the subtype-valued recursion equations to equalities of real values.
  constructor
  · intro hh
    constructor
    · exact congrArg Subtype.val hh.eq_one
    · intro i hi
      have h_step := congrArg Subtype.val (hh.eq_of_one_lt i hi)
      rw [positiveRealSqrtAddOneStep_apply] at h_step
      exact h_step
  · rintro ⟨h_one, h_step⟩
    apply Function.IsPositiveRecursionFormula.mk
    · apply Subtype.ext
      exact h_one
    · intro i hi
      apply Subtype.ext
      rw [positiveRealSqrtAddOneStep_apply]
      exact h_step i hi

/-- Exercise 8.5: there is a unique sequence of positive real numbers starting
at `3` and obtained by repeatedly taking the square root of the preceding term
plus `1`. -/
theorem existsUniquePositiveRealSqrtAddOneRecurrence :
    ∃! h : ℕ+ → {x : ℝ // 0 < x},
      (h 1 : ℝ) = 3 ∧
        ∀ (i : ℕ+) (hi : 1 < i),
          (h i : ℝ) = Real.sqrt ((h (i - 1) : ℝ) + 1) := by
  -- Obtain the canonical recursive function, then transport its property and uniqueness.
  obtain ⟨h, hh, h_unique⟩ :=
    existsUnique_positiveRecursive
      {x : ℝ // 0 < x} positiveThree positiveRealSqrtAddOneStep
  refine ⟨h, (isPositiveRecursionFormula_iff_sqrtAddOne h).mp hh, ?_⟩
  intro g hg
  exact h_unique g ((isPositiveRecursionFormula_iff_sqrtAddOne g).mpr hg)
