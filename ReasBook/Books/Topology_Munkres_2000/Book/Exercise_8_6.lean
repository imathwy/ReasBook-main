module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Analysis.Real.Sqrt

public section

/-- Part (a) of Exercise 8.6: no sequence of positive real numbers can start at
`3` and then repeatedly take the square root of the preceding term minus `1`. -/
theorem noPositiveRealSqrtSubOneRecurrence :
    ¬ ∃ h : ℕ+ → {x : ℝ // 0 < x},
      (h 1 : ℝ) = 3 ∧ ∀ n : ℕ+,
        (h (n + 1) : ℝ) = Real.sqrt ((h n : ℝ) - 1) := by
  -- Compute the first three recursive steps in the ambient real numbers.
  rintro ⟨h, h_one, h_succ⟩
  have h_two : (h ((1 : ℕ+) + 1) : ℝ) = Real.sqrt 2 := by
    rw [h_succ, h_one]
    norm_num
  have h_three : (h (((1 : ℕ+) + 1) + 1) : ℝ) = Real.sqrt (Real.sqrt 2 - 1) := by
    rw [h_succ, h_two]
  have h_four := h_succ (((1 : ℕ+) + 1) + 1)
  -- The third term is at most one, so the fourth term must be zero.
  have sqrt_two_le_two : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · norm_num
  have h_three_le_one : (h (((1 : ℕ+) + 1) + 1) : ℝ) ≤ 1 := by
    rw [h_three, Real.sqrt_le_one]
    linarith
  have fourth_sqrt_eq_zero :
      Real.sqrt ((h (((1 : ℕ+) + 1) + 1) : ℝ) - 1) = 0 :=
    Real.sqrt_eq_zero_of_nonpos (sub_nonpos.mpr h_three_le_one)
  have h_four_eq_zero : (h ((((1 : ℕ+) + 1) + 1) + 1) : ℝ) = 0 :=
    h_four.trans fourth_sqrt_eq_zero
  -- This contradicts the defining positivity of the fourth subtype value.
  have h_four_pos := (h ((((1 : ℕ+) + 1) + 1) + 1)).property
  rw [h_four_eq_zero] at h_four_pos
  exact (lt_irrefl 0) h_four_pos

/-- The recursive-definition explanation in Exercise 8.6: the preceding formula
does not define a self-map of the positive real numbers. -/
theorem sqrtSubOneDoesNotPreservePositiveReal :
    ¬ ∀ x : {x : ℝ // 0 < x}, 0 < Real.sqrt ((x : ℝ) - 1) := by
  -- The positive input `1 / 2` has a nonpositive radicand.
  intro h_preserves
  have half_pos : 0 < (1 / 2 : ℝ) := by
    norm_num
  let half : {x : ℝ // 0 < x} := ⟨1 / 2, half_pos⟩
  have h_half_pos := h_preserves half
  have half_sub_one_nonpos : (half : ℝ) - 1 ≤ 0 := by
    dsimp [half]
    norm_num
  have half_sqrt_eq_zero : Real.sqrt ((half : ℝ) - 1) = 0 :=
    Real.sqrt_eq_zero_of_nonpos half_sub_one_nonpos
  -- Hence the claimed positive output is actually zero.
  rw [half_sqrt_eq_zero] at h_half_pos
  exact (lt_irrefl 0) h_half_pos

/-- The positive-real self-map used in the modified recursion from Exercise 8.6 (3). -/
@[expose]
noncomputable def positiveRealSqrtSubOneOrFive
    (x : {x : ℝ // 0 < x}) : {x : ℝ // 0 < x} :=
  if hx : 1 < (x : ℝ) then
    ⟨Real.sqrt ((x : ℝ) - 1), Real.sqrt_pos.2 (sub_pos.2 hx)⟩
  else
    ⟨5, by norm_num⟩

/-- The sequence obtained by recursively applying `positiveRealSqrtSubOneOrFive`,
starting at `3`. -/
@[expose]
noncomputable def positiveRealPiecewiseRecurrence (n : ℕ+) : {x : ℝ // 0 < x} :=
  PNat.recOn n ⟨3, by norm_num⟩ (fun _ x ↦ positiveRealSqrtSubOneOrFive x)

@[simp]
theorem positiveRealPiecewiseRecurrence_one :
    (positiveRealPiecewiseRecurrence 1 : ℝ) = 3 := rfl

@[simp]
theorem positiveRealPiecewiseRecurrence_succ (n : ℕ+) :
    positiveRealPiecewiseRecurrence (n + 1) =
      positiveRealSqrtSubOneOrFive (positiveRealPiecewiseRecurrence n) := by
  simp [positiveRealPiecewiseRecurrence]

theorem positiveRealPiecewiseRecurrence_coe_succ (n : ℕ+) :
    (positiveRealPiecewiseRecurrence (n + 1) : ℝ) =
      if (positiveRealPiecewiseRecurrence n : ℝ) > 1 then
        Real.sqrt ((positiveRealPiecewiseRecurrence n : ℝ) - 1)
      else 5 := by
  rw [positiveRealPiecewiseRecurrence_succ]
  unfold positiveRealSqrtSubOneOrFive
  split <;> rfl

/-- Helper for Exercise 8.6: any positive-real sequence satisfying the guarded
recurrence equals the canonical recursively defined sequence. -/
lemma eq_positiveRealPiecewiseRecurrence
    (h : ℕ+ → {x : ℝ // 0 < x})
    (h_one : (h 1 : ℝ) = 3)
    (h_succ : ∀ n : ℕ+,
      (h (n + 1) : ℝ) =
        if (h n : ℝ) > 1 then Real.sqrt ((h n : ℝ) - 1) else 5) :
    h = positiveRealPiecewiseRecurrence := by
  -- Reduce function equality to the base and successor equations on `ℕ+`.
  funext n
  refine PNat.recOn n ?_ ?_
  · apply Subtype.ext
    simpa only [positiveRealPiecewiseRecurrence_one] using h_one
  · intro k h_k
    apply Subtype.ext
    -- Both successor values use the same branch after rewriting the predecessor.
    rw [h_succ k, positiveRealPiecewiseRecurrence_coe_succ k, h_k]

/-- Exercise 8.6 (3): the modified piecewise recursion determines a unique
sequence of positive real numbers. -/
theorem existsUniquePositiveRealPiecewiseRecurrence :
    ∃! h : ℕ+ → {x : ℝ // 0 < x},
      (h 1 : ℝ) = 3 ∧ ∀ n : ℕ+,
        (h (n + 1) : ℝ) =
          if (h n : ℝ) > 1 then Real.sqrt ((h n : ℝ) - 1) else 5 := by
  -- The canonical recursive sequence satisfies both displayed equations.
  refine ⟨positiveRealPiecewiseRecurrence, ?_, ?_⟩
  · constructor
    · exact positiveRealPiecewiseRecurrence_one
    · exact positiveRealPiecewiseRecurrence_coe_succ
  · intro h h_spec
    -- The companion induction lemma gives uniqueness of the witness.
    exact eq_positiveRealPiecewiseRecurrence h h_spec.1 h_spec.2
