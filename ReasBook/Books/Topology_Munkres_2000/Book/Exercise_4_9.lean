module

public import Topology_Munkres_2000.Book.Exercise_4_8
public import Topology_Munkres_2000.Book.Proposition_4_4

public section

/- Exercise 4.9 (1): Every nonempty set of integers that is bounded above has a
greatest element. This is the integer case of the canonical successor-order theorem. -/
#check (BddAbove.exists_isGreatest_of_nonempty :
  ∀ {s : Set ℤ}, BddAbove s → s.Nonempty → ∃ n, IsGreatest s n)

namespace Real

/-- Exercise 4.9 (2): Every noninteger real lies strictly between unique consecutive
integers. -/
theorem existsUnique_int_between (x : ℝ) (hx : x ∉ Set.range Int.cast) :
    ∃! n : ℤ, n < x ∧ x < n + 1 := by
  -- The floor of `x` supplies the consecutive integer interval containing `x`.
  refine ⟨⌊x⌋, ⟨Int.floor_lt_self_iff.mpr hx, Int.lt_floor_add_one x⟩, ?_⟩
  -- Any other such integer is characterized by the same floor equation.
  intro n hn
  exact (Int.floor_eq_iff.mpr ⟨hn.1.le, hn.2⟩).symm

/-- Exercise 4.9 (3): Every real interval of length greater than one contains an
integer. -/
theorem exists_int_between_of_one_lt_sub (x y : ℝ) (h : 1 < x - y) :
    ∃ n : ℤ, y < n ∧ n < x := by
  -- The successor of the floor of `y` is the first integer strictly above `y`.
  have hlower : y < ((⌊y⌋ + 1 : ℤ) : ℝ) := by
    simpa only [Int.cast_add, Int.cast_one] using Int.lt_floor_add_one y
  refine ⟨⌊y⌋ + 1, hlower, ?_⟩
  -- Its real value is at most `y + 1`, which is strictly below `x`.
  have hy : y + 1 < x := by
    linarith
  have hfloor : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
  have hupper : (⌊y⌋ : ℝ) + 1 < x := by
    linarith
  simpa only [Int.cast_add, Int.cast_one] using hupper

/- Exercise 4.9 (4): Between two distinct ordered reals lies a rational number. -/
#check (exists_rat_btwn :
  ∀ {y x : ℝ}, y < x → ∃ z : ℚ, y < z ∧ z < x)

end Real
