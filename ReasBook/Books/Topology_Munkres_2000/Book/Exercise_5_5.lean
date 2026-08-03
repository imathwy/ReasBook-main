module

public import Mathlib.Tactic.PNatToNat
public import Mathlib.Tactic.Rify
public import Mathlib.Order.SetNotation
public import Mathlib.Order.Minimal

import Mathlib.Tactic.NormNum

public section

/-- Exercise 5.5 (1): The real sequences with integer-valued coordinates form
the Cartesian product of the integer-valued reals in every coordinate. -/
theorem integerSequences_eq_pi :
    {x : ℕ+ → ℝ | ∀ i, x i ∈ Set.range Int.cast} =
      Set.univ.pi (fun _ ↦ Set.range Int.cast) := by
  ext
  simp

/-- Exercise 5.5 (2): The real sequences satisfying `i ≤ x i` in every
coordinate form the Cartesian product of the intervals `Set.Ici (i : ℝ)`. -/
theorem coordinateLowerBounds_eq_pi :
    {x : ℕ+ → ℝ | ∀ i : ℕ+, (i : ℝ) ≤ x i} =
      Set.univ.pi (fun i : ℕ+ ↦ Set.Ici (i : ℝ)) := by
  ext
  simp

/-- Exercise 5.5 (3): The real sequences whose coordinates are integers from
index `100` onward form a Cartesian product with earlier coordinates unrestricted. -/
theorem eventuallyIntegerSequences_eq_pi :
    {x : ℕ+ → ℝ | ∀ i, 100 ≤ i → x i ∈ Set.range Int.cast} =
      Set.univ.pi (fun i ↦ if 100 ≤ i then Set.range Int.cast else Set.univ) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  constructor
  · intro h i
    split_ifs with hi
    · exact h i hi
    · simp
  · intro h i hi
    simpa [hi] using h i

/-- Exercise 5.5 (4): The condition that coordinates `2` and `3` are equal
cannot be expressed as a Cartesian product of coordinate subsets of `ℝ`. -/
theorem coordinateEquality_not_pi :
    ¬ ∃ A : ℕ+ → Set ℝ, {x : ℕ+ → ℝ | x 2 = x 3} = Set.univ.pi A := by
  rintro ⟨A, hA⟩
  have h_const (r : ℝ) : (fun _ : ℕ+ ↦ r) ∈ Set.univ.pi A := by
    rw [← hA]
    simp
  have h_all (x : ℕ+ → ℝ) : x ∈ Set.univ.pi A := by
    rw [Set.mem_pi]
    intro i _
    exact Set.mem_pi.mp (h_const (x i)) i (Set.mem_univ i)
  have h_diagonal := h_all (fun i : ℕ+ ↦ if i = 2 then (0 : ℝ) else 1)
  rw [← hA] at h_diagonal
  norm_num at h_diagonal
