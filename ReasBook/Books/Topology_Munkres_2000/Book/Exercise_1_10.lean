module

public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.NormNum
public import Mathlib.Data.Rel

public section

/-- Clause (a) of Exercise 1.10: The pairs whose first coordinate is an
integer form the Cartesian product of the integer-valued reals with `Set.univ`. -/
theorem integerFirstCoordinate_eq_prod :
    ({p : ℝ × ℝ | p.1 ∈ Set.range Int.cast} : Set (ℝ × ℝ)) =
      (Set.range Int.cast : Set ℝ) ×ˢ Set.univ := by
  ext p
  simp

/-- Clause (b) of Exercise 1.10: The pairs whose second coordinate lies in
`(0, 1]` form `Set.univ ×ˢ Set.Ioc 0 1`. -/
theorem positiveAtMostOneSecondCoordinate_eq_prod :
    ({p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ 1} : Set (ℝ × ℝ)) =
      Set.univ ×ˢ Set.Ioc 0 1 := by
  ext p
  simp

/-- Helper for Exercise 1.10: a set equal to a Cartesian product contains the
point obtained by taking the first coordinate of one member and the second
coordinate of another. -/
lemma cross_mem_of_eq_prod {α β : Type*} {S : Set (α × β)} {A : Set α} {B : Set β}
    {p q : α × β} (hS : S = A ×ˢ B) (hp : p ∈ S) (hq : q ∈ S) :
    (p.1, q.2) ∈ S := by
  -- Transport both memberships to the product and recombine their coordinates.
  rw [hS] at hp hq ⊢
  exact ⟨hp.1, hq.2⟩

/-- Exercise 1.10 (c): The strict upper half-plane above the
diagonal is not the Cartesian product of two subsets of `ℝ`. -/
theorem strictAboveDiagonal_not_eq_prod :
    ¬ ∃ A B : Set ℝ,
      ({p : ℝ × ℝ | p.2 > p.1} : Set (ℝ × ℝ)) = A ×ˢ B := by
  rintro ⟨A, B, hS⟩
  -- Two points above the diagonal would force their forbidden mixed point.
  have hFirst : ((1, 2) : ℝ × ℝ) ∈ {p : ℝ × ℝ | p.2 > p.1} := by
    norm_num
  have hSecond : ((0, 1) : ℝ × ℝ) ∈ {p : ℝ × ℝ | p.2 > p.1} := by
    norm_num
  have hDiagonal := cross_mem_of_eq_prod hS hFirst hSecond
  norm_num at hDiagonal

/-- Clause (d) of Exercise 1.10: The pairs with noninteger first coordinate
and integer second coordinate form the stated Cartesian product. -/
theorem nonintegerIntegerCoordinates_eq_prod :
    ({p : ℝ × ℝ |
        p.1 ∉ Set.range Int.cast ∧ p.2 ∈ Set.range Int.cast} : Set (ℝ × ℝ)) =
      (Set.range Int.cast : Set ℝ)ᶜ ×ˢ (Set.range Int.cast : Set ℝ) := by
  ext p
  simp

/-- Exercise 1.10 (e): The open unit disk is not the Cartesian
product of two subsets of `ℝ`. -/
theorem openUnitDisk_not_eq_prod :
    ¬ ∃ A B : Set ℝ,
      ({p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1} : Set (ℝ × ℝ)) = A ×ˢ B := by
  rintro ⟨A, B, hS⟩
  -- Axis points in the disk would force a mixed point lying outside the disk.
  have hHorizontal : (((3 / 4 : ℝ), 0) : ℝ × ℝ) ∈
      {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1} := by
    norm_num
  have hVertical : ((0, (3 / 4 : ℝ)) : ℝ × ℝ) ∈
      {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1} := by
    norm_num
  have hOutside := cross_mem_of_eq_prod hS hHorizontal hVertical
  norm_num at hOutside
