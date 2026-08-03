module

public import Mathlib.GroupTheory.Torsion
public import Mathlib.Order.Disjoint

public section

/-- Helper for Exercise 67.2: an additive subgroup of `ℤ` disjoint from `2ℤ` is trivial. -/
private lemma eq_bot_of_disjoint_zmultiples_two (H : AddSubgroup ℤ)
    (h : Disjoint (AddSubgroup.zmultiples 2) H) : H = ⊥ := by
  -- Doubling an element of `H` puts it in both subgroups, so disjointness kills it.
  rw [AddSubgroup.eq_bot_iff_forall]
  intro x hx
  have hEven : 2 • x ∈ AddSubgroup.zmultiples (2 : ℤ) := by
    rw [Int.mem_zmultiples_iff, Int.nsmul_eq_mul]
    exact dvd_mul_right 2 x
  have hInH : 2 • x ∈ H := H.nsmul_mem hx 2
  have hDouble : 2 • x = 0 := AddSubgroup.disjoint_def.mp h hEven hInH
  -- The additive group of integers is torsion-free, hence the original element vanishes.
  exact two_nsmul_eq_zero.mp hDouble

/-- Helper for Exercise 67.2: the additive subgroup `2ℤ` is not all of `ℤ`. -/
private lemma zmultiples_two_ne_top : AddSubgroup.zmultiples (2 : ℤ) ≠ ⊤ := by
  -- If `2ℤ` were top, it would contain `1`, contradicting elementary divisibility.
  intro hTop
  have hOne : (1 : ℤ) ∈ AddSubgroup.zmultiples (2 : ℤ) := by
    rw [hTop]
    exact AddSubgroup.mem_top 1
  have hDvd : (2 : ℤ) ∣ 1 := Int.mem_zmultiples_iff.mp hOne
  norm_num at hDvd

/-- Exercise 67.2. The subgroup of even integers has no internal direct-sum complement in `ℤ`. -/
theorem evenIntegers_no_complement :
    ¬ ∃ G₂ : AddSubgroup ℤ, IsCompl (AddSubgroup.zmultiples 2) G₂ := by
  -- A hypothetical complement is disjoint from `2ℤ`, so the doubling lemma makes it bottom.
  rintro ⟨G₂, hCompl⟩
  have hBot : G₂ = ⊥ := eq_bot_of_disjoint_zmultiples_two G₂ hCompl.disjoint
  rw [hBot] at hCompl
  -- Complementarity with bottom would make `2ℤ` top, contradicting that `1` is odd.
  exact zmultiples_two_ne_top (eq_top_of_isCompl_bot hCompl)
