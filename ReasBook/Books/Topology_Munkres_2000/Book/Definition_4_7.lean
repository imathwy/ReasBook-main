module

public import Topology_Munkres_2000.Book.Definition_4_6
public import Mathlib.RingTheory.Localization.FractionRing

public section

namespace Real

/-- Definition 4.7 (1): The integers embedded in `ℝ` are the positive integers, zero,
and the negatives of the positive integers. -/
theorem integerCastRange_eq :
    Set.range (fun z : ℤ ↦ (z : ℝ)) = ℤ₊ ∪ {0} ∪ -ℤ₊ := by
  rw [positiveIntegers_eq_range_pnatCast]
  ext x
  simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff, Set.mem_neg]
  constructor
  · rintro ⟨z, rfl⟩
    cases z with
    | ofNat n =>
        cases n with
        | zero => exact Or.inl (Or.inr (by simp))
        | succ n => exact Or.inl (Or.inl ⟨n.succPNat, by simp⟩)
    | negSucc n =>
        exact Or.inr ⟨n.succPNat, by simp [Int.negSucc_eq]⟩
  · intro hx
    rcases hx with hx | hx
    · rcases hx with ⟨n, rfl⟩ | rfl
      · exact ⟨(n : ℕ), by simp⟩
      · exact ⟨0, by simp⟩
    · rcases hx with ⟨n, hn⟩
      exact ⟨-(n : ℕ), by simpa using congrArg Neg.neg hn⟩

end Real

namespace Rat

/-- Definition 4.7 (2): Every rational number is a quotient of two integers with
nonzero denominator. -/
theorem exists_eq_int_div (q : ℚ) :
    ∃ a b : ℤ, b ≠ 0 ∧ q = (a : ℚ) / (b : ℚ) := by
  exact ⟨q.num, q.den, by exact_mod_cast q.den_nz, (num_div_den q).symm⟩

end Rat

/- The canonical integer operations are supplied by its commutative-ring structure. -/
#check Int.instCommRing

/- The canonical rational operations and fraction-field description are already available. -/
#check Rat.instField
#check Rat.isFractionRing
