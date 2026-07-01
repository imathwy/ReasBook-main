import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {R : Type u}

/-- Definition 1.1.35 (1): a left zero divisor is a nonzero element `a` for which some nonzero
element `b` satisfies `b * a = 0`. -/
def IsLeftZeroDivisor [Mul R] [Zero R] (a : R) : Prop :=
  a ≠ 0 ∧ ∃ b : R, b ≠ 0 ∧ b * a = 0

/-- A left zero divisor is exactly a nonzero element that is not right-regular. -/
-- Proof sketch: use `isRightRegular_iff_left_eq_zero_of_mul` to rewrite right-regularity as the
-- statement that every left annihilator of `a` is zero, and then negate that statement while
-- keeping the textbook requirement `a ≠ 0`.
theorem isLeftZeroDivisor_iff_ne_zero_and_not_isRightRegular [NonUnitalNonAssocRing R] {a : R} :
    IsLeftZeroDivisor a ↔ a ≠ 0 ∧ ¬ IsRightRegular a := by
  classical
  rw [isRightRegular_iff_left_eq_zero_of_mul]
  constructor
  · rintro ⟨ha, b, hb, hba⟩
    refine ⟨ha, ?_⟩
    intro h
    exact hb (h b hba)
  · rintro ⟨ha, h⟩
    rw [not_forall] at h
    rcases h with ⟨b, h⟩
    rw [Classical.not_imp] at h
    exact ⟨ha, b, h.2, h.1⟩

/-- Definition 1.1.35 (2): a right zero divisor is a nonzero element `a` for which some nonzero
element `b` satisfies `a * b = 0`. -/
def IsRightZeroDivisor [Mul R] [Zero R] (a : R) : Prop :=
  a ≠ 0 ∧ ∃ b : R, b ≠ 0 ∧ a * b = 0

/-- A right zero divisor is exactly a nonzero element that is not left-regular. -/
-- Proof sketch: use `isLeftRegular_iff_right_eq_zero_of_mul` to express left-regularity as the
-- vanishing of every right annihilator of `a`, then negate that characterization and retain the
-- textbook nonzero hypothesis on `a`.
theorem isRightZeroDivisor_iff_ne_zero_and_not_isLeftRegular [NonUnitalNonAssocRing R] {a : R} :
    IsRightZeroDivisor a ↔ a ≠ 0 ∧ ¬ IsLeftRegular a := by
  classical
  rw [isLeftRegular_iff_right_eq_zero_of_mul]
  constructor
  · rintro ⟨ha, b, hb, hab⟩
    refine ⟨ha, ?_⟩
    intro h
    exact hb (h b hab)
  · rintro ⟨ha, h⟩
    rw [not_forall] at h
    rcases h with ⟨b, h⟩
    rw [Classical.not_imp] at h
    exact ⟨ha, b, h.2, h.1⟩

/- Definition 1.1.35 (3): a domain in the textbook sense is a ring with the canonical property
`NoZeroDivisors R`; equivalently, the product of two nonzero elements is nonzero. -/
recall NoZeroDivisors (R : Type u) [Mul R] [Zero R] : Prop

/-- A type has no zero divisors exactly when the product of two nonzero elements is nonzero. -/
-- Proof sketch: one direction is the contrapositive of `eq_zero_or_eq_zero_of_mul_eq_zero`; for
-- the converse, if `a * b = 0`, then the assumed nonvanishing criterion rules out the case where
-- both `a` and `b` are nonzero.
theorem noZeroDivisors_iff_mul_ne_zero_of_ne_zero [Mul R] [Zero R] :
    NoZeroDivisors R ↔ ∀ ⦃a b : R⦄, a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by
  constructor
  · intro h a b ha hb
    letI : NoZeroDivisors R := h
    exact mul_ne_zero ha hb
  · intro h
    refine ⟨fun {a b} hab ↦ ?_⟩
    by_cases ha : a = 0
    · exact Or.inl ha
    · by_cases hb : b = 0
      · exact Or.inr hb
      · exact False.elim (h ha hb hab)
