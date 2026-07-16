import Mathlib
import chapter1_reference_format.Chap01.Definition_1_1_35

-- Declarations for this item will be appended below by the statement pipeline.

open scoped nonZeroDivisors

/-- Theorem 1.1.82 (1): for a positive modulus, every nonzero residue class modulo `n` is either a
unit or a zero divisor, formalized with the chapter's source-facing predicate
`IsLeftZeroDivisor`. -/
-- Proof sketch: use the finite commutative ring structure on `ZMod n`; for a nonzero class `x`,
-- either `x` is a unit, or else `x ∉ (ZMod n)⁰`, which yields a nontrivial annihilator and hence a
-- zero divisor in the sense of Definition 1.1.35.
theorem zmod_nonzero_eq_unit_or_zero_divisor {n : ℕ} (hn : 0 < n) :
    {x : ZMod n | x ≠ 0} =
      ({x : ZMod n | IsUnit x} \ ({0} : Set (ZMod n))) ∪ {x : ZMod n | IsLeftZeroDivisor x} := by
  haveI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  ext x
  constructor
  · intro hx
    by_cases hunit : IsUnit x
    · exact Or.inl ⟨hunit, hx⟩
    · right
      have hmem : x ∉ (ZMod n)⁰ := by
        rw [← isUnit_iff_mem_nonZeroDivisors_of_finite]
        exact hunit
      rcases notMem_nonZeroDivisors_iff_right.mp hmem with ⟨y, hyx, hy⟩
      exact ⟨hx, y, hy, hyx⟩
  · rintro (hxUnit | hxZero)
    · exact hxUnit.2
    · exact hxZero.1

/-- Theorem 1.1.82 (2): the units in `ZMod n` and the zero divisors in `ZMod n` are disjoint. -/
-- Proof sketch: a unit lies in `(ZMod n)⁰`; if it were a zero divisor, its nontrivial annihilator
-- would contradict cancellation against a non-zero-divisor.
theorem zmod_unit_disjoint_zero_divisor (n : ℕ) :
    Disjoint {x : ZMod n | IsUnit x} {x : ZMod n | IsLeftZeroDivisor x} := by
  rw [Set.disjoint_left]
  intro x hxUnit hxZero
  rcases hxZero with ⟨_, y, hy, hyx⟩
  exact hy ((mul_right_mem_nonZeroDivisors_eq_zero_iff hxUnit.mem_nonZeroDivisors).mp hyx)

/-- A residue class modulo a positive integer `n` fails to be a non-zero divisor exactly when the
gcd of a natural representative with `n` is greater than `1`. -/
-- Proof sketch: combine `ZMod.mul_inv_eq_gcd` with the characterization of membership in
-- `(ZMod n)⁰`; the element fails to be a non-zero divisor precisely when its gcd with `n` is not
-- `1`, and positivity of `n` rules out the case `gcd a n = 0`.
theorem zmod_natCast_not_mem_nonZeroDivisors_iff_one_lt_gcd {a n : ℕ} (hn : 0 < n) :
    ((a : ZMod n) ∉ (ZMod n)⁰) ↔ 1 < Nat.gcd a n := by
  haveI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rw [← isUnit_iff_mem_nonZeroDivisors_of_finite, ZMod.isUnit_iff_coprime,
    Nat.coprime_iff_gcd_eq_one]
  have hgcd_pos : 0 < Nat.gcd a n := Nat.gcd_pos_of_pos_right a hn
  omega

/-- Theorem 1.1.82 (3): a residue class modulo a positive integer `n` is a zero divisor exactly
when it is nonzero and the gcd of a natural representative with `n` is greater than `1`. -/
-- Proof sketch: by Definition 1.1.35, a zero divisor is a nonzero element that is not
-- right-regular; in the commutative ring `ZMod n`, right-regularity is membership in `(ZMod n)⁰`,
-- so the preceding bridge theorem supplies the gcd criterion.
theorem zmod_natCast_isLeftZeroDivisor_iff {a n : ℕ} (hn : 0 < n) :
    IsLeftZeroDivisor (a : ZMod n) ↔ (a : ZMod n) ≠ 0 ∧ 1 < Nat.gcd a n := by
  haveI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rw [isLeftZeroDivisor_iff_ne_zero_and_not_isRightRegular,
    isRightRegular_iff_mem_nonZeroDivisorsRight, nonZeroDivisorsRight_eq_nonZeroDivisors]
  rw [zmod_natCast_not_mem_nonZeroDivisors_iff_one_lt_gcd hn]

/-- Theorem 1.1.82 (4): a residue class modulo `n` is a unit exactly when the gcd of a natural
representative with `n` is `1`. -/
-- Proof sketch: rewrite `IsUnit (a : ZMod n)` using `ZMod.isUnit_iff_coprime` and then unfold
-- coprimality as the equation `Nat.gcd a n = 1`.
theorem zmod_natCast_isUnit_iff_gcd_eq_one (a n : ℕ) :
    IsUnit (a : ZMod n) ↔ Nat.gcd a n = 1 := by
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_iff_gcd_eq_one]
