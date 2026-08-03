module

public import Topology_Munkres_2000.Book.Definition_7_1.CountablyInfinite

public section

/-- The natural-number value of the displayed integer enumeration. -/
def integerPositiveIndexNat (n : ℤ) : ℕ :=
  if 0 < n then 2 * n.natAbs else 2 * n.natAbs + 1

/-- The natural-number value of the integer enumeration is positive. -/
theorem integerPositiveIndexNat_pos (n : ℤ) : 0 < integerPositiveIndexNat n := by
  -- Each sign branch is visibly a positive natural number.
  unfold integerPositiveIndexNat
  split_ifs with hn
  · have hnabs : 0 < n.natAbs := Int.natAbs_pos.mpr hn.ne'
    omega
  · omega

/-- The displayed map from integers to positive integers. -/
def integerPositiveIndex (n : ℤ) : ℕ+ :=
  ⟨integerPositiveIndexNat n, integerPositiveIndexNat_pos n⟩

/-- On positive integers, the displayed map sends `n` to `2 * n`. -/
theorem integerPositiveIndex_of_pos (n : ℤ) (hn : 0 < n) :
    (integerPositiveIndex n : ℤ) = 2 * n := by
  -- On the positive branch, `natAbs` casts back to the original integer.
  have hval : (integerPositiveIndex n).val = 2 * n.natAbs := by
    change integerPositiveIndexNat n = 2 * n.natAbs
    rw [integerPositiveIndexNat, if_pos hn]
  have hcast := congrArg Int.ofNat hval
  calc
    (integerPositiveIndex n : ℤ) = Int.ofNat (2 * n.natAbs) := hcast
    _ = 2 * n := by
      rw [Int.ofNat_eq_natCast, Int.natCast_mul, Int.natAbs_of_nonneg hn.le]
      omega

/-- On nonpositive integers, the displayed map sends `n` to `-2 * n + 1`. -/
theorem integerPositiveIndex_of_nonpos (n : ℤ) (hn : n ≤ 0) :
    (integerPositiveIndex n : ℤ) = -2 * n + 1 := by
  -- On the nonpositive branch, the cast of `natAbs` is `-n`.
  have hval : (integerPositiveIndex n).val = 2 * n.natAbs + 1 := by
    change integerPositiveIndexNat n = 2 * n.natAbs + 1
    rw [integerPositiveIndexNat, if_neg (not_lt_of_ge hn)]
  have hcast := congrArg Int.ofNat hval
  calc
    (integerPositiveIndex n : ℤ) = Int.ofNat (2 * n.natAbs + 1) := hcast
    _ = -2 * n + 1 := by
      rw [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul, Int.natCast_one,
        Int.ofNat_natAbs_of_nonpos hn]
      omega

/-- The inverse of the displayed integer enumeration: even positive integers index
positive integers, while odd positive integers index nonpositive integers. -/
def positiveIndexInteger (n : ℕ+) : ℤ :=
  if Even n.val then Int.ofNat (n.val / 2) else -Int.ofNat (n.val / 2)

/-- Helper for Example 7.1: decoding an encoded integer recovers the integer. -/
lemma positiveIndexInteger_integerPositiveIndex (n : ℤ) :
    positiveIndexInteger (integerPositiveIndex n) = n := by
  -- The sign of `n` selects the even or odd branch of the encoding.
  by_cases hn : 0 < n
  · have heven : Even (integerPositiveIndex n).val := by
      change Even (integerPositiveIndexNat n)
      rw [integerPositiveIndexNat, if_pos hn]
      exact even_two_mul n.natAbs
    unfold positiveIndexInteger
    rw [if_pos heven]
    change Int.ofNat (integerPositiveIndexNat n / 2) = n
    rw [integerPositiveIndexNat, if_pos hn]
    have hdiv : 2 * n.natAbs / 2 = n.natAbs := by
      omega
    rw [hdiv, Int.ofNat_eq_natCast, Int.natAbs_of_nonneg hn.le]
  · have hnle : n ≤ 0 := le_of_not_gt hn
    have hodd : Odd (integerPositiveIndex n).val := by
      change Odd (integerPositiveIndexNat n)
      rw [integerPositiveIndexNat, if_neg hn]
      exact odd_two_mul_add_one n.natAbs
    unfold positiveIndexInteger
    rw [if_neg (Nat.not_even_iff_odd.mpr hodd)]
    change -Int.ofNat (integerPositiveIndexNat n / 2) = n
    rw [integerPositiveIndexNat, if_neg hn]
    have hdiv : (2 * n.natAbs + 1) / 2 = n.natAbs := by
      omega
    rw [hdiv, Int.ofNat_eq_natCast, Int.ofNat_natAbs_of_nonpos hnle]
    omega

/-- Helper for Example 7.1: encoding a decoded positive integer recovers its index. -/
lemma integerPositiveIndex_positiveIndexInteger (m : ℕ+) :
    integerPositiveIndex (positiveIndexInteger m) = m := by
  -- Parity determines which signed integer represents the positive index.
  by_cases hm : Even m.val
  · have hreconstruct := Nat.two_mul_div_two_of_even hm
    have hmpos : 0 < m.val := m.property
    have hhalf : 0 < m.val / 2 := by
      omega
    have hinverse : positiveIndexInteger m = Int.ofNat (m.val / 2) := by
      unfold positiveIndexInteger
      rw [if_pos hm]
    apply Subtype.ext
    change integerPositiveIndexNat (positiveIndexInteger m) = m.val
    rw [integerPositiveIndexNat, if_pos]
    · rw [hinverse, Int.ofNat_eq_natCast, Int.natAbs_natCast]
      exact hreconstruct
    · rw [hinverse, Int.ofNat_eq_natCast, Int.natCast_pos]
      exact hhalf
  · have hodd : Odd m.val := Nat.not_even_iff_odd.mp hm
    have hreconstruct := Nat.two_mul_div_two_add_one_of_odd hodd
    have hinverse : positiveIndexInteger m = -Int.ofNat (m.val / 2) := by
      unfold positiveIndexInteger
      rw [if_neg hm]
    apply Subtype.ext
    change integerPositiveIndexNat (positiveIndexInteger m) = m.val
    rw [integerPositiveIndexNat, if_neg]
    · rw [hinverse, Int.natAbs_neg, Int.ofNat_eq_natCast, Int.natAbs_natCast]
      exact hreconstruct
    · rw [hinverse]
      exact not_lt_of_ge (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg _))

/-- Example 7.1. The displayed enumeration is an equivalence from `ℤ` to the
positive integers `ℕ+`. -/
def integerEquivPositive : ℤ ≃ ℕ+ where
  toFun := integerPositiveIndex
  invFun := positiveIndexInteger
  left_inv := positiveIndexInteger_integerPositiveIndex
  right_inv := integerPositiveIndex_positiveIndexInteger

/-- The displayed map from `ℤ` to `ℕ+` is bijective. -/
theorem integerPositiveIndex_bijective : Function.Bijective integerPositiveIndex :=
  integerEquivPositive.bijective

/-- Example 7.1. The set of integers is countably infinite. -/
theorem integers_countablyInfinite : (Set.univ : Set ℤ).CountablyInfinite :=
  Set.CountablyInfinite.ofEquiv ((Equiv.Set.univ ℤ).trans integerEquivPositive)
