module

public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.NumberTheory.Real.Irrational

public section

/- Exercise 4.11 (1): For an integer `m`, evenness is the predicate `Even m`,
and being odd is equivalent to not being even. -/
#check (Even : ℤ → Prop)
#check (Odd : ℤ → Prop)
#check Int.not_even_iff_odd

/- Exercise 4.11 (2): Every odd integer has the form `2 * n + 1`. -/
#check (Odd.exists_bit1 : ∀ {m : ℤ}, Odd m → ∃ n : ℤ, m = 2 * n + 1)

/- Exercise 4.11 (3): The product of two odd integers is odd. -/
#check (Odd.mul : ∀ {p q : ℤ}, Odd p → Odd q → Odd (p * q))

/- Exercise 4.11 (4): Every positive natural power of an odd integer is odd.
The canonical theorem is stronger: the conclusion also holds for exponent zero. -/
#check (Odd.pow : ∀ {p : ℤ} {n : ℕ}, Odd p → Odd (p ^ n))

/-- Every positive rational number has a reduced presentation as a quotient of
positive natural numbers. -/
theorem exists_pos_nat_div_coprime (a : ℚ) (ha : 0 < a) :
    ∃ m : ℕ, 0 < m ∧ ∃ n : ℕ, 0 < n ∧ a = (m : ℚ) / n ∧ Nat.Coprime m n := by
  -- Positivity identifies the integer numerator with its natural absolute value.
  have hnum : 0 < a.num := Rat.num_pos.mpr ha
  have hnumNat : 0 < a.num.natAbs := Int.natAbs_pos.mpr hnum.ne'
  have hnumAbs : (a.num.natAbs : ℤ) = a.num := Int.natAbs_of_nonneg hnum.le
  have hnumCast : ((a.num.natAbs : ℕ) : ℚ) = (a.num : ℚ) := by
    rw [← Int.cast_natCast]
    exact congrArg (fun z : ℤ ↦ (z : ℚ)) hnumAbs
  -- The canonical rational representation already has a positive reduced denominator.
  refine ⟨a.num.natAbs, hnumNat, a.den, a.den_pos, ?_, a.reduced⟩
  rw [hnumCast]
  exact (Rat.num_div_den a).symm

/-- Helper for Exercise 4.11: coprime natural numbers are not both even. -/
theorem Nat.Coprime.not_both_even {m n : ℕ} (hcop : Nat.Coprime m n) :
    ¬(Even m ∧ Even n) := by
  -- A common factor `2` would have to equal `1`, contradicting arithmetic.
  intro hEven
  have htwo : 2 = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (Even.two_dvd hEven.1) (Even.two_dvd hEven.2)
  omega

/-- Exercise 4.11 (5): Every positive rational number is a quotient of positive
natural numbers that are not both even. -/
theorem exists_pos_nat_div_not_both_even (a : ℚ) (ha : 0 < a) :
    ∃ m : ℕ, 0 < m ∧ ∃ n : ℕ, 0 < n ∧ a = (m : ℚ) / n ∧ ¬(Even m ∧ Even n) := by
  -- Reuse the reduced presentation and replace coprimality by its parity consequence.
  obtain ⟨m, hm, n, hn, haDiv, hcop⟩ := exists_pos_nat_div_coprime a ha
  exact ⟨m, hm, n, hn, haDiv, hcop.not_both_even⟩

/- Exercise 4.11 (6): The real number `Real.sqrt 2` is irrational. -/
#check irrational_sqrt_two
