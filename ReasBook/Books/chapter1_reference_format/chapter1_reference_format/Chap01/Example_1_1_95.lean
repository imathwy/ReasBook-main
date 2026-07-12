import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Nat

section PrimitiveRootsMod

/-- Helper for Example 1.1.95: the element `2` has order `10` in `ZMod 11`. -/
lemma orderOf_two_zmod_eleven : orderOf (2 : ZMod 11) = 10 := by
  -- Fermat's little theorem gives the global order divisor `orderOf 2 ∣ 10`.
  have hpow10 : (2 : ZMod 11) ^ 10 = 1 := by
    decide
  have hdvd : orderOf (2 : ZMod 11) ∣ 10 :=
    orderOf_dvd_of_pow_eq_one hpow10
  -- The only divisors of `10` are `1`, `2`, `5`, and `10`.
  have hcases :
      orderOf (2 : ZMod 11) = 1 ∨
      orderOf (2 : ZMod 11) = 2 ∨
      orderOf (2 : ZMod 11) = 5 ∨
      orderOf (2 : ZMod 11) = 10 := by
    have hmem : orderOf (2 : ZMod 11) ∈ (10).divisors :=
      Nat.mem_divisors.mpr ⟨hdvd, by decide⟩
    have hdivs : (10).divisors = ({1, 2, 5, 10} : Finset ℕ) := by
      decide
    rw [hdivs] at hmem
    simp at hmem
    simpa [or_assoc] using hmem
  -- The source computations rule out the proper divisors.
  have hne1 : orderOf (2 : ZMod 11) ≠ 1 := by
    intro h
    have hpow : (2 : ZMod 11) ^ 1 = 1 := by
      simpa [h] using pow_orderOf_eq_one (2 : ZMod 11)
    exact (by decide : ((2 : ZMod 11) ^ 1) ≠ 1) hpow
  have hne2 : orderOf (2 : ZMod 11) ≠ 2 := by
    intro h
    have hpow : (2 : ZMod 11) ^ 2 = 1 := by
      simpa [h] using pow_orderOf_eq_one (2 : ZMod 11)
    exact (by decide : ((2 : ZMod 11) ^ 2) ≠ 1) hpow
  have hne5 : orderOf (2 : ZMod 11) ≠ 5 := by
    intro h
    have hpow : (2 : ZMod 11) ^ 5 = 1 := by
      simpa [h] using pow_orderOf_eq_one (2 : ZMod 11)
    exact (by decide : ((2 : ZMod 11) ^ 5) ≠ 1) hpow
  rcases hcases with h1 | h2 | h5 | h10
  · exact (hne1 h1).elim
  · exact (hne2 h2).elim
  · exact (hne5 h5).elim
  · exact h10

/-- Helper for Example 1.1.95: `2` is a primitive root modulo `11`. -/
lemma two_is_primitive_root_mod_eleven : IsPrimitiveRoot (2 : ZMod 11) (φ 11) := by
  -- Rewriting `φ 11` to `10` turns the order computation into the target predicate.
  have hφ : φ 11 = 10 := by
    simpa using Nat.totient_prime (by decide : Nat.Prime 11)
  simpa [hφ, orderOf_two_zmod_eleven] using IsPrimitiveRoot.orderOf (2 : ZMod 11)

-- Proof sketch: use the source computation `2 ^ 5 ≡ 10 [ZMOD 11]` to show `2 ^ 5 ≠ 1`, while
-- Fermat's little theorem gives `2 ^ 10 = 1` in `ZMod 11`; since the only proper divisors of
-- `10` are `1`, `2`, and `5`, the order of `2` is `10`. Minimality is immediate because the
-- only naturals smaller than `2` are `0` and `1`, and neither can be a primitive root of order
-- `10`.
/-- Example 1.1.95 (1): modulo `11`, the least positive primitive root is `2`. -/
theorem two_is_least_positive_primitive_root_mod_eleven :
    IsLeast {m : ℕ | IsPrimitiveRoot (m : ZMod 11) (φ 11)} 2 := by
  refine ⟨two_is_primitive_root_mod_eleven, ?_⟩
  intro m hm
  by_contra hlt
  have hm_lt : m < 2 := by
    omega
  interval_cases m
  · -- Route correction: exclude `0` from primitive roots by its impossible power equation.
    have hφ_ne_zero : φ 11 ≠ 0 := by
      norm_num [Nat.totient_prime (by decide : Nat.Prime 11)]
    have hpoweq : (0 : ZMod 11) = 1 := by
      simpa only [Nat.cast_zero, zero_pow hφ_ne_zero] using hm.pow_eq_one
    exact (by decide : (0 : ZMod 11) ≠ 1) hpoweq
  · -- The case `m = 1` contradicts the standard nontriviality of primitive roots.
    have hφ_gt : 1 < φ 11 := by
      norm_num [Nat.totient_prime (by decide : Nat.Prime 11)]
    exact (hm.ne_one hφ_gt) (by simp)

/-- Helper for Example 1.1.95: the element `2` has order `12` in `ZMod 13`. -/
lemma orderOf_two_zmod_thirteen : orderOf (2 : ZMod 13) = 12 := by
  -- Fermat's little theorem gives the global order divisor `orderOf 2 ∣ 12`.
  have hpow12 : (2 : ZMod 13) ^ 12 = 1 := by
    decide
  have hdvd : orderOf (2 : ZMod 13) ∣ 12 :=
    orderOf_dvd_of_pow_eq_one hpow12
  -- The only divisors of `12` are `1`, `2`, `3`, `4`, `6`, and `12`.
  have hcases :
      orderOf (2 : ZMod 13) = 1 ∨
      orderOf (2 : ZMod 13) = 2 ∨
      orderOf (2 : ZMod 13) = 3 ∨
      orderOf (2 : ZMod 13) = 4 ∨
      orderOf (2 : ZMod 13) = 6 ∨
      orderOf (2 : ZMod 13) = 12 := by
    have hmem : orderOf (2 : ZMod 13) ∈ (12).divisors :=
      Nat.mem_divisors.mpr ⟨hdvd, by decide⟩
    have hdivs : (12).divisors = ({1, 2, 3, 4, 6, 12} : Finset ℕ) := by
      decide
    rw [hdivs] at hmem
    simp at hmem
    simpa [or_assoc] using hmem
  -- The source computations `2 ^ 4 = 3` and `2 ^ 6 = 12` rule out the larger proper divisors.
  have hne1 : orderOf (2 : ZMod 13) ≠ 1 := by
    intro h
    have hpow : (2 : ZMod 13) ^ 1 = 1 := by
      simpa [h] using pow_orderOf_eq_one (2 : ZMod 13)
    exact (by decide : ((2 : ZMod 13) ^ 1) ≠ 1) hpow
  have hne2 : orderOf (2 : ZMod 13) ≠ 2 := by
    intro h
    have hpow : (2 : ZMod 13) ^ 2 = 1 := by
      simpa [h] using pow_orderOf_eq_one (2 : ZMod 13)
    exact (by decide : ((2 : ZMod 13) ^ 2) ≠ 1) hpow
  have hne3 : orderOf (2 : ZMod 13) ≠ 3 := by
    intro h
    have hpow : (2 : ZMod 13) ^ 3 = 1 := by
      simpa [h] using pow_orderOf_eq_one (2 : ZMod 13)
    exact (by decide : ((2 : ZMod 13) ^ 3) ≠ 1) hpow
  have hne4 : orderOf (2 : ZMod 13) ≠ 4 := by
    intro h
    have hpow : (2 : ZMod 13) ^ 4 = 1 := by
      simpa [h] using pow_orderOf_eq_one (2 : ZMod 13)
    exact (by decide : ((2 : ZMod 13) ^ 4) ≠ 1) hpow
  have hne6 : orderOf (2 : ZMod 13) ≠ 6 := by
    intro h
    have hpow : (2 : ZMod 13) ^ 6 = 1 := by
      simpa [h] using pow_orderOf_eq_one (2 : ZMod 13)
    exact (by decide : ((2 : ZMod 13) ^ 6) ≠ 1) hpow
  rcases hcases with h1 | h2 | h3 | h4 | h6 | h12
  · exact (hne1 h1).elim
  · exact (hne2 h2).elim
  · exact (hne3 h3).elim
  · exact (hne4 h4).elim
  · exact (hne6 h6).elim
  · exact h12

/-- Helper for Example 1.1.95: `2` is a primitive root modulo `13`. -/
lemma two_is_primitive_root_mod_thirteen : IsPrimitiveRoot (2 : ZMod 13) (φ 13) := by
  -- Rewriting `φ 13` to `12` turns the order computation into the target predicate.
  have hφ : φ 13 = 12 := by
    simpa using Nat.totient_prime (by decide : Nat.Prime 13)
  simpa [hφ, orderOf_two_zmod_thirteen] using IsPrimitiveRoot.orderOf (2 : ZMod 13)

-- Proof sketch: the source computations `2 ^ 6 ≡ 12 [ZMOD 13]` and `2 ^ 4 ≡ 3 [ZMOD 13]`
-- show that neither `6` nor `4` can be the order of `2`; hence none of the proper divisors
-- `1`, `2`, `3`, `4`, `6` of `12` is the order. Together with `2 ^ 12 = 1` in `ZMod 13`,
-- this yields order `12`, and minimality again reduces to ruling out `0` and `1`.
/-- Example 1.1.95 (2): modulo `13`, the least positive primitive root is `2`. -/
theorem two_is_least_positive_primitive_root_mod_thirteen :
    IsLeast {m : ℕ | IsPrimitiveRoot (m : ZMod 13) (φ 13)} 2 := by
  refine ⟨two_is_primitive_root_mod_thirteen, ?_⟩
  intro m hm
  by_contra hlt
  have hm_lt : m < 2 := by
    omega
  interval_cases m
  · -- Route correction: exclude `0` from primitive roots by its impossible power equation.
    have hφ_ne_zero : φ 13 ≠ 0 := by
      norm_num [Nat.totient_prime (by decide : Nat.Prime 13)]
    have hpoweq : (0 : ZMod 13) = 1 := by
      simpa only [Nat.cast_zero, zero_pow hφ_ne_zero] using hm.pow_eq_one
    exact (by decide : (0 : ZMod 13) ≠ 1) hpoweq
  · -- The case `m = 1` contradicts the standard nontriviality of primitive roots.
    have hφ_gt : 1 < φ 13 := by
      norm_num [Nat.totient_prime (by decide : Nat.Prime 13)]
    exact (hm.ne_one hφ_gt) (by simp)

end PrimitiveRootsMod
