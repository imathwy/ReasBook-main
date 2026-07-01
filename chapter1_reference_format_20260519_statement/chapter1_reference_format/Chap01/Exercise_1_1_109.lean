import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Nat

section HelperLemmas

/-- Helper for Exercise 1.1.109: zero cannot be a primitive root of positive order modulo a prime. -/
lemma zero_not_primitive_root {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    ¬ IsPrimitiveRoot (0 : ZMod p) k := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro h
  -- A primitive root has `k`-th power equal to `1`, but `0 ^ k` is still `0`.
  have hzero : (0 : ZMod p) = 1 := by
    simpa [zero_pow hk] using h.pow_eq_one
  exact zero_ne_one hzero

/-- Helper for Exercise 1.1.109: one cannot be a primitive root of order greater than `1`. -/
lemma one_not_primitive_root {n k : ℕ} (hk : 1 < k) :
    ¬ IsPrimitiveRoot (1 : ZMod n) k := by
  intro h
  -- Primitive roots of larger order are never equal to `1`.
  exact h.ne_one hk rfl

/-- Helper for Exercise 1.1.109: if a smaller positive power is already `1`, then the element
cannot be a primitive root of the larger order. -/
lemma not_primitive_root_of_pow_eq_one {n k l : ℕ} {ζ : ZMod n}
    (hpow : ζ ^ l = 1) (hndvd : ¬ k ∣ l) :
    ¬ IsPrimitiveRoot ζ k := by
  intro h
  -- The primitive-root divisibility criterion contradicts the given smaller relation.
  exact hndvd ((h.pow_eq_one_iff_dvd l).mp hpow)

/-- Helper for Exercise 1.1.109: an order computation together with the exclusion of all smaller
candidates gives the least positive primitive root statement. -/
lemma least_positive_primitive_root_of_order {p g : ℕ}
    (horder : orderOf (g : ZMod p) = φ p)
    (hsmall : ∀ n < g, ¬ IsPrimitiveRoot (n : ZMod p) (φ p)) :
    IsLeast {n : ℕ | IsPrimitiveRoot (n : ZMod p) (φ p)} g := by
  refine ⟨(IsPrimitiveRoot.iff_orderOf).2 horder, ?_⟩
  intro n hn
  -- Any smaller positive candidate was excluded explicitly.
  by_contra hlt
  exact hsmall n (Nat.lt_of_not_ge hlt) hn

/-- Helper for Exercise 1.1.109: for each prime divisor of `m`, one can choose a residue class
modulo that prime on which `a + b n` is a unit. -/
lemma residue_with_unit_value_mod_prime_factor
    (a b m : ℤ) (hab : IsCoprime a b) {p : ℕ} (hp : p ∈ m.natAbs.primeFactors) :
    ∃ r : ZMod p, IsUnit ((a : ZMod p) + (b : ZMod p) * r) := by
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have habNat : Nat.Coprime a.natAbs b.natAbs := Int.isCoprime_iff_nat_coprime.mp hab
  by_cases hpb : (p : ℤ) ∣ b
  · -- If `p ∣ b`, coprimeness forces `a` to stay nonzero modulo `p`.
    have hpa : ¬ (p : ℤ) ∣ a := by
      intro hpa
      have hnot :
          ¬ Nat.Coprime a.natAbs b.natAbs := by
        exact (Nat.Prime.not_coprime_iff_dvd).2
          ⟨p, hp_prime, (Int.natAbs_dvd_natAbs).2 hpa, (Int.natAbs_dvd_natAbs).2 hpb⟩
      exact hnot habNat
    refine ⟨0, ?_⟩
    -- In the prime field `ZMod p`, any nonzero element is a unit.
    have ha_ne_zero : (a : ZMod p) ≠ 0 := by
      simpa [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] using hpa
    simpa using (isUnit_iff_ne_zero.mpr ha_ne_zero)
  · -- If `p ∤ b`, solve the congruence `a + b r = 1` directly in the field `ZMod p`.
    refine ⟨(b : ZMod p)⁻¹ * (1 - (a : ZMod p)), ?_⟩
    have hb_ne_zero : (b : ZMod p) ≠ 0 := by
      simpa [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] using hpb
    have hvalue :
        (a : ZMod p) + (b : ZMod p) * ((b : ZMod p)⁻¹ * (1 - (a : ZMod p))) = 1 := by
      have hmul :
          (b : ZMod p) * ((b : ZMod p)⁻¹ * (1 - (a : ZMod p))) = 1 - (a : ZMod p) := by
        rw [← mul_assoc, mul_inv_cancel₀ hb_ne_zero, one_mul]
      calc
        (a : ZMod p) + (b : ZMod p) * ((b : ZMod p)⁻¹ * (1 - (a : ZMod p)))
            = (a : ZMod p) + (1 - (a : ZMod p)) := by rw [hmul]
        _ = 1 := by ring
    exact hvalue.symm ▸ isUnit_one

/-- Helper for Exercise 1.1.109: the element `2` has order `2` in `ZMod 3`. -/
lemma orderOf_two_zmod_three : orderOf (2 : ZMod 3) = 2 := by
  -- The only prime divisor of `2` is `2`, and `2 ^ 1 ≠ 1` modulo `3`.
  refine orderOf_eq_of_pow_and_pow_div_prime ?_ ?_ ?_
  · decide
  · decide
  · intro q hq hqd
    have hq2 : 2 ≤ q := hq.two_le
    have hqle : q ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hqd
    interval_cases q <;> decide

/-- Helper for Exercise 1.1.109: the element `2` has order `4` in `ZMod 5`. -/
lemma orderOf_two_zmod_five : orderOf (2 : ZMod 5) = 4 := by
  -- Fermat gives `2 ^ 4 = 1`, and the unique prime divisor `2` of `4` is excluded by `2 ^ 2 ≠ 1`.
  refine orderOf_eq_of_pow_and_pow_div_prime ?_ ?_ ?_
  · decide
  · decide
  · intro q hq hqd
    have hq2 : 2 ≤ q := hq.two_le
    have hqle : q ≤ 4 := Nat.le_of_dvd (by decide : 0 < 4) hqd
    interval_cases q <;> decide

/-- Helper for Exercise 1.1.109: the element `3` has order `6` in `ZMod 7`. -/
lemma orderOf_three_zmod_seven : orderOf (3 : ZMod 7) = 6 := by
  -- The prime divisors `2` and `3` of `6` are both ruled out by direct computation.
  refine orderOf_eq_of_pow_and_pow_div_prime ?_ ?_ ?_
  · decide
  · decide
  · intro q hq hqd
    have hq2 : 2 ≤ q := hq.two_le
    have hqle : q ≤ 6 := Nat.le_of_dvd (by decide : 0 < 6) hqd
    interval_cases q <;> decide

/-- Helper for Exercise 1.1.109: the element `3` has order `16` in `ZMod 17`. -/
lemma orderOf_three_zmod_seventeen : orderOf (3 : ZMod 17) = 16 := by
  -- The only prime divisor of `16` is `2`, and `3 ^ 8 ≠ 1` modulo `17`.
  refine orderOf_eq_of_pow_and_pow_div_prime ?_ ?_ ?_
  · decide
  · decide
  · intro q hq hqd
    have hq2 : 2 ≤ q := hq.two_le
    have hqle : q ≤ 16 := Nat.le_of_dvd (by decide : 0 < 16) hqd
    interval_cases q <;> decide

/-- Helper for Exercise 1.1.109: the element `2` has order `18` in `ZMod 19`. -/
lemma orderOf_two_zmod_nineteen : orderOf (2 : ZMod 19) = 18 := by
  -- The prime divisors `2` and `3` of `18` are excluded by the source computations.
  refine orderOf_eq_of_pow_and_pow_div_prime ?_ ?_ ?_
  · decide
  · decide
  · intro q hq hqd
    have hq2 : 2 ≤ q := hq.two_le
    have hqle : q ≤ 18 := Nat.le_of_dvd (by decide : 0 < 18) hqd
    interval_cases q <;> decide

/-- Helper for Exercise 1.1.109: the element `5` has order `22` in `ZMod 23`. -/
lemma orderOf_five_zmod_twenty_three : orderOf (5 : ZMod 23) = 22 := by
  -- The prime divisors `2` and `11` of `22` are both ruled out directly.
  refine orderOf_eq_of_pow_and_pow_div_prime ?_ ?_ ?_
  · decide
  · decide
  · intro q hq hqd
    have hq2 : 2 ≤ q := hq.two_le
    have hqle : q ≤ 22 := Nat.le_of_dvd (by decide : 0 < 22) hqd
    interval_cases q <;> decide

/-- Helper for Exercise 1.1.109: the element `3` has order `φ(7^2)` in `ZMod (7^2)`. -/
lemma orderOf_three_zmod_seven_sq : orderOf (3 : ZMod (7 ^ 2)) = φ (7 ^ 2) := by
  have hu : IsUnit (3 : ZMod (7 ^ 2)) := by
    simpa using (ZMod.isUnit_iff_coprime 3 (7 ^ 2)).2 (by decide : Nat.Coprime 3 (7 ^ 2))
  let u : (ZMod (7 ^ 2))ˣ := hu.unit
  have hu7 : IsUnit (3 : ZMod 7) := by
    simpa using (ZMod.isUnit_iff_coprime 3 7).2 (by decide : Nat.Coprime 3 7)
  let u7 : (ZMod 7)ˣ := hu7.unit
  have hu7_order : orderOf u7 = 6 := by
    -- Passing to units turns the prime-modulus order computation into a group statement.
    rw [← orderOf_injective (Units.coeHom (ZMod 7)) Units.val_injective u7]
    simpa [u7] using orderOf_three_zmod_seven
  have hdvd6 : 6 ∣ orderOf u := by
    -- Reduction modulo `7` shows the `(7 - 1)` part of the order.
    have hmap_eq : ZMod.unitsMap (show 7 ∣ 7 ^ 2 by decide) u = u7 := by
      ext
      change ZMod.cast (3 : ZMod (7 ^ 2)) = (3 : ZMod 7)
      rfl
    rw [← hu7_order, ← hmap_eq]
    exact orderOf_map_dvd _ u
  have hpow : orderOf (u ^ 6) = 7 := by
    -- The sixth power is `1 + 7 * 6`, whose order is exactly `7`.
    rw [← orderOf_injective (Units.coeHom (ZMod (7 ^ 2))) Units.val_injective (u ^ 6)]
    calc
      orderOf ((u ^ 6 : (ZMod (7 ^ 2))ˣ) : ZMod (7 ^ 2)) = orderOf ((3 : ZMod (7 ^ 2)) ^ 6) := by
        congr
      _ = orderOf (1 + 7 * 6 : ZMod (7 ^ 2)) := by
        congr
      _ = 7 ^ 1 := by
        simpa using
          ZMod.orderOf_one_add_mul_prime (p := 7) (by decide) (by decide) 6 (by decide) 1
      _ = 7 := by
        norm_num
  have hdiv : orderOf u / 6 = 7 := by
    -- Since `6 ∣ orderOf u`, the order formula for `u ^ 6` simplifies cleanly.
    calc
      orderOf u / 6 = orderOf (u ^ 6) := by
        symm
        simpa [Nat.gcd_eq_right hdvd6] using (orderOf_pow (x := u) (n := 6))
      _ = 7 := hpow
  obtain ⟨t, ht⟩ := hdvd6
  have ht' : t = 7 := by
    rw [ht] at hdiv
    simpa using hdiv
  have hu_order : orderOf (3 : ZMod (7 ^ 2)) = orderOf u := by
    -- The unit and its underlying residue class have the same multiplicative order.
    simpa [u] using
      (orderOf_injective (Units.coeHom (ZMod (7 ^ 2))) Units.val_injective u)
  rw [hu_order, ht, ht']
  simpa using (Nat.totient_prime_pow_succ (p := 7) (by decide) 1).symm

/-- Helper for Exercise 1.1.109: the element `2` has order `φ(5^10)` in `ZMod (5^10)`. -/
lemma orderOf_two_zmod_five_pow_ten : orderOf (2 : ZMod (5 ^ 10)) = φ (5 ^ 10) := by
  have hu : IsUnit (2 : ZMod (5 ^ 10)) := by
    simpa using (ZMod.isUnit_iff_coprime 2 (5 ^ 10)).2 (by decide : Nat.Coprime 2 (5 ^ 10))
  let u : (ZMod (5 ^ 10))ˣ := hu.unit
  have hu5 : IsUnit (2 : ZMod 5) := by
    simpa using (ZMod.isUnit_iff_coprime 2 5).2 (by decide : Nat.Coprime 2 5)
  let u5 : (ZMod 5)ˣ := hu5.unit
  have hu5_order : orderOf u5 = 4 := by
    -- Reduction modulo `5` already gives the order `4`.
    rw [← orderOf_injective (Units.coeHom (ZMod 5)) Units.val_injective u5]
    simpa [u5] using orderOf_two_zmod_five
  have hdvd4 : 4 ∣ orderOf u := by
    -- The order of the reduction divides the order upstairs.
    have hmap_eq : ZMod.unitsMap (show 5 ∣ 5 ^ 10 by decide) u = u5 := by
      ext
      change ZMod.cast (2 : ZMod (5 ^ 10)) = (2 : ZMod 5)
      rfl
    rw [← hu5_order, ← hmap_eq]
    exact orderOf_map_dvd _ u
  have hpow : orderOf (u ^ 4) = 5 ^ 9 := by
    -- The fourth power is `1 + 5 * 3`, whose order contributes the `5^9` factor.
    rw [← orderOf_injective (Units.coeHom (ZMod (5 ^ 10))) Units.val_injective (u ^ 4)]
    calc
      orderOf ((u ^ 4 : (ZMod (5 ^ 10))ˣ) : ZMod (5 ^ 10)) = orderOf ((2 : ZMod (5 ^ 10)) ^ 4) := by
        congr
      _ = orderOf (1 + 5 * 3 : ZMod (5 ^ 10)) := by
        congr
      _ = 5 ^ 9 := by
        simpa using
          ZMod.orderOf_one_add_mul_prime (p := 5) (by decide) (by decide) 3 (by decide) 9
  have hdiv : orderOf u / 4 = 5 ^ 9 := by
    -- The unit-group order formula now isolates the remaining prime-power contribution.
    calc
      orderOf u / 4 = orderOf (u ^ 4) := by
        symm
        simpa [Nat.gcd_eq_right hdvd4] using (orderOf_pow (x := u) (n := 4))
      _ = 5 ^ 9 := hpow
  obtain ⟨t, ht⟩ := hdvd4
  have ht' : t = 5 ^ 9 := by
    rw [ht] at hdiv
    simpa using hdiv
  have hu_order : orderOf (2 : ZMod (5 ^ 10)) = orderOf u := by
    -- As above, the unit order and the residue-class order agree.
    simpa [u] using
      (orderOf_injective (Units.coeHom (ZMod (5 ^ 10))) Units.val_injective u)
  rw [hu_order, ht, ht']
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    (Nat.totient_prime_pow_succ (p := 5) (by decide) 9).symm

end HelperLemmas

section ArithmeticProgressions

-- Proof sketch: choose one residue class modulo each prime divisor of `m` on which
-- `a + b * n` stays nonzero; then combine those local conditions with the Chinese remainder
-- theorem and keep the resulting arithmetic progression.
/-- Exercise 1.1.109 (1): if `a` and `b` are coprime integers and `m` is a positive integer, then
infinitely many terms of the arithmetic progression `a + b * n` are coprime to `m`. -/
theorem coprime_terms_in_arithmetic_progression_infinite
    (a b m : ℤ) (hab : IsCoprime a b) (hm : 0 < m) :
    Set.Infinite {n : ℕ | IsCoprime (a + b * (n : ℤ)) m} := by
  classical
  let M : ℕ := m.natAbs
  let residues : ℕ → ℕ := fun p =>
    if hp : p ∈ M.primeFactors then
      (Classical.choose (residue_with_unit_value_mod_prime_factor a b m hab hp)).val
    else
      0
  let R : ℕ := ∏ p ∈ M.primeFactors, p
  have hM0 : M ≠ 0 := by
    exact Int.natAbs_ne_zero.mpr (ne_of_gt hm)
  have hs : ∀ p ∈ M.primeFactors, p ≠ 0 := by
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hpair :
      Set.Pairwise (↑M.primeFactors : Set ℕ) (Function.onFun Nat.Coprime fun p : ℕ => p) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).2 hpq
  let n0 := Nat.chineseRemainderOfFinset residues (fun p : ℕ => p) M.primeFactors hs hpair
  have hRpos : 0 < R := by
    -- The product of prime factors is positive, with the empty product handled as `1`.
    refine Finset.prod_pos ?_
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).pos
  have hgood :
      ∀ k : ℕ, IsCoprime (a + b * ((n0 + k * R : ℕ) : ℤ)) m := by
    intro k
    apply Int.isCoprime_iff_nat_coprime.mpr
    by_contra hnot
    -- Any common prime divisor of the term and `m` must be one of the prime factors used in CRT.
    obtain ⟨p, hp_prime, hp_term, hpM⟩ := (Nat.Prime.not_coprime_iff_dvd).mp hnot
    have hp_mem : p ∈ M.primeFactors := hp_prime.mem_primeFactors hpM hM0
    haveI : Fact p.Prime := ⟨hp_prime⟩
    haveI : NeZero p := ⟨hp_prime.ne_zero⟩
    have hterm_int : (p : ℤ) ∣ a + b * ((n0 + k * R : ℕ) : ℤ) := by
      exact (Int.dvd_natAbs).mp ((Int.natCast_dvd_natCast).2 hp_term)
    have hRzero : (R : ZMod p) = 0 := by
      exact (ZMod.natCast_eq_zero_iff R p).2
        (Finset.dvd_prod_of_mem (fun q : ℕ => q) hp_mem)
    have hn0_cast : (n0 : ZMod p) = residues p := by
      exact (ZMod.natCast_eq_natCast_iff n0 (residues p) p).2 (n0.2 p hp_mem)
    have hterm_cast :
        (((n0 + k * R : ℕ) : ℤ) : ZMod p) =
          Classical.choose (residue_with_unit_value_mod_prime_factor a b m hab hp_mem) := by
      have hresidue_eq :
          residues p =
            (Classical.choose (residue_with_unit_value_mod_prime_factor a b m hab hp_mem)).val := by
        dsimp [residues]
        simp [hp_mem]
      -- Adding multiples of `R` does not change the class modulo any prime factor `p` of `R`.
      calc
        (((n0 + k * R : ℕ) : ℤ) : ZMod p) = ((n0 + k * R : ℕ) : ZMod p) := by norm_num
        _ = (n0 : ZMod p) + (k : ZMod p) * (R : ZMod p) := by simp
        _ = (n0 : ZMod p) := by simp [hRzero]
        _ = (residues p : ZMod p) := hn0_cast
        _ = ((Classical.choose (residue_with_unit_value_mod_prime_factor a b m hab hp_mem)).val :
              ZMod p) := by rw [hresidue_eq]
        _ = Classical.choose (residue_with_unit_value_mod_prime_factor a b m hab hp_mem) := by
          simpa using
            (ZMod.natCast_val
              (R := ZMod p)
              (Classical.choose (residue_with_unit_value_mod_prime_factor a b m hab hp_mem)))
    have hvalue_zero :
        ((a + b * ((n0 + k * R : ℕ) : ℤ)) : ZMod p) = 0 := by
      simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hterm_int
    have hvalue_eq :
        ((a + b * ((n0 + k * R : ℕ) : ℤ)) : ZMod p) =
          (a : ZMod p) + (b : ZMod p) *
            Classical.choose (residue_with_unit_value_mod_prime_factor a b m hab hp_mem) := by
      calc
        ((a + b * ((n0 + k * R : ℕ) : ℤ)) : ZMod p)
            = (a : ZMod p) + (b : ZMod p) * ((((n0 + k * R : ℕ) : ℤ) : ZMod p)) := by simp
        _ = (a : ZMod p) + (b : ZMod p) *
              Classical.choose (residue_with_unit_value_mod_prime_factor a b m hab hp_mem) := by
            rw [hterm_cast]
    have hunit :
        IsUnit ((a : ZMod p) + (b : ZMod p) *
          Classical.choose (residue_with_unit_value_mod_prime_factor a b m hab hp_mem)) :=
      Classical.choose_spec (residue_with_unit_value_mod_prime_factor a b m hab hp_mem)
    exact hunit.ne_zero (hvalue_eq.symm.trans hvalue_zero)
  have hinj : Function.Injective fun k : ℕ => n0 + k * R := by
    intro i j hij
    apply Nat.eq_of_mul_eq_mul_right hRpos
    exact Nat.add_left_cancel hij
  have hprogression :
      Set.Infinite (Set.range fun k : ℕ => n0 + k * R) :=
    Set.infinite_range_of_injective hinj
  refine hprogression.mono ?_
  intro n hn
  rcases hn with ⟨k, rfl⟩
  -- Every term in the chosen progression stays coprime to `m`.
  exact hgood k

end ArithmeticProgressions

section PrimitiveRootsModuloPrimes

-- Proof sketch: verify that `2 ^ 2 = 1` fails in `ZMod 3`, while Fermat's little theorem gives
-- `2 ^ 2 = 1`; minimality is immediate because `1` cannot have order `2`.
/-- Exercise 1.1.109 (2): modulo `3`, the least positive primitive root is `2`. -/
theorem two_is_least_positive_primitive_root_mod_three :
    IsLeast {n : ℕ | IsPrimitiveRoot (n : ZMod 3) (φ 3)} 2 := by
  refine least_positive_primitive_root_of_order orderOf_two_zmod_three ?_
  intro n hn
  interval_cases n
  · -- Route correction: exclude `0` via its impossible positive power equation.
    exact zero_not_primitive_root (p := 3) (by decide) (by norm_num [Nat.totient_prime (by decide : Nat.Prime 3)])
  · -- The class `1` cannot generate an order larger than `1`.
    exact one_not_primitive_root (n := 3) (by norm_num [Nat.totient_prime (by decide : Nat.Prime 3)])

-- Proof sketch: check that `2 ^ 2 ≠ 1` and `2 ^ 4 = 1` in `ZMod 5`, so the order of `2` is `4`;
-- minimality again reduces to ruling out `1`.
/-- Exercise 1.1.109 (3): modulo `5`, the least positive primitive root is `2`. -/
theorem two_is_least_positive_primitive_root_mod_five :
    IsLeast {n : ℕ | IsPrimitiveRoot (n : ZMod 5) (φ 5)} 2 := by
  refine least_positive_primitive_root_of_order orderOf_two_zmod_five ?_
  intro n hn
  interval_cases n
  · -- Route correction: exclude `0` from primitive roots exactly as above.
    exact zero_not_primitive_root (p := 5) (by decide) (by norm_num [Nat.totient_prime (by decide : Nat.Prime 5)])
  · -- The class `1` still has order `1`.
    exact one_not_primitive_root (n := 5) (by norm_num [Nat.totient_prime (by decide : Nat.Prime 5)])

-- Proof sketch: show that `3 ^ 6 = 1` in `ZMod 7` and that no proper divisor of `6` is the order
-- of `3`; then rule out the smaller positive classes `1` and `2`.
/-- Exercise 1.1.109 (4): modulo `7`, the least positive primitive root is `3`. -/
theorem three_is_least_positive_primitive_root_mod_seven :
    IsLeast {n : ℕ | IsPrimitiveRoot (n : ZMod 7) (φ 7)} 3 := by
  refine least_positive_primitive_root_of_order orderOf_three_zmod_seven ?_
  intro n hn
  interval_cases n
  · -- Route correction: the zero class cannot satisfy the primitive-root equation.
    exact zero_not_primitive_root (p := 7) (by decide) (by norm_num [Nat.totient_prime (by decide : Nat.Prime 7)])
  · -- The unit element never has order `6`.
    exact one_not_primitive_root (n := 7) (by norm_num [Nat.totient_prime (by decide : Nat.Prime 7)])
  · -- The class `2` already satisfies the smaller relation `2 ^ 3 = 1`.
    exact not_primitive_root_of_pow_eq_one
      (k := φ 7) (l := 3) (by decide)
      (by norm_num [Nat.totient_prime (by decide : Nat.Prime 7)])

-- Proof sketch: compute enough powers of `3` in `ZMod 17` to exclude the proper divisors of
-- `16`; minimality amounts to checking that `1` and `2` do not have order `16`.
/-- Exercise 1.1.109 (5): modulo `17`, the least positive primitive root is `3`. -/
theorem three_is_least_positive_primitive_root_mod_seventeen :
    IsLeast {n : ℕ | IsPrimitiveRoot (n : ZMod 17) (φ 17)} 3 := by
  refine least_positive_primitive_root_of_order orderOf_three_zmod_seventeen ?_
  intro n hn
  interval_cases n
  · -- Route correction: the zero class still cannot be a primitive root.
    exact zero_not_primitive_root (p := 17) (by decide) (by norm_num [Nat.totient_prime (by decide : Nat.Prime 17)])
  · -- The class `1` is again excluded by order considerations.
    exact one_not_primitive_root (n := 17) (by norm_num [Nat.totient_prime (by decide : Nat.Prime 17)])
  · -- The smaller candidate `2` satisfies `2 ^ 8 = 1`, so its order is not `16`.
    exact not_primitive_root_of_pow_eq_one
      (k := φ 17) (l := 8) (by decide)
      (by norm_num [Nat.totient_prime (by decide : Nat.Prime 17)])

-- Proof sketch: verify that the proper divisors of `18` do not occur as the order of `2` in
-- `ZMod 19`, and use the smaller positive class `1` to prove minimality.
/-- Exercise 1.1.109 (6): modulo `19`, the least positive primitive root is `2`. -/
theorem two_is_least_positive_primitive_root_mod_nineteen :
    IsLeast {n : ℕ | IsPrimitiveRoot (n : ZMod 19) (φ 19)} 2 := by
  refine least_positive_primitive_root_of_order orderOf_two_zmod_nineteen ?_
  intro n hn
  interval_cases n
  · -- Route correction: `0` never generates the unit group.
    exact zero_not_primitive_root (p := 19) (by decide) (by norm_num [Nat.totient_prime (by decide : Nat.Prime 19)])
  · -- The class `1` still has only trivial order.
    exact one_not_primitive_root (n := 19) (by norm_num [Nat.totient_prime (by decide : Nat.Prime 19)])

-- Proof sketch: compute powers of `5` modulo `23` to show its order is `22`, then rule out the
-- smaller positive classes `1`, `2`, `3`, and `4`.
/-- Exercise 1.1.109 (7): modulo `23`, the least positive primitive root is `5`. -/
theorem five_is_least_positive_primitive_root_mod_twenty_three :
    IsLeast {n : ℕ | IsPrimitiveRoot (n : ZMod 23) (φ 23)} 5 := by
  refine least_positive_primitive_root_of_order orderOf_five_zmod_twenty_three ?_
  intro n hn
  interval_cases n
  · -- Route correction: `0` is excluded exactly as in the earlier prime cases.
    exact zero_not_primitive_root (p := 23) (by decide) (by norm_num [Nat.totient_prime (by decide : Nat.Prime 23)])
  · -- The unit element cannot have order `22`.
    exact one_not_primitive_root (n := 23) (by norm_num [Nat.totient_prime (by decide : Nat.Prime 23)])
  · -- The class `2` already satisfies `2 ^ 11 = 1`.
    exact not_primitive_root_of_pow_eq_one
      (k := φ 23) (l := 11) (by decide)
      (by norm_num [Nat.totient_prime (by decide : Nat.Prime 23)])
  · -- The class `3` also satisfies `3 ^ 11 = 1`.
    exact not_primitive_root_of_pow_eq_one
      (k := φ 23) (l := 11) (by decide)
      (by norm_num [Nat.totient_prime (by decide : Nat.Prime 23)])
  · -- The class `4` again has a smaller power equal to `1`.
    exact not_primitive_root_of_pow_eq_one
      (k := φ 23) (l := 11) (by decide)
      (by norm_num [Nat.totient_prime (by decide : Nat.Prime 23)])

end PrimitiveRootsModuloPrimes

section PrimitiveRootsModuloPrimePowers

-- Proof sketch: `3` is already a primitive root modulo `7`, and `3 ^ 6 ≠ 1` modulo `7 ^ 2`;
-- apply the standard lifting criterion for primitive roots from `p` to `p ^ 2`.
/-- Exercise 1.1.109 (8): modulo `7^2`, the class `3` is a primitive root. -/
theorem three_is_primitive_root_mod_seven_sq :
    IsPrimitiveRoot (3 : ZMod (7 ^ 2)) (φ (7 ^ 2)) := by
  -- The helper order computation already matches the target totient.
  exact (IsPrimitiveRoot.iff_orderOf).2 orderOf_three_zmod_seven_sq

-- Proof sketch: `2` is a primitive root modulo `5`, and `2 ^ 4 ≠ 1` modulo `25`; therefore the
-- primitive-root lifting criterion gives order `φ(5 ^ 10)` modulo `5 ^ 10`.
/-- Exercise 1.1.109 (9): modulo `5^10`, the class `2` is a primitive root. -/
theorem two_is_primitive_root_mod_five_pow_ten :
    IsPrimitiveRoot (2 : ZMod (5 ^ 10)) (φ (5 ^ 10)) := by
  -- The unit-order argument packages the full `4 * 5^9` order computation.
  exact (IsPrimitiveRoot.iff_orderOf).2 orderOf_two_zmod_five_pow_ten

end PrimitiveRootsModuloPrimePowers

section QuadraticResiduesModuloEleven

-- Proof sketch: compute the squares of the classes `0, 1, 2, 3, 4, 5` in `ZMod 11`; symmetry
-- under `x ↦ -x` shows these already account for all residues, yielding exactly
-- `0, 1, 3, 4, 5, 9`.
/-- Exercise 1.1.109 (10): the quadratic residues modulo `11` are exactly
`0`, `1`, `3`, `4`, `5`, and `9`. -/
theorem zmod11_isSquare_iff (a : ZMod 11) :
    IsSquare a ↔ a = 0 ∨ a = 1 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 9 := by
  constructor
  · rintro ⟨x, rfl⟩
    -- Enumerating the eleven residue classes collapses to the six square classes.
    fin_cases x <;> decide
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · -- The residue `0` is the square of `0`.
      exact ⟨0, by simp⟩
    · -- The residue `1` is the square of `1`.
      exact ⟨1, by simp⟩
    · -- The residue `3` is the square of `5`.
      exact ⟨5, by decide⟩
    · -- The residue `4` is the square of `2`.
      exact ⟨2, by decide⟩
    · -- The residue `5` is the square of `4`.
      exact ⟨4, by decide⟩
    · -- The residue `9` is the square of `3`.
      exact ⟨3, by decide⟩

end QuadraticResiduesModuloEleven
