import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Helper for Exercise 1.1.65: a coprime pair `a, b` with `b ≥ 2` admits a reduced natural
Bezout pair. -/
lemma exists_reduced_bezout_data {a b : Nat} (hb : 2 ≤ b) (hcop : Nat.Coprime a b) :
    ∃ u0 v0 : Nat, (u0 : Int) * a - (v0 : Int) * b = 1 ∧ u0 < b ∧ v0 < a := by
  have hb_one : 1 < b := by
    omega
  have ha_pos : 0 < a := by
    by_contra ha_zero
    rw [Nat.eq_zero_of_not_pos ha_zero] at hcop
    have : b = 1 := (Nat.coprime_zero_left b).mp hcop
    omega
  -- Choose the reduced inverse of `a` modulo `b` and package the quotient as `v0`.
  obtain ⟨u0, hu0_lt, hu0_mod⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hb_one
  let v0 := (a * u0) / b
  have hdecomp := Nat.mod_add_div (a * u0) b
  rw [hu0_mod] at hdecomp
  have hEqNat : 1 + b * v0 = a * u0 := by
    simpa [v0, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hdecomp
  have hEqInt : (1 : Int) + b * v0 = a * u0 := by
    exact_mod_cast hEqNat
  -- The quotient bound comes from `u0 < b`, hence `a * u0 < a * b`.
  have hu_mul_lt : a * u0 < a * b := by
    exact Nat.mul_lt_mul_of_pos_left hu0_lt ha_pos
  have hv_mul_lt : b * v0 < b * a := by
    have h1 : b * v0 < a * u0 := by
      rw [← hEqNat]
      exact Nat.lt_add_of_pos_left (Nat.succ_pos 0)
    have h2 : b * v0 < a * b := lt_trans h1 hu_mul_lt
    simpa [Nat.mul_comm] using h2
  have hv0_lt : v0 < a := Nat.lt_of_mul_lt_mul_left hv_mul_lt
  refine ⟨u0, v0, ?_, hu0_lt, hv0_lt⟩
  linarith

/-- Helper for Exercise 1.1.65: an integer Bezout identity forces natural-number coprimality. -/
lemma nat_coprime_of_int_bezout_eq_one {a b u0 v0 : Nat}
    (h : (u0 : Int) * a - (v0 : Int) * b = 1) : Nat.Coprime a b := by
  -- Rewrite the given identity into the standard `IsCoprime` form over `Int`.
  rw [← Nat.isCoprime_iff_coprime]
  refine ⟨u0, -v0, ?_⟩
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
    using h

/-- Helper for Exercise 1.1.65: from `(a : Int) * x = (b : Int) * y` and `a ⟂ b`, the factor `b`
divides `x`. -/
lemma coprime_mul_eq_mul_implies_right_dvd {a b : Nat} (hcop : Nat.Coprime a b)
    {x y : Int} (h : (a : Int) * x = (b : Int) * y) : (b : Int) ∣ x := by
  -- View the equality as a divisibility statement and then cancel the coprime factor `a`.
  have hdiv : (b : Int) ∣ x * (a : Int) := ⟨y, by
    simpa [mul_comm, mul_left_comm, mul_assoc] using h⟩
  have hdiv' : (b : Int) ∣ (a : Int) * x := by
    simpa [mul_comm] using hdiv
  exact (Nat.Coprime.cast hcop).symm.dvd_of_dvd_mul_left hdiv'

/-- Helper for Exercise 1.1.65: a reduced natural Bezout pair is unique. -/
lemma reduced_bezout_pair_unique {a b : Nat} (hb : 0 < b) {p q : Nat × Nat}
    (hp : (p.1 : Int) * a - (p.2 : Int) * b = 1 ∧ p.1 < b ∧ p.2 < a)
    (hq : (q.1 : Int) * a - (q.2 : Int) * b = 1 ∧ q.1 < b ∧ q.2 < a) : p = q := by
  rcases hp with ⟨hp_eq, hp_lt_b, hp_lt_a⟩
  rcases hq with ⟨hq_eq, hq_lt_b, hq_lt_a⟩
  have hcop : Nat.Coprime a b := nat_coprime_of_int_bezout_eq_one hp_eq
  -- Subtract the two Bezout identities to see that the first coordinates differ by a multiple of `b`.
  have hdiff : (a : Int) * ((q.1 : Int) - p.1) = (b : Int) * ((q.2 : Int) - p.2) := by
    linarith
  have hbdvd : (b : Int) ∣ (q.1 : Int) - p.1 :=
    coprime_mul_eq_mul_implies_right_dvd hcop hdiff
  have hfst : q.1 = p.1 := by
    rcases hbdvd with ⟨k, hk⟩
    by_cases hk_zero : k = 0
    · have : (q.1 : Int) = p.1 := by
        have hk' : (q.1 : Int) - p.1 = 0 := by
          simpa [hk_zero] using hk
        linarith
      exact Int.ofNat.inj this
    · have hk_pos_or_neg : 0 < k ∨ k < 0 := lt_or_gt_of_ne (Ne.symm hk_zero)
      cases hk_pos_or_neg with
      | inl hk_pos =>
          have hb_int : (0 : Int) < b := by
            exact_mod_cast hb
          have hb_le : (b : Int) ≤ (q.1 : Int) - p.1 := by
            rw [hk]
            have : (1 : Int) ≤ k := by
              omega
            nlinarith
          have hlt : (q.1 : Int) - p.1 < b := by
            have : (q.1 : Int) < b := by
              exact_mod_cast hq_lt_b
            have hp_nonneg : (0 : Int) ≤ p.1 := by
              exact_mod_cast Nat.zero_le p.1
            linarith
          omega
      | inr hk_neg =>
          have hb_int : (0 : Int) < b := by
            exact_mod_cast hb
          have hb_le : (b : Int) ≤ -((q.1 : Int) - p.1) := by
            rw [hk]
            have : (1 : Int) ≤ -k := by
              omega
            nlinarith
          have hlt : -((q.1 : Int) - p.1) < b := by
            have : (p.1 : Int) < b := by
              exact_mod_cast hp_lt_b
            have hq_nonneg : (0 : Int) ≤ q.1 := by
              exact_mod_cast Nat.zero_le q.1
            linarith
          omega
  have hsnd : q.2 = p.2 := by
    -- Once the first coordinates agree, the second coordinates must agree as well.
    have hb_ne : (b : Int) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hb
    have hEq : (q.2 : Int) * b = (p.2 : Int) * b := by
      rw [hfst] at hq_eq
      linarith
    have : (q.2 : Int) = p.2 := mul_right_cancel₀ hb_ne hEq
    exact Int.ofNat.inj this
  rcases p with ⟨p1, p2⟩
  rcases q with ⟨q1, q2⟩
  simp at hfst hsnd
  simp [hfst, hsnd]

/-- Exercise 1.1.65 (1): the natural triples with `Nat.lcm a b = 42`,
`Nat.gcd a c = 3`, and `a + b + c = 29` are exactly `(21, 2, 6)`, `(6, 14, 9)`,
and `(3, 14, 12)`; in particular, positivity is automatic from these conditions. -/
-- Proof sketch: enumerate the divisors of `42` that can occur as `a`, use `Nat.lcm a b = 42`
-- to restrict `b`, then impose `Nat.gcd a c = 3` and `a + b + c = 29` to isolate the three cases.
theorem nat_triples_lcm_eq_42_gcd_eq_3_sum_eq_29 {a b c : Nat} :
    Nat.lcm a b = 42 ∧ Nat.gcd a c = 3 ∧ a + b + c = 29 ↔
      (a, b, c) = (21, 2, 6) ∨ (a, b, c) = (6, 14, 9) ∨ (a, b, c) = (3, 14, 12) := by
  constructor
  · rintro ⟨hlcm, hgcd, hsum⟩
    -- The lcm condition forces both `a` and `b` to divide `42`, and `b` is positive.
    have hb_pos : 0 < b := by
      by_contra hb_zero
      rw [Nat.eq_zero_of_not_pos hb_zero, Nat.lcm_zero_right] at hlcm
      norm_num at hlcm
    have ha_dvd : a ∣ 42 := by
      have : a ∣ Nat.lcm a b := Nat.dvd_lcm_left a b
      simpa [hlcm] using this
    have hb_dvd : b ∣ 42 := by
      have : b ∣ Nat.lcm a b := Nat.dvd_lcm_right a b
      simpa [hlcm] using this
    -- Since `3 = gcd a c`, the value of `a` must be a divisor of `42` that is also divisible by `3`.
    have h3dvd_a : 3 ∣ a := by
      simpa [hgcd] using (Nat.gcd_dvd_left a c)
    have ha_le : a ≤ 28 := by
      omega
    have ha_cases : a = 3 ∨ a = 6 ∨ a = 21 := by
      interval_cases a <;> simp_all
    rcases ha_cases with rfl | rfl | rfl
    · -- When `a = 3`, only `b = 14` survives the lcm condition and then `c = 12`.
      have hb_le : b ≤ 26 := by
        omega
      have hb_cases :
          b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 6 ∨ b = 7 ∨ b = 14 ∨ b = 21 := by
        interval_cases b <;> simp_all
      rcases hb_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have : Nat.lcm 3 1 ≠ 42 := by decide
        exact (this hlcm).elim
      · have : Nat.lcm 3 2 ≠ 42 := by decide
        exact (this hlcm).elim
      · have : Nat.lcm 3 3 ≠ 42 := by decide
        exact (this hlcm).elim
      · have : Nat.lcm 3 6 ≠ 42 := by decide
        exact (this hlcm).elim
      · have : Nat.lcm 3 7 ≠ 42 := by decide
        exact (this hlcm).elim
      · have hc : c = 12 := by
          omega
        subst hc
        exact Or.inr <| Or.inr rfl
      · have : Nat.lcm 3 21 ≠ 42 := by decide
        exact (this hlcm).elim
    · -- When `a = 6`, the lcm allows `b = 7, 14, 21`, and the gcd check singles out `b = 14`.
      have hb_le : b ≤ 23 := by
        omega
      have hb_cases :
          b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 6 ∨ b = 7 ∨ b = 14 ∨ b = 21 := by
        interval_cases b <;> simp_all
      rcases hb_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · have : Nat.lcm 6 1 ≠ 42 := by decide
        exact (this hlcm).elim
      · have : Nat.lcm 6 2 ≠ 42 := by decide
        exact (this hlcm).elim
      · have : Nat.lcm 6 3 ≠ 42 := by decide
        exact (this hlcm).elim
      · have : Nat.lcm 6 6 ≠ 42 := by decide
        exact (this hlcm).elim
      · have hc : c = 16 := by
          omega
        subst hc
        have : Nat.gcd 6 16 ≠ 3 := by decide
        exact (this hgcd).elim
      · have hc : c = 9 := by
          omega
        subst hc
        exact Or.inr <| Or.inl rfl
      · have hc : c = 2 := by
          omega
        subst hc
        have : Nat.gcd 6 2 ≠ 3 := by decide
        exact (this hgcd).elim
    · -- When `a = 21`, the sum bound makes `b` small, and only `b = 2` remains possible.
      have hb_le : b ≤ 8 := by
        omega
      have hb_cases : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 6 ∨ b = 7 := by
        interval_cases b <;> simp_all
      rcases hb_cases with rfl | rfl | rfl | rfl | rfl
      · have : Nat.lcm 21 1 ≠ 42 := by decide
        exact (this hlcm).elim
      · have hc : c = 6 := by
          omega
        subst hc
        exact Or.inl rfl
      · have : Nat.lcm 21 3 ≠ 42 := by decide
        exact (this hlcm).elim
      · have hc : c = 2 := by
          omega
        subst hc
        have : Nat.gcd 21 2 ≠ 3 := by decide
        exact (this hgcd).elim
      · have : Nat.lcm 21 7 ≠ 42 := by decide
        exact (this hlcm).elim
  · intro h
    -- Each listed triple is checked by direct calculation.
    rcases h with h | h | h
    · cases h
      norm_num
    · cases h
      norm_num
    · cases h
      norm_num

/-- Part (2): for coprime natural numbers `a` and `b >= 2`, there is a unique pair
`(u0, v0)` of natural numbers with `u0 * a - v0 * b = 1`, `u0 < b`, and `v0 < a`. -/
-- Proof sketch: use Bezout's identity from `Nat.gcd_eq_gcd_ab` or modular inverse existence to
-- produce one solution, then reduce it modulo `b` and modulo `a`; uniqueness follows by comparing
-- two reduced solutions and showing their difference is a multiple of both `a` and `b`.
theorem existsUnique_reduced_bezout_pair {a b : Nat} (hb : 2 ≤ b) (hcop : Nat.Coprime a b) :
    ∃! p : Nat × Nat, (p.1 : Int) * a - (p.2 : Int) * b = 1 ∧ p.1 < b ∧ p.2 < a := by
  -- First construct one reduced pair, then invoke the uniqueness lemma for any other pair.
  obtain ⟨u0, v0, huv_eq, hu_lt, hv_lt⟩ := exists_reduced_bezout_data hb hcop
  refine ⟨(u0, v0), ⟨huv_eq, hu_lt, hv_lt⟩, ?_⟩
  intro p hp
  have hb_pos : 0 < b := by
    omega
  exact reduced_bezout_pair_unique hb_pos hp ⟨huv_eq, hu_lt, hv_lt⟩

/-- Part (3): every integer solution of `u * a - v * b = 1` is obtained from one
particular solution `(u0, v0)` by adding multiples of `b` to `u` and the same multiples of `a`
to `v`. -/
-- Proof sketch: subtract the equation for `(u0, v0)` from the equation for `(u, v)` to get
-- `a * (u - u0) = b * (v - v0)`; then use coprimality forced by the existence of one solution to
-- show `u - u0` is a multiple of `b` and `v - v0` is the same multiple of `a`.
theorem bezout_eq_one_iff_eq_reduced_pair_add_multiples {a b u0 v0 : Nat} {u v : Int}
    (h0 : (u0 : Int) * a - (v0 : Int) * b = 1) :
    u * a - v * b = 1 ↔ ∃ k : Int, u = u0 + k * b ∧ v = v0 + k * a := by
  constructor
  · intro h
    have hcop := nat_coprime_of_int_bezout_eq_one h0
    by_cases hb0 : b = 0
    · -- In the degenerate case `b = 0`, the equation forces `a = u0 = 1`, so `v` carries the parameter.
      rw [hb0, Nat.coprime_zero_right] at hcop
      have hu0_eq : u0 = 1 := by
        rw [hb0, hcop] at h0
        norm_num at h0
        simpa using h0
      have hu_eq : u = 1 := by
        rw [hb0, hcop] at h
        norm_num at h
        simpa using h
      refine ⟨v - v0, ?_, ?_⟩
      · simp [hb0, hu_eq, hu0_eq]
      · rw [hcop]
        ring
    · have hb_pos : 0 < b := Nat.pos_of_ne_zero hb0
      -- Subtract the base Bezout identity and factor the result.
      have hdiff : (a : Int) * (u - u0) = (b : Int) * (v - v0) := by
        linarith
      have hbdvd : (b : Int) ∣ u - u0 :=
        coprime_mul_eq_mul_implies_right_dvd hcop hdiff
      rcases hbdvd with ⟨k, hk⟩
      refine ⟨k, ?_, ?_⟩
      · linarith
      · -- Substitute the parameter for `u - u0` back into the difference equation.
        have hb_ne : (b : Int) ≠ 0 := by
          exact_mod_cast Nat.ne_of_gt hb_pos
        have hEq : (b : Int) * (k * a) = (b : Int) * (v - v0) := by
          calc
            (b : Int) * (k * a) = (a : Int) * ((b : Int) * k) := by ring
            _ = (a : Int) * (u - u0) := by
              simp [hk, mul_comm, mul_left_comm]
            _ = (b : Int) * (v - v0) := hdiff
        have hkva : k * a = v - v0 := mul_left_cancel₀ hb_ne hEq
        linarith
  · rintro ⟨k, rfl, rfl⟩
    -- The added multiples cancel because both coordinates use the same parameter.
    linarith [h0]

/-- Part (4): the integer solutions of `47 * u + 111 * v = 1` are exactly
`u = 26 + 111k` and `v = -11 - 47k` for some integer `k`. -/
-- Proof sketch: check that `(26, -11)` is one Bezout solution, then apply the general
-- parametrization of all solutions to a linear Diophantine equation with coprime coefficients.
theorem int_solutions_47u_add_111v_eq_one {u v : Int} :
    47 * u + 111 * v = 1 ↔ ∃ k : Int, u = 26 + 111 * k ∧ v = -11 - 47 * k := by
  have hbase : (26 : Int) * 47 - (11 : Int) * 111 = 1 := by
    norm_num
  constructor
  · intro h
    -- Rewrite the equation as a Bezout identity for `(u, -v)` and apply the general theorem.
    have h' : u * 47 - (-v) * 111 = 1 := by
      linarith
    obtain ⟨k, hk1, hk2⟩ :=
      (bezout_eq_one_iff_eq_reduced_pair_add_multiples
        (a := 47) (b := 111) (u0 := 26) (v0 := 11) (u := u) (v := -v) hbase).1 h'
    refine ⟨k, ?_, ?_⟩
    · simpa [mul_comm, mul_left_comm, mul_assoc] using hk1
    · have hk2' : v = -((11 : Int) + k * 47) := neg_eq_iff_eq_neg.mp hk2
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
        mul_assoc] using hk2'
  · rintro ⟨k, rfl, rfl⟩
    -- Direct expansion shows that the parameter terms cancel.
    ring_nf
