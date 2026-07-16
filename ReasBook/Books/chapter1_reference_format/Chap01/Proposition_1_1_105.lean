import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Helper for Proposition 1.1.105: a cast integer is a root modulo `m` exactly when its integer
value is divisible by `m`. -/
lemma isRoot_intCast_iff_dvd
    (P : Polynomial ℤ) (m : ℕ) [NeZero m] (z : ℤ) :
    (P.map (Int.castRingHom (ZMod m))).IsRoot ((z : ℤ) : ZMod m) ↔ (m : ℤ) ∣ P.eval z := by
  -- Translate the root condition back to the integer evaluation before using the standard `ZMod`
  -- divisibility criterion for an integer cast to vanish.
  rw [Polynomial.IsRoot.def, Polynomial.eval_map]
  simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd (P.eval z) m)

/-- Helper for Proposition 1.1.105: evaluating the derivative after casting agrees with casting the
integer derivative value. -/
lemma derivative_eval_intCast
    (P : Polynomial ℤ) (m : ℕ) (z : ℤ) :
    ((P.derivative.eval z : ℤ) : ZMod m) =
      (P.derivative.map (Int.castRingHom (ZMod m))).eval (z : ZMod m) := by
  -- This is the usual compatibility of `eval` with `map`.
  rw [Polynomial.eval_map]
  simp

/-- Helper for Proposition 1.1.105: a shift by `p ^ (n + 1)` disappears modulo `p`. -/
lemma prime_pow_shift_cast_eq_zero
    (p n : ℕ) (t : ℤ) :
    ((((p ^ (n + 1) : ℤ) * t : ℤ) : ZMod p)) = 0 := by
  -- One extra factor of `p` is enough to annihilate the shift modulo `p`.
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine ⟨(p ^ n : ℤ) * t, ?_⟩
  simp [pow_succ, mul_left_comm, mul_comm]

/-- Helper for Proposition 1.1.105: once the linear congruence is solved modulo `p`, the shifted
integer gives a root modulo the next power `p ^ (n + 2)`. -/
lemma eval_shift_dvd_prime_pow_succ
    (p n : ℕ) (P : Polynomial ℤ) (r q t : ℤ)
    (hq : P.eval r = (p ^ (n + 1) : ℤ) * q)
    (ht : (p : ℤ) ∣ q + P.derivative.eval r * t) :
    ((p ^ (n + 2) : ℤ)) ∣ P.eval (r + (p ^ (n + 1) : ℤ) * t) := by
  -- Taylor-expand at `r`; the quadratic remainder is automatically divisible by the next power.
  obtain ⟨u, hu⟩ := P.binomExpansion r ((p ^ (n + 1) : ℤ) * t)
  rcases ht with ⟨m, hm⟩
  refine ⟨m + u * ((p ^ n : ℤ) * t ^ 2), ?_⟩
  rw [hu, hq]
  calc
    (p ^ (n + 1) : ℤ) * q + P.derivative.eval r * ((p ^ (n + 1) : ℤ) * t) +
        u * ((p ^ (n + 1) : ℤ) * t) ^ 2 =
      (p ^ (n + 1) : ℤ) * (q + P.derivative.eval r * t) +
        (p ^ (n + 2) : ℤ) * (u * ((p ^ n : ℤ) * t ^ 2)) := by
        ring_nf
    _ = (p ^ (n + 1) : ℤ) * ((p : ℤ) * m) +
        (p ^ (n + 2) : ℤ) * (u * ((p ^ n : ℤ) * t ^ 2)) := by
        rw [hm]
    _ = (p ^ (n + 2) : ℤ) * (m + u * ((p ^ n : ℤ) * t ^ 2)) := by
        ring_nf

/-- Helper for Proposition 1.1.105: any root of the shifted integer modulo `p ^ (n + 2)` must
satisfy the corresponding linear congruence modulo `p`. -/
lemma linear_correction_dvd_of_eval_shift_dvd
    (p n : ℕ) (hp : Nat.Prime p) (P : Polynomial ℤ) (r q t : ℤ)
    (hq : P.eval r = (p ^ (n + 1) : ℤ) * q)
    (hroot : ((p ^ (n + 2) : ℤ)) ∣ P.eval (r + (p ^ (n + 1) : ℤ) * t)) :
    (p : ℤ) ∣ q + P.derivative.eval r * t := by
  -- Compare the shifted root divisibility with the Taylor expansion and cancel the common
  -- `p ^ (n + 1)` factor.
  obtain ⟨u, hu⟩ := P.binomExpansion r ((p ^ (n + 1) : ℤ) * t)
  rcases hroot with ⟨m, hm⟩
  have hmul :
      ((p ^ (n + 1) : ℤ) * (q + P.derivative.eval r * t)) =
        (p ^ (n + 2) : ℤ) * (m - u * ((p ^ n : ℤ) * t ^ 2)) := by
    calc
      ((p ^ (n + 1) : ℤ) * (q + P.derivative.eval r * t)) =
          P.eval (r + (p ^ (n + 1) : ℤ) * t) -
            (p ^ (n + 2) : ℤ) * (u * ((p ^ n : ℤ) * t ^ 2)) := by
          rw [hu, hq]
          ring_nf
      _ = (p ^ (n + 2) : ℤ) * m -
            (p ^ (n + 2) : ℤ) * (u * ((p ^ n : ℤ) * t ^ 2)) := by
          rw [hm]
      _ = (p ^ (n + 2) : ℤ) * (m - u * ((p ^ n : ℤ) * t ^ 2)) := by
          ring
  have hdiv :
      ((p ^ (n + 1) : ℤ) * (p : ℤ)) ∣
        ((p ^ (n + 1) : ℤ) * (q + P.derivative.eval r * t)) := by
    refine ⟨m - u * ((p ^ n : ℤ) * t ^ 2), ?_⟩
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hpow_ne : (p ^ (n + 1) : ℤ) ≠ 0 := by
    exact_mod_cast pow_ne_zero (n + 1) hp.ne_zero
  exact Int.dvd_of_mul_dvd_mul_left hpow_ne hdiv

/-- Proposition 1.1.105: if the reduction of an integer polynomial has a simple root `a` modulo a
prime `p`, then for every positive exponent `k` there is a unique root modulo `p ^ k` reducing to
`a` modulo `p`. -/
-- Proof sketch: use induction on `k`. The step from `p ^ s` to `p ^ (s + 1)` comes from Taylor
-- expansion at a chosen lift `b_s`; because the derivative is nonzero modulo `p`, the linear term
-- is invertible modulo `p`, giving a unique correction and hence a unique next lift.
theorem existsUnique_root_mod_prime_pow_of_simple_root_mod_prime
    (p : ℕ) (hp : Nat.Prime p) (k : ℕ+) (P : Polynomial ℤ) (a : ZMod p)
    (ha_root : (P.map (Int.castRingHom (ZMod p))).IsRoot a)
    (ha_simple : ¬ (P.derivative.map (Int.castRingHom (ZMod p))).IsRoot a) :
    ∃! b : ZMod (p ^ (k : ℕ)),
      (P.map (Int.castRingHom (ZMod (p ^ (k : ℕ))))).IsRoot b ∧
        ZMod.castHom
          (show p ∣ p ^ (k : ℕ) by exact dvd_pow_self p k.2.ne')
          (ZMod p) b = a := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  suffices hmain :
      ∀ n : ℕ,
        ∃! b : ZMod (p ^ n.succ),
          (P.map (Int.castRingHom (ZMod (p ^ n.succ)))).IsRoot b ∧ b.cast = a by
    change
      ∃! b : ZMod (p ^ (k : ℕ)),
        (P.map (Int.castRingHom (ZMod (p ^ (k : ℕ))))).IsRoot b ∧ b.cast = a
    have hkEq : k.natPred + 1 = (k : ℕ) := by
      exact PNat.natPred_add_one k
    have hkMain := hmain k.natPred
    rw [Nat.succ_eq_add_one, hkEq] at hkMain
    simpa [ZMod.castHom_apply] using hkMain
  intro n
  induction n with
  | zero =>
      -- For `k = 1`, the given simple root modulo `p` is already the unique lift.
      rw [pow_one]
      refine ⟨a, ?_, ?_⟩
      · constructor
        · exact ha_root
        · exact ZMod.cast_id p a
      · intro b hb
        simpa using hb.2
  | succ n ih =>
      letI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
      letI : NeZero (p ^ (n + 2)) := ⟨pow_ne_zero _ hp.ne_zero⟩
      obtain ⟨b, hb, hb_unique⟩ := ih
      let r : ℤ := b.val
      have hr_cast :
          ((r : ℤ) : ZMod (p ^ (n + 1))) = b := by
        -- We work with the canonical integer representative of the previous lift.
        unfold r
        exact_mod_cast ZMod.natCast_zmod_val b
      have hr_mod_p : ((r : ℤ) : ZMod p) = a := by
        -- The predecessor lift still reduces to the original simple root.
        simpa [r] using hb.2
      have hb_dvd : (p ^ (n + 1) : ℤ) ∣ P.eval r := by
        -- Reinterpret the old root condition as divisibility in `ℤ`.
        refine (isRoot_intCast_iff_dvd P (p ^ (n + 1)) r).1 ?_
        simpa [r] using hb.1
      rcases hb_dvd with ⟨q, hq⟩
      have ha_simple_eval :
          (P.derivative.map (Int.castRingHom (ZMod p))).eval a ≠ 0 := by
        -- The simplicity assumption is exactly nonvanishing of the derivative at `a`.
        simpa [Polynomial.IsRoot.def] using ha_simple
      have hderiv_ne : (((P.derivative.eval r : ℤ) : ZMod p)) ≠ 0 := by
        -- The derivative keeps the same residue at any lift of `a`.
        intro hzero
        apply ha_simple_eval
        calc
          (P.derivative.map (Int.castRingHom (ZMod p))).eval a =
              (P.derivative.map (Int.castRingHom (ZMod p))).eval (r : ZMod p) := by
            rw [hr_mod_p]
          _ = (((P.derivative.eval r : ℤ) : ZMod p)) := by
            symm
            exact derivative_eval_intCast P p r
          _ = 0 := hzero
      let d : ZMod p := ((P.derivative.eval r : ℤ) : ZMod p)
      let correction : ZMod p := -(q : ZMod p) * d⁻¹
      let t : ℤ := correction.val
      have ht_cast : ((t : ℤ) : ZMod p) = correction := by
        -- We choose the canonical integer representative of the unique correction class.
        unfold t
        exact_mod_cast ZMod.natCast_zmod_val correction
      have ht_dvd : (p : ℤ) ∣ q + P.derivative.eval r * t := by
        -- The chosen correction solves the linear congruence modulo `p`.
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        calc
          (((q + P.derivative.eval r * t : ℤ) : ZMod p)) =
              (q : ZMod p) + d * (t : ZMod p) := by
            simp [d]
          _ = (q : ZMod p) + d * correction := by
            rw [ht_cast]
          _ = 0 := by
            simp [correction, d, hderiv_ne, mul_left_comm]
      let bNext : ZMod (p ^ (n + 2)) :=
        ((r + (p ^ (n + 1) : ℤ) * t : ℤ) : ZMod (p ^ (n + 2)))
      refine ⟨bNext, ?_, ?_⟩
      · constructor
        · -- Taylor's formula shows that the chosen correction gives a genuine next-stage root.
          refine (isRoot_intCast_iff_dvd P (p ^ (n + 2)) _).2 ?_
          exact eval_shift_dvd_prime_pow_succ p n P r q t hq ht_dvd
        · -- The extra `p ^ (n + 1)` shift vanishes modulo `p`.
          calc
            bNext.cast = ((r + (p ^ (n + 1) : ℤ) * t : ℤ) : ZMod p) := by
              simp [bNext]
            _ = (r : ZMod p) + ((((p ^ (n + 1) : ℤ) * t : ℤ) : ZMod p)) := by
              simp
            _ = (r : ZMod p) := by
              rw [prime_pow_shift_cast_eq_zero]
              simp
            _ = a := hr_mod_p
      · intro c hc
        let s : ℤ := c.val
        have hs_cast :
            ((s : ℤ) : ZMod (p ^ (n + 2))) = c := by
          -- Again we pass to the canonical integer representative of the competing lift.
          unfold s
          exact_mod_cast ZMod.natCast_zmod_val c
        have hs_dvd_next : (p ^ (n + 2) : ℤ) ∣ P.eval s := by
          -- Any competing root corresponds to an integer whose polynomial value is divisible by
          -- the next power of `p`.
          refine (isRoot_intCast_iff_dvd P (p ^ (n + 2)) s).1 ?_
          simpa [s] using hc.1
        have hs_mod_p : ((s : ℤ) : ZMod p) = a := by
          -- The competing lift has the same reduction modulo `p`.
          simpa [s] using hc.2
        have hs_dvd_prev : (p ^ (n + 1) : ℤ) ∣ P.eval s := by
          -- So it is also a root modulo the previous power, where the induction hypothesis
          -- already gives uniqueness.
          have hpow_dvd : (p ^ (n + 1) : ℤ) ∣ (p ^ (n + 2) : ℤ) := by
            refine ⟨(p : ℤ), ?_⟩
            simp [pow_succ, mul_comm]
          exact hpow_dvd.trans hs_dvd_next
        have hs_prev_eq : ((s : ℤ) : ZMod (p ^ (n + 1))) = b := by
          apply hb_unique
          constructor
          · exact (isRoot_intCast_iff_dvd P (p ^ (n + 1)) s).2 hs_dvd_prev
          · simpa using hs_mod_p
        have hrs_eq :
            ((r : ℤ) : ZMod (p ^ (n + 1))) = ((s : ℤ) : ZMod (p ^ (n + 1))) := by
          rw [hr_cast, hs_prev_eq]
        have hs_sub_dvd : (p ^ (n + 1) : ℤ) ∣ s - r := by
          -- Every competing lift differs from the chosen predecessor by a multiple of `p ^ (n+1)`.
          exact (ZMod.intCast_eq_intCast_iff_dvd_sub r s (p ^ (n + 1))).1 hrs_eq
        rcases hs_sub_dvd with ⟨u, hu⟩
        have hs_repr : s = r + (p ^ (n + 1) : ℤ) * u := by
          linarith
        have hu_lin_dvd : (p : ℤ) ∣ q + P.derivative.eval r * u := by
          -- The same Taylor expansion forces every competing correction to satisfy the same linear
          -- congruence modulo `p`.
          apply linear_correction_dvd_of_eval_shift_dvd p n hp P r q u hq
          simpa [hs_repr] using hs_dvd_next
        have hu_eq_zero : (q : ZMod p) + d * (u : ZMod p) = 0 := by
          -- Convert the divisibility statement for `u` back to the corresponding linear equation
          -- in the field `ZMod p`.
          rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hu_lin_dvd
          calc
            (q : ZMod p) + d * (u : ZMod p) =
                (((q + P.derivative.eval r * u : ℤ) : ZMod p)) := by
              simp [d, mul_comm]
            _ = 0 := hu_lin_dvd
        have hu_formula : (u : ZMod p) = correction := by
          -- Because the derivative coefficient is invertible, the linear equation has a unique
          -- solution modulo `p`.
          have hu_mul : (u : ZMod p) * d = -(q : ZMod p) := by
            have : d * (u : ZMod p) = -(q : ZMod p) := by
              exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hu_eq_zero)
            simpa [mul_comm] using this
          calc
            (u : ZMod p) = (-(q : ZMod p)) * d⁻¹ := by
              exact (eq_mul_inv_iff_mul_eq₀ hderiv_ne).2 hu_mul
            _ = correction := by
              rfl
        have htu_mod : (u : ZMod p) = (t : ZMod p) := by
          rw [ht_cast]
          exact hu_formula
        have huv_dvd : (p : ℤ) ∣ u - t := by
          -- So the competing correction differs from the chosen one by a multiple of `p`.
          exact (ZMod.intCast_eq_intCast_iff_dvd_sub t u p).1 htu_mod.symm
        rcases huv_dvd with ⟨v, hv⟩
        rw [← hs_cast]
        change
          (((s : ℤ) : ZMod (p ^ (n + 2))) =
            ((r + (p ^ (n + 1) : ℤ) * t : ℤ) : ZMod (p ^ (n + 2))))
        symm
        apply (ZMod.intCast_eq_intCast_iff_dvd_sub
          (r + (p ^ (n + 1) : ℤ) * t) s (p ^ (n + 2))).2
        refine ⟨v, ?_⟩
        calc
          s - (r + (p ^ (n + 1) : ℤ) * t) =
              (p ^ (n + 1) : ℤ) * (u - t) := by
            rw [hs_repr]
            ring
          _ = (p ^ (n + 1) : ℤ) * ((p : ℤ) * v) := by
            rw [hv]
          _ = (p ^ (n + 2) : ℤ) * v := by
            ring_nf
