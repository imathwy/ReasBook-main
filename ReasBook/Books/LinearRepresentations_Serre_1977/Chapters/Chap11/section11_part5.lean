import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_11_11_2_6 (from Chap11) -/
noncomputable section

open scoped BigOperators Representation

universe u

namespace Representation

section FrobeniusTheorem

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

local instance : Fintype G := Fintype.ofFinite G

local instance : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)

local instance nthPow_mem_conjClassCarrier_decidablePred
    (n : ℕ+) (c : ConjClasses G) :
    DecidablePred (fun x : G ↦ x ^ (n : ℕ) ∈ c.carrier) :=
  Classical.decPred _

-- Source/core/bridge triage:
-- * source-facing: the textbook sum `a_c` for a linear character.
-- * core/canonical: `conjugacyClassNthRootCharacterSum`, the Chapter 11 owner for this sum.
-- * bridge/view: the degree-`1` specialization along `MonoidHom.toRepresentation`.

/-- The source sum `a_c` is an algebraic integer. -/
theorem conjugacyClassNthRootCharacterSum_toRepresentation_isIntegral
    (n : ℕ+) (c : ConjClasses G) (χ : G →* ℂˣ) :
    IsIntegral ℤ (conjugacyClassNthRootCharacterSum n c χ.toRepresentation) := by
  rw [conjugacyClassNthRootCharacterSum]
  refine IsIntegral.sum _ fun x _ ↦ ?_
  simpa using char_isIntegral χ.toRepresentation x

/-- Helper for Lemma 11-11.2-6: summing the `n`th-root class sums over all conjugacy classes
recovers the total sum of the linear character. -/
theorem sum_conjugacyClassNthRootCharacterSum_over_classes
    (n : ℕ+) (χ : G →* ℂˣ) :
    ∑ d : ConjClasses G, conjugacyClassNthRootCharacterSum n d χ.toRepresentation =
      ∑ x : G, (χ x : ℂ) := by
  classical
  -- Rewrite each filtered sum as an indicator sum so the class and group sums can be exchanged.
  show
    Finset.sum (Finset.univ : Finset (ConjClasses G)) (fun d : ConjClasses G ↦
      Finset.sum (Finset.univ.filter fun x : G ↦ x ^ (n : ℕ) ∈ d.carrier)
        (fun x : G ↦ χ.toRepresentation.character x)) =
      Finset.sum (Finset.univ : Finset G) (fun x : G ↦ (χ x : ℂ))
  calc
    Finset.sum (Finset.univ : Finset (ConjClasses G)) (fun d : ConjClasses G ↦
        Finset.sum (Finset.univ.filter fun x : G ↦ x ^ (n : ℕ) ∈ d.carrier)
          (fun x : G ↦ χ.toRepresentation.character x))
        =
      Finset.sum (Finset.univ : Finset (ConjClasses G)) (fun d : ConjClasses G ↦
        Finset.sum (Finset.univ : Finset G) (fun x : G ↦
          if x ^ (n : ℕ) ∈ d.carrier then χ.toRepresentation.character x else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro d hd
          rw [Finset.sum_filter]
    _ =
      Finset.sum (Finset.univ : Finset G) (fun x : G ↦
        Finset.sum (Finset.univ : Finset (ConjClasses G)) (fun d : ConjClasses G ↦
          if x ^ (n : ℕ) ∈ d.carrier then χ.toRepresentation.character x else 0)) := by
          exact Finset.sum_comm
    _ = Finset.sum (Finset.univ : Finset G) (fun x : G ↦ χ.toRepresentation.character x) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          let d₀ : ConjClasses G := ConjClasses.mk (x ^ (n : ℕ))
          calc
            Finset.sum (Finset.univ : Finset (ConjClasses G)) (fun d : ConjClasses G ↦
                if x ^ (n : ℕ) ∈ d.carrier then χ.toRepresentation.character x else 0)
                =
              Finset.sum (Finset.univ : Finset (ConjClasses G)) (fun d : ConjClasses G ↦
                if d = d₀ then χ.toRepresentation.character x else 0) := by
                  refine Finset.sum_congr rfl ?_
                  intro d hd
                  by_cases hd : d = d₀
                  · subst hd
                    simp [d₀, ConjClasses.mem_carrier_iff_mk_eq]
                  · have hnot : x ^ (n : ℕ) ∉ d.carrier := by
                      intro hx
                      have hmk : ConjClasses.mk (x ^ (n : ℕ)) = d :=
                        ConjClasses.mem_carrier_iff_mk_eq.mp hx
                      exact hd (by simpa [d₀] using hmk.symm)
                    simp [hd, hnot]
            _ = χ.toRepresentation.character x := by
                  simpa [d₀] using
                    (Finset.sum_ite_eq (s := Finset.univ) d₀
                      (fun _ : ConjClasses G ↦ χ.toRepresentation.character x))
  -- Return to the source-facing linear character notation.
  simp [MonoidHom.toRepresentation_character_apply]

/-- Helper for Lemma 11-11.2-6: a nontrivial linear character has total sum `0`. -/
theorem sum_linearCharacter_eq_zero_of_ne_one
    (χ : G →* ℂˣ) (hχ : χ ≠ 1) :
    ∑ x : G, (χ x : ℂ) = 0 := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : G, χ g ≠ 1 := by
    by_contra hnot
    apply hχ
    ext x
    have hx : χ x = 1 := by
      by_contra hx
      exact hnot ⟨x, hx⟩
    simpa using congrArg (fun u : ℂˣ ↦ (u : ℂ)) hx
  let s : ℂ := ∑ x : G, (χ x : ℂ)
  have htranslate : (χ g : ℂ) * s = s := by
    -- Left translation permutes `G`, so multiplying every summand by `χ g` leaves the total sum
    -- unchanged.
    calc
      (χ g : ℂ) * s = ∑ x : G, (χ g : ℂ) * (χ x : ℂ) := by
        simpa [s] using Finset.mul_sum (Finset.univ) (fun x : G ↦ (χ x : ℂ)) (χ g : ℂ)
      _ = ∑ x : G, (χ (g * x) : ℂ) := by
        exact Fintype.sum_congr
          (fun x : G ↦ (χ g : ℂ) * (χ x : ℂ))
          (fun x : G ↦ (χ (g * x) : ℂ))
          (fun x ↦ by simp [map_mul])
      _ = s := by
        simpa [s] using Equiv.sum_comp (Equiv.mulLeft g) (fun x : G ↦ (χ x : ℂ))
  have hgC : (χ g : ℂ) ≠ 1 := by
    intro hgC
    apply hg
    ext
    simpa using hgC
  have hfactor : ((χ g : ℂ) - 1) * s = 0 := by
    calc
      ((χ g : ℂ) - 1) * s = (χ g : ℂ) * s - s := by ring
      _ = s - s := by rw [htranslate]
      _ = 0 := sub_self s
  have hs : s = 0 := by
    refine (mul_eq_zero.mp hfactor).resolve_left ?_
    exact sub_ne_zero.mpr hgC
  simpa [s] using hs

/-- Helper for Lemma 11-11.2-6: the total sum of a linear character is divisible by
`Nat.gcd (Nat.card G) n` in the ring of algebraic integers. -/
theorem linear_character_total_sum_mem_span_gcd_card
    (n : ℕ+) (χ : G →* ℂˣ) :
    (⟨∑ x : G, (χ x : ℂ),
      by
        -- Each linear-character value is a root of unity, hence integral; sums preserve
        -- integrality.
        refine IsIntegral.sum _ fun x ↦ ?_
        simpa using char_isIntegral χ.toRepresentation x⟩ :
      integralClosure ℤ ℂ) ∈
      Ideal.span
        ({(Nat.gcd (Nat.card G) (n : ℕ) : integralClosure ℤ ℂ)} :
          Set (integralClosure ℤ ℂ)) := by
  classical
  by_cases hχ : χ = 1
  · -- In the trivial-character case, the total sum is `|G|`, and `gcd(|G|, n)` divides `|G|`.
    have hsum : ∑ x : G, (χ x : ℂ) = Nat.card G := by
      subst hχ
      simp
    obtain ⟨m, hm⟩ := Nat.gcd_dvd_left (Nat.card G) (n : ℕ)
    refine Ideal.mem_span_singleton'.2 ⟨(m : integralClosure ℤ ℂ), ?_⟩
    apply Subtype.ext
    have hmC : (((Nat.gcd (Nat.card G) (n : ℕ)) * m : ℕ) : ℂ) = (Nat.card G : ℂ) := by
      exact_mod_cast hm.symm
    simpa [hsum, Nat.cast_mul, mul_comm] using hmC
  · -- In the nontrivial-character case, translation shows that the total sum is zero.
    have hsum : ∑ x : G, (χ x : ℂ) = 0 :=
      sum_linearCharacter_eq_zero_of_ne_one χ hχ
    have hzero :
        (⟨∑ x : G, (χ x : ℂ),
          by
            refine IsIntegral.sum _ fun x ↦ ?_
            simpa using char_isIntegral χ.toRepresentation x⟩ :
          integralClosure ℤ ℂ) = 0 := by
      apply Subtype.ext
      simp [hsum]
    rw [hzero]
    exact Ideal.zero_mem _

/-- Helper for Lemma 11-11.2-6: once every nonunit conjugacy class contributes an element of the
target ideal, the unit class does too. -/
theorem unit_conjugacyClassNthRootSum_mem_span_gcd_card_of_nonunit
    (n : ℕ+) (χ : G →* ℂˣ)
    (hnonunit :
      ∀ d : ConjClasses G, d ≠ ConjClasses.mk (1 : G) →
        (⟨conjugacyClassNthRootCharacterSum n d χ.toRepresentation,
          conjugacyClassNthRootCharacterSum_toRepresentation_isIntegral n d χ⟩ :
          integralClosure ℤ ℂ) ∈
          Ideal.span
            ({(Nat.gcd (Nat.card G) (n : ℕ) : integralClosure ℤ ℂ)} :
              Set (integralClosure ℤ ℂ))) :
    (⟨conjugacyClassNthRootCharacterSum n (ConjClasses.mk (1 : G)) χ.toRepresentation,
      conjugacyClassNthRootCharacterSum_toRepresentation_isIntegral n (ConjClasses.mk (1 : G)) χ⟩ :
      integralClosure ℤ ℂ) ∈
      Ideal.span
        ({(Nat.gcd (Nat.card G) (n : ℕ) : integralClosure ℤ ℂ)} :
          Set (integralClosure ℤ ℂ)) := by
  classical
  let I : Ideal (integralClosure ℤ ℂ) :=
    Ideal.span
      ({(Nat.gcd (Nat.card G) (n : ℕ) : integralClosure ℤ ℂ)} :
        Set (integralClosure ℤ ℂ))
  let a : ConjClasses G → integralClosure ℤ ℂ := fun d ↦
    ⟨conjugacyClassNthRootCharacterSum n d χ.toRepresentation,
      conjugacyClassNthRootCharacterSum_toRepresentation_isIntegral n d χ⟩
  let total : integralClosure ℤ ℂ := ⟨∑ x : G, (χ x : ℂ),
    by
      -- This is the same integral total sum controlled in the previous helper.
      refine IsIntegral.sum _ fun x ↦ ?_
      simpa using char_isIntegral χ.toRepresentation x⟩
  have hsum_total : ∑ d : ConjClasses G, a d = total := by
    apply Subtype.ext
    simp [a, total, sum_conjugacyClassNthRootCharacterSum_over_classes]
  have htotal_mem : total ∈ I := by
    simpa [I, total] using linear_character_total_sum_mem_span_gcd_card n χ
  have hrest_mem :
      Finset.sum (Finset.univ.erase (ConjClasses.mk (1 : G))) a ∈ I := by
    refine Ideal.sum_mem I ?_
    intro d hd
    exact hnonunit d (by simpa using (Finset.mem_erase.mp hd).1)
  have hsplit :
      a (ConjClasses.mk (1 : G)) +
        Finset.sum (Finset.univ.erase (ConjClasses.mk (1 : G))) a = total := by
    calc
      a (ConjClasses.mk (1 : G)) +
          Finset.sum (Finset.univ.erase (ConjClasses.mk (1 : G))) a
          = ∑ d : ConjClasses G, a d := by
            simpa using
              (Finset.add_sum_erase (s := Finset.univ) (f := a)
                (by simp : ConjClasses.mk (1 : G) ∈ (Finset.univ : Finset (ConjClasses G))))
      _ = total := hsum_total
  have hunit_eq :
      a (ConjClasses.mk (1 : G)) =
        total - Finset.sum (Finset.univ.erase (ConjClasses.mk (1 : G))) a := by
    exact eq_sub_iff_add_eq.mpr hsplit
  -- Isolate the unit-class contribution by subtracting the already-controlled nonunit terms.
  have hunit_mem : a (ConjClasses.mk (1 : G)) ∈ I := by
    rw [hunit_eq]
    exact I.sub_mem htotal_mem hrest_mem
  simpa [a, I] using hunit_mem

/-- Helper for Lemma 11-11.2-6: if the `n`th-root fiber over `c` is empty, then the source sum
vanishes. -/
theorem conjugacyClassNthRootCharacterSum_eq_zero_of_no_nthRoots
    (n : ℕ+) (c : ConjClasses G) (χ : G →* ℂˣ)
    (hempty : ¬ ∃ x : G, x ^ (n : ℕ) ∈ c.carrier) :
    conjugacyClassNthRootCharacterSum n c χ.toRepresentation = 0 := by
  classical
  -- With no contributing roots, every term in the filtered sum is excluded.
  rw [conjugacyClassNthRootCharacterSum]
  refine Finset.sum_eq_zero ?_
  intro x hx
  exfalso
  exact hempty ⟨x, (Finset.mem_filter.mp hx).2⟩

/-- Helper for Lemma 11-11.2-6: a nonunit conjugacy class in a `p`-group has `p`-power order
strictly bigger than `1`. -/
theorem nonunit_class_order_eq_prime_pow
    (hG : IsPGroup p G) {c : ConjClasses G} (hc : c ≠ ConjClasses.mk (1 : G))
    (g : c.carrier) :
    ∃ b : ℕ, 0 < b ∧ orderOf (g : G) = p ^ b := by
  -- The `p`-group hypothesis gives a prime-power order; nontriviality of the class rules out `b=0`.
  obtain ⟨b, hb⟩ := (IsPGroup.iff_orderOf (p := p) (G := G)).mp hG (g : G)
  refine ⟨b, ?_, hb⟩
  by_contra hb0
  have hb_eq : b = 0 := Nat.eq_zero_of_not_pos hb0
  have horder : orderOf (g : G) = 1 := by
    simpa [hb_eq] using hb
  have hg1 : (g : G) = 1 := orderOf_eq_one_iff.mp horder
  apply hc
  calc
    c = ConjClasses.mk (g : G) := (ConjClasses.mem_carrier_iff_mk_eq.mp g.property).symm
    _ = ConjClasses.mk (1 : G) := by simp [hg1]

/-- Helper for Lemma 11-11.2-6: every `n`th root landing in `c` has the same `n`th-power order as
any chosen representative of `c`. -/
theorem nonunit_fiber_order_eq_class_order
    (n : ℕ+) {c : ConjClasses G} (g : c.carrier) {x : G}
    (hx : x ^ (n : ℕ) ∈ c.carrier) :
    orderOf (x ^ (n : ℕ)) = orderOf (g : G) := by
  -- The `n`th power of `x` lies in the same conjugacy class as `g`, so its order matches `g`.
  exact orderOf_eq_of_mem_conjClass g hx

/-- Helper for Lemma 11-11.2-6: a nonunit root has order obtained by shifting the `p`-power order
of its `n`th power by the `p`-adic valuation of `n`. -/
theorem nonunit_root_order_eq_padic_shift
    (hG : IsPGroup p G) (n : ℕ+) {c : ConjClasses G}
    (hc : c ≠ ConjClasses.mk (1 : G)) {x : G}
    (hx : x ^ (n : ℕ) ∈ c.carrier) :
    ∃ b : ℕ, 0 < b ∧ orderOf x = p ^ (padicValNat p (n : ℕ) + b) := by
  -- First pin down the nontrivial `p`-power order of the image `x ^ n`.
  obtain ⟨b, hbpos, hb⟩ := nonunit_class_order_eq_prime_pow hG hc ⟨x ^ (n : ℕ), hx⟩
  have hxpow : orderOf (x ^ (n : ℕ)) = p ^ b := by
    simpa using hb
  -- Then separate the `p`-part of `n` from its prime-to-`p` part.
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := p) (G := G)).mp hG x
  let a : ℕ := padicValNat p (n : ℕ)
  let m : ℕ := Nat.divMaxPow (n : ℕ) p
  have hp : Nat.Prime p := Fact.out
  have hx_ne_one : x ≠ 1 := by
    intro hx1
    apply hc
    have hx_unit : (1 : G) ^ (n : ℕ) ∈ c.carrier := by
      simpa [hx1] using hx
    simpa using (ConjClasses.mem_carrier_iff_mk_eq.mp hx_unit).symm
  have hn : (n : ℕ) = p ^ a * m := by
    simpa [a, m] using (pow_padicValNat_mul_divMaxPow p (n : ℕ)).symm
  have hp1 : 1 < p := hp.one_lt
  have hn0 : (n : ℕ) ≠ 0 := ne_of_gt n.pos
  have hpm : ¬ p ∣ m := by
    simpa [m] using (Nat.not_dvd_divMaxPow (n := (n : ℕ)) hp1 hn0)
  have hkpos : 0 < k := by
    by_contra hk0
    have hk_eq : k = 0 := Nat.eq_zero_of_not_pos hk0
    have horder_one : orderOf x = 1 := by
      simpa [hk_eq] using hk
    exact hx_ne_one (orderOf_eq_one_iff.mp horder_one)
  have hcop : Nat.Coprime (p ^ k) m := by
    rw [Nat.coprime_pow_left_iff hkpos]
    exact hp.coprime_iff_not_dvd.2 hpm
  have hcop' : Nat.Coprime (orderOf x) m := by
    simpa [hk] using hcop
  have hxm : orderOf (x ^ m) = p ^ k := by
    simpa [hk] using (Nat.Coprime.orderOf_pow (y := x) (m := m) hcop')
  have hxpm : orderOf ((x ^ m) ^ (p ^ a)) = p ^ b := by
    calc
      orderOf ((x ^ m) ^ (p ^ a)) = orderOf (x ^ (m * p ^ a)) := by rw [pow_mul]
      _ = orderOf (x ^ (n : ℕ)) := by simp [hn, Nat.mul_comm]
      _ = p ^ b := hxpow
  -- The nontriviality of `x ^ n` forces at least `a` copies of `p` in `orderOf x`.
  have hka : a ≤ k := by
    by_contra hak
    have hle : k ≤ a := Nat.le_of_lt (lt_of_not_ge hak)
    have hpow1' : orderOf ((x ^ m) ^ (p ^ a)) = p ^ k / p ^ k := by
      simpa [hxm, Nat.gcd_eq_left (pow_dvd_pow p hle)] using
        (orderOf_pow' (x := x ^ m) (n := p ^ a) (pow_ne_zero _ hp.ne_zero))
    have hpow1 : orderOf ((x ^ m) ^ (p ^ a)) = 1 := by
      rw [hpow1']
      exact Nat.div_self (pow_pos hp.pos _)
    have hone : p ^ b = 1 := by
      calc
        p ^ b = orderOf ((x ^ m) ^ (p ^ a)) := hxpm.symm
        _ = 1 := hpow1
    have hp2 : 2 ≤ p := hp.two_le
    have hbzero : b = 0 := Nat.pow_right_injective hp2 hone
    omega
  -- Now compute the exact shift in the exponent.
  have hdiv : p ^ a ∣ p ^ k := pow_dvd_pow p hka
  have hpowk : orderOf ((x ^ m) ^ (p ^ a)) = p ^ (k - a) := by
    have hdiv' : p ^ a ∣ orderOf (x ^ m) := by
      simpa [hxm] using hdiv
    have horder :=
      orderOf_pow_of_dvd (x := x ^ m) (n := p ^ a) (pow_ne_zero _ hp.ne_zero) hdiv'
    have hdiv_eq : p ^ k / p ^ a = p ^ (k - a) := by
      apply Nat.div_eq_of_eq_mul_left (pow_pos hp.pos _)
      calc
        p ^ k = p ^ ((k - a) + a) := by rw [Nat.sub_add_cancel hka]
        _ = p ^ (k - a) * p ^ a := by rw [Nat.pow_add]
    simpa [hxm, hdiv_eq] using horder
  have hkb : k - a = b := by
    apply Nat.pow_right_injective hp.two_le
    simpa [hxpm] using hpowk.symm
  refine ⟨b, hbpos, ?_⟩
  rw [hk]
  have hsum : k = a + b := by
    omega
  simp [a, hsum]

/-- Helper for Lemma 11-11.2-6: once a root has order `p^(a+b)` with
`a = padicValNat p n`, the source exponent family `x ↦ x^(1 + p^b t)` preserves the `n`th
power. -/
theorem nonunit_exponent_nth_power_eq
    (n : ℕ+) {x : G} (b t : ℕ)
    (horder : orderOf x = p ^ (padicValNat p (n : ℕ) + b)) :
    (x ^ (1 + p ^ b * t)) ^ (n : ℕ) = x ^ (n : ℕ) := by
  let a : ℕ := padicValNat p (n : ℕ)
  let m : ℕ := Nat.divMaxPow (n : ℕ) p
  have hn : (n : ℕ) = p ^ a * m := by
    simpa [a, m] using (pow_padicValNat_mul_divMaxPow p (n : ℕ)).symm
  have hexp : ((1 + p ^ b * t) * (n : ℕ)) = (n : ℕ) + p ^ (a + b) * (m * t) := by
    rw [hn, Nat.pow_add]
    ring
  -- Expand the new exponent and isolate the multiple of `orderOf x`.
  calc
    (x ^ (1 + p ^ b * t)) ^ (n : ℕ)
        = x ^ ((1 + p ^ b * t) * (n : ℕ)) := by rw [pow_mul]
    _ = x ^ ((n : ℕ) + p ^ (a + b) * (m * t)) := by rw [hexp]
    _ = x ^ (n : ℕ) * (x ^ (p ^ (a + b))) ^ (m * t) := by rw [pow_add, pow_mul]
    _ = x ^ (n : ℕ) * 1 := by
        congr 1
        rw [show p ^ (a + b) = orderOf x by
          simpa [a, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using horder.symm]
        simp [pow_orderOf_eq_one x]
    _ = x ^ (n : ℕ) := by simp

/-- Helper for Lemma 11-11.2-6: the concrete source exponents `1 + p^b t` stay inside the same
`n`th-root fiber. -/
theorem nonunit_exponent_mem_nthRootFiber
    (n : ℕ+) {c : ConjClasses G} {x : G} (b t : ℕ)
    (hx : x ^ (n : ℕ) ∈ c.carrier)
    (horder : orderOf x = p ^ (padicValNat p (n : ℕ) + b)) :
    (x ^ (1 + p ^ b * t)) ^ (n : ℕ) ∈ c.carrier := by
  -- Replace the new `n`th power by the original one, then reuse the fiber hypothesis.
  simpa [nonunit_exponent_nth_power_eq (p := p) n b t horder] using hx

/-- Helper for Lemma 11-11.2-6: the character sum over one explicit exponent family is a geometric
series, hence either `0` or a multiple of `p^a`. -/
theorem nonunit_parameter_character_sum_eq_zero_or_padic_multiple
    (χ : G →* ℂˣ) (x : G) (a b : ℕ)
    (horder : orderOf x = p ^ (a + b)) :
    ∑ i : Fin (p ^ a), (χ (x ^ (1 + p ^ b * (i : ℕ))) : ℂ)
      = if (χ (x ^ (p ^ b)) : ℂ) = 1 then (p ^ a : ℂ) * (χ x : ℂ) else 0 := by
  let z : ℂ := (χ (x ^ (p ^ b)) : ℂ)
  have hz : z ^ (p ^ a) = 1 := by
    dsimp [z]
    have hpowx : (x ^ (p ^ b)) ^ (p ^ a) = 1 := by
      have hp : Nat.Prime p := Fact.out
      have hdiv : p ^ b ∣ orderOf x := by
        rw [horder, Nat.pow_add, Nat.mul_comm]
        exact dvd_mul_of_dvd_left (dvd_refl (p ^ b)) (p ^ a)
      have htmp := orderOf_pow_of_dvd (x := x) (n := p ^ b) (pow_ne_zero _ hp.ne_zero) hdiv
      have hdiv_eq : p ^ (a + b) / p ^ b = p ^ a := by
        rw [Nat.pow_add, Nat.mul_comm]
        exact Nat.mul_div_right (p ^ a) (pow_pos hp.pos _)
      have hpoword : orderOf (x ^ (p ^ b)) = p ^ a := by
        simpa [horder, hdiv_eq, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htmp
      simpa [hpoword] using pow_orderOf_eq_one (x ^ (p ^ b))
    simpa [map_pow] using congrArg (fun g : G ↦ (χ g : ℂ)) hpowx
  let geom : ℂ := Finset.sum (Finset.range (p ^ a)) fun i ↦ z ^ i
  have hgeom : geom = if z = 1 then (p ^ a : ℂ) else 0 := by
    by_cases h1 : z = 1
    · simp [geom, h1]
    · have hmul : geom * (z - 1) = 0 := by
        calc
          geom * (z - 1) = z ^ (p ^ a) - 1 := by
            simpa [geom] using geom_sum_mul z (p ^ a)
          _ = 0 := by simp [hz]
      have hzsub : z - 1 ≠ 0 := sub_ne_zero.mpr h1
      have hsum_zero : geom = 0 :=
        (mul_eq_zero.mp hmul).resolve_right hzsub
      simp [geom, h1, hsum_zero]
  calc
    ∑ i : Fin (p ^ a), (χ (x ^ (1 + p ^ b * (i : ℕ))) : ℂ)
        = (χ x : ℂ) * geom := by
            calc
              (∑ i : Fin (p ^ a), (χ (x ^ (1 + p ^ b * (i : ℕ))) : ℂ))
                  = ∑ i : Fin (p ^ a), (χ x : ℂ) * ((χ (x ^ (p ^ b)) : ℂ)) ^ (i : ℕ) := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      calc
                        (χ (x ^ (1 + p ^ b * (i : ℕ))) : ℂ)
                            = (χ x : ℂ) ^ (1 + p ^ b * (i : ℕ)) := by simp
                        _ = (χ x : ℂ) * ((χ x : ℂ) ^ (p ^ b)) ^ (i : ℕ) := by
                              rw [pow_add, pow_one, pow_mul]
                        _ = (χ x : ℂ) * ((χ (x ^ (p ^ b)) : ℂ)) ^ (i : ℕ) := by simp [map_pow]
              _ = (χ x : ℂ) * ∑ i : Fin (p ^ a), z ^ (i : ℕ) := by
                    rw [Finset.mul_sum]
              _ = (χ x : ℂ) * geom := by
                    simp_rw [Fin.sum_univ_eq_sum_range, geom]
    _ = if z = 1 then (p ^ a : ℂ) * (χ x : ℂ) else 0 := by
        by_cases h1 : z = 1
        · simp [geom, hgeom, h1, mul_comm]
        · simp [geom, hgeom, h1]

/-- Helper for Lemma 11-11.2-6: each explicit exponent family already contributes an element of
the ideal generated by `p^a`. -/
theorem nonunit_parameter_character_sum_mem_span_padic
    (χ : G →* ℂˣ) (x : G) (a b : ℕ)
    (horder : orderOf x = p ^ (a + b)) :
    (⟨∑ i : Fin (p ^ a), (χ (x ^ (1 + p ^ b * (i : ℕ))) : ℂ),
      by
        -- Each summand is a linear-character value, hence integral.
        refine IsIntegral.sum _ fun i ↦ ?_
        simpa using char_isIntegral χ.toRepresentation (x ^ (1 + p ^ b * (i : ℕ)))⟩ :
      integralClosure ℤ ℂ) ∈
      Ideal.span ({(p ^ a : integralClosure ℤ ℂ)} : Set (integralClosure ℤ ℂ)) := by
  let z : ℂ := (χ (x ^ (p ^ b)) : ℂ)
  have hsum :
      ∑ i : Fin (p ^ a), (χ (x ^ (1 + p ^ b * (i : ℕ))) : ℂ)
        = if z = 1 then (p ^ a : ℂ) * (χ x : ℂ) else 0 := by
    -- First compute the parameterized sum explicitly in `ℂ`.
    have hz : z ^ (p ^ a) = 1 := by
      dsimp [z]
      have hpowx : (x ^ (p ^ b)) ^ (p ^ a) = 1 := by
        have hp : Nat.Prime p := Fact.out
        have hdiv : p ^ b ∣ orderOf x := by
          rw [horder, Nat.pow_add, Nat.mul_comm]
          exact dvd_mul_of_dvd_left (dvd_refl (p ^ b)) (p ^ a)
        have htmp := orderOf_pow_of_dvd (x := x) (n := p ^ b) (pow_ne_zero _ hp.ne_zero) hdiv
        have hdiv_eq : p ^ (a + b) / p ^ b = p ^ a := by
          rw [Nat.pow_add, Nat.mul_comm]
          exact Nat.mul_div_right (p ^ a) (pow_pos hp.pos _)
        have hpoword : orderOf (x ^ (p ^ b)) = p ^ a := by
          simpa [horder, hdiv_eq, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htmp
        simpa [hpoword] using pow_orderOf_eq_one (x ^ (p ^ b))
      simpa [map_pow] using congrArg (fun g : G ↦ (χ g : ℂ)) hpowx
    let geom : ℂ := Finset.sum (Finset.range (p ^ a)) fun i ↦ z ^ i
    have hgeom : geom = if z = 1 then (p ^ a : ℂ) else 0 := by
      by_cases h1 : z = 1
      · simp [geom, h1]
      · have hmul : geom * (z - 1) = 0 := by
          calc
            geom * (z - 1) = z ^ (p ^ a) - 1 := by
              simpa [geom] using geom_sum_mul z (p ^ a)
            _ = 0 := by simp [hz]
        have hzsub : z - 1 ≠ 0 := sub_ne_zero.mpr h1
        have hsum_zero : geom = 0 :=
          (mul_eq_zero.mp hmul).resolve_right hzsub
        simp [geom, h1, hsum_zero]
    calc
      ∑ i : Fin (p ^ a), (χ (x ^ (1 + p ^ b * (i : ℕ))) : ℂ)
          = (χ x : ℂ) * geom := by
              calc
                (∑ i : Fin (p ^ a), (χ (x ^ (1 + p ^ b * (i : ℕ))) : ℂ))
                    = ∑ i : Fin (p ^ a), (χ x : ℂ) * ((χ (x ^ (p ^ b)) : ℂ)) ^ (i : ℕ) := by
                        refine Finset.sum_congr rfl ?_
                        intro i hi
                        calc
                          (χ (x ^ (1 + p ^ b * (i : ℕ))) : ℂ)
                              = (χ x : ℂ) ^ (1 + p ^ b * (i : ℕ)) := by simp
                          _ = (χ x : ℂ) * ((χ x : ℂ) ^ (p ^ b)) ^ (i : ℕ) := by
                                rw [pow_add, pow_one, pow_mul]
                          _ = (χ x : ℂ) * ((χ (x ^ (p ^ b)) : ℂ)) ^ (i : ℕ) := by simp [map_pow]
                _ = (χ x : ℂ) * ∑ i : Fin (p ^ a), z ^ (i : ℕ) := by
                      rw [Finset.mul_sum]
                _ = (χ x : ℂ) * geom := by
                      simp_rw [Fin.sum_univ_eq_sum_range, geom]
      _ = if z = 1 then (p ^ a : ℂ) * (χ x : ℂ) else 0 := by
            by_cases h1 : z = 1
            · simp [geom, hgeom, h1, mul_comm]
            · simp [geom, hgeom, h1]
  by_cases h1 : z = 1
  · refine Ideal.mem_span_singleton'.2 ?_
    refine ⟨⟨(χ x : ℂ), by simpa using char_isIntegral χ.toRepresentation x⟩, ?_⟩
    apply Subtype.ext
    simpa [h1, mul_comm] using hsum.symm
  · have hzero :
      (⟨∑ i : Fin (p ^ a), (χ (x ^ (1 + p ^ b * (i : ℕ))) : ℂ),
        by
          refine IsIntegral.sum _ fun i ↦ ?_
          simpa using char_isIntegral χ.toRepresentation (x ^ (1 + p ^ b * (i : ℕ)))⟩ :
        integralClosure ℤ ℂ) = 0 := by
        apply Subtype.ext
        simpa [h1] using hsum
    rw [hzero]
    exact Ideal.zero_mem _

/-- Helper for Lemma 11-11.2-6: a root of order `p^(a+b)` has `n`th power of order `p^b`, where
`a = padicValNat p n`. -/
theorem nonunit_nth_power_order_eq_prime_pow
    (n : ℕ+) {x : G} {b : ℕ} (hbpos : 0 < b)
    (horder : orderOf x = p ^ (padicValNat p (n : ℕ) + b)) :
    orderOf (x ^ (n : ℕ)) = p ^ b := by
  let a : ℕ := padicValNat p (n : ℕ)
  let m : ℕ := Nat.divMaxPow (n : ℕ) p
  have hp : Nat.Prime p := Fact.out
  have hn : (n : ℕ) = p ^ a * m := by
    simpa [a, m] using (pow_padicValNat_mul_divMaxPow p (n : ℕ)).symm
  have hp1 : 1 < p := hp.one_lt
  have hn0 : (n : ℕ) ≠ 0 := ne_of_gt n.pos
  have hpm : ¬ p ∣ m := by
    simpa [m] using (Nat.not_dvd_divMaxPow (n := (n : ℕ)) hp1 hn0)
  have habpos : 0 < a + b := Nat.add_pos_right _ hbpos
  have hcop : Nat.Coprime (p ^ (a + b)) m := by
    rw [Nat.coprime_pow_left_iff habpos]
    exact hp.coprime_iff_not_dvd.2 hpm
  have hcop' : Nat.Coprime (orderOf x) m := by
    simpa [a, horder] using hcop
  have hxm : orderOf (x ^ m) = p ^ (a + b) := by
    simpa [a, horder] using (Nat.Coprime.orderOf_pow (y := x) (m := m) hcop')
  have hdiv : p ^ a ∣ orderOf (x ^ m) := by
    rw [hxm]
    exact pow_dvd_pow p (Nat.le_add_right a b)
  have hpow :
      orderOf ((x ^ m) ^ (p ^ a)) = p ^ (a + b) / p ^ a := by
    simpa [hxm] using
      (orderOf_pow_of_dvd (x := x ^ m) (n := p ^ a)
        (pow_ne_zero _ hp.ne_zero) hdiv)
  have hdiv_eq : p ^ (a + b) / p ^ a = p ^ b := by
    calc
      p ^ (a + b) / p ^ a = (p ^ a * p ^ b) / p ^ a := by
        rw [Nat.pow_add]
      _ = p ^ b := Nat.mul_div_right (p ^ b) (pow_pos hp.pos _)
  calc
    orderOf (x ^ (n : ℕ)) = orderOf ((x ^ m) ^ (p ^ a)) := by
      rw [hn, Nat.mul_comm, pow_mul]
    _ = p ^ (a + b) / p ^ a := hpow
    _ = p ^ b := hdiv_eq

/-- Helper for Lemma 11-11.2-6: all roots in the same nonunit `n`th-root fiber have the same
order. -/
theorem nonunit_root_order_eq_uniform_shift
    (hG : IsPGroup p G) (n : ℕ+) {c : ConjClasses G}
    (hc : c ≠ ConjClasses.mk (1 : G)) {g x : G}
    (hg : g ^ (n : ℕ) ∈ c.carrier) (hx : x ^ (n : ℕ) ∈ c.carrier) :
    orderOf x = orderOf g := by
  let hp : Nat.Prime p := Fact.out
  -- Compute the `p`-power shift for each root separately and compare their `n`th powers inside
  -- the common conjugacy class.
  obtain ⟨bx, hbxpos, hxorder⟩ := nonunit_root_order_eq_padic_shift hG n hc hx
  obtain ⟨bg, hbgpos, hgorder⟩ := nonunit_root_order_eq_padic_shift hG n hc hg
  have hxn : orderOf (x ^ (n : ℕ)) = p ^ bx :=
    nonunit_nth_power_order_eq_prime_pow (p := p) n hbxpos hxorder
  have hgn : orderOf (g ^ (n : ℕ)) = p ^ bg :=
    nonunit_nth_power_order_eq_prime_pow (p := p) n hbgpos hgorder
  have hsame : orderOf (x ^ (n : ℕ)) = orderOf (g ^ (n : ℕ)) := by
    exact orderOf_eq_of_mem_conjClass ⟨g ^ (n : ℕ), hg⟩ hx
  have hpoweq : p ^ bx = p ^ bg := by simpa [hxn, hgn] using hsame
  have hbeq : bx = bg := Nat.pow_right_injective hp.two_le hpoweq
  calc
    orderOf x = p ^ (padicValNat p (n : ℕ) + bx) := hxorder
    _ = p ^ (padicValNat p (n : ℕ) + bg) := by simp [hbeq]
    _ = orderOf g := hgorder.symm

/-- Helper for Lemma 11-11.2-6: the explicit exponent parametrization of one nonunit orbit is
injective on the `Fin (p^a)` parameter. -/
theorem nonunit_exponent_embedding
    (n : ℕ+) {c : ConjClasses G} (b : ℕ)
    (x : {y : G // y ^ (n : ℕ) ∈ c.carrier})
    (horder : orderOf (x : G) = p ^ (padicValNat p (n : ℕ) + b)) :
    Function.Injective
      (fun i : Fin (p ^ padicValNat p (n : ℕ)) ↦
        (⟨(x : G) ^ (1 + p ^ b * (i : ℕ)),
          nonunit_exponent_mem_nthRootFiber (p := p) n b i x.property horder⟩ :
          {y : G // y ^ (n : ℕ) ∈ c.carrier})) := by
  intro i j hij
  have hij_pow :
      (x : G) ^ (1 + p ^ b * (i : ℕ)) = (x : G) ^ (1 + p ^ b * (j : ℕ)) := by
    exact congrArg Subtype.val hij
  have hmod :
      1 + p ^ b * (i : ℕ) ≡ 1 + p ^ b * (j : ℕ) [MOD orderOf (x : G)] :=
    (pow_eq_pow_iff_modEq).mp hij_pow
  have hmul :
      p ^ b * (i : ℕ) ≡ p ^ b * (j : ℕ) [MOD orderOf (x : G)] := by
    exact Nat.ModEq.add_left_cancel (Nat.ModEq.refl 1) hmod
  have hmul' :
      p ^ b * (i : ℕ) ≡ p ^ b * (j : ℕ)
        [MOD p ^ b * p ^ padicValNat p (n : ℕ)] := by
    simpa [horder, Nat.pow_add, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      hmul
  have hparam :
      (i : ℕ) ≡ (j : ℕ) [MOD p ^ padicValNat p (n : ℕ)] := by
    exact Nat.ModEq.mul_left_cancel' (pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero) hmul'
  have hi_lt : (i : ℕ) < p ^ padicValNat p (n : ℕ) := i.isLt
  have hj_lt : (j : ℕ) < p ^ padicValNat p (n : ℕ) := j.isLt
  have hij_val : (i : ℕ) = (j : ℕ) := by
    rcases le_total (i : ℕ) (j : ℕ) with hle | hle
    · have hdiv : p ^ padicValNat p (n : ℕ) ∣ (j : ℕ) - (i : ℕ) := by
        exact (Nat.modEq_iff_dvd' hle).mp hparam
      have hlt : (j : ℕ) - (i : ℕ) < p ^ padicValNat p (n : ℕ) := by
        exact lt_of_le_of_lt (Nat.sub_le _ _) hj_lt
      have hzero : (j : ℕ) - (i : ℕ) = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hlt
      exact Nat.le_antisymm hle (Nat.sub_eq_zero_iff_le.mp hzero)
    · have hdiv : p ^ padicValNat p (n : ℕ) ∣ (i : ℕ) - (j : ℕ) := by
        exact (Nat.modEq_iff_dvd' hle).mp hparam.symm
      have hlt : (i : ℕ) - (j : ℕ) < p ^ padicValNat p (n : ℕ) := by
        exact lt_of_le_of_lt (Nat.sub_le _ _) hi_lt
      have hzero : (i : ℕ) - (j : ℕ) = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hlt
      exact Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp hzero) hle
  exact Fin.ext hij_val

/-- Helper for Lemma 11-11.2-6: the explicit exponent family through one root, packaged as an
embedding from `Fin (p^a)` into the `n`th-root fiber. -/
noncomputable def nonunit_exponentCycleEmbedding
    (n : ℕ+) (c : ConjClasses G) (b : ℕ)
    (x : {y : G // y ^ (n : ℕ) ∈ c.carrier})
    (horder : orderOf (x : G) = p ^ (padicValNat p (n : ℕ) + b)) :
    Fin (p ^ padicValNat p (n : ℕ)) ↪ {y : G // y ^ (n : ℕ) ∈ c.carrier} :=
  { toFun := fun i ↦
      ⟨(x : G) ^ (1 + p ^ b * (i : ℕ)),
        nonunit_exponent_mem_nthRootFiber (p := p) n b i x.property horder⟩
    inj' := nonunit_exponent_embedding (p := p) n b x horder }

/-- Helper for Lemma 11-11.2-6: one free exponent orbit inside the nonunit `n`th-root fiber. -/
noncomputable def nonunit_exponentCycle
    (n : ℕ+) (c : ConjClasses G) (b : ℕ)
    (x : {y : G // y ^ (n : ℕ) ∈ c.carrier})
    (horder : orderOf (x : G) = p ^ (padicValNat p (n : ℕ) + b)) :
    Finset {y : G // y ^ (n : ℕ) ∈ c.carrier} :=
  let _ := Classical.decEq {y : G // y ^ (n : ℕ) ∈ c.carrier}
  Finset.univ.map (nonunit_exponentCycleEmbedding (p := p) n c b x horder)

/-- Helper for Lemma 11-11.2-6: the sum over one explicit exponent orbit already lies in the
ideal generated by `p^a`. -/
theorem nonunit_exponentCycle_sum_mem_span_padic
    (n : ℕ+) {c : ConjClasses G} (χ : G →* ℂˣ) (b : ℕ)
    (x : {y : G // y ^ (n : ℕ) ∈ c.carrier})
    (horder : orderOf (x : G) = p ^ (padicValNat p (n : ℕ) + b)) :
    (⟨∑ y ∈ nonunit_exponentCycle (p := p) n c b x horder, (χ y : ℂ),
      by
        -- Every orbit term is a linear-character value, hence integral.
        refine IsIntegral.sum _ fun y _ ↦ ?_
        simpa using char_isIntegral χ.toRepresentation (y : G)⟩ :
      integralClosure ℤ ℂ) ∈
      Ideal.span ({(p ^ padicValNat p (n : ℕ) : integralClosure ℤ ℂ)} :
        Set (integralClosure ℤ ℂ)) := by
  classical
  -- The cycle is a `Finset.map` of the parameter family, so the sum is exactly the already-proved
  -- parameterized sum.
  simpa [nonunit_exponentCycle, nonunit_exponentCycleEmbedding, Finset.sum_map] using
    (nonunit_parameter_character_sum_mem_span_padic (p := p) χ (x : G)
      (padicValNat p (n : ℕ)) b horder)

/-- Helper for Lemma 11-11.2-6: each explicit exponent cycle contains its base point. -/
theorem nonunit_exponentCycle_self_mem
    (n : ℕ+) {c : ConjClasses G} (b : ℕ)
    (x : {y : G // y ^ (n : ℕ) ∈ c.carrier})
    (horder : orderOf (x : G) = p ^ (padicValNat p (n : ℕ) + b)) :
    x ∈ nonunit_exponentCycle (p := p) n c b x horder := by
  classical
  -- The parameter `0 : Fin (p^a)` gives back the original root.
  refine Finset.mem_map.mpr ?_
  refine ⟨0, by simp, ?_⟩
  apply Subtype.ext
  simp [nonunit_exponentCycleEmbedding]

/-- Helper for Lemma 11-11.2-6: every explicit exponent cycle has cardinality `p^a`. -/
theorem nonunit_exponentCycle_card
    (n : ℕ+) {c : ConjClasses G} (b : ℕ)
    (x : {y : G // y ^ (n : ℕ) ∈ c.carrier})
    (horder : orderOf (x : G) = p ^ (padicValNat p (n : ℕ) + b)) :
    (nonunit_exponentCycle (p := p) n c b x horder).card = p ^ padicValNat p (n : ℕ) := by
  classical
  -- The cycle is the image of `Fin (p^a)` under an embedding.
  simp [nonunit_exponentCycle]

/-- Helper for Lemma 11-11.2-6: if one root lies in another explicit exponent cycle, then the
second cycle is contained in the first. -/
theorem nonunit_exponentCycle_subset_of_mem
    (n : ℕ+) {c : ConjClasses G} (b : ℕ)
    (x y : {z : G // z ^ (n : ℕ) ∈ c.carrier})
    (hx : orderOf (x : G) = p ^ (padicValNat p (n : ℕ) + b))
    (hy : orderOf (y : G) = p ^ (padicValNat p (n : ℕ) + b))
    (hxy : y ∈ nonunit_exponentCycle (p := p) n c b x hx) :
    nonunit_exponentCycle (p := p) n c b y hy ⊆
      nonunit_exponentCycle (p := p) n c b x hx := by
  classical
  intro z hz
  -- Unpack the two cycle memberships into explicit parameters and compose the exponents.
  rcases Finset.mem_map.mp hxy with ⟨i, -, rfl⟩
  rcases Finset.mem_map.mp hz with ⟨j, -, rfl⟩
  let a : ℕ := padicValNat p (n : ℕ)
  let k₀ : ℕ := (i : ℕ) + (j : ℕ) + p ^ b * (i : ℕ) * (j : ℕ)
  let k : Fin (p ^ a) := ⟨k₀ % p ^ a, Nat.mod_lt _ (pow_pos (Fact.out : Nat.Prime p).pos _)⟩
  refine Finset.mem_map.mpr ?_
  refine ⟨k, by simp, ?_⟩
  apply Subtype.ext
  -- Replace the composed exponent by its reduction modulo the order `p^(a+b)`.
  have hk_eq :
      (1 + p ^ b * (i : ℕ)) * (1 + p ^ b * (j : ℕ)) = 1 + p ^ b * k₀ := by
    dsimp [k₀]
    ring
  have hk_le : (k : ℕ) ≤ k₀ := by
    dsimp [k]
    exact Nat.mod_le _ _
  have hk_div : p ^ a ∣ k₀ - (k : ℕ) := by
    exact (Nat.modEq_iff_dvd' hk_le).mp (by
      simpa [k, a] using Nat.mod_modEq k₀ (p ^ a))
  have hpow_mod' :
      1 + p ^ b * (k : ℕ) ≡ 1 + p ^ b * k₀ [MOD p ^ (a + b)] := by
    have hle :
        1 + p ^ b * (k : ℕ) ≤ 1 + p ^ b * k₀ := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        add_le_add_left (Nat.mul_le_mul_left _ hk_le) 1
    apply (Nat.modEq_iff_dvd' hle).mpr
    rw [Nat.add_sub_add_left]
    rw [← Nat.mul_sub_left_distrib]
    have hmul : p ^ a * p ^ b ∣ (k₀ - (k : ℕ)) * p ^ b :=
      Nat.mul_dvd_mul_right hk_div (p ^ b)
    simpa [Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  have hpow_mod :
      1 + p ^ b * (k : ℕ) ≡ (1 + p ^ b * (i : ℕ)) * (1 + p ^ b * (j : ℕ))
        [MOD p ^ (a + b)] := by
    simpa [hk_eq] using hpow_mod'
  have hpow_eq :
      (x : G) ^ (1 + p ^ b * (k : ℕ)) =
        (x : G) ^ ((1 + p ^ b * (i : ℕ)) * (1 + p ^ b * (j : ℕ))) := by
    exact (pow_eq_pow_iff_modEq).mpr (by simpa [a, hx] using hpow_mod)
  calc
    (x : G) ^ (1 + p ^ b * (k : ℕ))
        = (x : G) ^ ((1 + p ^ b * (i : ℕ)) * (1 + p ^ b * (j : ℕ))) := hpow_eq
    _ = ((x : G) ^ (1 + p ^ b * (i : ℕ))) ^ (1 + p ^ b * (j : ℕ)) := by
      rw [pow_mul]

/-- Helper for Lemma 11-11.2-6: two explicit exponent cycles coincide as soon as they intersect. -/
theorem nonunit_exponentCycle_eq_of_mem
    (n : ℕ+) {c : ConjClasses G} (b : ℕ)
    (x y : {z : G // z ^ (n : ℕ) ∈ c.carrier})
    (hx : orderOf (x : G) = p ^ (padicValNat p (n : ℕ) + b))
    (hy : orderOf (y : G) = p ^ (padicValNat p (n : ℕ) + b))
    (hxy : y ∈ nonunit_exponentCycle (p := p) n c b x hx) :
    nonunit_exponentCycle (p := p) n c b y hy =
      nonunit_exponentCycle (p := p) n c b x hx := by
  classical
  -- The inclusion from overlap and the common cardinality `p^a` force equality.
  apply Finset.eq_of_subset_of_card_le
  · exact nonunit_exponentCycle_subset_of_mem (p := p) n b x y hx hy hxy
  · rw [nonunit_exponentCycle_card, nonunit_exponentCycle_card]

/-- Helper for Lemma 11-11.2-6: two explicit exponent cycles are equal exactly when one base
point lies in the other cycle. -/
theorem nonunit_exponentCycle_eq_iff_mem
    (n : ℕ+) {c : ConjClasses G} (b : ℕ)
    (x y : {z : G // z ^ (n : ℕ) ∈ c.carrier})
    (hx : orderOf (x : G) = p ^ (padicValNat p (n : ℕ) + b))
    (hy : orderOf (y : G) = p ^ (padicValNat p (n : ℕ) + b)) :
    nonunit_exponentCycle (p := p) n c b y hy =
      nonunit_exponentCycle (p := p) n c b x hx ↔
        y ∈ nonunit_exponentCycle (p := p) n c b x hx := by
  classical
  constructor
  · intro hEq
    simpa [hEq] using nonunit_exponentCycle_self_mem (p := p) n b y hy
  · intro hxy
    exact nonunit_exponentCycle_eq_of_mem (p := p) n b x y hx hy hxy

/-- Helper for Lemma 11-11.2-6: once one nonunit root has order `p^(a+b)`, the target ideal
generator is exactly `p^a = gcd(|G|, n)`. -/
theorem nonunit_padic_generator_eq_gcd_card
    (hG : IsPGroup p G) (n : ℕ+) {b : ℕ}
    (hcard_div : p ^ (padicValNat p (n : ℕ) + b) ∣ Nat.card G) :
    Nat.gcd (Nat.card G) (n : ℕ) = p ^ padicValNat p (n : ℕ) := by
  let a : ℕ := padicValNat p (n : ℕ)
  let m : ℕ := Nat.divMaxPow (n : ℕ) p
  have hp : Nat.Prime p := Fact.out
  have hn : (n : ℕ) = p ^ a * m := by
    simpa [a, m] using (pow_padicValNat_mul_divMaxPow p (n : ℕ)).symm
  have hp1 : 1 < p := hp.one_lt
  have hn0 : (n : ℕ) ≠ 0 := ne_of_gt n.pos
  have hpm : ¬ p ∣ m := by
    simpa [m] using (Nat.not_dvd_divMaxPow (n := (n : ℕ)) hp1 hn0)
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq hG
  have hak : a ≤ k := by
    rw [hk] at hcard_div
    have hpow : p ^ (a + b) ∣ p ^ k := by simpa [a] using hcard_div
    have hle := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hpow
    exact le_trans (Nat.le_add_right a b) hle
  have hcop : Nat.Coprime m (p ^ (k - a)) := by
    exact hp.coprime_pow_of_not_dvd (m := k - a) hpm
  have hk_split : p ^ k = p ^ (k - a) * p ^ a := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hak]
  calc
    Nat.gcd (Nat.card G) (n : ℕ) = Nat.gcd (p ^ k) (p ^ a * m) := by
      rw [hk, hn]
    _ = Nat.gcd (p ^ k) (m * p ^ a) := by rw [Nat.mul_comm]
    _ = Nat.gcd (p ^ (k - a) * p ^ a) (m * p ^ a) := by rw [hk_split]
    _ = Nat.gcd (p ^ (k - a)) m * p ^ a := by rw [Nat.gcd_mul_right]
    _ = 1 * p ^ a := by
      rw [Nat.gcd_comm, (Nat.coprime_iff_gcd_eq_one.mp hcop)]
    _ = p ^ a := by simp

/-- Helper for Lemma 11-11.2-6: once the `n`th-root fiber is known to be nonempty, the remaining
source-faithful step is the free exponent-orbit decomposition on that fiber. -/
theorem nonunit_fiber_sum_mem_span_gcd_card
    (hG : IsPGroup p G) (n : ℕ+) (c : ConjClasses G)
    (hc : c ≠ ConjClasses.mk (1 : G)) (χ : G →* ℂˣ)
    (hroot : ∃ x : G, x ^ (n : ℕ) ∈ c.carrier) :
    (⟨conjugacyClassNthRootCharacterSum n c χ.toRepresentation,
      conjugacyClassNthRootCharacterSum_toRepresentation_isIntegral n c χ⟩ :
      integralClosure ℤ ℂ) ∈
      Ideal.span
        ({(Nat.gcd (Nat.card G) (n : ℕ) : integralClosure ℤ ℂ)} :
          Set (integralClosure ℤ ℂ)) := by
  classical
  -- Route correction: the unresolved part is now only the nonempty orbit decomposition from the
  -- source proof, after the class-order and conjugacy-order bridges have been separated out.
  obtain ⟨g, hg⟩ := hroot
  obtain ⟨b, hbpos, hroot_order⟩ := nonunit_root_order_eq_padic_shift hG n hc hg
  let a : ℕ := padicValNat p (n : ℕ)
  let F : Type u := {x : G // x ^ (n : ℕ) ∈ c.carrier}
  have hcard_div : p ^ (a + b) ∣ Nat.card G := by
    rw [← hroot_order]
    exact orderOf_dvd_natCard g
  have huniform :
      ∀ x : F, orderOf (x : G) = p ^ (a + b) := by
    intro x
    calc
      orderOf (x : G) = orderOf g := by
        exact nonunit_root_order_eq_uniform_shift (p := p) hG n hc hg x.property
      _ = p ^ (a + b) := by simpa [a] using hroot_order
  have hcycle_mem :
      ∀ x : F,
        (⟨∑ y ∈ nonunit_exponentCycle (p := p) n c b x (huniform x), (χ y : ℂ),
          by
            -- Every cycle term is again a linear-character value, hence integral.
            refine IsIntegral.sum _ fun y hy ↦ ?_
            simpa using char_isIntegral χ.toRepresentation (y : G)⟩ :
          integralClosure ℤ ℂ) ∈
          Ideal.span ({(p ^ a : integralClosure ℤ ℂ)} :
            Set (integralClosure ℤ ℂ)) := by
    intro x
    simpa [a] using
      nonunit_exponentCycle_sum_mem_span_padic (p := p) n χ b x (huniform x)
  have hgcd : Nat.gcd (Nat.card G) (n : ℕ) = p ^ a := by
    simpa [a] using
      nonunit_padic_generator_eq_gcd_card (p := p) hG n hcard_div
  let cycleCode : F → Finset F := fun x ↦
    nonunit_exponentCycle (p := p) n c b x (huniform x)
  have hsum_eq :
      conjugacyClassNthRootCharacterSum n c χ.toRepresentation = ∑ x : F, (χ x : ℂ) := by
    -- Re-express the textbook sum as the plain sum over the `n`th-root fiber subtype.
    rw [conjugacyClassNthRootCharacterSum]
    simpa [F] using
      (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset G))
        (f := fun x : G ↦ (χ x : ℂ))
        (p := fun x : G ↦ x ^ (n : ℕ) ∈ c.carrier)).symm
  have hcode_eq :
      ∀ x : F,
        (Finset.univ.filter fun y : F ↦ cycleCode y = cycleCode x)
          = nonunit_exponentCycle (p := p) n c b x (huniform x) := by
    intro x
    -- The code fibers are precisely the actual cycles, because intersecting cycles coincide.
    apply Finset.ext
    intro y
    constructor
    · intro hy
      rcases Finset.mem_filter.mp hy with ⟨_, hyEq⟩
      exact
        (nonunit_exponentCycle_eq_iff_mem (p := p) n b x y
          (huniform x) (huniform y)).mp hyEq
    · intro hy
      refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
      exact
        (nonunit_exponentCycle_eq_iff_mem (p := p) n b x y
          (huniform x) (huniform y)).mpr hy
  let inner : Finset F → integralClosure ℤ ℂ := fun D ↦
    ⟨∑ y ∈ (Finset.univ : Finset F) with cycleCode y = D, (χ y : ℂ),
      by
        -- Every term of every fiber sum is again a linear-character value, hence integral.
        refine IsIntegral.sum _ fun y hy ↦ ?_
        simpa using char_isIntegral χ.toRepresentation (y : G)⟩
  have hinner_mem :
      ∀ D ∈ (Finset.univ : Finset F).image cycleCode,
        inner D ∈ Ideal.span ({(p ^ a : integralClosure ℤ ℂ)} :
          Set (integralClosure ℤ ℂ)) := by
    intro D hD
    rcases Finset.mem_image.mp hD with ⟨x, -, rfl⟩
    -- Replace the equality fiber by the actual explicit exponent cycle.
    simpa [inner, cycleCode, hcode_eq x] using hcycle_mem x
  have hfiberwise :
      ∑ D ∈ (Finset.univ : Finset F).image cycleCode,
        ∑ y ∈ (Finset.univ : Finset F) with cycleCode y = D, (χ y : ℂ)
        =
      ∑ y : F, (χ y : ℂ) := by
    -- Sum fiberwise over the image of the cycle-code map.
    simpa [cycleCode] using
      (Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset F))
        (t := (Finset.univ : Finset F).image cycleCode)
        (g := cycleCode)
        (fun x hx ↦ Finset.mem_image_of_mem cycleCode hx)
        (fun y : F ↦ (χ y : ℂ)))
  let totalFiber : integralClosure ℤ ℂ := ⟨∑ y : F, (χ y : ℂ),
    by
      -- The whole root fiber sum is integral for the same reason as each orbit sum.
      refine IsIntegral.sum _ fun y ↦ ?_
      simpa using char_isIntegral χ.toRepresentation (y : G)⟩
  have htotalFiber_mem :
      totalFiber ∈ Ideal.span ({(p ^ a : integralClosure ℤ ℂ)} :
        Set (integralClosure ℤ ℂ)) := by
    have hsum_mem :
        ∑ D ∈ (Finset.univ : Finset F).image cycleCode, inner D ∈
          Ideal.span ({(p ^ a : integralClosure ℤ ℂ)} :
            Set (integralClosure ℤ ℂ)) := by
      refine Ideal.sum_mem _ ?_
      intro D hD
      exact hinner_mem D hD
    have hEq :
        (∑ D ∈ (Finset.univ : Finset F).image cycleCode, inner D) = totalFiber := by
      apply Subtype.ext
      simpa [inner, totalFiber] using hfiberwise
    rw [hEq] at hsum_mem
    exact hsum_mem
  have hgcd_fintype : Nat.gcd (Fintype.card G) (n : ℕ) = p ^ a := by
    simpa using hgcd
  have htarget_mem :
      totalFiber ∈
        Ideal.span ({(Nat.gcd (Nat.card G) (n : ℕ) : integralClosure ℤ ℂ)} :
          Set (integralClosure ℤ ℂ)) := by
    rw [Nat.card_eq_fintype_card, hgcd_fintype]
    simpa [Nat.cast_pow] using htotalFiber_mem
  have hsource_eq :
      (⟨conjugacyClassNthRootCharacterSum n c χ.toRepresentation,
        conjugacyClassNthRootCharacterSum_toRepresentation_isIntegral n c χ⟩ :
        integralClosure ℤ ℂ) = totalFiber := by
    apply Subtype.ext
    simpa [totalFiber] using hsum_eq
  rw [hsource_eq]
  exact htarget_mem

theorem linearCharacter_nonunit_conjugacyClassNthRootSum_mem_span_gcd_card
    (hG : IsPGroup p G) (n : ℕ+) (c : ConjClasses G)
    (hc : c ≠ ConjClasses.mk (1 : G)) (χ : G →* ℂˣ) :
    (⟨conjugacyClassNthRootCharacterSum n c χ.toRepresentation,
      conjugacyClassNthRootCharacterSum_toRepresentation_isIntegral n c χ⟩ :
      integralClosure ℤ ℂ) ∈
      Ideal.span
        ({(Nat.gcd (Nat.card G) (n : ℕ) : integralClosure ℤ ℂ)} :
          Set (integralClosure ℤ ℂ)) := by
  classical
  by_cases hroot : ∃ x : G, x ^ (n : ℕ) ∈ c.carrier
  · -- Route correction: the nonempty case is reduced to the orbit decomposition helper above.
    exact nonunit_fiber_sum_mem_span_gcd_card hG n c hc χ hroot
  · -- If the fiber is empty, the source sum is `0`, hence already in the target ideal.
    have hsum :
        conjugacyClassNthRootCharacterSum n c χ.toRepresentation = 0 :=
      conjugacyClassNthRootCharacterSum_eq_zero_of_no_nthRoots n c χ hroot
    have hzero :
        (⟨conjugacyClassNthRootCharacterSum n c χ.toRepresentation,
          conjugacyClassNthRootCharacterSum_toRepresentation_isIntegral n c χ⟩ :
          integralClosure ℤ ℂ) = 0 := by
      apply Subtype.ext
      simp [hsum]
    rw [hzero]
    exact Ideal.zero_mem _

-- Proof sketch: decompose `n` into its `p`-part and prime-to-`p` part and let the subgroup of
-- units congruent to `1` modulo the order of the class act on the set of `n`th roots of `c`. The
-- action is free because `G` is a `p`-group, so the sum breaks into orbits of size
-- `Nat.gcd (Nat.card G) n`; each orbit contributes a geometric sum of roots of unity, hence an
-- element of the ideal generated by `Nat.gcd (Nat.card G) n`.
/-- Lemma 11-11.2-6: if `G` is a finite `p`-group, `c` is a conjugacy class of `G`, and `χ` is a
linear character of `G`, then the sum `a_c = ∑_{x^n ∈ c} χ(x)` is congruent to `0` modulo
`Nat.gcd (Nat.card G) n` in the ring of algebraic integers of `ℂ`. -/
theorem linearCharacter_conjugacyClassNthRootSum_mem_span_gcd_card
    (hG : IsPGroup p G) (n : ℕ+) (c : ConjClasses G)
    (χ : G →* ℂˣ) :
    (⟨conjugacyClassNthRootCharacterSum n c χ.toRepresentation,
      conjugacyClassNthRootCharacterSum_toRepresentation_isIntegral n c χ⟩ :
      integralClosure ℤ ℂ) ∈
      Ideal.span
        ({(Nat.gcd (Nat.card G) (n : ℕ) : integralClosure ℤ ℂ)} :
          Set (integralClosure ℤ ℂ)) := by
  classical
  by_cases hc : c = ConjClasses.mk (1 : G)
  · subst hc
    -- Route correction: recover the unit class from the total sum after controlling every
    -- nonunit class.
    exact unit_conjugacyClassNthRootSum_mem_span_gcd_card_of_nonunit n χ
      (fun d hd ↦ linearCharacter_nonunit_conjugacyClassNthRootSum_mem_span_gcd_card hG n d hd χ)
  · -- The remaining structural work is exactly the nonunit orbit decomposition from the source.
    exact linearCharacter_nonunit_conjugacyClassNthRootSum_mem_span_gcd_card hG n c hc χ

end FrobeniusTheorem

end Representation
