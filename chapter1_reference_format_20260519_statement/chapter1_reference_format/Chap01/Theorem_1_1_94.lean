import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Nat

section PrimitiveRootsMod

variable {n : ℕ}

/-- Helper for Theorem 1.1.94: if `g` generates the unit group modulo `n`, then the quotient-step
power `g ^ (φ n / d)` generates the unique subgroup of order `d` whenever `d ∣ φ n`. -/
lemma primitive_root_pow_div_isPrimitiveRoot
    {g : (ZMod n)ˣ} (hg : IsPrimitiveRoot g (φ n)) {d : ℕ} (hd : d ∣ φ n) :
    IsPrimitiveRoot (g ^ (φ n / d)) d := by
  -- Write `φ n = d * m`; then `g ^ m` has order `d`.
  have hφpos : 0 < φ n := by
    rw [hg.eq_orderOf]
    exact orderOf_pos g
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hφpos
  obtain ⟨m, hm⟩ := hd
  have hmpos : 0 < m := by
    apply Nat.pos_of_ne_zero
    intro hm0
    have : φ n = 0 := by
      simpa [hm0] using hm
    exact hφpos.ne' this
  have hpow := hg.pow_of_dvd hmpos.ne' (show m ∣ φ n from ⟨d, by simpa [Nat.mul_comm] using hm⟩)
  have hmq : φ n / d = m := by
    exact Nat.div_eq_of_eq_mul_left hdpos (by simpa [Nat.mul_comm] using hm)
  -- Rewrite the order computed by `pow_of_dvd` into the textbook divisor `d`.
  rw [hmq]
  rw [hm, Nat.mul_comm, Nat.mul_div_right _ hmpos] at hpow
  exact hpow

/-- Helper for Theorem 1.1.94: the admissible exponents `1 ≤ k ≤ d` with `gcd(k,d)=1` are
counted by `φ d`. -/
lemma card_Icc_filter_coprime_eq_totient (d : ℕ) :
    (((Finset.Icc 1 d).filter fun k : ℕ ↦ Nat.Coprime k d).card = φ d) := by
  -- Shift the interval to `Ico 1 (d + 1)` and use the standard totient counting formula.
  simpa [Finset.Ico_succ_right_eq_Icc, Nat.add_comm, Nat.coprime_comm] using
    (Nat.filter_coprime_Ico_eq_totient d 1)

/-- Helper for Theorem 1.1.94: distinct admissible exponents give distinct powers of a primitive
root of order `d`. -/
lemma reduced_residue_pow_injective {ζ : (ZMod n)ˣ} {d : ℕ} (hζ : IsPrimitiveRoot ζ d) :
    Function.Injective
      (fun a : {k // k ∈ ((Finset.Icc 1 d).filter fun k : ℕ ↦ Nat.Coprime k d)} ↦ ζ ^ a.1) := by
  intro a b hab
  have ha_filter : a.1 ∈ ((Finset.Icc 1 d).filter fun k : ℕ ↦ Nat.Coprime k d) := by
    exact a.2
  have hb_filter : b.1 ∈ ((Finset.Icc 1 d).filter fun k : ℕ ↦ Nat.Coprime k d) := by
    exact b.2
  by_cases hd1 : d = 1
  · -- When `d = 1`, the interval contains only the exponent `1`.
    have ha_bounds : 1 ≤ a.1 ∧ a.1 ≤ d := Finset.mem_Icc.mp (Finset.mem_filter.mp ha_filter).1
    have hb_bounds : 1 ≤ b.1 ∧ b.1 ≤ d := Finset.mem_Icc.mp (Finset.mem_filter.mp hb_filter).1
    have ha1 : a.1 = 1 := by
      exact le_antisymm (by simpa [hd1] using ha_bounds.2) ha_bounds.1
    have hb1 : b.1 = 1 := by
      exact le_antisymm (by simpa [hd1] using hb_bounds.2) hb_bounds.1
    exact Subtype.ext (ha1.trans hb1.symm)
  · -- For `d > 1`, coprimality rules out the endpoint `k = d`, so `pow_inj` applies.
    have ha_lt : a.1 < d := by
      have ha_le : a.1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha_filter).1).2
      refine lt_of_le_of_ne ha_le ?_
      intro had
      have hcop : Nat.Coprime d d := by
        simpa [had] using (Finset.mem_filter.mp ha_filter).2
      exact hd1 (by simpa [Nat.coprime_self] using hcop)
    have hb_lt : b.1 < d := by
      have hb_le : b.1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb_filter).1).2
      refine lt_of_le_of_ne hb_le ?_
      intro hbd
      have hcop : Nat.Coprime d d := by
        simpa [hbd] using (Finset.mem_filter.mp hb_filter).2
      exact hd1 (by simpa [Nat.coprime_self] using hcop)
    exact Subtype.ext (hζ.pow_inj ha_lt hb_lt hab)

/-- Theorem 1.1.94 (1): for `n > 1`, a primitive root modulo `n` exists if and only if `n = 2`,
`n = 4`, or `n` is of the form `p ^ m` or `2 * p ^ m` for an odd prime `p` and an exponent
`m ≥ 1`. -/
-- Proof sketch: rewrite the existence of a primitive root modulo `n` as cyclicity of the unit
-- group `(ZMod n)ˣ`, apply `ZMod.isCyclic_units_iff`, and remove the cases `n = 0` and `n = 1`
-- using `hn`.
theorem exists_primitiveRoot_mod_iff
    (hn : 1 < n) :
    (∃ g : (ZMod n)ˣ, IsPrimitiveRoot g (φ n)) ↔
      n = 2 ∨ n = 4 ∨ ∃ p m : ℕ, p.Prime ∧ Odd p ∧ 1 ≤ m ∧
        (n = p ^ m ∨ n = 2 * p ^ m) := by
  have h0 : n ≠ 0 := by
    omega
  have h1 : n ≠ 1 := by
    omega
  let _ : NeZero n := ⟨h0⟩
  -- Replace primitive roots by a generator of maximal order in the unit group.
  rw [show (∃ g : (ZMod n)ˣ, IsPrimitiveRoot g (φ n)) ↔ IsCyclic (ZMod n)ˣ by
    rw [isCyclic_iff_exists_orderOf_eq_natCard]
    constructor
    · intro h
      rcases h with ⟨g, hg⟩
      refine ⟨g, ?_⟩
      rw [← hg.eq_orderOf, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    · intro h
      rcases h with ⟨g, hg⟩
      refine ⟨g, (IsPrimitiveRoot.iff_orderOf).2 ?_⟩
      rw [hg, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]]
  -- The cyclicity criterion for `ZMod` units already gives the textbook classification.
  simp [ZMod.isCyclic_units_iff, h0, h1]

/-- Theorem 1.1.94 (2): if `g` is a primitive root modulo `n` and `d ∣ φ n`, then the class
`g ^ ((φ n / d) * k)` has order `d` exactly when `k` is coprime to `d`. -/
-- Proof sketch: from `hd`, the power `g ^ (φ n / d)` is itself a primitive root of order `d`;
-- then apply `IsPrimitiveRoot.pow_iff_coprime` to its `k`-th power.
theorem primitiveRoot_pow_orderOf_eq_iff_coprime
    {g : (ZMod n)ˣ} (hg : IsPrimitiveRoot g (φ n)) {d k : ℕ} (hd : d ∣ φ n) :
    orderOf (g ^ ((φ n / d) * k)) = d ↔ Nat.Coprime k d := by
  have hζ := primitive_root_pow_div_isPrimitiveRoot hg hd
  have hdpos : 0 < d := by
    have hφpos : 0 < φ n := by
      rw [hg.eq_orderOf]
      exact orderOf_pos g
    exact Nat.pos_of_dvd_of_pos hd hφpos
  -- View the textbook element as the `k`-th power of the primitive root of order `d`.
  simpa [pow_mul, IsPrimitiveRoot.iff_orderOf] using (hζ.pow_iff_coprime hdpos k)

/-- Theorem 1.1.94 (3): for `d ∣ φ n`, the residue classes
`g ^ ((φ n / d) * k)` with `1 ≤ k ≤ d` and `k` coprime to `d` form a set of exactly `φ d`
pairwise distinct classes modulo `n`. -/
-- Proof sketch: identify these classes with the powers of the primitive root `g ^ (φ n / d)` of
-- order `d`; injectivity on the admissible exponents comes from primitive-root power injectivity,
-- and the number of admissible exponents is `φ d`.
theorem primitiveRoot_powers_of_order_d_card
    {g : (ZMod n)ˣ} (hg : IsPrimitiveRoot g (φ n)) {d : ℕ} (hd : d ∣ φ n) :
    (((Finset.Icc 1 d).filter fun k : ℕ ↦ Nat.Coprime k d).image
      fun k : ℕ ↦ g ^ ((φ n / d) * k)).card = φ d := by
  let s : Finset ℕ := ((Finset.Icc 1 d).filter fun k : ℕ ↦ Nat.Coprime k d)
  let e : {k // k ∈ s} ↪ (ZMod n)ˣ :=
    ⟨fun a => (g ^ (φ n / d)) ^ a.1,
      reduced_residue_pow_injective (primitive_root_pow_div_isPrimitiveRoot hg hd)⟩
  have himage : s.image (fun k : ℕ ↦ g ^ ((φ n / d) * k)) = s.attach.map e := by
    -- Rewrite the image in terms of the order-`d` primitive root `g ^ (φ n / d)`.
    ext y
    simp [e, pow_mul]
  -- Count the image by transporting it to the attached finite set of admissible exponents.
  calc
    (s.image fun k : ℕ ↦ g ^ ((φ n / d) * k)).card = (s.attach.map e).card := by
      rw [himage]
    _ = s.attach.card := Finset.card_map _
    _ = s.card := Finset.card_attach
    _ = φ d := by
      simpa [s] using card_Icc_filter_coprime_eq_totient d

end PrimitiveRootsMod
