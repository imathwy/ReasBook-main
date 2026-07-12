import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Function

universe u

section PowerResidues

/-- Helper for Example 1.1.108: in a finite cyclic commutative group, an element is a `k`-th power
exactly when its `card / gcd(card, k)`-th power is trivial. -/
-- Proof sketch: compare the range of the `k`-th power map with the kernel of the
-- `card / gcd(card, k)`-th power map. In a cyclic finite group these subgroups have the same
-- cardinality, so the obvious inclusion is an equality.
lemma finite_cyclic_exists_pow_eq_iff_pow_card_div_gcd_eq_one
    {G : Type*} [CommGroup G] [Finite G] [IsCyclic G] (a : G) (k : ℕ) :
    (∃ x : G, x ^ k = a) ↔ a ^ (Nat.card G / Nat.gcd (Nat.card G) k) = 1 := by
  classical
  let n := Nat.card G / Nat.gcd (Nat.card G) k
  let R : Subgroup G := (powMonoidHom k).range
  let S : Subgroup G := (powMonoidHom n).ker
  have hRS : R ≤ S := by
    -- Any `k`-th power becomes trivial after the quotient exponent because `Nat.card G ∣ k * n`.
    intro y hy
    rcases hy with ⟨x, rfl⟩
    change (x ^ k) ^ n = 1
    rw [← pow_mul]
    have hdiv : Nat.card G ∣ k * n := by
      have hcard : Nat.card G = Nat.gcd (Nat.card G) k * n := by
        dsimp [n]
        rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left (Nat.card G) k)]
      rw [hcard]
      simpa [Nat.mul_comm] using
        Nat.mul_dvd_mul_right (Nat.gcd_dvd_right (Nat.card G) k) n
    rcases hdiv with ⟨m, hm⟩
    rw [hm, pow_mul, pow_card_eq_one', one_pow]
  have hcardR : Nat.card R = n := by
    -- The cyclic-group range formula gives the exact size of the `k`-th power subgroup.
    dsimp [R, n]
    simpa [Nat.gcd_comm] using (IsCyclic.card_powMonoidHom_range (G := G) k)
  have hndvd : n ∣ Nat.card G := by
    -- The quotient exponent is visibly a divisor of the group cardinality.
    dsimp [n]
    exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (Nat.card G) k)
  have hcardS : Nat.card S = n := by
    -- The kernel size matches the same quotient because `n` divides the group order.
    dsimp [S, n]
    rw [IsCyclic.card_powMonoidHom_ker (G := G), Nat.gcd_eq_right hndvd]
  have hEq : R = S := by
    -- Equal finite-cardinality subgroups with one included in the other must coincide.
    refine Subgroup.eq_of_le_of_card_ge hRS ?_
    rw [hcardS, hcardR]
  constructor
  · rintro ⟨x, rfl⟩
    -- A represented `k`-th power lies in the kernel subgroup, hence satisfies the displayed equation.
    have hxR : x ^ k ∈ R := ⟨x, rfl⟩
    have hxS : x ^ k ∈ S := hRS hxR
    simpa [S, n] using hxS
  · intro ha
    -- Conversely, membership in the kernel subgroup transports across `R = S` to produce a root.
    have hmemS : a ∈ S := by
      simpa [S, n] using ha
    have hmemR : a ∈ R := by
      rw [hEq]
      exact hmemS
    rcases hmemR with ⟨x, hx⟩
    exact ⟨x, hx⟩

/-- Helper for Example 1.1.108: a residue `k`-th root of a class prime to `n` is the same as a
unit-group `k`-th root of the corresponding canonical unit. -/
-- Proof sketch: when `k = 0`, both sides simply say that the target class is `1`. For `k ≠ 0`,
-- any residue root is automatically a unit because its `k`-th power is the unit represented by
-- `a`, so we can package it into `(ZMod n)ˣ` and compare by extensionality.
lemma zmod_residue_root_iff_unit_root_of_isCoprime
    {n k : ℕ} {a : ℤ} (ha : IsCoprime a (n : ℤ)) :
    (∃ x : ZMod n, x ^ k = a) ↔ ∃ u : (ZMod n)ˣ, u ^ k = ZMod.unitOfIsCoprime a ha := by
  by_cases hk : k = 0
  · subst hk
    constructor
    · rintro ⟨x, hx⟩
      -- In the zero-exponent case, the residue equation forces the target class itself to be `1`.
      refine ⟨1, ?_⟩
      apply Units.ext
      simpa [ZMod.coe_unitOfIsCoprime] using hx
    · rintro ⟨u, hu⟩
      -- Project the unit-group equality back to `ZMod n`.
      refine ⟨(u : ZMod n), ?_⟩
      simpa [ZMod.coe_unitOfIsCoprime, Units.val_pow_eq_pow_val] using
        congrArg (fun v : (ZMod n)ˣ ↦ (v : ZMod n)) hu
  · constructor
    · rintro ⟨x, hx⟩
      -- A nontrivial power equal to a unit can only come from a unit.
      have hx_unit : IsUnit (x : ZMod n) := by
        refine (isUnit_pow_iff hk).1 ?_
        rw [hx]
        exact (ZMod.unitOfIsCoprime a ha).isUnit
      refine ⟨hx_unit.unit, ?_⟩
      apply Units.ext
      rwa [ZMod.coe_unitOfIsCoprime, Units.val_pow_eq_pow_val]
    · rintro ⟨u, hu⟩
      -- Conversely, every unit-group root is already a residue-class root.
      refine ⟨(u : ZMod n), ?_⟩
      simpa [ZMod.coe_unitOfIsCoprime, Units.val_pow_eq_pow_val] using
        congrArg (fun v : (ZMod n)ˣ ↦ (v : ZMod n)) hu

/-- Helper for Example 1.1.108: modulo an odd prime power, solvability of `x^k = a` is equivalent
to the standard primitive-root power criterion. -/
-- Proof sketch: view the residue class `a` as a unit in the cyclic group `(ZMod (p^e))ˣ`, apply
-- the finite-cyclic `k`-th power criterion from the previous helper, and then translate the
-- result back to residue classes.
lemma odd_prime_power_exists_pow_eq_iff
    {p k : ℕ} (e : ℕ+) (hp : Nat.Prime p) (hpodd : Odd p) {a : ℤ}
    (ha : IsCoprime a ((p ^ (e : ℕ)) : ℤ)) :
    (∃ x : ZMod (p ^ (e : ℕ)), x ^ k = a) ↔
      (a : ZMod (p ^ (e : ℕ))) ^
          (Nat.totient (p ^ (e : ℕ)) / Nat.gcd k (Nat.totient (p ^ (e : ℕ)))) = 1 := by
  let ua : (ZMod (p ^ (e : ℕ)))ˣ := ZMod.unitOfIsCoprime a ha
  have hp_ne_two : p ≠ 2 := by
    intro htwo
    rw [htwo] at hpodd
    norm_num at hpodd
  let _ : NeZero (p ^ (e : ℕ)) := ⟨pow_ne_zero (e : ℕ) hp.ne_zero⟩
  let _ : Fintype (ZMod (p ^ (e : ℕ)))ˣ := Fintype.ofFinite _
  let _ : IsCyclic (ZMod (p ^ (e : ℕ)))ˣ :=
    ZMod.isCyclic_units_of_prime_pow p hp hp_ne_two (e : ℕ)
  have hcard : Fintype.card (ZMod (p ^ (e : ℕ)))ˣ = Nat.totient (p ^ (e : ℕ)) := by
    rw [ZMod.card_units_eq_totient]
  -- First transport the residue equation to the cyclic unit group.
  rw [zmod_residue_root_iff_unit_root_of_isCoprime (k := k) ha]
  -- Then apply the finite-cyclic `k`-th power criterion to the unit group.
  have hunit :
      (∃ u : (ZMod (p ^ (e : ℕ)))ˣ, u ^ k = ua) ↔
        ua ^ (Nat.totient (p ^ (e : ℕ)) / Nat.gcd k (Nat.totient (p ^ (e : ℕ)))) = 1 :=
    by
      simpa [hcard, Nat.gcd_comm] using
        (finite_cyclic_exists_pow_eq_iff_pow_card_div_gcd_eq_one
          (G := (ZMod (p ^ (e : ℕ)))ˣ) ua k)
  have hval :
      ua ^ (Nat.totient (p ^ (e : ℕ)) / Nat.gcd k (Nat.totient (p ^ (e : ℕ)))) = 1 ↔
        (a : ZMod (p ^ (e : ℕ))) ^
            (Nat.totient (p ^ (e : ℕ)) / Nat.gcd k (Nat.totient (p ^ (e : ℕ)))) = 1 := by
    constructor
    · intro hu
      -- Project the unit-group equation down to the residue ring.
      simpa [ua, ZMod.coe_unitOfIsCoprime, Units.val_pow_eq_pow_val] using
        congrArg (fun v : (ZMod (p ^ (e : ℕ)))ˣ ↦ (v : ZMod (p ^ (e : ℕ)))) hu
    · intro ha'
      -- Equality of units follows from equality of their values in the residue ring.
      apply Units.ext
      simpa [ua, ZMod.coe_unitOfIsCoprime, Units.val_pow_eq_pow_val] using ha'
  exact hunit.trans hval

/-- Helper for Example 1.1.108: the Chinese remainder equivalence transports the polynomial
`X^k - a` from the product modulus to coordinatewise evaluation on the factor moduli. -/
-- Proof sketch: apply `Polynomial.hom_eval₂` to the ring homomorphism underlying
-- `ZMod.prodEquivPi`, then project to each coordinate.
lemma kth_power_prodEquivPi_polynomial_eval
    {ι : Type u} [Fintype ι] (n : ι → ℕ) (P : Polynomial ℤ)
    (hcop : Pairwise (Nat.Coprime on n)) (y : ZMod (∏ i, n i)) :
    ZMod.prodEquivPi n hcop
      (Polynomial.eval y (P.map (Int.castRingHom (ZMod (∏ i, n i))))) =
      fun i ↦
        Polynomial.eval ((ZMod.prodEquivPi n hcop y) i)
          (P.map (Int.castRingHom (ZMod (n i)))) := by
  ext i
  let e : ZMod (∏ i, n i) →+* (j : ι) → ZMod (n j) :=
    (ZMod.prodEquivPi n hcop).toRingHom
  let φ : ((j : ι) → ZMod (n j)) →+* ZMod (n i) :=
    Pi.evalRingHom (fun j ↦ ZMod (n j)) i
  have hcomp :
      (φ.comp e).comp (Int.castRingHom (ZMod (∏ j, n j))) =
        Int.castRingHom (ZMod (n i)) := by
    -- Projecting the coefficient homomorphism is just the usual cast to the `i`-th factor.
    ext x
    simp [e, φ]
  have hh :=
    Polynomial.hom_eval₂ (p := P)
      (f := Int.castRingHom (ZMod (∏ j, n j))) (g := φ.comp e) (x := y)
  change φ (e (Polynomial.eval y (P.map (Int.castRingHom (ZMod (∏ j, n j)))))) = _
  rw [Polynomial.eval_map, Polynomial.eval_map]
  simpa [e, φ] using hh

/-- Helper for Example 1.1.108: a root of `X^k - a` modulo a product of pairwise-coprime moduli
is equivalent to compatible roots modulo each factor. -/
-- Proof sketch: project a root modulo the product to each coordinate with
-- `ZMod.prodEquivPi`, and conversely assemble a family of coordinate roots with its inverse.
lemma kth_power_exists_zmod_root_product_iff_forall_exists_zmod_root_factor
    {ι : Type u} [Fintype ι] (n : ι → ℕ) (P : Polynomial ℤ)
    (hcop : Pairwise (Nat.Coprime on n)) :
    (∃ y : ZMod (∏ i, n i),
      Polynomial.eval y (P.map (Int.castRingHom (ZMod (∏ i, n i)))) = 0) ↔
      ∀ i, ∃ z : ZMod (n i),
        Polynomial.eval z (P.map (Int.castRingHom (ZMod (n i)))) = 0 := by
  constructor
  · rintro ⟨y, hy⟩ i
    -- A root modulo the product projects to a root modulo every factor.
    refine ⟨(ZMod.prodEquivPi n hcop y) i, ?_⟩
    have htransport := congrFun (kth_power_prodEquivPi_polynomial_eval n P hcop y) i
    simpa [hy] using htransport.symm
  · intro h
    choose z hz using h
    let y : ZMod (∏ i, n i) := (ZMod.prodEquivPi n hcop).symm z
    -- The inverse CRT map assembles the chosen factor roots into one root modulo the product.
    refine ⟨y, ?_⟩
    apply (ZMod.prodEquivPi n hcop).injective
    ext i
    have htransport := congrFun (kth_power_prodEquivPi_polynomial_eval n P hcop y) i
    simpa [y, hz i] using htransport

/-- If the exponent is odd, every odd residue class modulo `2^r` has a unique `k`-th root. -/
-- Proof sketch: odd residues modulo `2^r` are exactly the units of `ZMod (2 ^ r)`. Their group
-- has cardinality a power of `2`, so when `k` is odd the `k`-th power map is a bijection by the
-- standard coprime-power automorphism `powCoprime`.
theorem zmod_two_pow_existsUnique_pow_eq_of_odd_exponent
    {r k : ℕ} {a : ℤ} (ha : Odd a) (hk : Odd k) :
    ∃! x : ZMod (2 ^ r), x ^ k = a := by
  have ha_coprime : IsCoprime a ((2 ^ r : ℕ) : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using
      (Odd.coprime_two_right (show Odd a.natAbs by
        rw [← Nat.not_even_iff_odd, Int.natAbs_even, Int.not_even_iff_odd]
        exact ha)).pow_right r
  let ua : (ZMod (2 ^ r))ˣ := ZMod.unitOfIsCoprime a ha_coprime
  let _ : Fintype (ZMod (2 ^ r))ˣ := Fintype.ofFinite _
  have hcard_coprime : Nat.Coprime (Nat.card (ZMod (2 ^ r))ˣ) k := by
    cases r with
    | zero =>
        simp
    | succ r =>
        -- The unit-group cardinality is a power of `2`, hence coprime to the odd exponent `k`.
        rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
          Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos _)]
        simpa [Nat.succ_sub_one] using (Odd.coprime_two_left hk).pow_left r
  let xu : (ZMod (2 ^ r))ˣ := (powCoprime hcard_coprime).symm ua
  have hxpow : xu ^ k = ua := by
    -- The chosen inverse under `powCoprime` is by construction a `k`-th root of `a`.
    simpa [xu] using (powCoprime hcard_coprime).apply_symm_apply ua
  refine ⟨(xu : ZMod (2 ^ r)), ?_, ?_⟩
  · -- Project the unit-group root back to the residue ring.
    simpa [ua, xu, ZMod.coe_unitOfIsCoprime, Units.val_pow_eq_pow_val] using
      congrArg (fun u : (ZMod (2 ^ r))ˣ ↦ (u : ZMod (2 ^ r))) hxpow
  · intro y hy
    have hk0 : k ≠ 0 := by
      intro hkz
      simp [hkz] at hk
    -- Any other root is a unit, so uniqueness reduces to injectivity of `powCoprime`.
    have hy_unit : IsUnit (y : ZMod (2 ^ r)) := by
      refine (isUnit_pow_iff hk0).1 ?_
      rw [hy]
      exact ua.isUnit
    let yu : (ZMod (2 ^ r))ˣ := hy_unit.unit
    have hyu : yu ^ k = ua := by
      apply Units.ext
      rwa [ZMod.coe_unitOfIsCoprime, Units.val_pow_eq_pow_val]
    have hy_eq : yu = xu := by
      apply (powCoprime hcard_coprime).injective
      exact hyu.trans hxpow.symm
    exact Units.ext_iff.mp hy_eq

/-- Helper for Example 1.1.108: every unit modulo `4` is either `1` or `-1`. -/
-- Proof sketch: the only unit residue classes modulo `4` are `1` and `3`, and `3 = -1` in
-- `ZMod 4`.
lemma zmod4_unit_eq_one_or_neg_one (u : (ZMod 4)ˣ) : u = 1 ∨ u = -1 := by
  have hu : ((u : ZMod 4) = 1 ∨ (u : ZMod 4) = 3) := by
    -- A unit in `ZMod 4` cannot have residue `0` or `2`, so only the odd classes remain.
    have h0 : ¬ IsUnit (0 : ZMod 4) := by
      decide
    have h2 : ¬ IsUnit (2 : ZMod 4) := by
      decide
    exact
      (show ∀ y : ZMod 4, IsUnit y → y = 1 ∨ y = 3 from by
        intro y hy
        fin_cases y
        · exact False.elim (h0 hy)
        · exact Or.inl rfl
        · exact False.elim (h2 hy)
        · exact Or.inr rfl) u u.isUnit
  cases hu with
  | inl h =>
      exact Or.inl (Units.ext h)
  | inr h =>
      right
      -- Translate the residue-class description `u = 3` into the unit identity `u = -1`.
      apply Units.ext
      have hneg : ((-1 : (ZMod 4)ˣ) : ZMod 4) = 3 := by
        decide
      exact h.trans hneg.symm

/-- Helper for Example 1.1.108: an even power of a unit modulo `4` is always trivial. -/
-- Proof sketch: by the previous helper, every unit modulo `4` is either `1` or `-1`, and an
-- even exponent kills the sign.
lemma zmod4_unit_pow_even_eq_one (u : (ZMod 4)ˣ) {k : ℕ} (hk : Even k) : u ^ k = 1 := by
  rcases zmod4_unit_eq_one_or_neg_one u with rfl | hu
  · simp
  · -- Once `u = -1`, the even exponent collapses the sign contribution.
    rw [hu, neg_pow]
    rcases hk with ⟨m, rfl⟩
    simp

/-- Helper for Example 1.1.108: for `r ≥ 3`, reduction modulo `4` is trivial exactly on the
cyclic subgroup generated by `5`. -/
-- Proof sketch: the unit `5` reduces to `1` modulo `4`, so its powers lie in the kernel. The
-- kernel and `Subgroup.zpowers 5` have the same finite cardinality `2^(r-2)`, so inclusion is an
-- equality.
lemma zmod_two_pow_unit_mod_four_eq_one_iff_mem_zpowers_five
    {r : ℕ} (hr : 3 ≤ r) (u : (ZMod (2 ^ r))ˣ) :
    let h4 : 4 ∣ 2 ^ r := by
      have h2r : 2 ≤ r := le_trans (by omega : 2 ≤ 3) hr
      have hpow : 2 ^ 2 ∣ 2 ^ r := pow_dvd_pow 2 h2r
      simpa using hpow
    let pi : (ZMod (2 ^ r))ˣ →* (ZMod 4)ˣ := ZMod.unitsMap h4
    let five : (ZMod (2 ^ r))ˣ :=
      ZMod.unitOfCoprime 5 ((show Nat.Coprime 5 2 by decide).pow_right r)
    pi u = 1 ↔ u ∈ Subgroup.zpowers five := by
  dsimp
  have h4 : 4 ∣ 2 ^ r := by
    have h2r : 2 ≤ r := le_trans (by omega : 2 ≤ 3) hr
    have hpow : 2 ^ 2 ∣ 2 ^ r := pow_dvd_pow 2 h2r
    simpa using hpow
  let pi : (ZMod (2 ^ r))ˣ →* (ZMod 4)ˣ := ZMod.unitsMap h4
  let five : (ZMod (2 ^ r))ˣ :=
    ZMod.unitOfCoprime 5 ((show Nat.Coprime 5 2 by decide).pow_right r)
  have hz_le : Subgroup.zpowers five ≤ pi.ker := by
    intro v hv
    -- The generator `5` already lands in the kernel because it is `1 mod 4`.
    have hfive : pi five = 1 := by
      apply Units.ext
      change ((5 : ZMod (2 ^ r)).cast : ZMod 4) = 1
      have hcast : ((5 : ZMod (2 ^ r)).cast : ZMod 4) = (5 : ZMod 4) := by
        simpa using (ZMod.cast_natCast h4 5)
      rw [hcast]
      decide
    rcases hv with ⟨m, rfl⟩
    simpa [MonoidHom.mem_ker, hfive]
  have hcard_z : Nat.card ↥(Subgroup.zpowers five) = 2 ^ (r - 2) := by
    -- The order of `5` modulo `2^r` is exactly `2^(r-2)`.
    rw [Nat.card_zpowers]
    rw [← ZMod.orderOf_five (r - 2), show r - 2 + 2 = r by omega,
      show (5 : ZMod (2 ^ r)) = five by rfl, orderOf_units]
  have hcard_k : Nat.card ↥pi.ker = 2 ^ (r - 2) := by
    have hindex : pi.ker.index = 2 := by
      -- Surjectivity of reduction to `ZMod 4` identifies the quotient with the two-element unit
      -- group modulo `4`.
      rw [Subgroup.index_ker]
      have hrange : pi.range = ⊤ := by
        ext y
        constructor
        · intro hy
          simp
        · intro hy
          rw [MonoidHom.mem_range]
          exact ZMod.unitsMap_surjective h4 y
      rw [hrange]
      simpa using
        (show Nat.card ((ZMod 4)ˣ) = 2 by
          rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
          decide)
    have hfull : Nat.card ((ZMod (2 ^ r))ˣ) = 2 ^ (r - 1) := by
      -- The full unit group has size `φ(2^r) = 2^(r-1)`.
      have hrpos : 0 < r := by
        omega
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime_pow Nat.prime_two hrpos]
      simp
    have hmul := Subgroup.index_mul_card pi.ker
    rw [hindex, hfull] at hmul
    have hpow : 2 ^ (r - 1) = 2 * 2 ^ (r - 2) := by
      rw [show r - 1 = (r - 2) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    rw [hpow] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hmul
  have hker_eq : pi.ker = Subgroup.zpowers five := by
    -- Equal cardinality upgrades the kernel inclusion to an equality of subgroups.
    exact (Subgroup.eq_of_le_of_card_ge hz_le (by rw [hcard_k, hcard_z])).symm
  constructor
  · intro hu1
    have hu_ker : u ∈ pi.ker := by
      simpa [MonoidHom.mem_ker] using hu1
    rw [hker_eq] at hu_ker
    exact hu_ker
  · intro hu
    have hu_ker : u ∈ pi.ker := by
      rw [hker_eq]
      exact hu
    simpa [MonoidHom.mem_ker] using hu_ker

/-- Helper for Example 1.1.108: when `k` is even, a `k`-th root of a unit reducing to `1 mod 4`
may be chosen inside the kernel of reduction modulo `4`. -/
-- Proof sketch: a witness reducing to `-1` can be multiplied by `-1`; evenness of `k` keeps its
-- `k`-th power unchanged while moving the witness into the kernel.
lemma zmod_two_pow_even_unit_root_iff_kernel_root
    {r k : ℕ} (hr : 3 ≤ r) (hk : Even k) {ua : (ZMod (2 ^ r))ˣ} :
    let h4 : 4 ∣ 2 ^ r := by
      have h2r : 2 ≤ r := le_trans (by omega : 2 ≤ 3) hr
      have hpow : 2 ^ 2 ∣ 2 ^ r := pow_dvd_pow 2 h2r
      simpa using hpow
    let pi : (ZMod (2 ^ r))ˣ →* (ZMod 4)ˣ := ZMod.unitsMap h4
    pi ua = 1 →
      ((∃ u : (ZMod (2 ^ r))ˣ, u ^ k = ua) ↔ ∃ v : pi.ker, v.1 ^ k = ua) := by
  dsimp
  intro hua
  have h4 : 4 ∣ 2 ^ r := by
    have h2r : 2 ≤ r := le_trans (by omega : 2 ≤ 3) hr
    have hpow : 2 ^ 2 ∣ 2 ^ r := pow_dvd_pow 2 h2r
    simpa using hpow
  let pi : (ZMod (2 ^ r))ˣ →* (ZMod 4)ˣ := ZMod.unitsMap h4
  constructor
  · rintro ⟨u, hu⟩
    have hcase : pi u = 1 ∨ pi u = -1 := zmod4_unit_eq_one_or_neg_one (pi u)
    cases hcase with
    | inl hu1 =>
        -- If the witness already reduces to `1`, it lives in the kernel as is.
        exact ⟨⟨u, hu1⟩, hu⟩
    | inr hune =>
        -- Otherwise multiply by `-1`; the sign disappears after raising to an even power.
        refine ⟨⟨-u, ?_⟩, ?_⟩
        · apply Units.ext
          have hval : (((pi u : (ZMod 4)ˣ) : ZMod 4)) = (-1 : ZMod 4) := by
            simpa using congrArg (fun x : (ZMod 4)ˣ ↦ (x : ZMod 4)) hune
          have hcast :
              (((pi (-u) : (ZMod 4)ˣ) : ZMod 4)) = -(((pi u : (ZMod 4)ˣ) : ZMod 4)) := by
            change ((-(u : ZMod (2 ^ r))).cast : ZMod 4) = -((u : ZMod (2 ^ r)).cast : ZMod 4)
            simpa using (map_neg (ZMod.castHom h4 (ZMod 4)) (u : ZMod (2 ^ r)))
          rw [hcast, hval]
          decide
        · rw [neg_pow]
          rcases hk with ⟨m, rfl⟩
          simp [hu]
  · rintro ⟨v, hv⟩
    -- A kernel witness is already a witness in the full unit group.
    exact ⟨v.1, hv⟩

/-- If the exponent is even and `2 ≤ r`, solvability of `x^k = a` modulo `2^r` is equivalent to
the standard congruence conditions on the odd residue `a`. -/
-- Route correction: the intended proof has to follow the source decomposition of
-- `(ZMod (2 ^ r))ˣ` into the mod-`4` sign part and the kernel generated by `5`, not just a
-- cardinality argument.
theorem zmod_two_pow_exists_pow_eq_iff_of_even_exponent
    {r k : ℕ} (hr : 2 ≤ r) {a : ℤ} (ha : Odd a) (hk : Even k) :
    (∃ x : ZMod (2 ^ r), x ^ k = a) ↔
      (a : ZMod 4) = 1 ∧
        (a : ZMod (2 ^ r)) ^ (2 ^ (r - 2) / Nat.gcd (2 ^ (r - 2)) k) = 1 := by
  have ha_coprime : IsCoprime a ((2 ^ r : ℕ) : ℤ) := by
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using
      (Odd.coprime_two_right (show Odd a.natAbs by
        rw [← Nat.not_even_iff_odd, Int.natAbs_even, Int.not_even_iff_odd]
        exact ha)).pow_right r
  let ua : (ZMod (2 ^ r))ˣ := ZMod.unitOfIsCoprime a ha_coprime
  -- First transport the residue equation to the unit group of odd classes.
  rw [zmod_residue_root_iff_unit_root_of_isCoprime (k := k) ha_coprime]
  by_cases hr3 : 3 ≤ r
  · have h4 : 4 ∣ 2 ^ r := by
      have hpow : 2 ^ 2 ∣ 2 ^ r := pow_dvd_pow 2 hr
      simpa using hpow
    let pi : (ZMod (2 ^ r))ˣ →* (ZMod 4)ˣ := ZMod.unitsMap h4
    let five : (ZMod (2 ^ r))ˣ :=
      ZMod.unitOfCoprime 5 ((show Nat.Coprime 5 2 by decide).pow_right r)
    have hua_mod4 : pi ua = 1 ↔ (a : ZMod 4) = 1 := by
      have hcast_a : ((a : ZMod (2 ^ r)).cast : ZMod 4) = (a : ZMod 4) := by
        simpa using (ZMod.cast_intCast h4 a)
      constructor
      · intro hua1
        -- Reduction of the canonical unit is exactly the residue class of `a` modulo `4`.
        simpa [pi, ua, ZMod.unitsMap_val, ZMod.coe_unitOfIsCoprime, hcast_a] using
          congrArg (fun x : (ZMod 4)ˣ ↦ (x : ZMod 4)) hua1
      · intro ha4
        -- Conversely, the residue-class condition lifts back to the unit reduction statement.
        apply Units.ext
        simpa [pi, ua, ZMod.unitsMap_val, ZMod.coe_unitOfIsCoprime, hcast_a] using ha4
    have hcard_z : Nat.card ↥(Subgroup.zpowers five) = 2 ^ (r - 2) := by
      -- The cyclic kernel has order `2^(r-2)` because it is generated by `5`.
      rw [Nat.card_zpowers]
      rw [← ZMod.orderOf_five (r - 2), show r - 2 + 2 = r by omega,
        show (5 : ZMod (2 ^ r)) = five by rfl, orderOf_units]
    have hcard_z' : Fintype.card (Subgroup.zpowers five) = 2 ^ (r - 2) := by
      simpa [Nat.card_eq_fintype_card] using hcard_z
    constructor
    · intro hroot
      -- Any root forces the mod-`4` sign part to vanish because the exponent is even.
      have hua1 : pi ua = 1 := by
        rcases hroot with ⟨u, hu⟩
        calc
          pi ua = pi (u ^ k) := by rw [hu]
          _ = (pi u) ^ k := by simp
          _ = 1 := zmod4_unit_pow_even_eq_one (pi u) hk
      have hua_mem : ua ∈ Subgroup.zpowers five := by
        exact (zmod_two_pow_unit_mod_four_eq_one_iff_mem_zpowers_five hr3 ua).1 hua1
      let uaz : Subgroup.zpowers five := ⟨ua, hua_mem⟩
      -- Move the root into the kernel, then into the cyclic subgroup generated by `5`.
      have hroot_kernel : ∃ v : pi.ker, v.1 ^ k = ua := by
        exact (zmod_two_pow_even_unit_root_iff_kernel_root hr3 hk (ua := ua) hua1).1 hroot
      have hroot_zpow : ∃ w : Subgroup.zpowers five, w ^ k = uaz := by
        rcases hroot_kernel with ⟨v, hv⟩
        refine ⟨⟨v.1, ?_⟩, ?_⟩
        · exact (zmod_two_pow_unit_mod_four_eq_one_iff_mem_zpowers_five hr3 v.1).1 v.2
        · apply Subtype.ext
          simpa [uaz] using hv
      -- The cyclic-group criterion now produces the required exponent test.
      have huaz_pow :
          uaz ^ (2 ^ (r - 2) / Nat.gcd (2 ^ (r - 2)) k) = 1 := by
        have huaz_pow' :=
          (finite_cyclic_exists_pow_eq_iff_pow_card_div_gcd_eq_one
            (G := Subgroup.zpowers five) uaz k).1 hroot_zpow
        simpa [Nat.card_eq_fintype_card, hcard_z'] using huaz_pow'
      refine ⟨hua_mod4.mp hua1, ?_⟩
      -- Finally project the subgroup equation back to the residue ring.
      simpa [uaz, ua, ZMod.coe_unitOfIsCoprime, Units.val_pow_eq_pow_val] using
        congrArg
          (fun x : Subgroup.zpowers five ↦ ((x : (ZMod (2 ^ r))ˣ) : ZMod (2 ^ r)))
          huaz_pow
    · rintro ⟨ha4, haPow⟩
      have hua1 : pi ua = 1 := hua_mod4.mpr ha4
      have hua_mem : ua ∈ Subgroup.zpowers five := by
        exact (zmod_two_pow_unit_mod_four_eq_one_iff_mem_zpowers_five hr3 ua).1 hua1
      let uaz : Subgroup.zpowers five := ⟨ua, hua_mem⟩
      -- Promote the residue-level exponent condition to the cyclic subgroup generated by `5`.
      have huaz_pow :
          uaz ^ (2 ^ (r - 2) / Nat.gcd (2 ^ (r - 2)) k) = 1 := by
        apply Subtype.ext
        apply Units.ext
        simpa [uaz, ua, ZMod.coe_unitOfIsCoprime, Units.val_pow_eq_pow_val] using haPow
      have hroot_zpow : ∃ w : Subgroup.zpowers five, w ^ k = uaz := by
        have huaz_pow' :
            uaz ^ (Nat.card (Subgroup.zpowers five) / Nat.gcd (Nat.card (Subgroup.zpowers five)) k) =
              1 := by
          simpa [Nat.card_eq_fintype_card, hcard_z'] using huaz_pow
        exact
          (finite_cyclic_exists_pow_eq_iff_pow_card_div_gcd_eq_one
            (G := Subgroup.zpowers five) uaz k).2 huaz_pow'
      have hroot_kernel : ∃ v : pi.ker, v.1 ^ k = ua := by
        rcases hroot_zpow with ⟨w, hw⟩
        refine ⟨⟨w.1, ?_⟩, ?_⟩
        · exact (zmod_two_pow_unit_mod_four_eq_one_iff_mem_zpowers_five hr3 w.1).2 w.2
        · simpa [uaz] using congrArg Subtype.val hw
      -- The kernel witness lifts back to a unit-group witness, hence to a residue-class root.
      exact (zmod_two_pow_even_unit_root_iff_kernel_root hr3 hk (ua := ua) hua1).2 hroot_kernel
  · have hr_eq : r = 2 := by
      omega
    subst r
    constructor
    · rintro ⟨u, hu⟩
      -- In `(ZMod 4)ˣ`, every even power is `1`, so the target residue must already be `1`.
      have hua1 : ua = 1 := hu.symm.trans (zmod4_unit_pow_even_eq_one u hk)
      have ha1 : (a : ZMod 4) = 1 := by
        simpa [ua, ZMod.coe_unitOfIsCoprime] using
          congrArg (fun x : (ZMod 4)ˣ ↦ (x : ZMod 4)) hua1
      simpa [ha1]
    · rintro ⟨ha1, _⟩
      -- Once `a = 1 mod 4`, the trivial unit gives the required root.
      refine ⟨1, ?_⟩
      apply Units.ext
      simpa [ua, ZMod.coe_unitOfIsCoprime, ha1] using ha1

/-- Example 1.1.108: for the modulus `2^r ∏ p_i^{e_i}`, an integer `a` coprime to
that modulus is a `k`-th power residue exactly when it is a `k`-th power residue modulo `2^r`
and, for every odd prime-power factor `p_i^{e_i}`, its image in `ZMod (p_i ^ e_i)` satisfies the
usual primitive-root criterion `a^(φ(p_i^e_i) / gcd(k, φ(p_i^e_i))) = 1`. -/
-- Proof sketch: encode `x^k = a` as the polynomial equation `X^k - a = 0`, apply the chapter CRT
-- theorem for polynomial congruences across the factors `2^r` and `p_i^{e_i}`, and then convert
-- each odd-prime-power factor by the unit-group criterion above.
theorem kth_power_congruence_mod_factored_modulus_iff
    {ι : Type u} [Fintype ι] (p : ι → ℕ) (e : ι → ℕ+) {r k : ℕ}
    (hp : ∀ i, Nat.Prime (p i)) (hoddp : ∀ i, Odd (p i))
    (hpair : Pairwise fun i j ↦ p i ≠ p j) {a : ℤ}
    (ha : IsCoprime a ((2 ^ r * ∏ i, p i ^ (e i : ℕ)) : ℤ)) :
    (∃ x : ZMod (2 ^ r * ∏ i, p i ^ (e i : ℕ)), x ^ k = a) ↔
      (∃ x₂ : ZMod (2 ^ r), x₂ ^ k = a) ∧
        ∀ i,
          (a : ZMod (p i ^ (e i : ℕ))) ^
              (Nat.totient (p i ^ (e i : ℕ)) /
                Nat.gcd k (Nat.totient (p i ^ (e i : ℕ)))) =
            1 := by
  let n : Option ι → ℕ := fun
    | none => 2 ^ r
    | some i => p i ^ (e i : ℕ)
  let P : Polynomial ℤ := Polynomial.X ^ k - Polynomial.C a
  have hcop : Pairwise (Nat.Coprime on n) := by
    intro i j hij
    cases i with
    | none =>
        cases j with
        | none =>
            cases hij rfl
        | some j =>
            -- The even factor is coprime to every odd prime-power factor.
            have h2p : Nat.Coprime 2 (p j) := by
              simpa [Nat.coprime_comm] using (hoddp j).coprime_two_right
            simpa [n] using (h2p.pow_left r).pow_right (e j : ℕ)
    | some i =>
        cases j with
        | none =>
            -- Coprimality is symmetric, so the reverse mixed case is identical.
            have h2p : Nat.Coprime 2 (p i) := by
              simpa [Nat.coprime_comm] using (hoddp i).coprime_two_right
            simpa [n, Nat.coprime_comm] using (h2p.pow_left r).pow_right (e i : ℕ)
        | some j =>
            -- Distinct odd primes give coprime prime powers.
            have hpij : Nat.Coprime (p i) (p j) := by
              refine (hp i).coprime_iff_not_dvd.2 ?_
              intro hdiv
              have hij' : i ≠ j := by
                intro hij_eq
                exact hij (by cases hij_eq; rfl)
              have hp_eq : p i = p j := by
                symm
                exact ((hp j).dvd_iff_eq (Nat.Prime.ne_one (hp i))).mp hdiv
              exact hpair hij' hp_eq
            simpa [n] using (hpij.pow_left (e i : ℕ)).pow_right (e j : ℕ)
  have hprod : (∏ o, n o) = 2 ^ r * ∏ i, p i ^ (e i : ℕ) := by
    rw [Fintype.prod_option]
  have hsplit :
      (∃ x : ZMod (2 ^ r * ∏ i, p i ^ (e i : ℕ)), x ^ k = a) ↔
        ∀ o : Option ι, ∃ z : ZMod (n o), z ^ k = a := by
    -- Encode `x ^ k = a` as the root condition for `X^k - a` and split it by CRT.
    have hsplit' :=
      kth_power_exists_zmod_root_product_iff_forall_exists_zmod_root_factor n P hcop
    rw [hprod] at hsplit'
    simpa [n, P, sub_eq_zero] using hsplit'
  rw [hsplit]
  constructor
  · intro h
    constructor
    · -- The `none` coordinate is exactly the `2 ^ r` congruence.
      simpa [n, P] using h none
    · intro i
      -- Each odd prime-power coordinate is converted by the local unit-group criterion.
      have ha_factor : IsCoprime a ((p i ^ (e i : ℕ)) : ℤ) := by
        refine ha.of_isCoprime_of_dvd_right ?_
        have hdiv_nat : p i ^ (e i : ℕ) ∣ ∏ j, p j ^ (e j : ℕ) := by
          exact Finset.dvd_prod_of_mem (fun j ↦ p j ^ (e j : ℕ)) (Finset.mem_univ i)
        have hdiv_nat' : p i ^ (e i : ℕ) ∣ 2 ^ r * ∏ j, p j ^ (e j : ℕ) := by
          exact dvd_mul_of_dvd_right hdiv_nat (2 ^ r)
        exact_mod_cast hdiv_nat'
      have hroot_i : ∃ z : ZMod (p i ^ (e i : ℕ)), z ^ k = a := by
        simpa [n, P] using h (some i)
      exact (odd_prime_power_exists_pow_eq_iff (e := e i) (k := k) (hp i) (hoddp i) ha_factor).mp
        hroot_i
  · rintro ⟨h₂, hodd⟩ o
    cases o with
    | none =>
        -- Reassemble the `2 ^ r` coordinate directly.
        simpa [n, P] using h₂
    | some i =>
        -- Reassemble each odd prime-power coordinate from the solved local criterion.
        have ha_factor : IsCoprime a ((p i ^ (e i : ℕ)) : ℤ) := by
          refine ha.of_isCoprime_of_dvd_right ?_
          have hdiv_nat : p i ^ (e i : ℕ) ∣ ∏ j, p j ^ (e j : ℕ) := by
            exact Finset.dvd_prod_of_mem (fun j ↦ p j ^ (e j : ℕ)) (Finset.mem_univ i)
          have hdiv_nat' : p i ^ (e i : ℕ) ∣ 2 ^ r * ∏ j, p j ^ (e j : ℕ) := by
            exact dvd_mul_of_dvd_right hdiv_nat (2 ^ r)
          exact_mod_cast hdiv_nat'
        have hroot_i : ∃ z : ZMod (p i ^ (e i : ℕ)), z ^ k = a := by
          exact
            (odd_prime_power_exists_pow_eq_iff (e := e i) (k := k) (hp i) (hoddp i)
              ha_factor).mpr (hodd i)
        simpa [n, P] using hroot_i

end PowerResidues
