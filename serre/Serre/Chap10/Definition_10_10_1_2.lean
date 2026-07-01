import Mathlib
import Serre.Chap10.Definition_10_10_1_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section Monoid

variable {G : Type u} [Monoid G]

/-- A pair `(x_u, x_r)` is a `p`-component decomposition of `x` if `x_u` has `p`-power order, `x_r`
has order prime to `p`, the factors commute, and their product is `x`. -/
def IsPComponentDecomposition (p : ℕ) (x xu xr : G) : Prop :=
  IsPElement p xu ∧
    IsPRegular p xr ∧
      Commute xu xr ∧ xu * xr = x

namespace IsPComponentDecomposition

variable {p : ℕ} {x xu xr : G}

/-- The left factor in a `p`-component decomposition is a `p`-element. -/
theorem isPElement (h : IsPComponentDecomposition p x xu xr) : IsPElement p xu :=
  h.1

/-- The right factor in a `p`-component decomposition is `p`-regular. -/
theorem isPRegular (h : IsPComponentDecomposition p x xu xr) : IsPRegular p xr :=
  h.2.1

/-- The two factors in a `p`-component decomposition commute. -/
theorem commute (h : IsPComponentDecomposition p x xu xr) : Commute xu xr :=
  h.2.2.1

/-- The product of the two factors in a `p`-component decomposition is the original element. -/
theorem mul_eq (h : IsPComponentDecomposition p x xu xr) : xu * xr = x :=
  h.2.2.2

/-- A `p`-component decomposition rewrites the original element as the product of its two
factors. -/
theorem eq_mul (h : IsPComponentDecomposition p x xu xr) : x = xu * xr :=
  h.mul_eq.symm

/-- A `p`-component decomposition of `x` forces `x` to have finite order. -/
theorem isOfFinOrder [Fact p.Prime] (h : IsPComponentDecomposition p x xu xr) :
    IsOfFinOrder x := by
  have hp : Nat.Prime p := Fact.out
  -- The `p`-unipotent factor has explicit `p`-power order, hence finite order.
  have hxu : IsOfFinOrder xu := by
    rcases h.isPElement with ⟨n, hn⟩
    exact orderOf_ne_zero_iff.mp (by rw [hn]; exact pow_ne_zero n hp.ne_zero)
  -- A `p`-regular factor cannot have order `0`, because that would force `p = 1`.
  have hxr : IsOfFinOrder xr := by
    refine orderOf_ne_zero_iff.mp ?_
    intro hzero
    have hreg : IsPRegular p xr := h.isPRegular
    have hreg' : p = 1 := by
      simpa [IsPRegular, hzero] using hreg
    exact hp.ne_one hreg'
  -- Finite order is closed under multiplying commuting elements.
  rw [← h.mul_eq]
  exact h.commute.isOfFinOrder_mul hxu hxr

end IsPComponentDecomposition

end Monoid

section Group

variable {G : Type u} [Group G]
variable {p : ℕ}

-- Source/core/bridge triage:
-- * source-facing: `IsPComponentDecomposition p x xu xr` and the chosen components
--   `pUnipotentComponent p x`, `pRegularComponent p x`.
-- * core/canonical: `Subgroup.zpowers x`, together with the order-of-element and
--   `Nat.divMaxPow` / `padicValNat` APIs controlling the `p`-part and `p'`-part of `orderOf x`.
-- * bridge/view: the uniqueness lemmas identifying any `p`-component decomposition with the
--   chosen one.

/-- The explicitly chosen `p`-unipotent component of `x`, defined from the `p'`-part of
`orderOf x` and Bézout coefficients for the decomposition of `orderOf x` into its `p`-part and
`p'`-part. -/
noncomputable def pUnipotentComponent (p : ℕ) (x : G) : G :=
  let m := Nat.divMaxPow (orderOf x) p
  let n := p ^ padicValNat p (orderOf x)
  x ^ ((m : ℤ) * Nat.gcdA m n)

/-- The explicitly chosen `p`-regular component of `x`, defined from the `p`-part of `orderOf x`
and Bézout coefficients for the decomposition of `orderOf x` into its `p`-part and `p'`-part. -/
noncomputable def pRegularComponent (p : ℕ) (x : G) : G :=
  let m := Nat.divMaxPow (orderOf x) p
  let n := p ^ padicValNat p (orderOf x)
  x ^ ((n : ℤ) * Nat.gcdB m n)

/-- Helper for Definition 10-10.1-2: in any `p`-component decomposition, the orders of the
two factors are coprime. -/
theorem IsPComponentDecomposition.orders_coprime
    {x xu xr : G} (h : IsPComponentDecomposition p x xu xr) :
    Nat.Coprime (orderOf xu) (orderOf xr) := by
  -- One order is a `p`-power, while the other is prime to `p`.
  rcases h.isPElement with ⟨k, hk⟩
  simpa [hk] using (h.isPRegular.pow_left k)

/-- Helper for Definition 10-10.1-2: the order of the product in a `p`-component decomposition is
the product of the two coprime factor orders. -/
theorem IsPComponentDecomposition.orderOf_eq_mul_orderOf
    {x xu xr : G} (h : IsPComponentDecomposition p x xu xr) :
    orderOf x = orderOf xu * orderOf xr := by
  -- The commuting factors have coprime orders, so the usual multiplicative formula applies.
  calc
    orderOf x = orderOf (xu * xr) := by rw [h.eq_mul]
    _ = orderOf xu * orderOf xr :=
      h.commute.orderOf_mul_eq_mul_orderOf_of_coprime h.orders_coprime

namespace IsPComponentDecomposition

variable {x xu xr : G}

-- Proof sketch: in a finite group with `p` prime, the `p`-power-order factor `xu` and the
-- prime-to-`p` factor `xr` have coprime orders. Since they commute and multiply to `x`, Bézout
-- exponents for `orderOf xu` and `orderOf xr` recover `xu` as a power of `x`.
/-- In a `p`-component decomposition, the `p`-unipotent factor lies in the cyclic subgroup
generated by the original element. -/
theorem left_mem_zpowers (h : IsPComponentDecomposition p x xu xr) :
    xu ∈ Subgroup.zpowers x := by
  -- Raising the decomposition to `orderOf xr` kills the `p'`-part and isolates `xu`.
  have hx : x ^ orderOf xr = xu ^ orderOf xr := by
    calc
      x ^ orderOf xr = (xu * xr) ^ orderOf xr := by rw [h.eq_mul]
      _ = xu ^ orderOf xr * xr ^ orderOf xr := by
        simpa using h.commute.mul_pow (orderOf xr)
      _ = xu ^ orderOf xr := by rw [pow_orderOf_eq_one, mul_one]
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime h.orders_coprime.symm
  refine Subgroup.mem_zpowers_iff.mpr ?_
  refine ⟨(orderOf xr * m : ℤ), ?_⟩
  calc
    x ^ (orderOf xr * m : ℤ) = (x ^ orderOf xr) ^ m := by
      simpa [zpow_natCast] using (zpow_mul x (orderOf xr : ℤ) m)
    _ = (xu ^ orderOf xr) ^ m := by rw [hx]
    _ = xu := by simpa [zpow_natCast] using hm

-- Proof sketch: apply the same coprime-order argument symmetrically to the `p`-regular factor.
/-- In a `p`-component decomposition, the `p`-regular factor lies in the cyclic subgroup
generated by the original element. -/
theorem right_mem_zpowers (h : IsPComponentDecomposition p x xu xr) :
    xr ∈ Subgroup.zpowers x := by
  -- Raising the decomposition to `orderOf xu` kills the `p`-part and isolates `xr`.
  have hx : x ^ orderOf xu = xr ^ orderOf xu := by
    calc
      x ^ orderOf xu = (xu * xr) ^ orderOf xu := by rw [h.eq_mul]
      _ = xu ^ orderOf xu * xr ^ orderOf xu := by
        simpa using h.commute.mul_pow (orderOf xu)
      _ = xr ^ orderOf xu := by rw [pow_orderOf_eq_one, one_mul]
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime h.orders_coprime
  refine Subgroup.mem_zpowers_iff.mpr ?_
  refine ⟨(orderOf xu * m : ℤ), ?_⟩
  calc
    x ^ (orderOf xu * m : ℤ) = (x ^ orderOf xu) ^ m := by
      simpa [zpow_natCast] using (zpow_mul x (orderOf xu : ℤ) m)
    _ = (xr ^ orderOf xu) ^ m := by rw [hx]
    _ = xr := by simpa [zpow_natCast] using hm

end IsPComponentDecomposition

section Prime

variable [Fact p.Prime]

/-- Helper for Definition 10-10.1-2: the order of a finite-order element splits into its
prime-to-`p` part and its `p`-power part. -/
theorem orderOf_divMaxPow_split (x : G) (hx : IsOfFinOrder x) :
    let q := orderOf x
    let m := Nat.divMaxPow q p
    let n := p ^ padicValNat p q
    m * n = q ∧ Nat.Coprime m n := by
  let q := orderOf x
  let m := Nat.divMaxPow q p
  let n := p ^ padicValNat p q
  have hp : Nat.Prime p := Fact.out
  have hq0 : q ≠ 0 := orderOf_ne_zero_iff.mpr hx
  -- `divMaxPow` and `padicValNat` give the canonical factorization of `orderOf x`.
  have hm : m * n = q := by
    simp [m, n, q]
  have hnot : ¬ p ∣ m := by
    simpa [m, q] using Nat.not_dvd_divMaxPow hp.one_lt hq0
  have hcop_pm : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hnot
  have hcop_mn : Nat.Coprime m n := by
    simpa [m, n, q, Nat.coprime_comm] using (hcop_pm.pow_left (padicValNat p q))
  exact ⟨hm, hcop_mn⟩

/-- Helper for Definition 10-10.1-2: if `y^n = 1` and `m,n` are coprime, then the Bézout
exponent built from `m` recovers `y`. -/
theorem zpow_mul_gcdA_eq_self_of_zpow_eq_one {y : G} {m n : ℕ}
    (hcop : Nat.Coprime m n) (hn : y ^ n = 1) :
    y ^ ((m : ℤ) * Nat.gcdA m n) = y := by
  -- The Bézout term involving `n` vanishes because `y ^ n = 1`.
  have hkill : y ^ ((n : ℤ) * Nat.gcdB m n) = 1 := by
    rw [zpow_mul]
    simpa [zpow_natCast] using congrArg (fun t : G => t ^ Nat.gcdB m n) hn
  have key : y ^ ((m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n) = y := by
    simpa [hcop.gcd_eq_one] using
      (congrArg (fun z : ℤ => y ^ z) (Nat.gcd_eq_gcd_ab m n)).symm
  calc
    y ^ ((m : ℤ) * Nat.gcdA m n) =
        y ^ ((m : ℤ) * Nat.gcdA m n) * y ^ ((n : ℤ) * Nat.gcdB m n) := by
          rw [hkill, mul_one]
    _ = y ^ ((m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n) := by
          rw [← zpow_add]
    _ = y := key

/-- Helper for Definition 10-10.1-2: if `y^m = 1` and `m,n` are coprime, then the Bézout
exponent built from `n` recovers `y`. -/
theorem zpow_mul_gcdB_eq_self_of_zpow_eq_one {y : G} {m n : ℕ}
    (hcop : Nat.Coprime m n) (hm : y ^ m = 1) :
    y ^ ((n : ℤ) * Nat.gcdB m n) = y := by
  -- Symmetrically, the Bézout term involving `m` vanishes.
  have hkill : y ^ ((m : ℤ) * Nat.gcdA m n) = 1 := by
    rw [zpow_mul]
    simpa [zpow_natCast] using congrArg (fun t : G => t ^ Nat.gcdA m n) hm
  have key : y ^ ((m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n) = y := by
    simpa [hcop.gcd_eq_one] using
      (congrArg (fun z : ℤ => y ^ z) (Nat.gcd_eq_gcd_ab m n)).symm
  calc
    y ^ ((n : ℤ) * Nat.gcdB m n) =
        y ^ ((m : ℤ) * Nat.gcdA m n) * y ^ ((n : ℤ) * Nat.gcdB m n) := by
          rw [hkill, one_mul]
    _ = y ^ ((m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n) := by
          rw [← zpow_add]
    _ = y := key

-- Proof sketch: write `orderOf x` as the product of its `p`-power part and its prime-to-`p` part
-- using `padicValNat` and `Nat.divMaxPow`. Bézout coefficients for these coprime integers produce
-- commuting powers of `x` whose product is `x`; the order formulas for powers of an element then
-- show one factor is `p`-unipotent and the other is `p`-regular.
/-- Definition 10-10.1-2 (1): the explicitly defined `p`-unipotent and `p`-regular components of
`x` form a `p`-component decomposition of `x` for any finite-order element `x`. -/
theorem p_component_decomposition_exists (x : G) (hx : IsOfFinOrder x) :
    IsPComponentDecomposition p x (pUnipotentComponent p x) (pRegularComponent p x) := by
  let q := orderOf x
  let m := Nat.divMaxPow q p
  let n := p ^ padicValNat p q
  have hp : Nat.Prime p := Fact.out
  have hq0 : q ≠ 0 := orderOf_ne_zero_iff.mpr hx
  have hsplit := orderOf_divMaxPow_split (p := p) x hx
  dsimp [q, m, n] at hsplit
  rcases hsplit with ⟨hmn, hcop⟩
  have hmn' : m * n = q := by
    exact hmn
  have hcop' : Nat.Coprime m n := by
    simpa [q, m, n] using hcop
  have hnot : ¬ p ∣ m := by
    simpa [m, q] using Nat.not_dvd_divMaxPow hp.one_lt hq0
  have hcop_pm : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hnot
  have hn0 : n ≠ 0 := by
    simp [n, hp.ne_zero]
  have hm0 : m ≠ 0 := by
    intro hm
    rw [hm, zero_mul] at hmn'
    exact hq0 hmn'.symm
  have hm_dvd_q : m ∣ q := by
    refine ⟨n, ?_⟩
    exact hmn'.symm
  have hn_dvd_q : n ∣ q := by
    refine ⟨m, ?_⟩
    rw [Nat.mul_comm, hmn']
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The chosen `p`-unipotent component is a power of `x ^ m`, whose order is the `p`-part.
    have hpu_mem : pUnipotentComponent p x ∈ Subgroup.zpowers (x ^ m) := by
      refine Subgroup.mem_zpowers_iff.mpr ⟨Nat.gcdA m n, ?_⟩
      calc
        (x ^ m) ^ Nat.gcdA m n = x ^ ((m : ℤ) * Nat.gcdA m n) := by
          simpa [zpow_natCast] using (zpow_mul x (m : ℤ) (Nat.gcdA m n)).symm
        _ = pUnipotentComponent p x := by
          simp [pUnipotentComponent, m, n, q]
    have horder_pow : orderOf (x ^ m) = n := by
      have hdiv : q / m = n := by
        simpa [hmn'] using (Nat.mul_div_right n (Nat.pos_of_ne_zero hm0))
      calc
        orderOf (x ^ m) = q / m := by
          simpa [q] using (orderOf_pow_of_dvd (x := x) hm0 hm_dvd_q)
        _ = n := hdiv
    have hdvd_pu : orderOf (pUnipotentComponent p x) ∣ n := by
      simpa [horder_pow] using (orderOf_dvd_of_mem_zpowers hpu_mem)
    obtain ⟨k, -, hpk⟩ := (Nat.dvd_prime_pow hp).mp hdvd_pu
    exact ⟨k, hpk⟩
  · -- The chosen `p'`-component is a power of `x ^ n`, whose order is prime to `p`.
    have hpr_mem : pRegularComponent p x ∈ Subgroup.zpowers (x ^ n) := by
      refine Subgroup.mem_zpowers_iff.mpr ⟨Nat.gcdB m n, ?_⟩
      calc
        (x ^ n) ^ Nat.gcdB m n = x ^ ((n : ℤ) * Nat.gcdB m n) := by
          simpa [zpow_natCast] using (zpow_mul x (n : ℤ) (Nat.gcdB m n)).symm
        _ = pRegularComponent p x := by
          simp [pRegularComponent, m, n, q]
    have horder_pow : orderOf (x ^ n) = m := by
      have hdiv : q / n = m := by
        simpa [hmn'] using (Nat.mul_div_left m (Nat.pos_of_ne_zero hn0))
      calc
        orderOf (x ^ n) = q / n := by
          simpa [q] using (orderOf_pow_of_dvd (x := x) hn0 hn_dvd_q)
        _ = m := hdiv
    have hdvd_pr : orderOf (pRegularComponent p x) ∣ m := by
      simpa [horder_pow] using (orderOf_dvd_of_mem_zpowers hpr_mem)
    exact hcop_pm.coprime_dvd_right hdvd_pr
  · -- Both chosen factors are powers of the same element, so they commute.
    exact (Commute.refl x).zpow_zpow _ _
  · -- Bézout coefficients make the two chosen powers multiply back to `x`.
    have hprod : x ^ ((m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n) = x := by
      simpa [hcop'.gcd_eq_one] using
        (congrArg (fun z : ℤ => x ^ z) (Nat.gcd_eq_gcd_ab m n)).symm
    calc
      pUnipotentComponent p x * pRegularComponent p x =
          x ^ ((m : ℤ) * Nat.gcdA m n) * x ^ ((n : ℤ) * Nat.gcdB m n) := by
            simp [pUnipotentComponent, pRegularComponent, m, n, q]
      _ = x ^ ((m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n) := by
            rw [← zpow_add]
      _ = x := hprod

/-- The chosen `p`-unipotent component of a finite-order element is a `p`-element. -/
theorem isPElement_pUnipotentComponent_of_isOfFinOrder (x : G) (hx : IsOfFinOrder x) :
    IsPElement p (pUnipotentComponent p x) := by
  -- This is exactly the left-factor property in the canonical decomposition.
  exact (p_component_decomposition_exists x hx).isPElement

/-- The chosen `p`-unipotent component of an element of a finite group is a `p`-element. -/
theorem isPElement_pUnipotentComponent [Finite G] (x : G) :
    IsPElement p (pUnipotentComponent p x) := by
  -- Finite groups give finite order for every element, so the finite-order result applies.
  exact isPElement_pUnipotentComponent_of_isOfFinOrder x (isOfFinOrder_of_finite x)

/-- The chosen `p`-regular component of a finite-order element is `p`-regular. -/
theorem isPRegular_pRegularComponent_of_isOfFinOrder (x : G) (hx : IsOfFinOrder x) :
    IsPRegular p (pRegularComponent p x) :=
  (p_component_decomposition_exists x hx).isPRegular

/-- The chosen `p`-regular component of an element of a finite group is `p`-regular. -/
theorem isPRegular_pRegularComponent [Finite G] (x : G) :
    IsPRegular p (pRegularComponent p x) :=
  isPRegular_pRegularComponent_of_isOfFinOrder x (isOfFinOrder_of_finite x)

-- Proof sketch: if `x = xu * xr` is any `p`-component decomposition with `xu` a `p`-element and
-- `xr` `p`-regular, then the preceding two lemmas show both factors lie in the cyclic subgroup
-- generated by `x`; uniqueness follows there from the coprime decomposition of `orderOf x`.
/-- Definition 10-10.1-2 (2): any `p`-component decomposition of `x` agrees with the explicitly
defined `p`-unipotent and `p`-regular components. -/
theorem p_component_decomposition_unique (x xu xr : G) (h : IsPComponentDecomposition p x xu xr) :
    xu = pUnipotentComponent p x ∧
      xr = pRegularComponent p x := by
  let q := orderOf x
  let m := Nat.divMaxPow q p
  let n := p ^ padicValNat p q
  have hp : Nat.Prime p := Fact.out
  have hq0 : q ≠ 0 := orderOf_ne_zero_iff.mpr h.isOfFinOrder
  have hsplit := orderOf_divMaxPow_split (p := p) x h.isOfFinOrder
  dsimp [q, m, n] at hsplit
  rcases hsplit with ⟨hmn, hcop⟩
  have hmn' : m * n = q := by
    exact hmn
  have hcop' : Nat.Coprime m n := by
    simpa [q, m, n] using hcop
  -- The two factor orders divide the corresponding split pieces of `orderOf x`.
  have hxu_dvd_q : orderOf xu ∣ q := by
    refine ⟨orderOf xr, ?_⟩
    simpa [q] using h.orderOf_eq_mul_orderOf
  have hxr_dvd_q : orderOf xr ∣ q := by
    refine ⟨orderOf xu, ?_⟩
    simpa [q, Nat.mul_comm] using h.orderOf_eq_mul_orderOf
  rcases h.isPElement with ⟨k, hkxu⟩
  have hk_le : k ≤ padicValNat p q := by
    have hdvd : p ^ k ∣ q := by
      simpa [hkxu] using hxu_dvd_q
    exact (Nat.pow_dvd_iff_le_padicValNat hp.ne_one hq0).mp hdvd
  have hxu_dvd_n : orderOf xu ∣ n := by
    simpa [hkxu, n] using (Nat.pow_dvd_pow p hk_le)
  have hxu_pow : xu ^ n = 1 := (orderOf_dvd_iff_pow_eq_one).mp hxu_dvd_n
  have hcop_xr_n : Nat.Coprime (orderOf xr) n := by
    simpa [n, Nat.coprime_comm] using
      (h.isPRegular.pow_left (padicValNat p q)).symm
  have hxr_dvd_m : orderOf xr ∣ m := by
    have hxr_dvd_mn : orderOf xr ∣ m * n := by
      simpa [q, hmn'] using hxr_dvd_q
    exact hcop_xr_n.dvd_of_dvd_mul_right hxr_dvd_mn
  have hxr_pow : xr ^ m = 1 := (orderOf_dvd_iff_pow_eq_one).mp hxr_dvd_m
  -- Raising the decomposition to `m` or `n` isolates the two factors.
  have hxum : x ^ m = xu ^ m := by
    calc
      x ^ m = (xu * xr) ^ m := by rw [h.eq_mul]
      _ = xu ^ m * xr ^ m := by simpa using h.commute.mul_pow m
      _ = xu ^ m := by rw [hxr_pow, mul_one]
  have hxnr : x ^ n = xr ^ n := by
    calc
      x ^ n = (xu * xr) ^ n := by rw [h.eq_mul]
      _ = xu ^ n * xr ^ n := by simpa using h.commute.mul_pow n
      _ = xr ^ n := by rw [hxu_pow, one_mul]
  constructor
  · -- The Bézout exponent with `m` recovers the `p`-unipotent factor from `x ^ m`.
    calc
      xu = xu ^ ((m : ℤ) * Nat.gcdA m n) := by
        symm
        exact zpow_mul_gcdA_eq_self_of_zpow_eq_one hcop' hxu_pow
      _ = (xu ^ m) ^ Nat.gcdA m n := by
        simpa [zpow_natCast] using (zpow_mul xu (m : ℤ) (Nat.gcdA m n))
      _ = (x ^ m) ^ Nat.gcdA m n := by rw [hxum]
      _ = x ^ ((m : ℤ) * Nat.gcdA m n) := by
        simpa [zpow_natCast] using (zpow_mul x (m : ℤ) (Nat.gcdA m n)).symm
      _ = pUnipotentComponent p x := by
        simp [pUnipotentComponent, m, n, q]
  · -- The symmetric Bézout recovery identifies the `p'`-regular factor.
    calc
      xr = xr ^ ((n : ℤ) * Nat.gcdB m n) := by
        symm
        exact zpow_mul_gcdB_eq_self_of_zpow_eq_one hcop' hxr_pow
      _ = (xr ^ n) ^ Nat.gcdB m n := by
        simpa [zpow_natCast] using (zpow_mul xr (n : ℤ) (Nat.gcdB m n))
      _ = (x ^ n) ^ Nat.gcdB m n := by rw [hxnr]
      _ = x ^ ((n : ℤ) * Nat.gcdB m n) := by
        simpa [zpow_natCast] using (zpow_mul x (n : ℤ) (Nat.gcdB m n)).symm
      _ = pRegularComponent p x := by
        simp [pRegularComponent, m, n, q]

namespace IsPComponentDecomposition

variable {x xu xr : G}

/-- In a `p`-component decomposition, the `p`-unipotent factor is the canonical
`pUnipotentComponent`. -/
theorem eq_pUnipotentComponent (h : IsPComponentDecomposition p x xu xr) :
    xu = pUnipotentComponent p x :=
  (p_component_decomposition_unique x xu xr h).1

/-- In a `p`-component decomposition, the `p`-regular factor is the canonical
`pRegularComponent`. -/
theorem eq_pRegularComponent (h : IsPComponentDecomposition p x xu xr) :
    xr = pRegularComponent p x :=
  (p_component_decomposition_unique x xu xr h).2

end IsPComponentDecomposition

/-- A `p`-regular element is its own canonical `p`-regular component. -/
theorem pRegularComponent_eq_self_of_isPRegular {x : G} (hx : IsPRegular p x) :
    pRegularComponent p x = x := by
  have hdecomp : IsPComponentDecomposition p x 1 x := by
    refine ⟨?_, hx, Commute.one_left _, by simp⟩
    exact ⟨0, by simp⟩
  exact hdecomp.eq_pRegularComponent.symm

end Prime

/-- Conjugation commutes with the canonical `p`-regular component. -/
theorem pRegularComponent_conj {p : ℕ} (x t : G) :
    pRegularComponent p (t * x * t⁻¹) = t * pRegularComponent p x * t⁻¹ := by
  simp [pRegularComponent, conj_zpow, (SemiconjBy.conj_mk t x).orderOf_eq t]

end Group
