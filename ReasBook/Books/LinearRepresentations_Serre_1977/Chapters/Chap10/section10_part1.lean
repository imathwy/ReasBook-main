import Mathlib
import Mathlib.Data.ZMod.QuotientRing

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_10_1_1 (from Chap10) -/
universe u

-- Source/core/bridge triage:
-- * source-facing: `IsPElement` and `IsPRegular` are the textbook order-theoretic predicates on
--   individual elements.
-- * core/canonical: `IsPGroup p G` and, in the commutative setting, `CommGroup.primaryComponent`.
-- * bridge/view: the comparison lemmas below connect the source-facing elementwise predicates to
--   those owner-level declarations.

section Monoid

variable {G : Type u} [Monoid G]

/-- Definition 10-10.1-1 (1): an element `x` is a `p`-element, or `p`-unipotent, if its order is
a power of `p`. -/
abbrev IsPElement (p : ℕ) (x : G) : Prop :=
  ∃ n : ℕ, orderOf x = p ^ n

/-- Definition 10-10.1-1 (2): an element `x` is a `p'`-element, or `p`-regular, if its order is
prime to `p`. -/
abbrev IsPRegular (p : ℕ) (x : G) : Prop :=
  Nat.Coprime p (orderOf x)

section Prime

variable {p : ℕ} [Fact p.Prime]

/-- For prime `p`, the source-facing `p`-element predicate matches mathlib's canonical
prime-power torsion criterion. -/
theorem isPElement_iff_exists_pow_eq_one (x : G) :
    IsPElement p x ↔ ∃ n : ℕ, x ^ p ^ n = 1 := by
  simpa [IsPElement] using
    (exists_orderOf_eq_prime_pow_iff :
      (∃ n : ℕ, orderOf x = p ^ n) ↔ ∃ n : ℕ, x ^ p ^ n = 1)

/-- An element is `p`-regular exactly when `p` does not divide its order. -/
theorem isPRegular_iff_not_dvd_orderOf (x : G) :
    IsPRegular p x ↔ ¬ p ∣ orderOf x := by
  simpa [IsPRegular] using
    ((Fact.out : Nat.Prime p).coprime_iff_not_dvd :
      Nat.Coprime p (orderOf x) ↔ ¬ p ∣ orderOf x)

end Prime

/-- The identity element is `p`-regular. -/
theorem isPRegular_one (p : ℕ) : IsPRegular p (1 : G) := by
  simp [IsPRegular]

end Monoid

section GroupRegular

variable {G : Type u} [Group G]

/-- Conjugation preserves `p`-regularity. -/
theorem isPRegular_conj (p : ℕ) (s t : G) (hs : IsPRegular p s) :
    IsPRegular p (t * s * t⁻¹) := by
  rw [IsPRegular, ← (SemiconjBy.conj_mk t s).orderOf_eq t]
  exact hs

end GroupRegular

section CommGroup

variable {G : Type u} [CommGroup G] {p : ℕ} [Fact p.Prime]

open CommGroup

/-- In the commutative setting, `p`-elements are exactly the elements of the canonical owner
`primaryComponent G p`. -/
theorem isPElement_iff_mem_primaryComponent (x : G) :
    IsPElement p x ↔ x ∈ primaryComponent G p :=
  Iff.rfl

end CommGroup

section Group

variable {G : Type u} [Group G] {p : ℕ}

/- Definition 10-10.1-1 (3) reuses the canonical owner `IsPGroup p G` already fixed in
Definition 8-8.3-4. -/
recall IsPGroup

section Prime

variable [Fact p.Prime]

/-- Companion source-facing characterization: a group is a `p`-group exactly when each of its
elements is a `p`-element. -/
theorem isPGroup_iff_forall_isPElement :
    IsPGroup p G ↔ ∀ x : G, IsPElement p x := by
  simpa [IsPElement] using
    (IsPGroup.iff_orderOf : IsPGroup p G ↔ ∀ g : G, ∃ k, orderOf g = p ^ k)

end Prime

end Group

/-! ### Definition_10_10_1_2 (from Chap10) -/
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

/-! ### Definition_10_10_1_3 (from Chap10) -/
universe u

section Group

open Subgroup

variable {H : Type u} [Group H]

-- Source/core/bridge triage:
-- * source-facing: `IsPElementaryDecomposition p C P`, `IsPElementary p H`, and `IsElementary H`.
-- * core/canonical: `IsPGroup`, `Subgroup.IsComplement'`, and `Subgroup.centralizer`.
-- * bridge/view: `Subgroup.IsComplement'.prodMulEquiv` identifies complementary commuting factors
--   with a direct product.
--
-- Primitive data are the cyclic prime-to-`p` factor `C`, the finite `p`-group factor `P`, their
-- centralizing relation, and their complement decomposition. Finiteness of `C`, commutation of
-- individual elements, and finiteness of the ambient group are derived API.

/-- A pair of subgroups `C` and `P` gives a `p`-elementary decomposition of `H` if `p` is prime,
`C` is a finite cyclic group of order prime to `p`, `P` is a finite `p`-group, `C` centralizes
`P`, and every element of `H` admits a unique factorization as an element of `C` times an element
of `P`. -/
def IsPElementaryDecomposition (p : ℕ) (C P : Subgroup H) : Prop :=
  Nat.Prime p ∧
    Finite P ∧
      IsCyclic C ∧
        Nat.Coprime p (Nat.card C) ∧
          IsPGroup p P ∧
            C ≤ centralizer (P : Set H) ∧
              C.IsComplement' P

namespace IsPElementaryDecomposition

variable {p : ℕ} {C P : Subgroup H}

/-- The prime attached to a `p`-elementary decomposition. -/
theorem prime (h : IsPElementaryDecomposition p C P) : Nat.Prime p := by
  rcases h with ⟨hp, -, -, -, -, -, -⟩
  exact hp

/-- The cyclic factor in a `p`-elementary decomposition is finite. -/
theorem finite_cyclic_factor (h : IsPElementaryDecomposition p C P) : Finite C := by
  rcases h with ⟨hp, -, -, hcoprime, -, -, -⟩
  by_contra hC
  haveI : Infinite C := not_finite_iff_infinite.mp hC
  have hc : Nat.Coprime p 0 := by
    simpa [Nat.card_eq_zero_of_infinite] using hcoprime
  rw [Nat.coprime_zero_right] at hc
  exact hp.ne_one hc

/-- The `p`-group factor in a `p`-elementary decomposition is finite. -/
theorem finite_pGroup_factor (h : IsPElementaryDecomposition p C P) : Finite P := by
  rcases h with ⟨-, hP, -, -, -, -, -⟩
  exact hP

/-- The cyclic factor in a `p`-elementary decomposition. -/
theorem cyclic (h : IsPElementaryDecomposition p C P) : IsCyclic C := by
  rcases h with ⟨-, -, hC, -, -, -, -⟩
  exact hC

/-- The cyclic factor has order prime to `p`. -/
theorem coprime_card (h : IsPElementaryDecomposition p C P) :
    Nat.Coprime p (Nat.card C) := by
  rcases h with ⟨-, -, -, hcoprime, -, -, -⟩
  exact hcoprime

/-- The second factor is a `p`-group. -/
theorem isPGroup (h : IsPElementaryDecomposition p C P) : IsPGroup p P := by
  rcases h with ⟨-, -, -, -, hP, -, -⟩
  exact hP

/-- The cyclic factor centralizes the `p`-group factor. -/
theorem centralizes (h : IsPElementaryDecomposition p C P) :
    C ≤ centralizer (P : Set H) := by
  rcases h with ⟨-, -, -, -, -, hcentral, -⟩
  exact hcentral

/-- The two factors are complementary subgroups of `H`. -/
theorem isComplement (h : IsPElementaryDecomposition p C P) : C.IsComplement' P := by
  rcases h with ⟨-, -, -, -, -, -, hcomp⟩
  exact hcomp

/-- Elements of the two factors commute. -/
theorem commute (h : IsPElementaryDecomposition p C P) (c : C) (u : P) :
    Commute (c : H) (u : H) := by
  change (c : H) * (u : H) = (u : H) * (c : H)
  exact (h.centralizes c.2 u.1 u.2).symm

/-- A `p`-elementary decomposition has finite ambient group. -/
theorem finite (h : IsPElementaryDecomposition p C P) : Finite H := by
  letI : Finite C := h.finite_cyclic_factor
  letI : Finite P := h.finite_pGroup_factor
  exact Finite.of_equiv (C × P) (h.isComplement.prodMulEquiv h.commute).toEquiv

end IsPElementaryDecomposition

/-- Definition 10-10.1-3: a group `H` is `p`-elementary if `p` is prime and `H` admits finite
complementary subgroups `C` and `P`, with `C` cyclic of order prime to `p`, `P` a `p`-group, and
`C` centralizing `P`. -/
def IsPElementary (p : ℕ) (H : Type u) [Group H] : Prop :=
  ∃ C P : Subgroup H, IsPElementaryDecomposition p C P

/-- A group is elementary if it is `p`-elementary for some `p`. -/
def IsElementary (H : Type u) [Group H] : Prop :=
  ∃ p : ℕ, IsPElementary p H

-- Proof sketch: this is the direct elimination of the existential definition of
-- `IsPElementary`.
theorem IsPElementary.prime {p : ℕ} (hH : IsPElementary p H) : Nat.Prime p := by
  rcases hH with ⟨C, P, h⟩
  exact h.prime

/-- A `p`-elementary group is finite. -/
theorem IsPElementary.finite {p : ℕ} (hH : IsPElementary p H) : Finite H := by
  rcases hH with ⟨C, P, h⟩
  exact h.finite

section

variable {p : ℕ}

-- Proof sketch: choose a `p`-elementary decomposition `H ≃ C × P`; the cyclic factor is abelian
-- and hence nilpotent, the `p`-group factor is nilpotent by `IsPGroup.isNilpotent`, and the
-- products and isomorphic images of nilpotent groups are nilpotent.
/-- A `p`-elementary group is nilpotent. -/
theorem IsPElementary.isNilpotent (hH : IsPElementary p H) :
    Group.IsNilpotent H := by
  rcases hH with ⟨C, P, h⟩
  letI : Fact p.Prime := ⟨h.prime⟩
  letI : Finite P := h.finite_pGroup_factor
  letI : Group.IsNilpotent P := h.isPGroup.isNilpotent
  letI : IsCyclic C := h.cyclic
  let _ : CommGroup C := IsCyclic.commGroup
  exact (Group.isNilpotent_congr (h.isComplement.prodMulEquiv h.commute)).1 inferInstance

variable {C P : Subgroup H}

/-- Helper for Definition 10-10.1-3: the coordinates of `x` under the complementary product
equivalence multiply back to `x`. -/
theorem IsPElementaryDecomposition.symm_apply_eq_mul_coords
    (h : IsPElementaryDecomposition p C P) (x : H) :
    let e := h.isComplement.prodMulEquiv h.commute
    ((e.symm x).1 : H) * ((e.symm x).2 : H) = x := by
  let e := h.isComplement.prodMulEquiv h.commute
  -- Unfold the product equivalence only at the final multiplication formula.
  change e (e.symm x) = x
  exact e.apply_symm_apply x

/-- Helper for Definition 10-10.1-3: the subgroup coordinates of `x` form its `p`-component
decomposition. -/
theorem IsPElementaryDecomposition.symm_isPComponentDecomposition
    (h : IsPElementaryDecomposition p C P) (x : H) :
    let e := h.isComplement.prodMulEquiv h.commute
    IsPComponentDecomposition p x ((e.symm x).2 : H) ((e.symm x).1 : H) := by
  letI : Fact p.Prime := ⟨h.prime⟩
  let e := h.isComplement.prodMulEquiv h.commute
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The `P`-coordinate has `p`-power order because `P` is a `p`-group.
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp h.isPGroup) ((e.symm x).2)
    exact ⟨n, by simpa [Subgroup.orderOf_mk] using hn⟩
  · -- The `C`-coordinate has order dividing the prime-to-`p` order of `C`.
    have hdiv : orderOf (((e.symm x).1 : H)) ∣ Nat.card C := by
      simpa using C.orderOf_dvd_natCard ((e.symm x).1).2
    exact h.coprime_card.of_dvd_right hdiv
  · -- Coordinates commute because every element of `C` centralizes every element of `P`.
    exact (h.commute ((e.symm x).1) ((e.symm x).2)).symm
  · -- The product equivalence reconstructs `x`, and commutation swaps the factor order.
    calc
      ((e.symm x).2 : H) * ((e.symm x).1 : H) = ((e.symm x).1 : H) * ((e.symm x).2 : H) := by
        exact (h.commute ((e.symm x).1) ((e.symm x).2)).symm
      _ = x := by
        simpa [e] using h.symm_apply_eq_mul_coords x

/-- Helper for Definition 10-10.1-3: a `p`-regular element has trivial `P`-coordinate in the
canonical `C × P` decomposition. -/
theorem IsPElementaryDecomposition.right_coord_eq_one_of_isPRegular
    (h : IsPElementaryDecomposition p C P) {x : H} (hx : IsPRegular p x) :
    let e := h.isComplement.prodMulEquiv h.commute
    ((e.symm x).2 : H) = 1 := by
  letI : Fact p.Prime := ⟨h.prime⟩
  let e := h.isComplement.prodMulEquiv h.commute
  have hcoords : IsPComponentDecomposition p x ((e.symm x).2 : H) ((e.symm x).1 : H) := by
    simpa [e] using h.symm_isPComponentDecomposition x
  have htriv : IsPComponentDecomposition p x 1 x := by
    -- The trivial decomposition of a `p`-regular element has vanishing `p`-part.
    refine ⟨?_, hx, Commute.one_left _, by simp⟩
    exact ⟨0, by simp⟩
  -- Uniqueness of `p`-component decompositions identifies the `P`-coordinate with `1`.
  exact hcoords.eq_pUnipotentComponent.trans htriv.eq_pUnipotentComponent.symm

/-- Helper for Definition 10-10.1-3: a `p`-element has trivial `C`-coordinate in the canonical
`C × P` decomposition. -/
theorem IsPElementaryDecomposition.left_coord_eq_one_of_isPElement
    (h : IsPElementaryDecomposition p C P) {x : H} (hx : IsPElement p x) :
    let e := h.isComplement.prodMulEquiv h.commute
    ((e.symm x).1 : H) = 1 := by
  letI : Fact p.Prime := ⟨h.prime⟩
  let e := h.isComplement.prodMulEquiv h.commute
  have hcoords : IsPComponentDecomposition p x ((e.symm x).2 : H) ((e.symm x).1 : H) := by
    simpa [e] using h.symm_isPComponentDecomposition x
  have htriv : IsPComponentDecomposition p x x 1 := by
    -- The trivial decomposition of a `p`-element has vanishing prime-to-`p` part.
    refine ⟨hx, isPRegular_one p, Commute.one_right _, by simp⟩
  -- Uniqueness of `p`-component decompositions identifies the `C`-coordinate with `1`.
  exact hcoords.eq_pRegularComponent.trans htriv.eq_pRegularComponent.symm

-- Proof sketch: in a `p`-elementary decomposition, every element factors uniquely as `c * u`
-- with `c ∈ C` and `u ∈ P`. The order of `c` is prime to `p`, the order of `u` is a power of `p`,
-- and the factors commute, so the `p'`-elements are exactly the elements of `C`.
/-- In a `p`-elementary decomposition, the cyclic factor is exactly the set of `p`-regular
elements. -/
theorem IsPElementaryDecomposition.cyclic_factor_eq_setOf_isPRegular
    (h : IsPElementaryDecomposition p C P) :
    (C : Set H) = {x | IsPRegular p x} := by
  ext x
  constructor
  · intro hx
    -- Membership in `C` forces the order of `x` to divide the prime-to-`p` order of `C`.
    have hdiv : orderOf x ∣ Nat.card C := C.orderOf_dvd_natCard hx
    exact h.coprime_card.of_dvd_right hdiv
  · intro hx
    let e := h.isComplement.prodMulEquiv h.commute
    have hright : ((e.symm x).2 : H) = 1 := by
      simpa [e] using h.right_coord_eq_one_of_isPRegular hx
    -- Route correction: rather than doing fresh order arithmetic in `H`, collapse the `P`
    -- coordinate to `1` and read `x` off from the remaining `C`-coordinate.
    have hx_eq : x = ((e.symm x).1 : H) := by
      calc
        x = ((e.symm x).1 : H) * ((e.symm x).2 : H) := by
          simpa [e] using (h.symm_apply_eq_mul_coords x).symm
        _ = ((e.symm x).1 : H) * 1 := by rw [hright]
        _ = ((e.symm x).1 : H) := by simp
    rw [hx_eq]
    exact ((e.symm x).1).2

-- Proof sketch: use the same unique factorization as above. The commuting decomposition separates
-- the `p`-power part and the prime-to-`p` part of the order, so the `p`-elements are exactly the
-- elements of the `p`-group factor `P`.
/-- In a `p`-elementary decomposition, the `p`-group factor is exactly the set of
`p`-elements. -/
theorem IsPElementaryDecomposition.p_group_factor_eq_setOf_isPElement
    (h : IsPElementaryDecomposition p C P) :
    (P : Set H) = {x | IsPElement p x} := by
  letI : Fact p.Prime := ⟨h.prime⟩
  ext x
  constructor
  · intro hx
    -- Membership in the `p`-group factor gives a `p`-power order immediately.
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp h.isPGroup) ⟨x, hx⟩
    exact ⟨n, by simpa [Subgroup.orderOf_mk] using hn⟩
  · intro hx
    let e := h.isComplement.prodMulEquiv h.commute
    have hleft : ((e.symm x).1 : H) = 1 := by
      simpa [e] using h.left_coord_eq_one_of_isPElement hx
    -- Once the prime-to-`p` coordinate vanishes, `x` is exactly the `P`-coordinate.
    have hx_eq : x = ((e.symm x).2 : H) := by
      calc
        x = ((e.symm x).1 : H) * ((e.symm x).2 : H) := by
          simpa [e] using (h.symm_apply_eq_mul_coords x).symm
        _ = 1 * ((e.symm x).2 : H) := by rw [hleft]
        _ = ((e.symm x).2 : H) := by simp
    rw [hx_eq]
    exact ((e.symm x).2).2

end

end Group

/-! ### Definition_10_10_1_4 (from Chap10) -/
open scoped Pointwise

universe u

section Group

variable {G : Type u} [Group G]

local notation "C(" x ")" => Subgroup.centralizer ({x} : Set G)

/-- Definition 10-10.1-4: for an element `x` and a Sylow `p`-subgroup `P` of its centralizer, the
associated subgroup is generated by `x` together with the image of `P` in `G`. -/
def associatedPElementarySubgroup (p : ℕ) (x : G)
    (P : Sylow p C(x)) : Subgroup G :=
  Subgroup.zpowers x ⊔ Subgroup.map C(x).subtype (P : Subgroup C(x))

/-- The cyclic subgroup generated by `x` is one of the two defining factors of the associated
subgroup. -/
theorem zpowers_le_associatedPElementarySubgroup (p : ℕ) (x : G) (P : Sylow p C(x)) :
    Subgroup.zpowers x ≤ associatedPElementarySubgroup p x P :=
  le_sup_left

section

variable {p : ℕ} [Fact p.Prime] [Finite G]

-- Source/core/bridge triage:
-- * source-facing: `associatedPElementarySubgroup p x P` is LinearRepresentations_Serre_1977's associated subgroup.
-- * core/canonical: `IsPElementaryDecomposition`.
-- * bridge/view: the next theorem records the canonical decomposition data carried by the
--   associated subgroup.
-- Proof sketch: the cyclic subgroup `Subgroup.zpowers x` has order prime to `p` when `x` is
-- `p`-regular, the chosen Sylow subgroup gives the `p`-group factor, and every element of the
-- centralizer commutes with `x`, so these two subgroups form a `p`-elementary decomposition.
/-- The associated subgroup carries the canonical `p`-elementary decomposition whose cyclic factor
is `⟨x⟩` and whose `p`-group factor is the image of the chosen Sylow subgroup of `C(x)`. -/
theorem associatedPElementarySubgroup_decomposition (x : G) (hx : IsPRegular p x)
    (P : Sylow p C(x)) :
    IsPElementaryDecomposition p
      ((Subgroup.zpowers x).subgroupOf (associatedPElementarySubgroup p x P))
      ((Subgroup.map C(x).subtype (P : Subgroup C(x))).subgroupOf
        (associatedPElementarySubgroup p x P)) := by
  let H := associatedPElementarySubgroup p x P
  let C₀ : Subgroup H := (Subgroup.zpowers x).subgroupOf H
  let Pimg : Subgroup G := Subgroup.map C(x).subtype (P : Subgroup C(x))
  let P₀ : Subgroup H := Pimg.subgroupOf H
  have hz : Subgroup.zpowers x ≤ H := zpowers_le_associatedPElementarySubgroup p x P
  have hPimg_le : Pimg ≤ H := le_sup_right
  have hPimg_le_centralizer : Pimg ≤ C(x) := by
    rintro _ ⟨y, hy, rfl⟩
    exact y.2
  have hPimg_pgroup : IsPGroup p Pimg :=
    P.isPGroup'.of_surjective
      (C(x).subtype.subgroupMap (P : Subgroup C(x)))
      (C(x).subtype.subgroupMap_surjective (P : Subgroup C(x)))
  have hP₀_pgroup : IsPGroup p P₀ :=
    hPimg_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hPimg_le).symm
  have hx_centralizes_Pimg : x ∈ Subgroup.centralizer (Pimg : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hPimg_le_centralizer hy)
  have hPimg_centralizes_zpowers : Pimg ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
    exact hx_centralizes_Pimg
  have hPimg_normalizes : Pimg ≤ Subgroup.normalizer (Subgroup.zpowers x) :=
    hPimg_centralizes_zpowers.trans (Subgroup.centralizer_le_normalizer _)
  have hH_mul :
      (↑H : Set G) = (↑(Subgroup.zpowers x) : Set G) * (↑Pimg : Set G) := by
    -- The ambient subgroup is exactly the product of the cyclic and `p`-parts.
    simpa [H, associatedPElementarySubgroup] using
      (Subgroup.coe_mul_of_right_le_normalizer_left (Subgroup.zpowers x) Pimg hPimg_normalizes)
  have hC₀P₀_mul_univ : ((↑C₀ : Set H) * (↑P₀ : Set H)) = Set.univ := by
    -- Lift the product description from `G` to the ambient associated subgroup `H`.
    rw [Set.eq_univ_iff_forall]
    intro h
    have hhMul : ((h : H) : G) ∈ (↑(Subgroup.zpowers x) : Set G) * (↑Pimg : Set G) := by
      have hhH : ((h : H) : G) ∈ (↑H : Set G) := h.2
      rwa [hH_mul] at hhH
    rcases Set.mem_mul.mp hhMul with ⟨u, hu, v, hv, huv⟩
    let uH : H := ⟨u, hz hu⟩
    let vH : H := ⟨v, hPimg_le hv⟩
    have huH : uH ∈ C₀ := Subgroup.mem_subgroupOf.mpr hu
    have hvH : vH ∈ P₀ := Subgroup.mem_subgroupOf.mpr hv
    refine Set.mem_mul.mpr ⟨uH, huH, vH, hvH, ?_⟩
    apply Subtype.ext
    exact huv
  have hC₀P₀_disjoint : Disjoint C₀ P₀ := by
    -- Any element in both factors has order dividing `orderOf x` and also a power of `p`.
    rw [disjoint_iff]
    ext z
    constructor
    · intro hzInf
      rw [Subgroup.mem_bot]
      rw [Subgroup.mem_inf] at hzInf
      have hzC : ((z : H) : G) ∈ Subgroup.zpowers x := Subgroup.mem_subgroupOf.mp hzInf.1
      have hzPimg : ((z : H) : G) ∈ Pimg := Subgroup.mem_subgroupOf.mp hzInf.2
      have hzDiv : orderOf ((z : H) : G) ∣ orderOf x := orderOf_dvd_of_mem_zpowers hzC
      rcases (IsPGroup.iff_orderOf.mp hPimg_pgroup) (⟨((z : H) : G), hzPimg⟩ : Pimg) with
        ⟨n, hn⟩
      have hzOrder : orderOf ((z : H) : G) = p ^ n := by
        simpa [Subgroup.orderOf_mk] using hn
      have hzOne : orderOf ((z : H) : G) = 1 := by
        exact hzOrder.trans (Nat.Coprime.eq_one_of_dvd (hx.pow_left n) (hzOrder ▸ hzDiv))
      apply Subtype.ext
      exact orderOf_eq_one_iff.mp hzOne
    · intro hzBot
      rw [Subgroup.mem_inf]
      have hzOne : z = 1 := Subgroup.mem_bot.mp hzBot
      constructor <;> simp [hzOne]
  have hC₀P₀ : C₀.IsComplement' P₀ :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hC₀P₀_disjoint hC₀P₀_mul_univ
  have hC₀_cyclic : IsCyclic C₀ := by
    -- `C₀` is just the cyclic subgroup `⟨x⟩` viewed inside the ambient subgroup `H`.
    letI : IsCyclic ↥(Subgroup.zpowers x) := Subgroup.isCyclic_zpowers x
    exact
      isCyclic_of_surjective
        (Subgroup.subgroupOfEquivOfLe hz).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hz).symm.surjective
  have hC₀_card : Nat.card C₀ = orderOf x := by
    simpa [C₀] using
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hz).toEquiv).trans (Nat.card_zpowers x)
  have hC₀_centralizes : C₀ ≤ Subgroup.centralizer (P₀ : Set H) := by
    -- The `P`-factor centralizes `x`, hence it centralizes every power of `x`.
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    change (y : G) * (c : G) = (c : G) * (y : G)
    have hyPimg : (y : G) ∈ Pimg := Subgroup.mem_subgroupOf.mp hy
    have hyComm : Commute (y : G) x :=
      Subgroup.mem_centralizer_singleton_iff.mp (hPimg_le_centralizer hyPimg)
    rcases Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hc) with ⟨n, hn⟩
    rw [← hn]
    simpa using (hyComm.zpow_right n).eq
  refine ⟨Fact.out, inferInstance, hC₀_cyclic, ?_, hP₀_pgroup, hC₀_centralizes, hC₀P₀⟩
  exact hC₀_card ▸ hx

/-- The subgroup associated with a `p'`-element and a Sylow subgroup of its centralizer is
`p`-elementary. -/
theorem associatedPElementarySubgroup_isPElementary (x : G) (hx : IsPRegular p x)
    (P : Sylow p C(x)) : IsPElementary p (associatedPElementarySubgroup p x P) := by
  exact ⟨_, _, associatedPElementarySubgroup_decomposition x hx P⟩

-- Proof sketch: any two Sylow `p`-subgroups of `Subgroup.centralizer {x}` are conjugate inside
-- that centralizer. Conjugation by such an element fixes `Subgroup.zpowers x`, because it
-- centralizes `x`, and transports the image of one Sylow subgroup to the other.
/-- Associated subgroups built from different Sylow `p`-subgroups of the centralizer are conjugate
by an element of that centralizer. -/
theorem associatedPElementarySubgroup_conjugate_in_centralizer (x : G)
    (P Q : Sylow p C(x)) :
    ∃ z : C(x),
      MulAut.conj (z : G) • associatedPElementarySubgroup p x P =
        associatedPElementarySubgroup p x Q := by
  obtain ⟨z, hz⟩ := MulAction.exists_smul_eq C(x) P Q
  refine ⟨z, ?_⟩
  change
    Subgroup.map (MulAut.conj (z : G)).toMonoidHom (associatedPElementarySubgroup p x P) =
      associatedPElementarySubgroup p x Q
  have hz_fix_x : MulAut.conj (z : G) x = x := by
    have hz_comm : (z : G) * x = x * (z : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp z.2
    change (z : G) * x * (z : G)⁻¹ = x
    calc
      (z : G) * x * (z : G)⁻¹ = (x * (z : G)) * (z : G)⁻¹ := by rw [hz_comm]
      _ = x := by simp [mul_assoc]
  have hz_smul_subgroup :
      ((z • P : Sylow p C(x)) : Subgroup C(x)) =
        Subgroup.map (MulAut.conj z).toMonoidHom (P : Subgroup C(x)) := by
    simpa [Sylow.smul_def] using (Sylow.coe_subgroup_smul (g := z) (P := P))
  have hz_map_zpowers :
      Subgroup.map (MulAut.conj (z : G)).toMonoidHom (Subgroup.zpowers x) =
        Subgroup.zpowers x := by
    rw [MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers hz_fix_x
  have hcomp :
      (MulAut.conj (z : G)).toMonoidHom.comp C(x).subtype =
        C(x).subtype.comp (MulAut.conj z).toMonoidHom := by
    ext y
    rfl
  calc
    Subgroup.map (MulAut.conj (z : G)).toMonoidHom (associatedPElementarySubgroup p x P)
        = Subgroup.map (MulAut.conj (z : G)).toMonoidHom (Subgroup.zpowers x) ⊔
            Subgroup.map (MulAut.conj (z : G)).toMonoidHom
              (Subgroup.map C(x).subtype (P : Subgroup C(x))) := by
      rw [associatedPElementarySubgroup, Subgroup.map_sup]
    _ = Subgroup.zpowers x ⊔
          Subgroup.map (MulAut.conj (z : G)).toMonoidHom
            (Subgroup.map C(x).subtype (P : Subgroup C(x))) := by
      -- Conjugation by an element of `C(x)` fixes the cyclic factor `⟨x⟩`.
      rw [hz_map_zpowers]
    _ = Subgroup.zpowers x ⊔
          Subgroup.map C(x).subtype ((z • P : Sylow p C(x)) : Subgroup C(x)) := by
      -- On the Sylow factor, conjugation commutes with the subtype map from `C(x)` to `G`.
      rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hz_smul_subgroup]
    _ = associatedPElementarySubgroup p x (z • P) := by
      rw [associatedPElementarySubgroup]
    _ = associatedPElementarySubgroup p x Q := by
      rw [hz]

end

end Group

/-! ### Exercise_10_10_1_5 (from Chap10) -/
universe u

section Group

variable {G : Type u} [Group G]
variable {p : ℕ}

local notation "C(" x ")" => Subgroup.centralizer ({x} : Set G)

namespace IsPElementaryDecomposition

-- Proof sketch: the decomposition hypothesis makes the image of `P` in `G` a `p`-subgroup of the
-- centralizer of `x`, because every element of `P` commutes with the cyclic factor `C` and `x`
-- generates `C`. Reconstruct `Fact p.Prime` from `hH.prime`, then enlarge that `p`-subgroup to a
-- Sylow subgroup `Q ≤ C_G(x)` using `IsPGroup.exists_le_sylow`; then the decomposition
-- `H = C ⋅ P` maps to the inclusion `H ≤ associatedPElementarySubgroup p x Q`.
/-- Exercise 10-10.1-5: if the cyclic factor in a `p`-elementary decomposition of `H` is `⟨x⟩`,
then `H` is contained in the associated subgroup of `G` attached to `x`; its `p`-elementarity is
the canonical content of `associatedPElementarySubgroup_isPElementary`. -/
theorem exists_le_associatedPElementarySubgroup {H : Subgroup G} {x : H} {P : Subgroup H}
    (hH : IsPElementaryDecomposition p (Subgroup.zpowers x) P) :
    ∃ Q : Sylow p C((x : G)),
      H ≤ associatedPElementarySubgroup p (x : G) Q := by
  letI : Fact p.Prime := ⟨hH.prime⟩
  let CGx : Subgroup G := C((x : G))
  let P' : Subgroup G := P.map H.subtype
  have hxC : x ∈ Subgroup.zpowers x :=
    Subgroup.mem_zpowers x
  have hP'_le_centralizer : P' ≤ CGx := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((hH.commute ⟨x, hxC⟩ ⟨y, hy⟩).map H.subtype).symm.eq
  have hP' : IsPGroup p P' :=
    hH.isPGroup.of_surjective (H.subtype.subgroupMap P) (H.subtype.subgroupMap_surjective P)
  have hP'_centralizer : IsPGroup p (P'.subgroupOf CGx) :=
    hP'.of_equiv (Subgroup.subgroupOfEquivOfLe hP'_le_centralizer).symm
  obtain ⟨Q, hPQ⟩ := hP'_centralizer.exists_le_sylow
  have hP'_le_Qmap : P' ≤ Subgroup.map CGx.subtype (Q : Subgroup CGx) := by
    calc
      P' = Subgroup.map CGx.subtype (P'.subgroupOf CGx) := by
        symm
        exact Subgroup.map_subgroupOf_eq_of_le hP'_le_centralizer
      _ ≤ Subgroup.map CGx.subtype (Q : Subgroup CGx) := Subgroup.map_mono hPQ
  have hH_eq :
      H = Subgroup.zpowers (x : G) ⊔ P' := by
    calc
      H = (⊤ : Subgroup H).map H.subtype := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      _ = (Subgroup.zpowers x ⊔ P).map H.subtype := by rw [← hH.isComplement.sup_eq_top]
      _ = Subgroup.zpowers (H.subtype x) ⊔ P' := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      _ = Subgroup.zpowers (x : G) ⊔ P.map H.subtype := by rfl
  refine ⟨Q, ?_⟩
  calc
    H = Subgroup.zpowers (x : G) ⊔ P' := hH_eq
    _ ≤ Subgroup.zpowers (x : G) ⊔ Subgroup.map CGx.subtype (Q : Subgroup CGx) :=
      sup_le_sup le_rfl hP'_le_Qmap
    _ = associatedPElementarySubgroup p (x : G) Q := by
      simp [associatedPElementarySubgroup, CGx]

end IsPElementaryDecomposition

end Group

/-! ### Exercise_10_10_1_6 (from Chap10) -/
universe u v

section

variable {k : Type u} [Semiring k]
variable {p : ℕ} [Fact p.Prime] [CharP k p]
variable {V : Type v} [AddCommGroup V] [Module k V]

-- Layer triage:
-- * source-facing: LinearRepresentations_Serre_1977's `p`-unipotence criterion for a linear automorphism.
-- * core/canonical: `IsPElement` and `IsNilpotent` on the owner `Module.End k V`.
-- * bridge/view: `LinearEquiv.toLinearMap`.
--
-- Proof sketch: if `x` has `p`-power order `p ^ m`, then in characteristic `p` one has
-- `(x - 1)^(p ^ m) = x^(p ^ m) - 1 = 0`, so `x - 1` is nilpotent. Conversely, if `x - 1` is
-- nilpotent, then for some `m` we have `(x - 1)^(p ^ m) = 0`; the same characteristic-`p`
-- binomial identity rewrites this as `x^(p ^ m) - 1 = 0`, hence `x^(p ^ m) = 1`.
/-- Helper for Exercise 10-10.1-6: in characteristic `2`, every positive power `2 ^ n` of the
negation endomorphism acts as negation, because `v = -v` for every vector. -/
lemma neg_one_end_pow_two_apply [CharP k 2] (n : ℕ) (v : V) :
    ((-(1 : Module.End k V)) ^ (2 ^ n)) v = -v := by
  -- For `n = 0` the claim is just the definition of `-1`.
  induction n with
  | zero =>
      simp
  | succ n ih =>
      -- In characteristic `2`, every vector satisfies `v = -v`.
      have htwo : (2 : k) • v = 0 := by
        simpa using
          (show ((2 : k) • v) = (0 : k) • v from
            congrArg (fun a : k => a • v) (CharP.cast_eq_zero (R := k) (p := 2)))
      have htwo' : (2 : ℕ) • v = 0 := by
        convert htwo using 1
        symm
        exact Nat.cast_smul_eq_nsmul k 2 v
      have hv : v = -v := by
        rw [eq_neg_iff_add_eq_zero]
        simpa [two_nsmul] using htwo'
      have heven : Even (2 ^ (n + 1)) := by
        refine ⟨2 ^ n, by omega⟩
      have hpow : (-(1 : Module.End k V)) ^ (2 ^ (n + 1)) = 1 :=
        heven.neg_one_pow
      rw [hpow]
      exact hv

/-- Helper for Exercise 10-10.1-6: the `p ^ n`-th power of the negation endomorphism acts as
negation in characteristic `p`. -/
lemma neg_one_end_pow_prime_apply (n : ℕ) (v : V) :
    ((-(1 : Module.End k V)) ^ p ^ n) v = -v := by
  have hp : Nat.Prime p := Fact.out
  -- Split according to whether the prime is `2` or odd.
  rcases hp.eq_two_or_odd' with rfl | hpodd
  · simpa using neg_one_end_pow_two_apply (k := k) (V := V) n v
  · have hpown : Odd (p ^ n) := hpodd.pow
    have hpow : (-(1 : Module.End k V)) ^ (p ^ n) = -1 :=
      hpown.neg_one_pow
    rw [hpow]
    rfl

/-- Helper for Exercise 10-10.1-6: applying the characteristic-`p` binomial identity to the
linear endomorphism `x.toLinearMap - 1` gives the pointwise formula
`(x - 1)^(p ^ n) v = (x^(p ^ n) - 1) v`. -/
lemma sub_pow_prime_pow_apply (x : V ≃ₗ[k] V) (n : ℕ) (v : V) :
    (((x.toLinearMap - 1) ^ p ^ n) v) = ((x.toLinearMap ^ p ^ n - 1) v) := by
  have hp : Nat.Prime p := Fact.out
  have hcomm : Commute x.toLinearMap (-(1 : Module.End k V)) := by
    simpa using (Commute.all x.toLinearMap (-(1 : Module.End k V)))
  -- The extra `p`-multiple from the noncommutative binomial formula vanishes on vectors.
  obtain ⟨r, hr⟩ := Commute.exists_add_pow_prime_pow_eq hp hcomm n
  have hterm : p • x (r v) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul k]
    simp
  have hv := congrArg (fun f : Module.End k V => f v) hr
  simpa [sub_eq_add_neg, Module.End.pow_apply, neg_one_end_pow_prime_apply (k := k) (p := p)
    (V := V) n v, hterm] using hv

/-- Exercise 10-10.1-6 (1): for a linear automorphism `x` of a `k`-module in characteristic `p`,
with `p` prime, `x` is a `p`-element if and only if the endomorphism `x - 1` is nilpotent. -/
theorem isPElement_iff_isNilpotent_sub_one (x : V ≃ₗ[k] V) :
    IsPElement p x ↔ IsNilpotent (x.toLinearMap - 1) := by
  constructor
  · intro hx
    -- Push the `p`-power order witness to the endomorphism side.
    rcases (isPElement_iff_exists_pow_eq_one x).mp hx with ⟨n, hn⟩
    refine ⟨p ^ n, ?_⟩
    ext v
    rw [sub_pow_prime_pow_apply (k := k) (p := p) (V := V) x n v]
    have hval : (x ^ p ^ n) v = v := by
      simpa using congrArg (fun e : V ≃ₗ[k] V => e v) hn
    have hiter : (x.toLinearMap ^ p ^ n) v = v := by
      simpa [Module.End.pow_apply, LinearEquiv.pow_apply] using hval
    simpa using sub_eq_zero.mpr hiter
  · rintro ⟨n, hn⟩
    -- Raise the nilpotence exponent to a prime-power exponent large enough for LinearRepresentations_Serre_1977's criterion.
    let m := Nat.clog p n
    have hp : Nat.Prime p := Fact.out
    have hle : n ≤ p ^ m :=
      Nat.le_pow_clog hp.one_lt n
    have hzero : (x.toLinearMap - 1) ^ (p ^ m) = 0 :=
      pow_eq_zero_of_le hle hn
    have hxpow : x.toLinearMap ^ p ^ m = 1 := by
      ext v
      have hsub : (((x.toLinearMap - 1) ^ p ^ m) v) = ((x.toLinearMap ^ p ^ m - 1) v) :=
        sub_pow_prime_pow_apply (k := k) (p := p) (V := V) x m v
      rw [hzero] at hsub
      have hsub' : ((x.toLinearMap ^ p ^ m - 1) v) = 0 := by
        simpa using hsub.symm
      simpa using sub_eq_zero.mp hsub'
    -- Convert the endomorphism equality back to the original automorphism.
    refine (isPElement_iff_exists_pow_eq_one x).2 ⟨m, ?_⟩
    ext v
    have hval : (⇑x)^[p ^ m] v = v := by
      simpa [Module.End.pow_apply] using congrArg (fun f : Module.End k V => f v) hxpow
    simpa [LinearEquiv.pow_apply] using hval

end

section

variable {k : Type u} [Field k]
variable {p : ℕ} [CharP k p]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

open Module.End

-- Layer triage:
-- * source-facing: the two LinearRepresentations_Serre_1977 criteria for `p`-elements and `p'`-elements of a linear
--   automorphism.
-- * core/canonical: `IsPElement`, `IsPRegular`, `IsNilpotent`, and `Module.End.IsSemisimple`.
-- * bridge/view: `LinearEquiv.toLinearMap`.
--
-- Proof sketch: if `x` has order prime to `p`, then its minimal polynomial divides `X^m - 1`
-- for some `m` with `Nat.Coprime p m`, and `X^m - 1` is squarefree in characteristic `p`; hence
-- the induced endomorphism is semisimple. Conversely, one may pass to a finite extension over
-- which a semisimple endomorphism diagonalizes; there its eigenvalues lie in a finite
-- multiplicative group of order prime to `p`, so the order of `x` is also prime to `p`.
/-- Helper for Exercise 10-10.1-6: a `p'`-regular linear automorphism is semisimple because
`X ^ orderOf x - 1` is squarefree and annihilates `x.toLinearMap`. -/
lemma isPRegular_toLinearMap_isSemisimple [Fact p.Prime] (x : V ≃ₗ[k] V)
    (hx : IsPRegular p x) :
    IsSemisimple x.toLinearMap := by
  have hreg : ¬ p ∣ orderOf x := (isPRegular_iff_not_dvd_orderOf x).mp hx
  have hcast : (orderOf x : k) ≠ 0 := by
    intro hzero
    exact hreg ((CharP.cast_eq_zero_iff k p (orderOf x)).mp hzero)
  have hsep : ((Polynomial.X ^ orderOf x - (1 : Polynomial k))).Separable := by
    rw [Polynomial.X_pow_sub_one_separable_iff]
    exact hcast
  -- Evaluate the annihilating polynomial on the endomorphism.
  have hpow : x.toLinearMap ^ orderOf x = 1 := by
    ext v
    change (x.toLinearMap ^ orderOf x) v = (1 : Module.End k V) v
    rw [Module.End.pow_apply]
    change (⇑x)^[orderOf x] v = v
    rw [← LinearEquiv.pow_apply]
    exact congrArg (fun e : V ≃ₗ[k] V => e v) (pow_orderOf_eq_one x)
  have haeval : Polynomial.aeval x.toLinearMap (Polynomial.X ^ orderOf x - (1 : Polynomial k)) = 0 := by
    simp [hpow]
  exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree haeval

/-- Helper for Exercise 10-10.1-6: over a finite field, every linear automorphism has finite
order because its underlying permutation of the finite set `V` does. -/
lemma linearEquiv_isOfFinOrder_of_finite_field [Finite k] (x : V ≃ₗ[k] V) :
    IsOfFinOrder x := by
  let b := Module.Free.chooseBasis k V
  let e : Equiv.Perm V := x.toEquiv
  haveI : Finite (Module.Free.ChooseBasisIndex k V) := Module.Finite.finite_basis b
  letI : Fintype (Module.Free.ChooseBasisIndex k V) :=
    Fintype.ofFinite (Module.Free.ChooseBasisIndex k V)
  letI : Fintype k := Fintype.ofFinite k
  letI : Fintype (Module.Free.ChooseBasisIndex k V →₀ k) := by
    infer_instance
  haveI : Finite V := by
    exact Finite.of_equiv (Module.Free.ChooseBasisIndex k V →₀ k) b.repr.toEquiv.symm
  rcases isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite e) with ⟨n, hnpos, hn⟩
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hnpos, ?_⟩
  ext v
  have hperm : (x.toEquiv ^ n) v = v := by
    simpa [e] using congrArg (fun σ : Equiv.Perm V => σ v) hn
  simpa [LinearEquiv.pow_apply] using hperm

/-- Helper for Exercise 10-10.1-6: any power of a finite-order semisimple automorphism is again
semisimple. This is used for the `p`-unipotent factor, which lies in `Subgroup.zpowers x`. -/
lemma isSemisimple_toLinearMap_of_mem_zpowers (x y : V ≃ₗ[k] V)
    (hx : IsOfFinOrder x) (hs : IsSemisimple x.toLinearMap) (hy : y ∈ Subgroup.zpowers x) :
    IsSemisimple y.toLinearMap := by
  classical
  -- Replace the `zpow` witness by a natural power representative modulo `orderOf x`.
  rw [hx.mem_zpowers_iff_mem_range_orderOf] at hy
  rcases Finset.mem_image.mp hy with ⟨n, _, hy⟩
  subst hy
  convert (hs.pow n : IsSemisimple (x.toLinearMap ^ n)) using 1
  ext v
  simp [Module.End.pow_apply, LinearEquiv.pow_apply]

/-- Helper for Exercise 10-10.1-6: a semisimple unipotent automorphism is the identity. -/
lemma linearEquiv_eq_one_of_isSemisimple_of_isNilpotent_sub_one (y : V ≃ₗ[k] V)
    (hs : IsSemisimple y.toLinearMap) (hn : IsNilpotent (y.toLinearMap - 1)) :
    y = 1 := by
  -- Shift by the identity and use that a nilpotent semisimple endomorphism must be zero.
  have hsemisimple_sub : IsSemisimple (y.toLinearMap - 1) := by
    simpa using
      (Module.End.isSemisimple_sub_algebraMap_iff (f := y.toLinearMap) (μ := (1 : k))).2 hs
  have hzero : y.toLinearMap - 1 = 0 :=
    Module.End.eq_zero_of_isNilpotent_isSemisimple hn hsemisimple_sub
  exact LinearEquiv.toLinearMap_injective (sub_eq_zero.mp hzero)

/-- Exercise 10-10.1-6 (2): for a linear automorphism `x` of a finite-dimensional vector space
over a finite field `k` of characteristic `p`, `x` is a `p'`-element if and only if the
induced endomorphism `x.toLinearMap` is semisimple. -/
theorem isPRegular_iff_isSemisimple [Finite k] (x : V ≃ₗ[k] V) :
    IsPRegular p x ↔ IsSemisimple x.toLinearMap := by
  letI : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  constructor
  · intro hx
    -- The forward implication is the standard squarefree-polynomial criterion.
    exact isPRegular_toLinearMap_isSemisimple (p := p) x hx
  · intro hs
    -- Decompose `x` into its canonical `p`-unipotent and `p'`-regular parts.
    have hxfin : IsOfFinOrder x :=
      linearEquiv_isOfFinOrder_of_finite_field (k := k) (V := V) x
    let hdecomp := p_component_decomposition_exists (p := p) x hxfin
    -- The `p`-unipotent component is a power of `x`, hence still semisimple.
    have hxu_semisimple : IsSemisimple (pUnipotentComponent p x).toLinearMap := by
      exact isSemisimple_toLinearMap_of_mem_zpowers (x := x) (y := pUnipotentComponent p x)
        hxfin hs hdecomp.left_mem_zpowers
    -- Part (1) identifies the `p`-unipotent component with a unipotent semisimple map.
    have hxu_nilpotent : IsNilpotent ((pUnipotentComponent p x).toLinearMap - 1) := by
      exact (isPElement_iff_isNilpotent_sub_one (p := p) (x := pUnipotentComponent p x)).mp
        hdecomp.isPElement
    have hxu_one : pUnipotentComponent p x = 1 :=
      linearEquiv_eq_one_of_isSemisimple_of_isNilpotent_sub_one
        (y := pUnipotentComponent p x) hxu_semisimple hxu_nilpotent
    -- Once the `p`-unipotent component is trivial, only the `p'`-regular part remains.
    have hxeq : x = pRegularComponent p x := by
      calc
        x = pUnipotentComponent p x * pRegularComponent p x := hdecomp.eq_mul
        _ = pRegularComponent p x := by simp [hxu_one]
    rw [hxeq]
    exact hdecomp.isPRegular

end
