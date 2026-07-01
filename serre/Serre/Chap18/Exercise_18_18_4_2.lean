import Mathlib
import Serre.Chap10.Definition_10_10_1_2
import Serre.Chap12.Definition_12_12_6_1
import Serre.Chap16.Theorem_16_16_2_1
import Serre.Chap18.Remark_18_18_1_3
import Serre.Chap18.Theorem_18_18_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

namespace Representation

open scoped Representation

/-
Domain-style sampling for this item:
* `pRegularComponent` in Chapter `10` is the source-facing owner for the chosen `p`-regular
  component of a group element, defined using the `p`-part `p ^ padicValNat p (orderOf x)` and
  the prime-to-`p` part `Nat.divMaxPow (orderOf x) p`.
* `virtualModularCharacter` in Remark `18-18.1-3` and `pRegularComponentVirtualModularCharacter`
  in Theorem `18-18.4-1` are the canonical Chapter `18` owners for modular characters and Serre's
  `f ↦ f'` construction.
* `R[K](G)` in Chapter `12` is the core/canonical owner for ordinary virtual characters on `G`.
* `finiteRepGrothendieckCharacter` in Theorem `16-16.2-1` is only the bridge from `R₀[K](G)` to
  that owner.

Layer triage:
* source-facing: the congruence description of `pRegularComponent p s` and the resulting formulas
  for Serre's `f'`.
* core/canonical: `pRegularComponent`, `virtualModularCharacter`, `x′[p, lift]`, and `R[K](G)`.
* bridge/view: the restriction map from ordinary class functions on `G` to the `p`-regular locus;
  the theorem below should quantify over `R[K](G)` directly, using `finiteRepGrothendieckCharacter`
  only when a Grothendieck-group lift is genuinely part of the data.
-/

section

variable {p q : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [Finite G]

/-- Helper for Exercise 18-18.4-2: the `p`-part and the prime-to-`p` part of `orderOf s` divide
the corresponding parts of the group exponent. -/
private theorem order_parts_dvd_exponent_parts (s : G) :
    Nat.divMaxPow (orderOf s) p ∣ Nat.divMaxPow (Monoid.exponent G) p ∧
      p ^ padicValNat p (orderOf s) ∣ p ^ padicValNat p (Monoid.exponent G) := by
  let d := orderOf s
  let m := Nat.divMaxPow d p
  let n := p ^ padicValNat p d
  let E := Monoid.exponent G
  let M := Nat.divMaxPow E p
  let N := p ^ padicValNat p E
  have hp : Nat.Prime p := Fact.out
  have hd0 : d ≠ 0 := by
    exact orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite s)
  have hE0 : E ≠ 0 := Monoid.exponent_ne_zero_of_finite (G := G)
  have hsplit := orderOf_divMaxPow_split (p := p) s (isOfFinOrder_of_finite s)
  dsimp [d, m, n] at hsplit
  rcases hsplit with ⟨hmn, _⟩
  have hMN : M * N = E := by
    -- This is the ambient exponent analogue of the local split `m * n = orderOf s`.
    dsimp [M, N, E]
    rw [Nat.mul_comm]
    exact Nat.pow_padicValNat_mul_divMaxPow p (Monoid.exponent G)
  have hm_dvd_E : m ∣ E := by
    exact dvd_trans ⟨n, hmn.symm⟩ (Monoid.order_dvd_exponent s)
  have hn_dvd_E : n ∣ E := by
    exact dvd_trans ⟨m, by rw [Nat.mul_comm, hmn]⟩ (Monoid.order_dvd_exponent s)
  have hnot_dvd_m : ¬ p ∣ m := by
    -- The prime-to-`p` part of `orderOf s` is, by construction, not divisible by `p`.
    simpa [d, m] using Nat.not_dvd_divMaxPow hp.one_lt hd0
  have hnot_dvd_M : ¬ p ∣ M := by
    -- The same divisibility fact holds for the prime-to-`p` part of the group exponent.
    simpa [E, M] using Nat.not_dvd_divMaxPow hp.one_lt hE0
  have hcop_pm : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hnot_dvd_m
  have hcop_pM : Nat.Coprime p M := hp.coprime_iff_not_dvd.mpr hnot_dvd_M
  have hcop_mN : Nat.Coprime m N := by
    -- Any divisor prime to `p` is automatically coprime to the ambient `p`-power part `N`.
    simpa [m, N, E, Nat.coprime_comm] using (hcop_pm.pow_left (padicValNat p E))
  have hcop_nM : Nat.Coprime n M := by
    -- Symmetrically, the local `p`-power part is coprime to the ambient prime-to-`p` part.
    simpa [n, M, d] using (hcop_pM.pow_left (padicValNat p d))
  constructor
  · -- Since `m ∣ orderOf s ∣ Monoid.exponent G = M * N` and `m` is coprime to `N`, it must
    -- divide `M`.
    have hm_dvd_MN : m ∣ M * N := by
      simpa [hMN] using hm_dvd_E
    exact hcop_mN.dvd_of_dvd_mul_right hm_dvd_MN
  · -- Likewise, the local `p`-power part `n` can only contribute to the ambient `p`-power part.
    have hn_dvd_NM : n ∣ N * M := by
      rw [Nat.mul_comm, hMN]
      exact hn_dvd_E
    exact hcop_nM.dvd_of_dvd_mul_right hn_dvd_NM

/-- Helper for Exercise 18-18.4-2: the congruence conditions modulo the ambient exponent parts
descend to the corresponding congruences modulo the split parts of `orderOf s`. -/
private theorem modEq_order_parts_of_modEq_exponent_parts
    (hqp : q ≡ 0 [MOD p ^ padicValNat p (Monoid.exponent G)])
    (hqm : q ≡ 1 [MOD Nat.divMaxPow (Monoid.exponent G) p])
    (s : G) :
    q ≡ 0 [MOD p ^ padicValNat p (orderOf s)] ∧
      q ≡ 1 [MOD Nat.divMaxPow (orderOf s) p] := by
  -- Once the local parts divide the ambient parts, congruences descend by `Nat.ModEq.of_dvd`.
  obtain ⟨hm, hn⟩ := order_parts_dvd_exponent_parts (p := p) (G := G) s
  exact ⟨Nat.ModEq.of_dvd hn hqp, Nat.ModEq.of_dvd hm hqm⟩

/-- Helper for Exercise 18-18.4-2: local congruences on the split parts of `orderOf s` produce a
`p`-component decomposition whose `p'`-factor is `s ^ q`. -/
private theorem isPComponentDecomposition_mul_inv_pow_pow_of_modEq_order_parts
    (s : G)
    (hqn : q ≡ 0 [MOD p ^ padicValNat p (orderOf s)])
    (hqm : q ≡ 1 [MOD Nat.divMaxPow (orderOf s) p]) :
    IsPComponentDecomposition p s (s * (s ^ q)⁻¹) (s ^ q) := by
  let d := orderOf s
  let m := Nat.divMaxPow d p
  let n := p ^ padicValNat p d
  have hp : Nat.Prime p := Fact.out
  have hd0 : d ≠ 0 := by
    exact orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite s)
  have hsplit := orderOf_divMaxPow_split (p := p) s (isOfFinOrder_of_finite s)
  dsimp [d, m, n] at hsplit
  rcases hsplit with ⟨hmn, _⟩
  have hnot_dvd_m : ¬ p ∣ m := by
    -- The factor `m` is the prime-to-`p` part of `orderOf s`.
    simpa [d, m] using Nat.not_dvd_divMaxPow hp.one_lt hd0
  have hcop_pm : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hnot_dvd_m
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The left factor has `p`-power order because its `n`th power is trivial.
    have hqnm : q * n ≡ n [MOD d] := by
      simpa [d, m, n, hmn, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hqm.mul_right' n
    have hpow : (s * (s ^ q)⁻¹) ^ n = 1 := by
      have hcomm : Commute s (s ^ q)⁻¹ := ((Commute.refl s).pow_right q).inv_right
      calc
        (s * (s ^ q)⁻¹) ^ n = s ^ n * ((s ^ q)⁻¹) ^ n := by
          simpa using hcomm.mul_pow n
        _ = s ^ n * (s ^ (q * n))⁻¹ := by
          rw [inv_pow, pow_mul]
        _ = s ^ n * (s ^ n)⁻¹ := by
          rw [pow_eq_pow_of_modEq hqnm (pow_orderOf_eq_one s)]
        _ = 1 := by simp
    have horder_dvd : orderOf (s * (s ^ q)⁻¹) ∣ n := by
      exact (orderOf_dvd_iff_pow_eq_one).2 hpow
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp (by simpa [n] using horder_dvd)
    exact ⟨k, hk⟩
  · -- The right factor has order dividing the prime-to-`p` part `m`, hence is `p`-regular.
    have hqmm : q * m ≡ 0 [MOD d] := by
      simpa [d, m, n, hmn, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hqn.mul_right' m
    have hpow : (s ^ q) ^ m = 1 := by
      calc
        (s ^ q) ^ m = s ^ (q * m) := by rw [pow_mul]
        _ = s ^ 0 := by
          rw [pow_eq_pow_of_modEq hqmm (pow_orderOf_eq_one s)]
        _ = 1 := by simp
    have horder_dvd : orderOf (s ^ q) ∣ m := by
      exact (orderOf_dvd_iff_pow_eq_one).2 hpow
    exact Nat.Coprime.of_dvd_right horder_dvd hcop_pm
  · -- Both factors are built from powers of `s`, so they commute.
    have hpow : Commute s (s ^ q) := (Commute.refl s).pow_right q
    have hpow_inv : Commute (s ^ q)⁻¹ (s ^ q) := (Commute.refl (s ^ q)).inv_left
    exact Commute.mul_left hpow hpow_inv
  · -- The decomposition was chosen so that the two factors multiply back to `s`.
    calc
      (s * (s ^ q)⁻¹) * s ^ q = s * ((s ^ q)⁻¹ * s ^ q) := by rw [mul_assoc]
      _ = s * 1 := by rw [inv_mul_cancel]
      _ = s := by simp

-- Proof sketch: the congruence hypotheses force `q` to be congruent modulo `orderOf s` to the
-- Bézout exponent defining the chosen `p`-regular component, because `orderOf s` divides the group
-- exponent and its `p`- and `p'`-parts divide the corresponding parts of `Monoid.exponent G`.
/-- Exercise 18-18.4-2 (1): if `q` is congruent to `0` modulo the `p`-part of `Monoid.exponent G`
and to `1` modulo the prime-to-`p` part of `Monoid.exponent G`, then the chosen `p'`-component of
an element `s` is `s ^ q`. -/
theorem pRegularComponent_eq_pow_of_modEq_exponent_parts
    (hqp :
      q ≡ 0 [MOD p ^ padicValNat p (Monoid.exponent G)])
    (hqm :
      q ≡ 1 [MOD Nat.divMaxPow (Monoid.exponent G) p])
    (s : G) :
    pRegularComponent p s = s ^ q := by
  -- First descend the ambient exponent congruences to the canonical split of `orderOf s`.
  obtain ⟨hqn, hqm_local⟩ :=
    modEq_order_parts_of_modEq_exponent_parts (p := p) (q := q) (G := G) hqp hqm s
  -- Then `s ^ q` is the `p'`-factor in a `p`-component decomposition of `s`, so uniqueness of the
  -- canonical decomposition identifies it with `pRegularComponent p s`.
  exact
    (isPComponentDecomposition_mul_inv_pow_pow_of_modEq_order_parts
      (p := p) (q := q) (G := G) s hqn hqm_local).eq_pRegularComponent.symm

end

section

variable {p q : ℕ} [Fact p.Prime]
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Type u} [Field K]
variable {G : Type u} [Group G] [Finite G]
variable (lift : PrimeToPRoot p k →* Kˣ)

/-- Helper for Exercise 18-18.4-2: the restriction identity can be evaluated at the canonical
`p`-regular component of any element `s : G`. -/
private theorem virtualModularCharacter_apply_pRegularComponent_of_restriction
    (E : FDRep k G) (χ : R[K](G))
    (hχ :
      virtualModularCharacter (PrimeToPRoot.toFieldLift lift) [E]₀ = χ ∘ Subtype.val)
    (s : G) :
    virtualModularCharacter (PrimeToPRoot.toFieldLift lift) [E]₀
        ⟨pRegularComponent p s, isPRegular_pRegularComponent s⟩ =
      χ (pRegularComponent p s) := by
  -- Evaluate the restriction hypothesis at the chosen `p`-regular component of `s`.
  exact congrFun hχ ⟨pRegularComponent p s, isPRegular_pRegularComponent s⟩

/-- Helper for Exercise 18-18.4-2: after part `(1)`, evaluating the ordinary character `χ` on
the chosen `p'`-component of `s` is the same as evaluating it on `s ^ q`. -/
private theorem character_apply_pRegularComponent_eq_apply_pow
    (hqp :
      q ≡ 0 [MOD p ^ padicValNat p (Monoid.exponent G)])
    (hqm :
      q ≡ 1 [MOD Nat.divMaxPow (Monoid.exponent G) p])
    (χ : R[K](G)) (s : G) :
    χ (pRegularComponent p s) = χ (s ^ q) := by
  -- Part `(1)` identifies the canonical `p'`-component with the source exponent `s ^ q`.
  rw [pRegularComponent_eq_pow_of_modEq_exponent_parts
    (p := p) (q := q) (G := G) hqp hqm s]

-- Proof sketch: on each `s : G`, part `(1)` identifies the chosen `p'`-component with `s ^ q`.
-- Evaluating the restriction hypothesis at the `p`-regular element `s ^ q` then rewrites `f'`
-- exactly as the `q`th power operation applied to the ordinary character `χ`.
/-- Exercise 18-18.4-2 (2): if `f` is the modular character of `E` and `χ ∈ R_K(G)` restricts to
`f` on the `p`-regular locus, then the class function `f'` is the `Ψ^q`-transform of the ordinary
character `χ`, written here as `s ↦ χ (s ^ q)`. -/
theorem pRegularComponentVirtualModularCharacter_eq_character_pow_of_restriction
    (hqp :
      q ≡ 0 [MOD p ^ padicValNat p (Monoid.exponent G)])
    (hqm :
      q ≡ 1 [MOD Nat.divMaxPow (Monoid.exponent G) p])
    (E : FDRep k G) (χ : R[K](G))
    (hχ :
      virtualModularCharacter (PrimeToPRoot.toFieldLift lift) [E]₀ = χ ∘ Subtype.val) :
    ([E]₀)′[p, PrimeToPRoot.toFieldLift lift] =
      fun s ↦ χ (s ^ q) := by
  ext s
  -- First rewrite Serre's `f'` by evaluating the restriction identity on the canonical
  -- `p`-regular component of `s`.
  have hχs :=
    virtualModularCharacter_apply_pRegularComponent_of_restriction
      (p := p) (k := k) (K := K) (G := G) lift E χ hχ s
  -- Then part `(1)` replaces that canonical component by the source power `s ^ q`.
  calc
    ([E]₀)′[p, PrimeToPRoot.toFieldLift lift] s
        = virtualModularCharacter (PrimeToPRoot.toFieldLift lift) [E]₀
            ⟨pRegularComponent p s, isPRegular_pRegularComponent s⟩ := by
              rw [pRegularComponentVirtualModularCharacter_apply]
    _ = χ (pRegularComponent p s) := hχs
    _ = χ (s ^ q) := character_apply_pRegularComponent_eq_apply_pow
      (p := p) (q := q) (G := G) hqp hqm χ s

end

section

variable {p : ℕ} [Fact p.Prime]
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {K : Type u} [Field K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]
variable (lift : PrimeToPRoot p k →* Kˣ)

/-
`omit [CharZero K]` keeps the source-facing statement free of an unnecessary characteristic-zero
parameter. The helper body below is the only remaining local placeholder for this item.
-/
/-- Helper for Exercise 18-18.4-2: the final character-ring membership statement is exactly the
specialization of Theorem `18-18.4-1` to the Grothendieck class `[E]₀`. -/
private theorem pRegularComponent_modularCharacter_mem_characterRingOverField_of_finiteRep
    (E : FDRep k G) :
    ([E]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](G) := by
  -- This is exactly Theorem `18-18.4-1 (1)` specialized to the Grothendieck class `[E]₀`.
  exact
    pRegularComponentVirtualModularCharacter_mem_characterRingOverField
      (p := p) (k := k) (K := K) (G := G) lift [E]₀

-- Proof sketch: this is the source-facing specialization of Theorem `18-18.4-1 (1)` to the
-- Grothendieck class `[E]₀`, but its public statement only depends on the characteristic-`p`
-- field `k`,
-- the characteristic-zero field `K`, and the chosen lift `PrimeToPRoot p k →* Kˣ`. The local-ring
-- realization from Theorem `18-18.4-1` is proof data upstream, not part of this exercise's
-- owner-level interface.
/-- Exercise 18-18.4-2 (3): the class function `f'` attached to the modular character of `E`
belongs to `R_K(G)`. -/
theorem pRegularComponent_modularCharacter_mem_characterRingOverField
    (E : FDRep k G) :
    ([E]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](G) := by
  -- The exercise closes by specializing the already-proved stability theorem to `[E]₀`.
  exact
    pRegularComponent_modularCharacter_mem_characterRingOverField_of_finiteRep
      (p := p) (k := k) (K := K) (G := G) lift E

end

end Representation
