import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap09.Exercise_9_9_1_4.IrreducibleCharacterTransport
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_2
import LinearRepresentations_Serre_1977.Serre.Chap12.Definition_12_12_6_1
import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_2_1
import LinearRepresentations_Serre_1977.Serre.Chap18.Remark_18_18_1_3
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_4_1

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
* Semantic recall (`lean_leansearch`) did not surface a better owner than the Chapter `10`/`18`
  APIs already used here, so the statement stays on `pRegularComponent` and `R[K](G)`.

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
  have hp : Nat.Prime p := Fact.out
  have hs0 : orderOf s ≠ 0 := orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite s)
  have hE0 : Monoid.exponent G ≠ 0 := Monoid.exponent_ne_zero_of_finite
  have hdiv : orderOf s ∣ Monoid.exponent G := Monoid.order_dvd_exponent s
  -- First descend the `p`-power divisibility by comparing `p`-adic valuations.
  have hle : padicValNat p (orderOf s) ≤ padicValNat p (Monoid.exponent G) := by
    apply (Nat.pow_dvd_iff_le_padicValNat hp.ne_one hE0).1
    exact dvd_trans (pow_padicValNat_dvd (p := p) (n := orderOf s)) hdiv
  have hpow_div :
      p ^ padicValNat p (orderOf s) ∣ p ^ padicValNat p (Monoid.exponent G) :=
    Nat.pow_dvd_pow p hle
  set ms := Nat.divMaxPow (orderOf s) p
  set ns := p ^ padicValNat p (orderOf s)
  set me := Nat.divMaxPow (Monoid.exponent G) p
  set ne := p ^ padicValNat p (Monoid.exponent G)
  have hs_split : ms * ns = orderOf s := by
    simp [ms, ns, Nat.mul_comm]
  have hE_split : me * ne = Monoid.exponent G := by
    simp [me, ne, Nat.mul_comm]
  have hnot : ¬ p ∣ ms := by
    simpa [ms] using Nat.not_dvd_divMaxPow hp.one_lt hs0
  have hcop_pm : Nat.Coprime p ms := hp.coprime_iff_not_dvd.mpr hnot
  have hcop_ms_ns : Nat.Coprime ms ns := by
    simpa [ns] using (hcop_pm.symm.pow_right (padicValNat p (orderOf s)))
  have hcop_ms_ne : Nat.Coprime ms ne := by
    simpa [ne] using (hcop_pm.symm.pow_right (padicValNat p (Monoid.exponent G)))
  have hns_dvd_ne : ns ∣ ne := by
    simpa [ns, ne] using hpow_div
  rcases hns_dvd_ne with ⟨t, ht⟩
  -- Then cancel the `p`-power factor to descend the prime-to-`p` divisibility.
  have hprod : ms * ns ∣ ns * (me * t) := by
    rw [show ns * (me * t) = Monoid.exponent G by
      calc
        ns * (me * t) = me * (ns * t) := by ac_rfl
        _ = me * ne := by rw [ht]
        _ = Monoid.exponent G := hE_split]
    exact hs_split ▸ hdiv
  have hms_dvd : ms ∣ ns * (me * t) := by
    exact dvd_trans (by simp [Nat.mul_comm]) hprod
  have hms_mt : ms ∣ me * t := hcop_ms_ns.dvd_of_dvd_mul_left hms_dvd
  have ht_dvd : t ∣ ne := ⟨ns, by rw [ht, Nat.mul_comm]⟩
  have hcop_ms_t : Nat.Coprime ms t := Nat.Coprime.of_dvd_right ht_dvd hcop_ms_ne
  have hms_me : ms ∣ me :=
    hcop_ms_t.dvd_of_dvd_mul_right (by simpa [Nat.mul_comm] using hms_mt)
  exact ⟨hms_me, ⟨t, ht⟩⟩

/-- Helper for Exercise 18-18.4-2: the congruence conditions modulo the ambient exponent parts
descend to the corresponding congruences modulo the split parts of `orderOf s`. -/
private theorem modEq_order_parts_of_modEq_exponent_parts
    (hqp : q ≡ 0 [MOD p ^ padicValNat p (Monoid.exponent G)])
    (hqm : q ≡ 1 [MOD Nat.divMaxPow (Monoid.exponent G) p])
    (s : G) :
    q ≡ 0 [MOD p ^ padicValNat p (orderOf s)] ∧
      q ≡ 1 [MOD Nat.divMaxPow (orderOf s) p] := by
  -- Restrict each ambient congruence along the divisibility proved just above.
  rcases order_parts_dvd_exponent_parts (p := p) (G := G) s with ⟨hm, hn⟩
  exact ⟨Nat.ModEq.of_dvd hn hqp, Nat.ModEq.of_dvd hm hqm⟩

/-- Helper for Exercise 18-18.4-2: local congruences on the split parts of `orderOf s` produce a
`p`-component decomposition whose `p'`-factor is `s ^ q`. -/
private theorem isPComponentDecomposition_mul_inv_pow_pow_of_modEq_order_parts
    (s : G)
    (hqn : q ≡ 0 [MOD p ^ padicValNat p (orderOf s)])
    (hqm : q ≡ 1 [MOD Nat.divMaxPow (orderOf s) p]) :
    IsPComponentDecomposition p s (s * (s ^ q)⁻¹) (s ^ q) := by
  have hp : Nat.Prime p := Fact.out
  have hs0 : orderOf s ≠ 0 := orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite s)
  set m := Nat.divMaxPow (orderOf s) p
  set n := p ^ padicValNat p (orderOf s)
  have hs_split : m * n = orderOf s := by
    simp [m, n, Nat.mul_comm]
  have hcop_pm : Nat.Coprime p m := by
    refine hp.coprime_iff_not_dvd.mpr ?_
    simpa [m] using Nat.not_dvd_divMaxPow hp.one_lt hs0
  have hsq_comm : Commute s (s ^ q) := (Commute.refl s).pow_right q
  -- The `p'`-factor has order dividing the prime-to-`p` part of `orderOf s`.
  have hpow_regular : (s ^ q) ^ m = 1 := by
    have hmod : q * m ≡ 0 [MOD orderOf s] := by
      simpa [m, n, hs_split, Nat.mul_comm] using hqn.mul_right' m
    have hpow := pow_eq_pow_of_modEq (x := s) hmod (pow_orderOf_eq_one s)
    simpa [pow_mul] using hpow
  have hregular : IsPRegular p (s ^ q) := by
    exact hcop_pm.coprime_dvd_right ((orderOf_dvd_iff_pow_eq_one).2 hpow_regular)
  -- The remaining factor is killed by the `p`-part because `q ≡ 1` modulo the prime-to-`p` part.
  have hpow_match : (s ^ q) ^ n = s ^ n := by
    have hmod : q * n ≡ n [MOD orderOf s] := by
      simpa [m, n, hs_split, Nat.mul_comm] using hqm.mul_right' n
    have hpow := pow_eq_pow_of_modEq (x := s) hmod (pow_orderOf_eq_one s)
    simpa [pow_mul] using hpow
  have hunip_pow : (s * (s ^ q)⁻¹) ^ n = 1 := by
    calc
      (s * (s ^ q)⁻¹) ^ n = s ^ n * ((s ^ q)⁻¹) ^ n := by
        simpa using (hsq_comm.inv_right.mul_pow n)
      _ = s ^ n * ((s ^ q) ^ n)⁻¹ := by simp
      _ = 1 := by
        rw [hpow_match]
        simp
  have hunipotent : IsPElement p (s * (s ^ q)⁻¹) := by
    rw [isPElement_iff_exists_pow_eq_one]
    refine ⟨padicValNat p (orderOf s), ?_⟩
    simpa [n] using hunip_pow
  -- Both factors lie in the cyclic subgroup generated by `s`, so they commute.
  have hcomm : Commute (s * (s ^ q)⁻¹) (s ^ q) := by
    rw [Commute]
    calc
      (s * (s ^ q)⁻¹) * (s ^ q) = s := by simp [mul_assoc]
      _ = (s ^ q) * ((s ^ q)⁻¹ * s) := by simp
      _ = (s ^ q) * (s * (s ^ q)⁻¹) := by rw [hsq_comm.inv_right.eq]
  refine ⟨hunipotent, hregular, hcomm, ?_⟩
  -- The displayed decomposition multiplies back to `s`.
  simp

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
  -- Descend the ambient congruences to `orderOf s` and apply uniqueness of the chosen
  -- `p`-component decomposition.
  rcases modEq_order_parts_of_modEq_exponent_parts (p := p) (q := q) hqp hqm s with
    ⟨hqn, hqm'⟩
  exact
    (isPComponentDecomposition_mul_inv_pow_pow_of_modEq_order_parts
      (p := p) (q := q) s hqn hqm').eq_pRegularComponent.symm

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
  -- Evaluate the restriction identity at the canonical `p`-regular component of `s`.
  rw [hχ]
  simp

/-- Helper for Exercise 18-18.4-2: after part `(1)`, evaluating the ordinary character `χ` on
the chosen `p'`-component of `s` is the same as evaluating it on `s ^ q`. -/
private theorem character_apply_pRegularComponent_eq_apply_pow
    (hqp :
      q ≡ 0 [MOD p ^ padicValNat p (Monoid.exponent G)])
    (hqm :
      q ≡ 1 [MOD Nat.divMaxPow (Monoid.exponent G) p])
    (χ : R[K](G)) (s : G) :
    χ (pRegularComponent p s) = χ (s ^ q) := by
  -- Part `(1)` identifies the chosen `p'`-component with `s ^ q`.
  rw [pRegularComponent_eq_pow_of_modEq_exponent_parts (p := p) (q := q) hqp hqm s]

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
  -- Evaluate `f'` on each `s`, then rewrite the chosen `p'`-component using part `(1)`.
  ext s
  calc
    ([E]₀)′[p, PrimeToPRoot.toFieldLift lift] s =
        virtualModularCharacter (PrimeToPRoot.toFieldLift lift) [E]₀
          ⟨pRegularComponent p s, isPRegular_pRegularComponent s⟩ := by
            rfl
    _ = χ (pRegularComponent p s) :=
        virtualModularCharacter_apply_pRegularComponent_of_restriction
          (p := p) (lift := lift) E χ hχ s
    _ = χ (s ^ q) :=
        character_apply_pRegularComponent_eq_apply_pow (p := p) (q := q) hqp hqm χ s

end

section

variable {p q : ℕ} [Fact p.Prime]
variable {k : Type} [Field k] [IsAlgClosed k] [CharP k p]
variable {K : Type} [Field K] [CharZero K]
variable {G : Type} [Group G] [Finite G]
variable (lift : PrimeToPRoot p k →* Kˣ)

/-- Exercise 18-18.4-2 (3): if an ordinary virtual character `χ ∈ R_K(G)` restricts to the
modular character of `E` on the `p`-regular locus, then the corresponding class function `f'`
belongs to `R_K(G)`. This is Serre's deduction from part `(2)` and the stability of `R_K(G)` under
`Ψ^q`; the existence of such a `χ` is the separate Theorem 33 input in the source. -/
theorem pRegularComponent_modularCharacter_mem_characterRingOverField
    (hqpos : 0 < q)
    (hqp :
      q ≡ 0 [MOD p ^ padicValNat p (Monoid.exponent G)])
    (hqm :
      q ≡ 1 [MOD Nat.divMaxPow (Monoid.exponent G) p])
    (E : FDRep k G) (χ : R[K](G))
    (hχ :
      virtualModularCharacter (PrimeToPRoot.toFieldLift lift) [E]₀ = χ ∘ Subtype.val) :
    ([E]₀)′[p, PrimeToPRoot.toFieldLift lift] ∈ R[K](G) := by
  -- Route correction: the source does not assert this from field-only lift data.  It first chooses
  -- an ordinary virtual character `χ` restricting to the modular character, then rewrites `f'` as
  -- `Ψ^q χ`.
  let qpos : ℕ+ := ⟨q, hqpos⟩
  rw [pRegularComponentVirtualModularCharacter_eq_character_pow_of_restriction
    (p := p) (q := q) (lift := lift) hqp hqm E χ hχ]
  -- The right-hand side is the positive Adams operation on `χ`, and Chapter 9 supplies stability
  -- of the ordinary character ring under this operation.
  change Ψ^qpos((χ : G → K)) ∈ R[K](G)
  exact adamsOperator_mem_characterRingOverField (K := K) (G := G) qpos χ

end

end Representation
