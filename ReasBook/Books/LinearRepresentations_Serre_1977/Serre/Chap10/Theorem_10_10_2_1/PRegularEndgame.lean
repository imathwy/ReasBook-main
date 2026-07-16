import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap06.Proposition_6_6_5_1
import LinearRepresentations_Serre_1977.Serre.Chap10.Lemma_10_10_3_1
import LinearRepresentations_Serre_1977.Serre.Chap10.Lemma_10_10_3_2
import LinearRepresentations_Serre_1977.Serre.Chap10.Lemma_10_10_3_3
import LinearRepresentations_Serre_1977.Serre.FiniteToFintype

/-!
# Support file for Theorem 10-10.2-1: Serre's §10.4 endgame

This file proves, following the book's actual argument (GTM 42, §10.4, proof of
Theorem 18'), that the constant function `l` (the prime-to-`p` part of `|G|`)
lies in the cyclotomic-coefficient span `A ⊗ V_p` of Brauer's subgroup `V_p`,
where `A = integralClosure ℤ ℂ`.  The argument is:

* (Lemmas 8/9 of §10.3) build `θ ∈ A ⊗ V_p` with rational values, constant `= N`
  on the `p`-regular locus, with `p ∤ N`; the values are algebraic integers, so
  they are in fact integers;
* (Lemma 7 of §10.3) every value of `θ` is `≡ N (mod p)`, hence prime to `p`;
* (Euler) `η = θ ^ φ(pⁿ)` has integer values `≡ 1 (mod pⁿ)`;
* (Lemma 6 of §10.3) `l • (η - 1)` has integer values divisible by `g = pⁿ·l`,
  hence is an `A`-combination of characters induced from cyclic subgroups;
  cyclic groups are `p`-elementary, so `l • (η - 1) ∈ A ⊗ V_p`;
* `A ⊗ V_p` is an ideal of `A ⊗ R(G)`, so `l • η ∈ A ⊗ V_p`, and subtracting
  gives the constant `l` in `A ⊗ V_p`.

Everything is phrased for an abstract `ℤ`-submodule `W ≤ R(G)` (to be
instantiated with `V_p` inside `Theorem_10_10_2_1.lean`) satisfying the two
properties actually used: `W` is an ideal of `R(G)`, and `W` contains every
character induced from a `p`-elementary subgroup.

The file also records a **disproof** of the previously sorried statement
`pregular_indicator_mem_characterRing`: the indicator of the `p`-regular locus
is *not* a virtual character as soon as `G` has a `p`-singular element, because
by Lemma 7 its (integer) values would satisfy `0 ≡ 1 (mod p)`.
-/

noncomputable section

open scoped BigOperators Representation SubgroupInduction TensorProduct

namespace Representation

namespace Brauer18

variable {G : Type} [Group G] [Finite G]

/-- The coefficient ring of Serre's Chapter 10: the algebraic integers of `ℂ`
(the cyclotomic subring `A` embeds in it, and only integrality over `ℤ` is ever
used). -/
abbrev CoeffRing : Type := ↥(integralClosure ℤ ℂ)

/-- The ambient complex-function realization of `A ⊗ W` for a `ℤ`-submodule
`W ≤ R(G)`.  For `W = V_p` this is definitionally the local owner
`pElementaryScalarExtensionOwner` of `Theorem_10_10_2_1.lean`. -/
abbrev ownerSpan (W : Submodule ℤ (R(G))) : Submodule CoeffRing (G → ℂ) :=
  Submodule.span CoeffRing { φ : G → ℂ | ∃ β : W, φ = ((β : R(G)) : G → ℂ) }

/-- The realized span `A ⊗ W` sits inside the realized span `A ⊗ R(G)`. -/
theorem ownerSpan_le_characterRingScalarExtension (W : Submodule ℤ (R(G))) :
    ownerSpan W ≤ characterRingScalarExtension CoeffRing G := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨β, rfl⟩
  exact Submodule.subset_span (β : R(G)).property

/-- Members of the realized span `A ⊗ W` are class functions. -/
theorem isClassFunction_of_mem_ownerSpan {W : Submodule ℤ (R(G))} {φ : G → ℂ}
    (hφ : φ ∈ ownerSpan W) : _root_.IsClassFunction φ := by
  induction hφ using Submodule.span_induction with
  | mem ψ hψ =>
      rcases hψ with ⟨β, rfl⟩
      exact Representation.isClassFunction_of_mem_characterRingOverField (K := ℂ)
        ((β : R(G)) : G → ℂ) (β : R(G)).property
  | zero => exact ⟨fun x y _ ↦ rfl⟩
  | add ψ ξ _ _ h₁ h₂ =>
      exact ⟨fun x y h ↦ by
        show ψ x + ξ x = ψ y + ξ y
        rw [h₁.factorsThrough h, h₂.factorsThrough h]⟩
  | smul a ψ _ h₁ =>
      exact ⟨fun x y h ↦ by
        show a • ψ x = a • ψ y
        rw [h₁.factorsThrough h]⟩

/-- Values of virtual characters are algebraic integers (Serre §6.5). -/
theorem characterRing_value_isIntegral {χ : G → ℂ} (hχ : χ ∈ R(G)) (x : G) :
    IsIntegral ℤ (χ x) := by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hχ
  · rintro ψ ⟨ρ, hρfd, _hρirr, rfl⟩
    letI : FiniteDimensional ℂ ρ := hρfd
    exact char_isIntegral ρ.ρ x
  · intro m
    exact isIntegral_algebraMap
  · intro f g _ _ hf hg
    exact hf.add hg
  · intro f g _ _ hf hg
    exact hf.mul hg

/-- Values of members of the realized span `A ⊗ W` are algebraic integers. -/
theorem value_isIntegral_of_mem_ownerSpan {W : Submodule ℤ (R(G))} {φ : G → ℂ}
    (hφ : φ ∈ ownerSpan W) (x : G) : IsIntegral ℤ (φ x) := by
  induction hφ using Submodule.span_induction with
  | mem ψ hψ =>
      rcases hψ with ⟨β, rfl⟩
      exact characterRing_value_isIntegral (β : R(G)).property x
  | zero => exact isIntegral_zero
  | add ψ ξ _ _ h₁ h₂ => exact h₁.add h₂
  | smul a ψ _ h₁ =>
      have ha : IsIntegral ℤ ((a : ℂ)) := a.2
      have hval : (a • ψ) x = (a : ℂ) * ψ x := by
        simp [Pi.smul_apply, Algebra.smul_def]
      rw [hval]
      exact ha.mul h₁

/-- A rational algebraic integer is an integer (`ℚ ∩ A = ℤ`, Serre §6.4). -/
theorem exists_int_value {z : ℂ} (hq : ∃ q : ℚ, z = (q : ℂ)) (hz : IsIntegral ℤ z) :
    ∃ m : ℤ, z = (m : ℂ) := by
  rcases hq with ⟨q, rfl⟩
  have hzq : IsIntegral ℤ q := by
    rw [show ((q : ℂ)) = algebraMap ℚ ℂ q from (eq_ratCast (algebraMap ℚ ℂ) q).symm,
      isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective] at hz
    exact hz
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hzq
  refine ⟨m, ?_⟩
  have hqm : q = (m : ℚ) := by rw [← hm]; simp
  rw [hqm]
  push_cast
  rfl

/-- The induced class function of an integer-valued function has rational
values. -/
theorem inducedClassFunction_value_rat {H : Subgroup G} {f : H → ℂ}
    (hf : ∀ h : H, ∃ m : ℤ, f h = (m : ℂ)) (g : G) :
    ∃ q : ℚ, Ind[H](f) g = (q : ℂ) := by
  classical
  have hterm : ∀ s : G, ∃ m : ℤ,
      (if hsg : s⁻¹ * g * s ∈ H then f ⟨s⁻¹ * g * s, hsg⟩ else 0) = (m : ℂ) := by
    intro s
    by_cases hsg : s⁻¹ * g * s ∈ H
    · obtain ⟨m, hm⟩ := hf ⟨s⁻¹ * g * s, hsg⟩
      exact ⟨m, by rw [dif_pos hsg, hm]⟩
    · exact ⟨0, by rw [dif_neg hsg]; simp⟩
  choose m hm using hterm
  refine ⟨(Nat.card H : ℚ)⁻¹ * ((∑ s : G, m s : ℤ) : ℚ), ?_⟩
  simp only [Subgroup.inducedClassFunction]
  rw [Finset.sum_congr rfl fun s _ => hm s]
  push_cast
  ring

/-- A tensor character induced from a subgroup whose induced characters lie in
`W` lands in the realized span `A ⊗ W`. -/
theorem induced_tensor_mem_ownerSpan {W : Submodule ℤ (R(G))} {H : Subgroup G}
    (hmem : ∀ χ : R(H), H.characterRingInduction χ ∈ W)
    (ψ : CoeffRing ⊗R(H)) :
    Ind[H]((ψ : H → ℂ)) ∈ ownerSpan W := by
  induction ψ using TensorProduct.induction_on with
  | zero =>
      have h0 : ((0 : CoeffRing ⊗R(H)) : H → ℂ) = (0 : H → ℂ) := by
        simp
      have hzero : Ind[H]((0 : H → ℂ)) = (0 : G → ℂ) := by
        ext g
        simp [Subgroup.inducedClassFunction]
      rw [h0, hzero]
      exact (ownerSpan W).zero_mem
  | tmul a χ =>
      have hcoe : ((a ⊗ₜ[ℤ] χ : CoeffRing ⊗R(H)) : H → ℂ) = a • (χ : H → ℂ) := rfl
      have hsmul : Ind[H]((a • (χ : H → ℂ))) = a • Ind[H]((χ : H → ℂ)) :=
        Subgroup.inducedClassFunction_map_smul H a (χ : H → ℂ)
      rw [hcoe, hsmul]
      refine (ownerSpan W).smul_mem a ?_
      exact Submodule.subset_span ⟨⟨H.characterRingInduction χ, hmem χ⟩, rfl⟩
  | add ψ₁ ψ₂ h₁ h₂ =>
      have hadd :
          Ind[H](((ψ₁ : H → ℂ) + (ψ₂ : H → ℂ))) =
            (Ind[H]((ψ₁ : H → ℂ)) : G → ℂ) + Ind[H]((ψ₂ : H → ℂ)) :=
        Subgroup.inducedClassFunction_map_add H (ψ₁ : H → ℂ) (ψ₂ : H → ℂ)
      rw [map_add, hadd]
      exact (ownerSpan W).add_mem h₁ h₂

section Provider

variable {p : ℕ} [Fact p.Prime]

/-- A concrete representative of a conjugacy class. -/
private def rep (c : ConjClasses G) : G :=
  Classical.choose (ConjClasses.mk_surjective c)

private theorem rep_mk (c : ConjClasses G) : ConjClasses.mk (rep c) = c :=
  Classical.choose_spec (ConjClasses.mk_surjective c)

/-- Lemma 8 of §10.3, packaged on the level of realized functions: each
`p`-regular class carries a function in `A ⊗ W` with rational values, value an
integer prime to `p` on the class, vanishing on the other `p`-regular classes. -/
theorem exists_auxiliary_function_on_pregular_class
    {W : Submodule ℤ (R(G))}
    (hpel : ∀ K : Subgroup G, IsPElementary p K → ∀ χ : R(K), K.characterRingInduction χ ∈ W)
    {x : G} (hx : IsPRegular p x) :
    ∃ β : G → ℂ, ∃ n : ℤ,
      β ∈ ownerSpan W ∧
      (∀ s : G, ∃ q : ℚ, β s = (q : ℂ)) ∧
      (β x = (n : ℂ) ∧ ¬ (p : ℤ) ∣ n) ∧
      (∀ s : G, IsPRegular p s → ¬ IsConj s x → β s = 0) := by
  classical
  let P : Sylow p (Subgroup.centralizer ({x} : Set G)) :=
    Classical.choice (Sylow.nonempty (p := p) (G := Subgroup.centralizer ({x} : Set G)))
  have hH : IsPElementary p (associatedPElementarySubgroup p x P) :=
    associatedPElementarySubgroup_isPElementary (p := p) x hx P
  obtain ⟨ψ, hψint, ⟨n, hnx, hndiv⟩, hψzero⟩ :=
    exists_associated_auxiliary_character_with_brauer_induction_support
      (p := p) (x := x) P hx
  refine ⟨Ind[associatedPElementarySubgroup p x P]((ψ : associatedPElementarySubgroup p x P → ℂ)),
    n, ?_, ?_, ⟨hnx, hndiv⟩, hψzero⟩
  · exact induced_tensor_mem_ownerSpan (fun χ => hpel _ hH χ) ψ
  · intro s
    exact inducedClassFunction_value_rat hψint s

/-- Lemma 9 of §10.3, strengthened: there is a function `θ ∈ A ⊗ W` with
rational values which is the constant `N` on the whole `p`-regular locus,
where `N` is a positive integer prime to `p`. -/
theorem exists_constant_pregular_integer_function
    {W : Submodule ℤ (R(G))}
    (hpel : ∀ K : Subgroup G, IsPElementary p K → ∀ χ : R(K), K.characterRingInduction χ ∈ W) :
    ∃ N : ℕ, Nat.Coprime p N ∧
      ∃ θ : G → ℂ, θ ∈ ownerSpan W ∧
        (∀ s : G, ∃ q : ℚ, θ s = (q : ℂ)) ∧
        ∀ s : G, IsPRegular p s → θ s = (N : ℂ) := by
  classical
  let C : Type := { c : ConjClasses G // IsPRegular p (rep c) }
  letI : Fintype C := Fintype.ofFinite C
  have haux :
      ∀ c : C, ∃ β : G → ℂ, ∃ n : ℤ,
        β ∈ ownerSpan W ∧
        (∀ s : G, ∃ q : ℚ, β s = (q : ℂ)) ∧
        (β (rep c.1) = (n : ℂ) ∧ ¬ (p : ℤ) ∣ n) ∧
        (∀ s : G, IsPRegular p s → ¬ IsConj s (rep c.1) → β s = 0) := fun c =>
    exists_auxiliary_function_on_pregular_class hpel c.2
  choose β n hβmem hβrat hβval hβzero using haux
  let N : ℕ := ∏ c : C, (n c).natAbs
  let coeff : C → ℤ := fun c ↦
    ((Finset.prod ((Finset.univ : Finset C).erase c) fun d : C ↦ (n d).natAbs : ℕ) : ℤ) *
      Int.sign (n c)
  let θ : G → ℂ := ∑ c : C, coeff c • β c
  have hNcoprime : Nat.Coprime p N := by
    change Nat.Coprime p (∏ c : C, (n c).natAbs)
    refine (Nat.coprime_prod_right_iff).2 ?_
    intro c _
    refine ((Fact.out : p.Prime).coprime_iff_not_dvd).2 ?_
    intro hpdiv
    exact (hβval c).2 (Int.natCast_dvd.2 hpdiv)
  refine ⟨N, hNcoprime, θ, ?_, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun c _ => zsmul_mem (hβmem c) (coeff c)
  · intro s
    have hterm : ∀ c : C, ∃ q : ℚ, (coeff c • β c) s = (q : ℂ) := by
      intro c
      obtain ⟨q, hq⟩ := hβrat c s
      refine ⟨(coeff c : ℚ) * q, ?_⟩
      rw [Pi.smul_apply, zsmul_eq_mul, hq]
      push_cast
      ring
    choose qs hqs using hterm
    refine ⟨∑ c : C, qs c, ?_⟩
    rw [show θ s = ∑ c : C, (coeff c • β c) s from Finset.sum_apply s Finset.univ _,
      Finset.sum_congr rfl fun c _ => hqs c]
    push_cast
    rfl
  · intro s hs
    have hsrep : IsPRegular p (rep (ConjClasses.mk s)) := by
      have hconj : IsConj s (rep (ConjClasses.mk s)) := by
        apply ConjClasses.mk_eq_mk_iff_isConj.mp
        simpa using (rep_mk (G := G) (ConjClasses.mk s)).symm
      rcases isConj_iff.1 hconj with ⟨t, ht⟩
      simpa [ht, mul_assoc] using isPRegular_conj (p := p) s t hs
    let c₀ : C := ⟨ConjClasses.mk s, hsrep⟩
    have hβsame : (β c₀) s = (n c₀ : ℂ) := by
      have hβclass : _root_.IsClassFunction (β c₀) :=
        isClassFunction_of_mem_ownerSpan (hβmem c₀)
      have hconj : IsConj s (rep c₀.1) := by
        apply ConjClasses.mk_eq_mk_iff_isConj.mp
        simpa [c₀] using (rep_mk (G := G) (ConjClasses.mk s)).symm
      calc
        (β c₀) s = (β c₀) (rep c₀.1) := _root_.IsClassFunction.eq_of_isConj hβclass hconj
        _ = (n c₀ : ℂ) := (hβval c₀).1
    have hcoeffprod : coeff c₀ * n c₀ = N := by
      simp only [coeff, N]
      rw [mul_assoc, Int.sign_mul_self_eq_natAbs, ← Int.natCast_mul]
      exact congrArg (fun m : ℕ ↦ (m : ℤ))
        (Finset.prod_erase_mul (s := Finset.univ) (f := fun c : C ↦ (n c).natAbs) (by simp))
    have hcoeffprodC : ((coeff c₀ : ℤ) : ℂ) * (n c₀ : ℂ) = (N : ℂ) := by
      exact_mod_cast hcoeffprod
    calc
      θ s = ∑ c : C, (((coeff c : ℤ) : ℂ) * (β c) s) := by
        rw [show θ s = ∑ c : C, (coeff c • β c) s from Finset.sum_apply s Finset.univ _]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Pi.smul_apply, zsmul_eq_mul]
      _ = (((coeff c₀ : ℤ) : ℂ) * (β c₀) s) := by
        refine Finset.sum_eq_single c₀ ?_ ?_
        · intro c _ hne
          have hs_not_conj : ¬ IsConj s (rep c.1) := by
            intro hsconj
            apply hne
            apply Subtype.ext
            simpa [c₀, rep_mk (G := G) c.1] using
              (ConjClasses.mk_eq_mk_iff_isConj.2 hsconj).symm
          simp [hβzero c s hs hs_not_conj]
        · intro hc₀
          exact False.elim (hc₀ (by simp))
      _ = (((coeff c₀ : ℤ) : ℂ) * (n c₀ : ℂ)) := by rw [hβsame]
      _ = (N : ℂ) := hcoeffprodC

end Provider

/-- Euler's theorem in the needed form: if `p ∤ k` then
`pⁿ ∣ k ^ φ(pⁿ) - 1`. -/
theorem int_pow_totient_sub_one_dvd {p : ℕ} (hp : p.Prime) (n : ℕ) {k : ℤ}
    (hk : ¬ (p : ℤ) ∣ k) :
    ((p : ℤ) ^ n) ∣ k ^ (Nat.totient (p ^ n)) - 1 := by
  have hpZ : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hp
  have hcop : IsCoprime ((p : ℤ) ^ n) k :=
    ((hpZ.coprime_iff_not_dvd).2 hk).pow_left
  have hunit : IsUnit ((k : ZMod (p ^ n))) := by
    obtain ⟨a, b, hab⟩ := hcop
    refine IsUnit.of_mul_eq_one ((b : ZMod (p ^ n))) ?_
    have hcast := congrArg (fun z : ℤ => ((z : ZMod (p ^ n)))) hab
    push_cast at hcast
    have hzero : ((p : ZMod (p ^ n))) ^ n = 0 := by
      have : (((p ^ n : ℕ)) : ZMod (p ^ n)) = 0 := ZMod.natCast_self (p ^ n)
      push_cast at this
      exact this
    rw [hzero, mul_zero, zero_add] at hcast
    rw [mul_comm] at hcast
    exact hcast
  obtain ⟨u, hu⟩ := hunit
  have hpow : ((k : ZMod (p ^ n))) ^ (Nat.totient (p ^ n)) = 1 := by
    rw [← hu, ← Units.val_pow_eq_pow_val, ZMod.pow_totient u, Units.val_one]
  have hzero : ((k ^ (Nat.totient (p ^ n)) - 1 : ℤ) : ZMod (p ^ n)) = 0 := by
    push_cast
    rw [hpow]
    ring
  have hdvd : ((p ^ n : ℕ) : ℤ) ∣ k ^ (Nat.totient (p ^ n)) - 1 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hzero
  exact_mod_cast hdvd

/-- Every finite cyclic group is `p`-elementary (its `p`-part and prime-to-`p`
part decompose it as required). -/
theorem isPElementary_of_isCyclic {p : ℕ} (hp : p.Prime) (H : Type) [Group H] [Finite H]
    (hH : IsCyclic H) : IsPElementary p H := by
  obtain ⟨x, hx⟩ := hH.exists_generator
  have hcard0 : Nat.card H ≠ 0 := Nat.card_pos.ne'
  set a := (Nat.card H).factorization p with ha
  set m := ordCompl[p] (Nat.card H) with hm
  have hmpos : 0 < m := Nat.ordCompl_pos p hcard0
  have hcard : p ^ a * m = Nat.card H := Nat.ordProj_mul_ordCompl_eq_self (Nat.card H) p
  have hxord : orderOf x = Nat.card H := orderOf_eq_card_of_forall_mem_zpowers hx
  have hCcard : Nat.card (Subgroup.zpowers (x ^ (p ^ a))) = m := by
    rw [Nat.card_zpowers, orderOf_pow, hxord, ← hcard]
    have hg : Nat.gcd (p ^ a * m) (p ^ a) = p ^ a := by
      rw [Nat.gcd_comm]
      exact Nat.gcd_eq_left (dvd_mul_right _ _)
    rw [hg]
    exact Nat.mul_div_cancel_left m (pow_pos hp.pos a)
  have hPcard : Nat.card (Subgroup.zpowers (x ^ m)) = p ^ a := by
    rw [Nat.card_zpowers, orderOf_pow, hxord, ← hcard]
    have hg : Nat.gcd (p ^ a * m) m = m := by
      rw [Nat.gcd_comm]
      exact Nat.gcd_eq_left (dvd_mul_left _ _)
    rw [hg]
    exact Nat.mul_div_cancel _ hmpos
  refine ⟨Subgroup.zpowers (x ^ (p ^ a)), Subgroup.zpowers (x ^ m), hp, inferInstance,
    inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [hCcard]
    exact Nat.coprime_ordCompl hp hcard0
  · exact IsPGroup.of_card hPcard
  · intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (((Commute.refl x).pow_pow m (p ^ a)).zpow_zpow j i).eq
  · refine Subgroup.isComplement'_of_coprime ?_ ?_
    · rw [hCcard, hPcard, mul_comm]
      exact hcard
    · rw [hCcard, hPcard]
      exact ((Nat.coprime_ordCompl hp hcard0).symm).pow_right a

/-- Lemma 6 transit: the cyclic induced-character span lands in `A ⊗ W` as soon
as `W` contains all characters induced from `p`-elementary subgroups. -/
theorem cyclicInducedCharacterSpan_le_ownerSpan {p : ℕ} (hp : p.Prime)
    {W : Submodule ℤ (R(G))}
    (hpel : ∀ K : Subgroup G, IsPElementary p K → ∀ χ : R(K), K.characterRingInduction χ ∈ W) :
    cyclicInducedCharacterSpan CoeffRing G ≤ ownerSpan W := by
  rw [cyclicInducedCharacterSpan]
  refine Submodule.span_le.2 ?_
  rintro φ ⟨χ, hχ, rfl⟩
  have hle : cyclicInducedCharacterSubmodule G ≤ W := by
    refine iSup_le ?_
    rintro ⟨H, hHmem⟩
    rintro ξ hξ
    obtain ⟨ψ, rfl⟩ := hξ
    exact hpel H (isPElementary_of_isCyclic hp H (Subgroup.mem_cyclicSubgroups.1 hHmem)) ψ
  exact Submodule.subset_span ⟨⟨χ, hle hχ⟩, rfl⟩

/-- `A ⊗ W` is an ideal of `A ⊗ R(G)` whenever `W` is an ideal of `R(G)`. -/
theorem mul_mem_ownerSpan {W : Submodule ℤ (R(G))}
    (hmul : ∀ (χ : R(G)) ⦃ψ : R(G)⦄, ψ ∈ W → χ * ψ ∈ W)
    {φ ξ : G → ℂ} (hφ : φ ∈ characterRingScalarExtension CoeffRing G)
    (hξ : ξ ∈ ownerSpan W) :
    φ * ξ ∈ ownerSpan W := by
  induction hφ using Submodule.span_induction with
  | mem χ hχ =>
      induction hξ using Submodule.span_induction with
      | mem ψ hψ =>
          rcases hψ with ⟨β, rfl⟩
          refine Submodule.subset_span ?_
          exact ⟨⟨(⟨χ, hχ⟩ : R(G)) * (β : R(G)), hmul _ β.2⟩, rfl⟩
      | zero => simpa using (ownerSpan W).zero_mem
      | add ξ₁ ξ₂ _ _ h₁ h₂ => simpa [mul_add] using (ownerSpan W).add_mem h₁ h₂
      | smul a ξ' _ h₁ => simpa [mul_smul_comm] using (ownerSpan W).smul_mem a h₁
  | zero => simpa using (ownerSpan W).zero_mem
  | add φ₁ φ₂ _ _ h₁ h₂ => simpa [add_mul] using (ownerSpan W).add_mem h₁ h₂
  | smul a φ' _ h₁ => simpa [smul_mul_assoc] using (ownerSpan W).smul_mem a h₁

/-- Positive powers stay in the ideal `A ⊗ W`. -/
theorem pow_mem_ownerSpan {W : Submodule ℤ (R(G))}
    (hmul : ∀ (χ : R(G)) ⦃ψ : R(G)⦄, ψ ∈ W → χ * ψ ∈ W)
    {θ : G → ℂ} (hθ : θ ∈ ownerSpan W) (M : ℕ) (hM : M ≠ 0) :
    θ ^ M ∈ ownerSpan W := by
  induction M with
  | zero => exact absurd rfl hM
  | succ M ih =>
      rcases Nat.eq_zero_or_pos M with hM0 | hMpos
      · subst hM0
        simpa [pow_one] using hθ
      · have hθext : θ ∈ characterRingScalarExtension CoeffRing G :=
          ownerSpan_le_characterRingScalarExtension W hθ
        have hstep := mul_mem_ownerSpan hmul hθext (ih hMpos.ne')
        rw [pow_succ]
        rw [mul_comm]
        exact hstep

/-- **Serre's Theorem 18' over `A` (GTM 42, §10.4).**  If `|G| = pⁿ·l` with
`(p, l) = 1`, `W ≤ R(G)` is an ideal of `R(G)`, and `W` contains every
character induced from a `p`-elementary subgroup, then the constant function
`l` lies in the realized span `A ⊗ W`. -/
theorem const_primeToPart_mem_ownerSpan
    (W : Submodule ℤ (R(G))) (p : ℕ) [Fact p.Prime] (n l : ℕ)
    (hcard : Nat.card G = p ^ n * l)
    (hmul : ∀ (χ : R(G)) ⦃ψ : R(G)⦄, ψ ∈ W → χ * ψ ∈ W)
    (hpel : ∀ K : Subgroup G, IsPElementary p K → ∀ χ : R(K), K.characterRingInduction χ ∈ W) :
    (fun _ : G ↦ (l : ℂ)) ∈ ownerSpan W := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨N, hNcop, θ, hθmem, hθrat, hθreg⟩ :=
    exists_constant_pregular_integer_function (p := p) hpel
  -- the values of `θ` are integers (rational algebraic integers)
  have hθint : ∀ s : G, ∃ m : ℤ, θ s = (m : ℂ) := fun s =>
    exists_int_value (hθrat s) (value_isIntegral_of_mem_ownerSpan hθmem s)
  choose k hk using hθint
  -- Lemma 7: every value is `≡ N (mod p)`, hence prime to `p`
  have hkndvd : ∀ s : G, ¬ (p : ℤ) ∣ k s := by
    intro s hdvd
    have hχmem : θ ∈ characterRingScalarExtension CoeffRing G :=
      ownerSpan_le_characterRingScalarExtension W hθmem
    have hreg : IsPRegular p (pRegularComponent p s) :=
      isPRegular_pRegularComponent (p := p) s
    have hmod : k s ≡ (N : ℤ) [ZMOD p] :=
      integerValued_character_modEq_pRegularComponent_of_mem_characterRingScalarExtension
        (A := CoeffRing) ⟨θ, hχmem⟩ (fun g => ⟨k g, hk g⟩) s (k s) (N : ℤ) (hk s)
        (by
          show θ (pRegularComponent p s) = ((N : ℤ) : ℂ)
          rw [hθreg _ hreg]
          push_cast
          rfl)
    have hNdvd : (p : ℤ) ∣ (N : ℤ) := by
      have hsub : (p : ℤ) ∣ (N : ℤ) - k s := Int.ModEq.dvd hmod
      have := dvd_add hsub hdvd
      simpa using this
    have : (p : ℕ) ∣ N := Int.natCast_dvd_natCast.mp hNdvd
    exact (hp.coprime_iff_not_dvd.1 hNcop) this
  -- Euler: `η = θ^φ(pⁿ)` has integer values `≡ 1 (mod pⁿ)`
  set M := Nat.totient (p ^ n) with hMdef
  have hMne : M ≠ 0 := by
    have : 0 < Nat.totient (p ^ n) := Nat.totient_pos.2 (pow_pos hp.pos n)
    omega
  set η := θ ^ M with hηdef
  have hηmem : η ∈ ownerSpan W := pow_mem_ownerSpan hmul hθmem M hMne
  have hηval : ∀ s : G, η s = ((k s ^ M : ℤ) : ℂ) := by
    intro s
    rw [hηdef, Pi.pow_apply, hk s]
    push_cast
    ring
  have hηmod : ∀ s : G, ((p : ℤ) ^ n) ∣ k s ^ M - 1 := fun s =>
    int_pow_totient_sub_one_dvd hp n (hkndvd s)
  -- Lemma 6: `l•(η - 1)` has integer values divisible by `|G|`
  set f : G → ℂ := (l : ℂ) • η - (l : ℂ) • (1 : G → ℂ) with hfdef
  have hfval : ∀ x : G, f x = (l : ℂ) * ((k x ^ M : ℤ) : ℂ) - (l : ℂ) := by
    intro x
    rw [hfdef]
    simp [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, hηval x]
  have hfdiv : ∀ x : G, ∃ t : ℤ, f x = ((Nat.card G : ℤ) * t : ℂ) := by
    intro x
    obtain ⟨t, ht⟩ := hηmod x
    refine ⟨t, ?_⟩
    have htC : ((k x ^ M - 1 : ℤ) : ℂ) = ((p : ℂ) ^ n) * (t : ℂ) := by
      rw [ht]
      push_cast
      ring
    rw [hfval x, hcard]
    calc
      (l : ℂ) * ((k x ^ M : ℤ) : ℂ) - (l : ℂ)
          = (l : ℂ) * ((k x ^ M - 1 : ℤ) : ℂ) := by push_cast; ring
      _ = (l : ℂ) * (((p : ℂ) ^ n) * (t : ℂ)) := by rw [htC]
      _ = (((p ^ n * l : ℕ) : ℤ) : ℂ) * (t : ℂ) := by push_cast; ring
  have hηclass : _root_.IsClassFunction η := isClassFunction_of_mem_ownerSpan hηmem
  have hfclass : _root_.IsClassFunction f := by
    refine ⟨fun x y h => ?_⟩
    show (l : ℂ) • η x - (l : ℂ) • (1 : ℂ) = (l : ℂ) • η y - (l : ℂ) • (1 : ℂ)
    rw [hηclass.factorsThrough h]
  have h6 : f ∈ cyclicInducedCharacterSpan CoeffRing G :=
    classFunction_mem_cyclicInducedCharacterSpan_of_groupOrder_dvd_values
      (A := CoeffRing) ⟨f, (_root_.mem_classFunctionSubspace_iff f).2 hfclass⟩ hfdiv
  have hfmem : f ∈ ownerSpan W := cyclicInducedCharacterSpan_le_ownerSpan hp hpel h6
  -- ideal property: `l•η ∈ A ⊗ W`; subtract
  have hlη : (l : ℂ) • η ∈ ownerSpan W := by
    have hnsmul : l • η ∈ ownerSpan W := nsmul_mem hηmem l
    rwa [← Nat.cast_smul_eq_nsmul ℂ l η] at hnsmul
  have hconst : (fun _ : G ↦ (l : ℂ)) = (l : ℂ) • η - f := by
    rw [hfdef]
    ext s
    simp
  rw [hconst]
  exact (ownerSpan W).sub_mem hlη hfmem

/-- **Disproof of the sorried statement `pregular_indicator_mem_characterRing`.**
If `G` has any element that is not `p`-regular (equivalently, `p ∣ |G|`), the
indicator of the `p`-regular locus is *not* a virtual character: by Lemma 7 of
§10.3 its integer values would satisfy `0 ≡ 1 (mod p)`. -/
theorem pregular_indicator_not_mem_characterRing
    {p : ℕ} [Fact p.Prime] {s₀ : G} (hs₀ : ¬ IsPRegular p s₀) :
    (fun s : G ↦ if IsPRegular p s then (1 : ℂ) else 0) ∉ R(G) := by
  classical
  intro hmem
  set χ : G → ℂ := fun s => if IsPRegular p s then (1 : ℂ) else 0 with hχdef
  have hmem' : χ ∈ characterRingScalarExtension CoeffRing G :=
    mem_characterRingScalarExtension_of_mem_characterRing χ hmem
  have hInt : ∀ g : G, ∃ m : ℤ, χ g = (m : ℂ) := by
    intro g
    by_cases h : IsPRegular p g
    · exact ⟨1, by simp [hχdef, h]⟩
    · exact ⟨0, by simp [hχdef, h]⟩
  have hmod : (0 : ℤ) ≡ (1 : ℤ) [ZMOD p] :=
    integerValued_character_modEq_pRegularComponent_of_mem_characterRingScalarExtension
      (A := CoeffRing) ⟨χ, hmem'⟩ hInt s₀ 0 1
      (by
        show χ s₀ = ((0 : ℤ) : ℂ)
        simp [hχdef, hs₀])
      (by
        show χ (pRegularComponent p s₀) = ((1 : ℤ) : ℂ)
        simp [hχdef, isPRegular_pRegularComponent (p := p) s₀])
  have hdvd : (p : ℤ) ∣ 1 := by simpa using hmod.dvd
  have hdvd' : p ∣ 1 := by exact_mod_cast hdvd
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp hdvd')

end Brauer18

end Representation
