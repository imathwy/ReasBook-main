import Mathlib
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_1
noncomputable section
universe u
namespace Representation
open scoped MonoidAlgebra
section
variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [Finite G]

-- helper: orderOf (g^q) = m
private lemma orderOf_pow_eq_aux (g : G) (q m : ℕ) (hq : q ≠ 0)
    (hqm : q * m = orderOf g) : orderOf ((g : G) ^ q) = m := by
  have hqdvd : q ∣ orderOf g := ⟨m, hqm.symm⟩
  rw [orderOf_pow_of_dvd hq hqdvd, ← hqm, Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hq)]

private lemma zpow_mul_mem_zpowers (g : G) (q : ℕ) (b : ℤ) :
    (g : G) ^ ((q : ℤ) * b) ∈ Subgroup.zpowers ((g : G) ^ q) := by
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨b, by rw [← zpow_natCast ((g:G)) q, ← zpow_mul]⟩

theorem exists_pRegular_pElement_decomp (g : G) (hg : ¬ IsPRegular p g) :
    ∃ s u : G, s * u = g ∧ Commute s u ∧ IsPRegular p s ∧ IsPElement p u ∧ u ≠ 1 := by
  classical
  have hpprime : p.Prime := Fact.out
  have hpdvd : p ∣ orderOf g := by
    by_contra h
    exact hg ((isPRegular_iff_not_dvd_orderOf (p := p) g).2 h)
  have hn0 : orderOf g ≠ 0 := by
    rintro h
    exact absurd (orderOf_eq_zero_iff.mp h) (not_not.mpr (isOfFinOrder_of_finite g))
  set q := ordProj[p] (orderOf g) with hq
  set m := ordCompl[p] (orderOf g) with hm
  have hqm : q * m = orderOf g := Nat.ordProj_mul_ordCompl_eq_self (orderOf g) p
  have hq0 : q ≠ 0 := pow_ne_zero _ hpprime.pos.ne'
  have hm0 : m ≠ 0 := (Nat.ordCompl_pos p hn0).ne'
  have hcop_pm : Nat.Coprime p m := Nat.coprime_ordCompl hpprime hn0
  have hcop_qm : Nat.Coprime q m := hcop_pm.pow_left _
  have ha1 : 1 ≤ (orderOf g).factorization p :=
    Nat.Prime.factorization_pos_of_dvd hpprime hn0 hpdvd
  have hbez : (q : ℤ) * Nat.gcdA q m + (m : ℤ) * Nat.gcdB q m = 1 := by
    have := Nat.gcd_eq_gcd_ab q m
    rw [hcop_qm.gcd_eq_one] at this
    push_cast at this ⊢
    linarith [this]
  set b := Nat.gcdA q m with hb
  set c := Nat.gcdB q m with hc
  have horder_gq : orderOf ((g : G) ^ q) = m := orderOf_pow_eq_aux g q m hq0 hqm
  have horder_gm : orderOf ((g : G) ^ m) = q :=
    orderOf_pow_eq_aux g m q hm0 (by rw [mul_comm]; exact hqm)
  have hsumeq : (q : ℤ) * b + (m : ℤ) * c = 1 := by linarith [hbez]
  refine ⟨(g : G) ^ ((q : ℤ) * b), (g : G) ^ ((m : ℤ) * c), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← zpow_add, hsumeq]; simp
  · exact (Commute.refl g).zpow_zpow _ _
  · -- IsPRegular p (g^(qb)) : orderOf ∣ m, p ∤ m
    have hdvd : orderOf ((g : G) ^ ((q : ℤ) * b)) ∣ m := by
      rw [← horder_gq]; exact orderOf_dvd_of_mem_zpowers (zpow_mul_mem_zpowers g q b)
    rw [isPRegular_iff_not_dvd_orderOf]
    intro hp
    exact (Nat.Prime.coprime_iff_not_dvd hpprime).1 hcop_pm (hp.trans hdvd)
  · -- IsPElement p (g^(mc)) : orderOf ∣ q = p^a
    have hdvd : orderOf ((g : G) ^ ((m : ℤ) * c)) ∣ q := by
      rw [← horder_gm]; exact orderOf_dvd_of_mem_zpowers (zpow_mul_mem_zpowers g m c)
    rw [hq] at hdvd
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hpprime).1 hdvd
    exact ⟨k, hk⟩
  · -- u ≠ 1
    intro hu
    apply hg
    have hgs : g = (g : G) ^ ((q : ℤ) * b) := by
      have h1 : (g : G) ^ ((q : ℤ) * b) * (g : G) ^ ((m : ℤ) * c) = g := by
        rw [← zpow_add, hsumeq]; simp
      rw [hu, mul_one] at h1; exact h1.symm
    have hdvd : orderOf ((g : G) ^ ((q : ℤ) * b)) ∣ m := by
      rw [← horder_gq]; exact orderOf_dvd_of_mem_zpowers (zpow_mul_mem_zpowers g q b)
    rw [isPRegular_iff_not_dvd_orderOf]
    intro hp
    rw [hgs] at hp
    exact (Nat.Prime.coprime_iff_not_dvd hpprime).1 hcop_pm (hp.trans hdvd)

end
end Representation
