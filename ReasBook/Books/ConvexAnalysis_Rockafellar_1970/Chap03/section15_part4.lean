/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section15_part3

section Chap03
section Section15

open scoped BigOperators
open scoped Pointwise
open scoped RealInnerProductSpace

/-- Epigraph of the polar gauge as a sign-flipped inner-dual cone in `H₂`. -/
lemma epigraph_polarGauge_eq_preimage_innerDualCone_H2 {n : ℕ} {k : (Fin n → ℝ) → EReal}
    (hk : IsGauge k) (xStar : Fin n → ℝ) (μ : ℝ) :
    ((xStar, μ) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarGauge k)) ↔
      (let E₂ := EuclideanSpace ℝ (Fin n)
        let H₂ := WithLp 2 (E₂ × ℝ)
        let eH := eH_transport_to_H2 n
        let σ₂ : H₂ → H₂ := fun p => WithLp.toLp 2 (- (WithLp.ofLp p).1, (WithLp.ofLp p).2)
        let S₂ : Set H₂ := eH.symm '' epigraph (S := (Set.univ : Set (Fin n → ℝ))) k
        σ₂ (eH.symm (xStar, μ)) ∈
          (ProperCone.innerDual (E := H₂) S₂ : Set H₂)) := by
  classical
  let E₂ := EuclideanSpace ℝ (Fin n)
  let H₂ := WithLp 2 (E₂ × ℝ)
  let eH := eH_transport_to_H2 n
  let σ₂ : H₂ → H₂ := fun p => WithLp.toLp 2 (- (WithLp.ofLp p).1, (WithLp.ofLp p).2)
  let S₂ : Set H₂ := eH.symm '' epigraph (S := (Set.univ : Set (Fin n → ℝ))) k
  constructor
  · intro hmem
    have hμ : polarGauge k xStar ≤ (μ : EReal) :=
      (mem_epigraph_univ_iff (f := polarGauge k) (x := xStar) (μ := μ)).1 hmem
    refine
      (ProperCone.mem_innerDual (E := H₂) (s := S₂)
          (y := σ₂ (eH.symm (xStar, μ)))).2 ?_
    intro z hz
    rcases hz with ⟨p, hp, rfl⟩
    rcases p with ⟨x, r⟩
    have hx_le : k x ≤ (r : EReal) :=
      (mem_epigraph_univ_iff (f := k) (x := x) (μ := r)).1 hp
    have hr0 : 0 ≤ r := mem_epigraph_snd_nonneg_of_isGauge (k := k) hk hp
    have hEps : ∀ ε > 0, dotProduct x xStar ≤ (μ + ε) * r := by
      intro ε hε
      have hlt : polarGauge k xStar < ((μ + ε : ℝ) : EReal) := by
        have hltμ : (μ : EReal) < ((μ + ε : ℝ) : EReal) := by
          exact (EReal.coe_lt_coe_iff).2 (by linarith)
        exact lt_of_le_of_lt hμ hltμ
      obtain ⟨μ', hμ'mem, hμ'lt⟩ := (sInf_lt_iff).1 hlt
      have hineq1 : ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ μ' * k x := hμ'mem.2 x
      have hineq2 : μ' * k x ≤ μ' * (r : EReal) :=
        mul_le_mul_of_nonneg_left hx_le hμ'mem.1
      have hineq3 :
          μ' * (r : EReal) ≤ ((μ + ε : ℝ) : EReal) * (r : EReal) := by
        have hμ'le : μ' ≤ ((μ + ε : ℝ) : EReal) := le_of_lt hμ'lt
        exact mul_le_mul_of_nonneg_right hμ'le (by exact_mod_cast hr0)
      have hineq :
          ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ ((μ + ε : ℝ) : EReal) * (r : EReal) :=
        le_trans hineq1 (le_trans hineq2 hineq3)
      have hineq' :
          ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ ((μ + ε) * r : ℝ) := by
        simpa [EReal.coe_mul, mul_comm, mul_left_comm, mul_assoc] using hineq
      exact (EReal.coe_le_coe_iff).1 hineq'
    have hdot : dotProduct x xStar ≤ μ * r :=
      le_mul_of_forall_pos_add_mul hr0 hEps
    have hinner_nonneg : 0 ≤ - dotProduct x xStar + r * μ := by
      nlinarith [hdot]
    have hinner_eq :
        inner (𝕜 := ℝ) (eH.symm (x, r)) (σ₂ (eH.symm (xStar, μ))) =
          - dotProduct x xStar + r * μ := by
      dsimp [eH, σ₂]
      exact
        (inner_eH_symm_signflip (n := n) (x := x) (xStar := xStar) (r := r) (μ := μ))
    simpa [hinner_eq] using hinner_nonneg
  · intro hmem
    have hinner : ∀ x ∈ S₂, 0 ≤ inner (𝕜 := ℝ) x (σ₂ (eH.symm (xStar, μ))) :=
      (ProperCone.mem_innerDual (E := H₂) (s := S₂) (y := σ₂ (eH.symm (xStar, μ)))).1 hmem
    have hineq : ∀ {x : Fin n → ℝ} {r : ℝ},
        (x, r) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) k →
          dotProduct x xStar ≤ μ * r := by
      intro x r hx
      have hz : eH.symm (x, r) ∈ S₂ := by
        exact ⟨(x, r), hx, rfl⟩
      have hinner0 := hinner _ hz
      have hinner_eq :
          inner (𝕜 := ℝ) (eH.symm (x, r)) (σ₂ (eH.symm (xStar, μ))) =
            - dotProduct x xStar + r * μ := by
        dsimp [eH, σ₂]
        exact
          (inner_eH_symm_signflip (n := n) (x := x) (xStar := xStar) (r := r) (μ := μ))
      have hinner_nonneg : 0 ≤ - dotProduct x xStar + r * μ := by
        simpa [hinner_eq] using hinner0
      nlinarith [hinner_nonneg]
    have hμ0 : 0 ≤ μ := by
      have h0mem : ((0 : Fin n → ℝ), (1 : ℝ)) ∈
          epigraph (S := (Set.univ : Set (Fin n → ℝ))) k := by
        have h0le : k (0 : Fin n → ℝ) ≤ (1 : EReal) := by
          simp [hk.2.2.2]
        simpa [mem_epigraph_univ_iff] using h0le
      have h0 := hineq (x := 0) (r := (1 : ℝ)) h0mem
      simp at h0
      exact h0
    have hfeas :
        ∀ ε > 0,
          0 ≤ ((μ + ε : ℝ) : EReal) ∧
            ∀ x : Fin n → ℝ,
              ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ ((μ + ε : ℝ) : EReal) * k x := by
      intro ε hε
      refine ⟨?_, ?_⟩
      · exact_mod_cast (by linarith [hμ0, hε])
      · intro x
        by_cases hkx_top : k x = ⊤
        · have hpos : 0 < ((μ + ε : ℝ) : EReal) := by
            exact_mod_cast (by linarith [hμ0, hε])
          have hmul :
              ((μ + ε : ℝ) : EReal) * k x = ⊤ := by
            simpa [hkx_top] using (EReal.mul_top_of_pos (x := ((μ + ε : ℝ) : EReal)) hpos)
          have hle : ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ ((μ + ε : ℝ) : EReal) * k x := by
            rw [hmul]
            exact le_top
          exact hle
        · have hkx_bot : k x ≠ ⊥ := IsGauge.ne_bot hk x
          set r : ℝ := (k x).toReal
          have hkx_eq : k x = (r : EReal) := by
            simpa [r] using (EReal.coe_toReal (x := k x) hkx_top hkx_bot).symm
          have hr0 : 0 ≤ r := by
            have : (0 : EReal) ≤ (r : EReal) := by
              simpa [hkx_eq] using (hk.2.1 x)
            exact (EReal.coe_le_coe_iff).1 this
          have hforall : ∀ δ > 0, dotProduct x xStar ≤ μ * (r + δ) := by
            intro δ hδ
            have hxr : (x, r + δ) ∈
                epigraph (S := (Set.univ : Set (Fin n → ℝ))) k := by
              have hle : k x ≤ ((r + δ : ℝ) : EReal) := by
                have : (r : EReal) ≤ ((r + δ : ℝ) : EReal) := by
                  exact_mod_cast (by linarith)
                simpa [hkx_eq] using this
              simpa [mem_epigraph_univ_iff] using hle
            have hineq' := hineq (x := x) (r := r + δ) hxr
            simpa [mul_comm, mul_left_comm, mul_assoc] using hineq'
          have hdot : dotProduct x xStar ≤ μ * r := by
            by_cases hμ0' : μ = 0
            · have hδ := hforall 1 (by linarith)
              simpa [hμ0'] using hδ
            · have hμpos : 0 < μ := lt_of_le_of_ne hμ0 (Ne.symm hμ0')
              refine le_of_forall_pos_le_add ?_
              intro δ hδ
              have hδpos : 0 < δ / μ := div_pos hδ hμpos
              have hδ' := hforall (δ / μ) hδpos
              have hcalc : μ * (r + δ / μ) = μ * r + δ := by
                calc
                  μ * (r + δ / μ) = μ * r + μ * (δ / μ) := by ring
                  _ = μ * r + δ := by
                        have hμne : μ ≠ 0 := ne_of_gt hμpos
                        field_simp [hμne]
              simpa [hcalc] using hδ'
          have hdot' : dotProduct x xStar ≤ (μ + ε) * r := by
            have hμle : μ ≤ μ + ε := by linarith
            have hmul : μ * r ≤ (μ + ε) * r :=
              mul_le_mul_of_nonneg_right hμle hr0
            exact le_trans hdot hmul
          have hdotE :
              ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (((μ + ε) * r : ℝ) : EReal) := by
            exact_mod_cast hdot'
          have hmulE :
              (((μ + ε) * r : ℝ) : EReal) =
                ((μ + ε : ℝ) : EReal) * k x := by
            simp [hkx_eq, EReal.coe_mul, mul_comm]
          simpa [hmulE] using hdotE
    have hle_eps :
        ∀ ε > 0, polarGauge k xStar ≤ ((μ + ε : ℝ) : EReal) := by
      intro ε hε
      exact sInf_le (hfeas ε hε)
    have htop : polarGauge k xStar ≠ ⊤ := by
      intro htop
      have hle := hle_eps 1 (by linarith)
      have hle' : (⊤ : EReal) ≤ ((μ + 1 : ℝ) : EReal) := by
        simpa [htop] using hle
      exact (not_le_of_gt (EReal.coe_lt_top (μ + 1))) hle'
    have hbot : polarGauge k xStar ≠ ⊥ := polarGauge_ne_bot (k := k) xStar
    set a : ℝ := (polarGauge k xStar).toReal
    have ha : polarGauge k xStar = (a : EReal) := by
      simpa [a] using (EReal.coe_toReal (x := polarGauge k xStar) htop hbot).symm
    have hale : a ≤ μ := by
      refine le_of_forall_pos_le_add ?_
      intro ε hε
      have hle := hle_eps ε hε
      have hle' : (a : EReal) ≤ ((μ + ε : ℝ) : EReal) := by
        simpa [ha] using hle
      exact (EReal.coe_le_coe_iff).1 hle'
    have hleE : polarGauge k xStar ≤ (μ : EReal) := by
      have hle' : (a : EReal) ≤ (μ : EReal) := (EReal.coe_le_coe_iff).2 hale
      simpa [ha] using hle'
    exact (mem_epigraph_univ_iff (f := polarGauge k) (x := xStar) (μ := μ)).2 hleE

/-- The epigraph of the polar gauge is closed. -/
lemma isClosed_epigraph_polarGauge {n : ℕ} {k : (Fin n → ℝ) → EReal} (hk : IsGauge k) :
    IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarGauge k)) := by
  classical
  let E₂ := EuclideanSpace ℝ (Fin n)
  let H₂ := WithLp 2 (E₂ × ℝ)
  let eH := eH_transport_to_H2 n
  let σ₂ : H₂ → H₂ := fun p => WithLp.toLp 2 (- (WithLp.ofLp p).1, (WithLp.ofLp p).2)
  let S₂ : Set H₂ := eH.symm '' epigraph (S := (Set.univ : Set (Fin n → ℝ))) k
  let A : Set H₂ := σ₂ ⁻¹' (ProperCone.innerDual (E := H₂) S₂ : Set H₂)
  have hAeq :
      A = (ProperCone.innerDual (E := H₂) (σ₂ ⁻¹' S₂) : Set H₂) := by
    simpa [A, E₂, H₂, σ₂] using
      (innerDual_preimage_signflip (n := n) (A := S₂)).symm
  have hAclosed : IsClosed A := by
    simpa [hAeq] using (isClosed_innerDual_H2 (n := n) (S := σ₂ ⁻¹' S₂))
  have hset :
      epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarGauge k) =
        (fun p => eH.symm p) ⁻¹' A := by
    ext p
    rcases p with ⟨xStar, μ⟩
    simpa [A, E₂, H₂, eH, σ₂, S₂] using
      (epigraph_polarGauge_eq_preimage_innerDualCone_H2 (hk := hk) (xStar := xStar) (μ := μ))
  have hpre : IsClosed ((fun p => eH.symm p) ⁻¹' A) :=
    hAclosed.preimage eH.symm.continuous
  simpa [hset] using hpre

end Section15
end Chap03
