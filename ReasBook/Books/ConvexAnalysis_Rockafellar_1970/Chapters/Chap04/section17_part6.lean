/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yunfei Zhang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section17_part5

open scoped BigOperators Pointwise
open Topology

section Chap04
section Section17

/-- Expand `rightScalarMultiple` of a convex-hull family into scaled convex-combination data. -/
lemma rightScalarMultiple_convexHullFamily_eq_sInf_scaled_affineIndependent
    {n : Nat} {ι : Type*} {fᵢ : ι → (Fin n → Real) → EReal}
    (hf : ∀ i, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (fᵢ i))
    {lam : Real} (hlam : 0 < lam) (x : Fin n → Real) :
    rightScalarMultiple (convexHullFunctionFamily fᵢ) lam x =
      sInf { z : EReal |
        ∃ m : Nat, m ≤ n + 1 ∧
          ∃ (idx : Fin m → ι) (p : Fin m → Fin n → Real) (w : Fin m → Real),
            IsConvexWeights m w ∧
              (∀ j, w j ≠ 0) ∧
              x = ∑ j, (lam * w j) • p j ∧
              AffineIndependent ℝ p ∧
              z = ∑ j, ((lam * w j : Real) : EReal) * fᵢ (idx j) (p j) } := by
  classical
  let g := convexHullFunctionFamily fᵢ
  have hconv :
      ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) g := by
    simpa [g] using (convexHullFunctionFamily_greatest_convex_minorant (f := fᵢ)).1
  have hpos :
      rightScalarMultiple g lam x = (lam : EReal) * g (lam⁻¹ • x) :=
    rightScalarMultiple_pos (f := g) hconv hlam x
  let B : Set EReal :=
    { z : EReal |
      ∃ m : Nat, m ≤ n + 1 ∧
        ∃ (idx : Fin m → ι) (p : Fin m → Fin n → Real) (w : Fin m → Real),
          IsConvexWeights m w ∧
            (∀ j, w j ≠ 0) ∧
            lam⁻¹ • x = convexCombination n m p w ∧
            AffineIndependent ℝ p ∧
            z = ∑ j, ((w j : Real) : EReal) * fᵢ (idx j) (p j) }
  have hB : g (lam⁻¹ • x) = sInf B := by
    simpa [g, B] using
      (convexHullFunctionFamily_eq_sInf_affineIndependent_convexCombination_le_add_one
        (f := fᵢ) (hf := hf) (x := lam⁻¹ • x))
  have hmap :
      (lam : EReal) * sInf B = sInf ((fun z : EReal => (lam : EReal) * z) '' B) := by
    have hmap' :
        (lam : EReal) * sInf B = ⨅ z ∈ B, (lam : EReal) * z := by
      have hmap' := OrderIso.map_sInf (ereal_mulPosOrderIso (t := lam) hlam) B
      dsimp [ereal_mulPosOrderIso] at hmap'
      simpa using hmap'
    have hmap'' :
        sInf ((fun z : EReal => (lam : EReal) * z) '' B) = ⨅ z ∈ B, (lam : EReal) * z := by
      simpa using (sInf_image (s := B) (f := fun z : EReal => (lam : EReal) * z))
    exact hmap'.trans hmap''.symm
  let C : Set EReal :=
    { z : EReal |
      ∃ m : Nat, m ≤ n + 1 ∧
        ∃ (idx : Fin m → ι) (p : Fin m → Fin n → Real) (w : Fin m → Real),
          IsConvexWeights m w ∧
            (∀ j, w j ≠ 0) ∧
            x = ∑ j, (lam * w j) • p j ∧
            AffineIndependent ℝ p ∧
            z = ∑ j, ((lam * w j : Real) : EReal) * fᵢ (idx j) (p j) }
  have hC : ((fun z : EReal => (lam : EReal) * z) '' B) = C := by
    ext z
    constructor
    · rintro ⟨z0, hz0, rfl⟩
      rcases hz0 with ⟨m, hm, idx, p, w, hw, hwnz, hxcomb, haff, hz0⟩
      refine ⟨m, hm, idx, p, w, hw, hwnz, ?_, haff, ?_⟩
      ·
        have hx1 : x = lam • (lam⁻¹ • x) := by
          have hlam_ne : lam ≠ 0 := ne_of_gt hlam
          calc
            x = (1 : Real) • x := by simp
            _ = (lam * lam⁻¹) • x := by simp [hlam_ne]
            _ = lam • (lam⁻¹ • x) := by simp [smul_smul]
        have hx2 : lam • (lam⁻¹ • x) = ∑ j, (lam * w j) • p j := by
          calc
            lam • (lam⁻¹ • x) = lam • convexCombination n m p w := by
              simp [hxcomb]
            _ = ∑ j, (lam * w j) • p j := by
              simp [convexCombination, Finset.smul_sum, smul_smul]
        exact hx1.trans hx2
      ·
        calc
          (lam : EReal) * z0 =
              (lam : EReal) * ∑ j, ((w j : Real) : EReal) * fᵢ (idx j) (p j) := by
                simp [hz0]
          _ = ∑ j, (lam : EReal) * (((w j : Real) : EReal) * fᵢ (idx j) (p j)) := by
                have hlam_nonneg : (0 : EReal) ≤ (lam : EReal) := by
                  exact_mod_cast (le_of_lt hlam)
                have hlam_ne_top : (lam : EReal) ≠ ⊤ := by simp
                simpa using
                  (ereal_mul_sum (s := (Finset.univ : Finset (Fin m)))
                    (f := fun j => ((w j : Real) : EReal) * fᵢ (idx j) (p j))
                    (a := (lam : EReal)) hlam_nonneg hlam_ne_top)
          _ = ∑ j, ((lam * w j : Real) : EReal) * fᵢ (idx j) (p j) := by
                simp [mul_assoc, EReal.coe_mul]
    · rintro ⟨m, hm, idx, p, w, hw, hwnz, hxsum, haff, hz⟩
      refine ⟨∑ j, ((w j : Real) : EReal) * fᵢ (idx j) (p j), ?_, ?_⟩
      ·
        refine ⟨m, hm, idx, p, w, hw, hwnz, ?_, haff, rfl⟩
        have hx1 : lam⁻¹ • x = ∑ j, w j • p j := by
          have hlam_ne : lam ≠ 0 := ne_of_gt hlam
          have hx2 : lam⁻¹ • x = lam⁻¹ • ∑ j, (lam * w j) • p j := by
            simp [hxsum]
          calc
            lam⁻¹ • x = lam⁻¹ • ∑ j, (lam * w j) • p j := hx2
            _ = ∑ j, (lam⁻¹ * (lam * w j)) • p j := by
                  simp [Finset.smul_sum, smul_smul, mul_comm, mul_assoc]
            _ = ∑ j, w j • p j := by
                  simp [hlam_ne]
        simpa [convexCombination] using hx1
      ·
        calc
          (lam : EReal) * ∑ j, ((w j : Real) : EReal) * fᵢ (idx j) (p j) =
              ∑ j, (lam : EReal) * (((w j : Real) : EReal) * fᵢ (idx j) (p j)) := by
                have hlam_nonneg : (0 : EReal) ≤ (lam : EReal) := by
                  exact_mod_cast (le_of_lt hlam)
                have hlam_ne_top : (lam : EReal) ≠ ⊤ := by simp
                simpa using
                  (ereal_mul_sum (s := (Finset.univ : Finset (Fin m)))
                    (f := fun j => ((w j : Real) : EReal) * fᵢ (idx j) (p j))
                    (a := (lam : EReal)) hlam_nonneg hlam_ne_top)
          _ = ∑ j, ((lam * w j : Real) : EReal) * fᵢ (idx j) (p j) := by
                simp [mul_assoc, EReal.coe_mul]
          _ = z := by simp [hz]
  calc
    rightScalarMultiple g lam x = (lam : EReal) * g (lam⁻¹ • x) := hpos
    _ = (lam : EReal) * sInf B := by simp [hB]
    _ = sInf ((fun z : EReal => (lam : EReal) * z) '' B) := hmap
    _ = sInf C := by simp [hC]

/-- Flatten an `iInf` of `sInf` into a single `sInf` over existentials. -/
lemma iInf_sInf_eq_sInf_exists {α : Sort _} (B : α → Set EReal) :
    (⨅ a, sInf (B a)) = sInf {z : EReal | ∃ a, z ∈ B a} := by
  refine le_antisymm ?_ ?_
  · refine le_sInf ?_
    intro z hz
    rcases hz with ⟨a, hz⟩
    have h1 : (⨅ a, sInf (B a)) ≤ sInf (B a) := iInf_le _ a
    exact le_trans h1 (sInf_le hz)
  · refine le_iInf ?_
    intro a
    refine le_sInf ?_
    intro z hz
    exact sInf_le (by exact ⟨a, hz⟩)

/-- Reparameterize the infimum over positive right scalar multiples into explicit data. -/
lemma sInf_pos_rightScalarMultiple_eq_sInf_exists_scaled_convexCombo
    {n : Nat} {ι : Type*} {fᵢ : ι → (Fin n → Real) → EReal}
    (hf : ∀ i, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (fᵢ i))
    (x : Fin n → Real) :
    sInf { z : EReal | ∃ lam : Real, 0 < lam ∧
      z = rightScalarMultiple (convexHullFunctionFamily fᵢ) lam x } =
      sInf { z : EReal |
        ∃ lam : Real, 0 < lam ∧
          ∃ m : Nat, m ≤ n + 1 ∧
            ∃ (idx : Fin m → ι) (p : Fin m → Fin n → Real) (w : Fin m → Real),
              IsConvexWeights m w ∧
                (∀ j, w j ≠ 0) ∧
                x = ∑ j, (lam * w j) • p j ∧
                AffineIndependent ℝ p ∧
                z = ∑ j, ((lam * w j : Real) : EReal) * fᵢ (idx j) (p j) } := by
  classical
  let g := convexHullFunctionFamily fᵢ
  let B : {lam : Real // 0 < lam} → Set EReal := fun lam =>
    { z : EReal |
      ∃ m : Nat, m ≤ n + 1 ∧
        ∃ (idx : Fin m → ι) (p : Fin m → Fin n → Real) (w : Fin m → Real),
          IsConvexWeights m w ∧
            (∀ j, w j ≠ 0) ∧
            x = ∑ j, (lam.1 * w j) • p j ∧
            AffineIndependent ℝ p ∧
            z = ∑ j, ((lam.1 * w j : Real) : EReal) * fᵢ (idx j) (p j) }
  have hset :
      { z : EReal |
        ∃ lam : Real, 0 < lam ∧ z = rightScalarMultiple g lam x } =
        Set.range (fun lam : {lam : Real // 0 < lam} =>
          rightScalarMultiple g lam.1 x) := by
    ext z
    constructor
    · rintro ⟨lam, hlam, rfl⟩
      exact ⟨⟨lam, hlam⟩, rfl⟩
    · rintro ⟨lam, rfl⟩
      exact ⟨lam.1, lam.2, rfl⟩
  have hB : ∀ lam : {lam : Real // 0 < lam}, rightScalarMultiple g lam.1 x = sInf (B lam) := by
    intro lam
    simpa [g, B] using
      (rightScalarMultiple_convexHullFamily_eq_sInf_scaled_affineIndependent
        (fᵢ := fᵢ) (hf := hf) (lam := lam.1) (hlam := lam.2) (x := x))
  have hS :
      sInf { z : EReal |
        ∃ lam : Real, 0 < lam ∧ z = rightScalarMultiple g lam x } =
          ⨅ lam : {lam : Real // 0 < lam}, sInf (B lam) := by
    calc
      sInf { z : EReal |
        ∃ lam : Real, 0 < lam ∧ z = rightScalarMultiple g lam x } =
          sInf (Set.range (fun lam : {lam : Real // 0 < lam} =>
            rightScalarMultiple g lam.1 x)) := by
              simp [hset]
      _ = ⨅ lam : {lam : Real // 0 < lam}, rightScalarMultiple g lam.1 x := by
            simpa using
              (sInf_range (f := fun lam : {lam : Real // 0 < lam} =>
                rightScalarMultiple g lam.1 x))
      _ = ⨅ lam : {lam : Real // 0 < lam}, sInf (B lam) := by
            refine iInf_congr ?_
            intro lam
            exact hB lam
  have hflat :
      (⨅ lam : {lam : Real // 0 < lam}, sInf (B lam)) =
        sInf {z : EReal | ∃ lam : {lam : Real // 0 < lam}, z ∈ B lam} := by
    simpa using (iInf_sInf_eq_sInf_exists (B := B))
  have hBset :
      {z : EReal | ∃ lam : {lam : Real // 0 < lam}, z ∈ B lam} =
        { z : EReal |
          ∃ lam : Real, 0 < lam ∧
            ∃ m : Nat, m ≤ n + 1 ∧
              ∃ (idx : Fin m → ι) (p : Fin m → Fin n → Real) (w : Fin m → Real),
                IsConvexWeights m w ∧
                  (∀ j, w j ≠ 0) ∧
                  x = ∑ j, (lam * w j) • p j ∧
                  AffineIndependent ℝ p ∧
                  z = ∑ j, ((lam * w j : Real) : EReal) * fᵢ (idx j) (p j) } := by
    ext z
    constructor
    · rintro ⟨lam, hz⟩
      rcases hz with ⟨m, hm, idx, p, w, hw, hwnz, hxsum, haff, hz⟩
      exact ⟨lam.1, lam.2, m, hm, idx, p, w, hw, hwnz, hxsum, haff, hz⟩
    · rintro ⟨lam, hlam, m, hm, idx, p, w, hw, hwnz, hxsum, haff, hz⟩
      exact ⟨⟨lam, hlam⟩, ⟨m, hm, idx, p, w, hw, hwnz, hxsum, haff, hz⟩⟩
  calc
    sInf { z : EReal |
        ∃ lam : Real, 0 < lam ∧ z = rightScalarMultiple g lam x } =
        ⨅ lam : {lam : Real // 0 < lam}, sInf (B lam) := hS
    _ = sInf {z : EReal | ∃ lam : {lam : Real // 0 < lam}, z ∈ B lam} := hflat
    _ = sInf { z : EReal |
        ∃ lam : Real, 0 < lam ∧
          ∃ m : Nat, m ≤ n + 1 ∧
            ∃ (idx : Fin m → ι) (p : Fin m → Fin n → Real) (w : Fin m → Real),
              IsConvexWeights m w ∧
                (∀ j, w j ≠ 0) ∧
                x = ∑ j, (lam * w j) • p j ∧
                AffineIndependent ℝ p ∧
                z = ∑ j, ((lam * w j : Real) : EReal) * fᵢ (idx j) (p j) } := by
        exact congrArg sInf hBset

/-- Replace scaled convex weights by strictly positive coefficients. -/
lemma scaled_convexCombo_witness_iff_pos_coeff_witness
    {n : Nat} {ι : Type*} {fᵢ : ι → (Fin n → Real) → EReal}
    {x : Fin n → Real} (hx : x ≠ 0) :
    sInf { z : EReal |
      ∃ lam : Real, 0 < lam ∧
        ∃ m : Nat, m ≤ n + 1 ∧
          ∃ (idx : Fin m → ι) (p : Fin m → Fin n → Real) (w : Fin m → Real),
            IsConvexWeights m w ∧
              (∀ j, w j ≠ 0) ∧
              x = ∑ j, (lam * w j) • p j ∧
              AffineIndependent ℝ p ∧
              z = ∑ j, ((lam * w j : Real) : EReal) * fᵢ (idx j) (p j) } =
      sInf { z : EReal |
        ∃ m : Nat, m ≤ n + 1 ∧
          ∃ (idx : Fin m → ι) (p : Fin m → Fin n → Real) (c : Fin m → Real),
            (∀ j, 0 < c j) ∧
              x = ∑ j, c j • p j ∧
              AffineIndependent ℝ p ∧
              z = ∑ j, ((c j : Real) : EReal) * fᵢ (idx j) (p j) } := by
  classical
  let S1 : Set EReal :=
    { z : EReal |
      ∃ lam : Real, 0 < lam ∧
        ∃ m : Nat, m ≤ n + 1 ∧
          ∃ (idx : Fin m → ι) (p : Fin m → Fin n → Real) (w : Fin m → Real),
            IsConvexWeights m w ∧
              (∀ j, w j ≠ 0) ∧
              x = ∑ j, (lam * w j) • p j ∧
              AffineIndependent ℝ p ∧
              z = ∑ j, ((lam * w j : Real) : EReal) * fᵢ (idx j) (p j) }
  let S2 : Set EReal :=
    { z : EReal |
      ∃ m : Nat, m ≤ n + 1 ∧
        ∃ (idx : Fin m → ι) (p : Fin m → Fin n → Real) (c : Fin m → Real),
          (∀ j, 0 < c j) ∧
            x = ∑ j, c j • p j ∧
            AffineIndependent ℝ p ∧
            z = ∑ j, ((c j : Real) : EReal) * fᵢ (idx j) (p j) }
  have hset : S1 = S2 := by
    ext z
    constructor
    · rintro ⟨lam, hlam, m, hm, idx, p, w, hw, hwnz, hxsum, haff, hz⟩
      let c : Fin m → Real := fun j => lam * w j
      have hwpos : ∀ j, 0 < w j := by
        intro j
        have hw0 : 0 ≤ w j := (hw.1 j)
        have hne : (0 : Real) ≠ w j := by
          simpa [eq_comm] using (hwnz j)
        exact lt_of_le_of_ne hw0 hne
      have hcpos : ∀ j, 0 < c j := by
        intro j
        exact mul_pos hlam (hwpos j)
      refine ⟨m, hm, idx, p, c, hcpos, ?_, haff, ?_⟩
      · simpa [c] using hxsum
      · simpa [c] using hz
    · rintro ⟨m, hm, idx, p, c, hcpos, hxsum, haff, hz⟩
      have hm0 : m ≠ 0 := by
        intro hm0
        subst hm0
        have hx0 : x = 0 := by
          simpa using hxsum
        exact (hx hx0).elim
      have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
      have hne : (Finset.univ : Finset (Fin m)).Nonempty := by
        haveI : Nonempty (Fin m) := ⟨⟨0, hm_pos⟩⟩
        simp
      have hpos : 0 < ∑ j : Fin m, c j := by
        have hpos' : ∀ j ∈ (Finset.univ : Finset (Fin m)), 0 < c j := by
          intro j _hj
          exact hcpos j
        have hsum_pos :
            0 < ∑ j ∈ (Finset.univ : Finset (Fin m)), c j := Finset.sum_pos hpos' hne
        simpa using hsum_pos
      let lam : Real := ∑ j : Fin m, c j
      have hlam : 0 < lam := by simpa [lam] using hpos
      let w : Fin m → Real := fun j => c j / lam
      have hw_nonneg : ∀ j, 0 ≤ w j := by
        intro j
        have hlam_nonneg : 0 ≤ lam := le_of_lt hlam
        exact div_nonneg (le_of_lt (hcpos j)) hlam_nonneg
      have hsum_w : ∑ j, w j = 1 := by
        have hlam_ne : lam ≠ 0 := ne_of_gt hlam
        calc
          ∑ j, w j = ∑ j, c j * lam⁻¹ := by
            simp [w, div_eq_mul_inv]
          _ = ∑ j, lam⁻¹ * c j := by simp [mul_comm]
          _ = lam⁻¹ * ∑ j, c j := by
            symm
            simpa using
              (Finset.mul_sum (s := (Finset.univ : Finset (Fin m)))
                (f := fun j => c j) (a := lam⁻¹))
          _ = 1 := by
            simp [lam, inv_mul_cancel₀ (a := lam) hlam_ne]
      have hw : IsConvexWeights m w := ⟨hw_nonneg, hsum_w⟩
      have hwnz : ∀ j, w j ≠ 0 := by
        intro j
        have hpos_w : 0 < w j := by
          exact div_pos (hcpos j) hlam
        exact ne_of_gt hpos_w
      have hmul : ∀ j, lam * w j = c j := by
        intro j
        have hlam_ne : lam ≠ 0 := ne_of_gt hlam
        calc
          lam * w j = lam * (c j / lam) := by rfl
          _ = (lam * c j) / lam := by
                simpa using (mul_div_assoc lam (c j) lam).symm
          _ = c j := by
                simpa [mul_comm] using (mul_div_cancel_left₀ (b := c j) (a := lam) hlam_ne)
      have hxsum' : x = ∑ j, (lam * w j) • p j := by
        have hsum_eq :
            ∑ j, (lam * w j) • p j = ∑ j, c j • p j := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          simp [hmul]
        simpa [hsum_eq] using hxsum
      have hz' :
          z = ∑ j, ((lam * w j : Real) : EReal) * fᵢ (idx j) (p j) := by
        have hsum_eq :
            ∑ j, ((c j : Real) : EReal) * fᵢ (idx j) (p j) =
              ∑ j, ((lam * w j : Real) : EReal) * fᵢ (idx j) (p j) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          simp [hmul]
        simpa [hsum_eq, EReal.coe_mul, mul_assoc] using hz
      exact ⟨lam, hlam, m, hm, idx, p, w, hw, hwnz, hxsum', haff, hz'⟩
  exact congrArg sInf hset

/-- Drop a zero coefficient in a conic sum while preserving the linear objective. -/
lemma drop_zero_coeff_sum_smul_and_sum_mul_to_shorter_fin {n m : Nat}
    {x : Fin n → Real} (v : Fin (m + 1) → Fin n → Real) (c : Fin (m + 1) → Real)
    (a : Fin (m + 1) → Real)
    (hc : ∀ i, 0 ≤ c i) (hx : x = ∑ i, c i • v i)
    (i0 : Fin (m + 1)) (hci0 : c i0 = 0) :
    ∃ e : Fin m ↪ Fin (m + 1), ∃ c' : Fin m → Real,
      (∀ j, 0 ≤ c' j) ∧
        x = ∑ j, c' j • v (e j) ∧
        (∑ j, c' j * a (e j) = ∑ i, c i * a i) := by
  classical
  let I : Type := {i : Fin (m + 1) // i ≠ i0}
  let e' : Fin m ≃ I := finSuccAboveEquiv i0
  let e : Fin m ↪ Fin (m + 1) :=
    { toFun := fun j => (e' j).1
      inj' := by
        intro j1 j2 h
        have h' : e' j1 = e' j2 := by
          apply Subtype.ext
          simpa using h
        exact e'.injective h' }
  let c' : Fin m → Real := fun j => c (e j)
  have hc' : ∀ j, 0 ≤ c' j := by
    intro j
    simpa [c', e] using hc (e' j).1
  have hsum_filter :
      (∑ i, c i * a i) =
        ∑ i ∈ Finset.univ.filter (fun i => i ≠ i0), c i * a i := by
    have hsum_if :
        (∑ i, c i * a i) = ∑ i, (if i ≠ i0 then c i * a i else 0) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      by_cases h : i = i0
      · subst h
        simp [hci0]
      · simp [h]
    have hsum_filter' :
        ∑ i ∈ Finset.univ.filter (fun i => i ≠ i0), c i * a i =
          ∑ i, (if i ≠ i0 then c i * a i else 0) := by
      simpa using
        (Finset.sum_filter (s := (Finset.univ : Finset (Fin (m + 1))))
          (f := fun i => c i * a i) (p := fun i => i ≠ i0))
    calc
      (∑ i, c i * a i) = ∑ i, (if i ≠ i0 then c i * a i else 0) := hsum_if
      _ = ∑ i ∈ Finset.univ.filter (fun i => i ≠ i0), c i * a i := by
          symm
          exact hsum_filter'
  have hsum_subtype :
      ∑ i ∈ Finset.univ.filter (fun i => i ≠ i0), c i * a i =
        ∑ i : I, c i.1 * a i.1 := by
    refine (Finset.sum_subtype (s := Finset.univ.filter (fun i => i ≠ i0))
      (p := fun i => i ≠ i0) (f := fun i => c i * a i) ?_)
    intro i
    simp
  have hsum_equiv :
      ∑ j, c' j * a (e j) = ∑ i : I, c i.1 * a i.1 := by
    simpa [c', e] using
      (Equiv.sum_comp e' (fun i : I => c i.1 * a i.1))
  have hsum_filter_smul :
      (∑ i, c i • v i) =
        ∑ i ∈ Finset.univ.filter (fun i => i ≠ i0), c i • v i := by
    have hsum_if :
        (∑ i, c i • v i) = ∑ i, (if i ≠ i0 then c i • v i else 0) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      by_cases h : i = i0
      · subst h
        simp [hci0]
      · simp [h]
    have hsum_filter' :
        ∑ i ∈ Finset.univ.filter (fun i => i ≠ i0), c i • v i =
          ∑ i, (if i ≠ i0 then c i • v i else 0) := by
      simpa using
        (Finset.sum_filter (s := (Finset.univ : Finset (Fin (m + 1))))
          (f := fun i => c i • v i) (p := fun i => i ≠ i0))
    calc
      (∑ i, c i • v i) = ∑ i, (if i ≠ i0 then c i • v i else 0) := hsum_if
      _ = ∑ i ∈ Finset.univ.filter (fun i => i ≠ i0), c i • v i := by
          symm
          exact hsum_filter'
  have hsum_subtype_smul :
      ∑ i ∈ Finset.univ.filter (fun i => i ≠ i0), c i • v i =
        ∑ i : I, c i.1 • v i.1 := by
    refine (Finset.sum_subtype (s := Finset.univ.filter (fun i => i ≠ i0))
      (p := fun i => i ≠ i0) (f := fun i => c i • v i) ?_)
    intro i
    simp
  have hsum_equiv_smul :
      ∑ j, c' j • v (e j) = ∑ i : I, c i.1 • v i.1 := by
    simpa [c', e] using
      (Equiv.sum_comp e' (fun i : I => c i.1 • v i.1))
  have hx' :
      x = ∑ j, c' j • v (e j) := by
    calc
      x = ∑ i, c i • v i := hx
      _ = ∑ i ∈ Finset.univ.filter (fun i => i ≠ i0), c i • v i := hsum_filter_smul
      _ = ∑ i : I, c i.1 • v i.1 := hsum_subtype_smul
      _ = ∑ j, c' j • v (e j) := by
            symm
            exact hsum_equiv_smul
  refine ⟨e, c', hc', hx', ?_⟩
  calc
    ∑ j, c' j * a (e j) = ∑ i : I, c i.1 * a i.1 := hsum_equiv
    _ = ∑ i ∈ Finset.univ.filter (fun i => i ≠ i0), c i * a i := by
          symm
          exact hsum_subtype
    _ = ∑ i, c i * a i := by
          symm
          exact hsum_filter

/-- Corollary 17.1.4. Let `{fᵢ | i ∈ I}` be an arbitrary collection of proper convex functions on
`ℝⁿ`. Let `f` be the greatest positively homogeneous convex function such that `f ≤ fᵢ i` for
every `i`, i.e. the positively homogeneous convex function generated by `conv {fᵢ | i ∈ I}`.

Then, for every vector `x ≠ 0`, one has

`f x = inf { ∑ j, λ j * fᵢ (idx j) (xⱼ j) | x = ∑ j, λ j • xⱼ j }`,

where the infimum is taken over all expressions of `x` as a positive linear combination of at
most `n + 1` vectors, which are affinely independent. -/
theorem positivelyHomogeneousConvexFunctionGenerated_convexHullFunctionFamily_eq_sInf_linearIndependent_nonnegLinearCombination_le
    {n : Nat} {ι : Type _} {fᵢ : ι → (Fin n → Real) → EReal}
    (hf : ∀ i, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (fᵢ i)) :
    ∀ x : Fin n → Real,
      x ≠ 0 →
        positivelyHomogeneousConvexFunctionGenerated (convexHullFunctionFamily fᵢ) x =
          sInf { z : EReal |
            ∃ m : Nat, m ≤ n + 1 ∧
              ∃ (idx : Fin m → ι) (x' : Fin m → Fin n → Real) (c : Fin m → Real),
                (∀ j, 0 < c j) ∧
                  x = ∑ j, c j • x' j ∧
                  AffineIndependent ℝ x' ∧
                  z = ∑ j, ((c j : Real) : EReal) * fᵢ (idx j) (x' j) } := by
  classical
  intro x hx
  by_cases hI : Nonempty ι
  ·
    have hmain :=
      posHomGen_convexHullFamily_eq_sInf_pos_rightScalarMultiple (hf := hf) (hI := hI) x hx
    refine hmain.trans ?_
    -- Reparameterize the positive scalar / convex-combination formula to positive coefficients.
    have hstep1 :=
      sInf_pos_rightScalarMultiple_eq_sInf_exists_scaled_convexCombo (hf := hf) (x := x)
    have hstep2 :=
      scaled_convexCombo_witness_iff_pos_coeff_witness (fᵢ := fᵢ) (x := x) hx
    have hpos :
        sInf { z : EReal | ∃ lam : Real, 0 < lam ∧
          z = rightScalarMultiple (convexHullFunctionFamily fᵢ) lam x } =
          sInf { z : EReal |
            ∃ m : Nat, m ≤ n + 1 ∧
              ∃ (idx : Fin m → ι) (p : Fin m → Fin n → Real) (c : Fin m → Real),
                (∀ j, 0 < c j) ∧
                  x = ∑ j, c j • p j ∧
                  AffineIndependent ℝ p ∧
                  z = ∑ j, ((c j : Real) : EReal) * fᵢ (idx j) (p j) } := by
      simpa using hstep1.trans hstep2
    exact hpos
  ·
    -- Empty index set: the right-hand side is empty for `x ≠ 0`, and the left-hand side is `⊤`.
    haveI : IsEmpty ι := by
      exact not_nonempty_iff.mp hI
    have htop :=
      posHomGen_convexHullFamily_eq_top_of_isEmpty (hf := hf) (hI := (inferInstance : IsEmpty ι))
        x hx
    have hset :
        { z : EReal |
          ∃ m : Nat, m ≤ n + 1 ∧
            ∃ (idx : Fin m → ι) (x' : Fin m → Fin n → Real) (c : Fin m → Real),
              (∀ j, 0 < c j) ∧
                x = ∑ j, c j • x' j ∧
                AffineIndependent ℝ x' ∧
                z = ∑ j, ((c j : Real) : EReal) * fᵢ (idx j) (x' j) } = (∅ : Set EReal) :=
      cor17_1_4_rhs_empty_of_isEmpty (hI := (inferInstance : IsEmpty ι)) (x := x) hx
    calc
      positivelyHomogeneousConvexFunctionGenerated (convexHullFunctionFamily fᵢ) x = (⊤ : EReal) :=
        htop
      _ = sInf { z : EReal |
          ∃ m : Nat, m ≤ n + 1 ∧
            ∃ (idx : Fin m → ι) (x' : Fin m → Fin n → Real) (c : Fin m → Real),
              (∀ j, 0 < c j) ∧
                x = ∑ j, c j • x' j ∧
                AffineIndependent ℝ x' ∧
                z = ∑ j, ((c j : Real) : EReal) * fᵢ (idx j) (x' j) } := by
        symm
        simp [hset]

/-- Pad a convex combination by one zero-weight entry. -/
lemma pad_convexCombination_succ {n m : Nat}
    {x' : Fin m → Fin n → Real} {w : Fin m → Real}
    (hw : IsConvexWeights m w) (x0 : Fin n → Real) :
    IsConvexWeights (m + 1) (Fin.cons (n := m) (α := fun _ => Real) 0 w) ∧
      convexCombination n (m + 1)
          (Fin.cons (n := m) (α := fun _ => Fin n → Real) x0 x')
          (Fin.cons (n := m) (α := fun _ => Real) 0 w) =
        convexCombination n m x' w := by
  rcases hw with ⟨hw_nonneg, hw_sum⟩
  have hnonneg :
      ∀ i, 0 ≤ (Fin.cons (n := m) (α := fun _ => Real) 0 w) i := by
    intro i
    cases i using Fin.cases with
    | zero => simp
    | succ i => simpa using hw_nonneg i
  have hsum : ∑ i, (Fin.cons (n := m) (α := fun _ => Real) 0 w) i = 1 := by
    calc
      ∑ i, (Fin.cons (n := m) (α := fun _ => Real) 0 w) i
          = (Fin.cons (n := m) (α := fun _ => Real) 0 w) 0 +
              ∑ i : Fin m, (Fin.cons (n := m) (α := fun _ => Real) 0 w) i.succ := by
              simp
      _ = 0 + ∑ i, w i := by simp
      _ = 1 := by simp [hw_sum]
  refine ⟨⟨hnonneg, hsum⟩, ?_⟩
  calc
    convexCombination n (m + 1)
        (Fin.cons (n := m) (α := fun _ => Fin n → Real) x0 x')
        (Fin.cons (n := m) (α := fun _ => Real) 0 w)
        = ∑ i, (Fin.cons (n := m) (α := fun _ => Real) 0 w) i •
            (Fin.cons (n := m) (α := fun _ => Fin n → Real) x0 x') i := by rfl
    _ = (Fin.cons (n := m) (α := fun _ => Real) 0 w) 0 •
          (Fin.cons (n := m) (α := fun _ => Fin n → Real) x0 x') 0 +
          ∑ i : Fin m, (Fin.cons (n := m) (α := fun _ => Real) 0 w) i.succ •
            (Fin.cons (n := m) (α := fun _ => Fin n → Real) x0 x') i.succ := by
          simpa using
            (Fin.sum_univ_succ (f := fun i =>
              (Fin.cons (n := m) (α := fun _ => Real) 0 w) i •
                (Fin.cons (n := m) (α := fun _ => Fin n → Real) x0 x') i))
    _ = 0 + ∑ i, w i • x' i := by simp
    _ = ∑ i, w i • x' i := by simp
    _ = convexCombination n m x' w := by rfl

/-- Padding by a zero weight leaves the objective sum unchanged. -/
lemma pad_objective_sum_succ {n m : Nat} {f : (Fin n → Real) → EReal}
    {x0 : Fin n → Real} {x' : Fin m → Fin n → Real} {w : Fin m → Real} :
    ∑ i, ((Fin.cons (n := m) (α := fun _ => Real) 0 w i : Real) : EReal) *
        f (Fin.cons (n := m) (α := fun _ => Fin n → Real) x0 x' i) =
      ∑ i, ((w i : Real) : EReal) * f (x' i) := by
  calc
    ∑ i, ((Fin.cons (n := m) (α := fun _ => Real) 0 w i : Real) : EReal) *
        f (Fin.cons (n := m) (α := fun _ => Fin n → Real) x0 x' i) =
        ((Fin.cons (n := m) (α := fun _ => Real) 0 w 0 : Real) : EReal) *
            f (Fin.cons (n := m) (α := fun _ => Fin n → Real) x0 x' 0) +
          ∑ i : Fin m,
              ((Fin.cons (n := m) (α := fun _ => Real) 0 w i.succ : Real) : EReal) *
                f (Fin.cons (n := m) (α := fun _ => Fin n → Real) x0 x' i.succ) := by
            simpa using
              (Fin.sum_univ_succ (f := fun i =>
                ((Fin.cons (n := m) (α := fun _ => Real) 0 w i : Real) : EReal) *
                  f (Fin.cons (n := m) (α := fun _ => Fin n → Real) x0 x' i)))
    _ = 0 + ∑ i, ((w i : Real) : EReal) * f (x' i) := by simp
    _ = ∑ i, ((w i : Real) : EReal) * f (x' i) := by simp

/-- Pad a convex combination to length `n + 1`, preserving the weighted sum. -/
lemma pad_convexCombination_to_fin_add_one {n m : Nat} {f : (Fin n → Real) → EReal}
    (hm : m ≤ n + 1) {x' : Fin m → Fin n → Real} {w : Fin m → Real}
    (hw : IsConvexWeights m w) :
    ∃ x'' : Fin (n + 1) → Fin n → Real, ∃ w'' : Fin (n + 1) → Real,
      IsConvexWeights (n + 1) w'' ∧
        convexCombination n (n + 1) x'' w'' = convexCombination n m x' w ∧
        (∑ i, ((w'' i : Real) : EReal) * f (x'' i) =
          ∑ i, ((w i : Real) : EReal) * f (x' i)) := by
  classical
  let k : Nat := n + 1 - m
  have hpad :
      ∀ k, ∃ x'' : Fin (m + k) → Fin n → Real, ∃ w'' : Fin (m + k) → Real,
        IsConvexWeights (m + k) w'' ∧
          convexCombination n (m + k) x'' w'' = convexCombination n m x' w ∧
          (∑ i, ((w'' i : Real) : EReal) * f (x'' i) =
            ∑ i, ((w i : Real) : EReal) * f (x' i)) := by
    intro k
    induction k with
    | zero =>
        refine ⟨x', w, ?_, ?_, ?_⟩
        · simpa using hw
        · simp [convexCombination]
        · simp
    | succ k ih =>
        rcases ih with ⟨xk, wk, hwk, hxk, hzk⟩
        have hpad' :=
          pad_convexCombination_succ (n := n) (m := m + k) (x' := xk) (w := wk) hwk (x0 := 0)
        rcases hpad' with ⟨hwk', hxk'⟩
        refine ⟨Fin.cons (n := m + k) (α := fun _ => Fin n → Real) 0 xk,
          Fin.cons (n := m + k) (α := fun _ => Real) 0 wk, hwk', ?_, ?_⟩
        ·
          simpa [Nat.add_assoc] using hxk'.trans hxk
        ·
          have hpadz :
              ∑ i, ((Fin.cons (n := m + k) (α := fun _ => Real) 0 wk i : Real) : EReal) *
                  f (Fin.cons (n := m + k) (α := fun _ => Fin n → Real) 0 xk i) =
                ∑ i, ((wk i : Real) : EReal) * f (xk i) := by
            simpa using (pad_objective_sum_succ (f := f) (x0 := 0) (x' := xk) (w := wk))
          simpa [Nat.add_assoc] using hpadz.trans hzk
  rcases hpad k with ⟨x'', w'', hw'', hx'', hz''⟩
  have hk : m + k = n + 1 := by
    dsimp [k]
    exact Nat.add_sub_of_le hm
  refine (hk ▸ ?_)
  exact ⟨x'', w'', hw'', hx'', hz''⟩

/-- Convert an `EReal` objective into a real sum when the total is not `⊤`. -/
lemma toReal_objective_of_sum_ne_top_for_weights {n m : Nat}
    {f : (Fin n → Real) → EReal} (h_not_bot : ∀ x, f x ≠ (⊥ : EReal))
    {x' : Fin m → Fin n → Real} {w : Fin m → Real} {x : Fin n → Real} {z : EReal}
    (hw : IsConvexWeights m w) (hx : x = convexCombination n m x' w)
    (hz : z = ∑ i, ((w i : Real) : EReal) * f (x' i)) (hz_top : z ≠ ⊤) :
    ∃ x'' : Fin m → Fin n → Real,
      x = convexCombination n m x'' w ∧
      (∀ i, f (x'' i) ≠ ⊤) ∧
      z = ((∑ i, w i * (f (x'' i)).toReal : Real) : EReal) := by
  classical
  rcases hw with ⟨hw_nonneg, hw_sum⟩
  have hpos_exists : ∃ i, 0 < w i := by
    by_contra hpos
    have hzero : ∀ i, w i = 0 := by
      intro i
      have hle : w i ≤ 0 := le_of_not_gt ((not_exists.mp hpos) i)
      exact le_antisymm hle (hw_nonneg i)
    have hsum0 : ∑ i, w i = 0 := by
      simp [hzero]
    have hsum1' : (0 : Real) = 1 := by
      have hsum1'' := hw_sum
      rw [hsum0] at hsum1''
      exact hsum1''
    exact (one_ne_zero (α := Real)) hsum1'.symm
  have hnot_top_pos : ∀ i, 0 < w i → f (x' i) ≠ ⊤ := by
    intro i hi
    by_contra htop
    have hposE : (0 : EReal) < (w i : EReal) := (EReal.coe_pos).2 hi
    have hterm_top :
        ((w i : Real) : EReal) * f (x' i) = ⊤ := by
      simpa [htop] using (EReal.mul_top_of_pos (x := (w i : EReal)) hposE)
    have hsum_ne_bot :
        (Finset.univ.erase i).sum
            (fun j => ((w j : Real) : EReal) * f (x' j)) ≠ ⊥ := by
      refine
        sum_ne_bot_of_ne_bot (s := Finset.univ.erase i)
          (f := fun j => ((w j : Real) : EReal) * f (x' j)) ?_
      intro j hj
      have hne_bot : f (x' j) ≠ ⊥ := h_not_bot (x' j)
      refine (EReal.mul_ne_bot ((w j : Real) : EReal) (f (x' j))).2 ?_
      refine ⟨?_, ?_, ?_, ?_⟩
      · left
        exact EReal.coe_ne_bot _
      · right
        exact hne_bot
      · left
        exact EReal.coe_ne_top _
      · left
        exact (EReal.coe_nonneg).2 (hw_nonneg j)
    have hsum_top :
        (∑ j, ((w j : Real) : EReal) * f (x' j)) = ⊤ := by
      have hsum :=
        (Finset.add_sum_erase (s := Finset.univ)
          (f := fun j => ((w j : Real) : EReal) * f (x' j))
          (a := i) (h := by simp))
      calc
        (∑ j, ((w j : Real) : EReal) * f (x' j)) =
            ((w i : Real) : EReal) * f (x' i) +
              (Finset.univ.erase i).sum
                (fun j => ((w j : Real) : EReal) * f (x' j)) := by
          simpa using hsum.symm
        _ = ⊤ := by
          simpa [hterm_top] using (EReal.top_add_of_ne_bot hsum_ne_bot)
    have hz' : z = ⊤ := by
      simpa [hz] using hsum_top
    exact hz_top hz'
  obtain ⟨i0, hi0pos⟩ := hpos_exists
  have hi0top : f (x' i0) ≠ ⊤ := hnot_top_pos i0 hi0pos
  let x'' : Fin m → Fin n → Real := fun i => if w i = 0 then x' i0 else x' i
  have hsumx' :
      ∑ i, w i • x'' i = ∑ i, w i • x' i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hwi : w i = 0
    · simp [x'', hwi]
    · simp [x'', hwi]
  have hx' : x = convexCombination n m x'' w := by
    have hx_sum : x = ∑ i, w i • x' i := by
      simpa [convexCombination] using hx
    calc
      x = ∑ i, w i • x' i := hx_sum
      _ = ∑ i, w i • x'' i := by symm; exact hsumx'
      _ = convexCombination n m x'' w := by simp [convexCombination]
  have hnot_top : ∀ i, f (x'' i) ≠ ⊤ := by
    intro i
    by_cases hwi : w i = 0
    · simp [x'', hwi, hi0top]
    · have hpos : 0 < w i := lt_of_le_of_ne (hw_nonneg i) (Ne.symm hwi)
      have hnot : f (x' i) ≠ ⊤ := hnot_top_pos i hpos
      simp [x'', hwi, hnot]
  have hsum_x'' :
      ∑ i, ((w i : Real) : EReal) * f (x'' i) =
        ∑ i, ((w i : Real) : EReal) * f (x' i) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hwi : w i = 0
    · simp [x'', hwi]
    · simp [x'', hwi]
  have hz' : z = ∑ i, ((w i : Real) : EReal) * f (x'' i) := by
    calc
      z = ∑ i, ((w i : Real) : EReal) * f (x' i) := hz
      _ = ∑ i, ((w i : Real) : EReal) * f (x'' i) := by symm; exact hsum_x''
  let a : Fin m → Real := fun i => (f (x'' i)).toReal
  have hsum' :
      ∑ i, ((w i : Real) : EReal) * f (x'' i) =
        ∑ i, ((w i * a i : Real) : EReal) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have htop : f (x'' i) ≠ ⊤ := hnot_top i
    have hbot : f (x'' i) ≠ ⊥ := h_not_bot (x'' i)
    have hcoe : (a i : EReal) = f (x'' i) := by
      simpa [a] using (EReal.coe_toReal htop hbot)
    calc
      ((w i : Real) : EReal) * f (x'' i)
          = ((w i : Real) : EReal) * (a i : EReal) := by simp [hcoe]
      _ = ((w i * a i : Real) : EReal) := by simp [EReal.coe_mul]
  have hsum'' :
      ∑ i, ((w i * a i : Real) : EReal) =
        ((∑ i, w i * a i : Real) : EReal) := by
    simpa using (ereal_coe_sum (s := Finset.univ) (f := fun i => w i * a i))
  refine ⟨x'', hx', hnot_top, ?_⟩
  calc
    z = ∑ i, ((w i : Real) : EReal) * f (x'' i) := hz'
    _ = ((∑ i, w i * a i : Real) : EReal) := by exact hsum'.trans hsum''

/-- Reduce a convex-combination objective to at most `n + 1` points. -/
lemma reduce_convexCombo_objective_to_le_add_one {n k : Nat}
    {p : Fin k → Fin n → Real} {w : Fin k → Real} {x : Fin n → Real} {a : Fin k → Real}
    (hw : IsConvexWeights k w) (hx : x = convexCombination n k p w) :
    ∃ m : Nat, m ≤ n + 1 ∧
      ∃ (e : Fin m ↪ Fin k) (w' : Fin m → Real),
        IsConvexWeights m w' ∧
          x = convexCombination n m (fun j => p (e j)) w' ∧
          (∑ j, w' j * a (e j) ≤ ∑ i, w i * a i) := by
  classical
  by_cases hzero : ∃ i, w i = 0
  ·
    rcases
        drop_zero_weights_preserves_convexCombination_obj (p := p) (w := w) (x := x) (a := a)
          hw hx hzero with
      ⟨k', e1, w1, hw1, hwnz1, hx1, hobj_eq1, _hk'⟩
    rcases
        exists_affineIndependent_convexCombination_obj_le (n := n) (k := k') (p := fun j => p (e1 j))
          (w := w1) (x := x) (a := fun j => a (e1 j)) hw1 hwnz1 hx1 with
      ⟨m, hm, e2, w2, hw2, _hwnz2, hx2, _hAff2, hobj_le2⟩
    let e : Fin m ↪ Fin k :=
      { toFun := fun j => e1 (e2 j)
        inj' := by
          intro i j h
          exact e2.injective (e1.injective h) }
    have hobj_le2' :
        ∑ j, w2 j * a (e j) ≤ ∑ i, w1 i * a (e1 i) := by
      simpa [e] using hobj_le2
    have hobj_le1 : ∑ i, w1 i * a (e1 i) ≤ ∑ i, w i * a i := by
      exact le_of_eq hobj_eq1
    refine ⟨m, hm, e, w2, hw2, ?_, ?_⟩
    · simpa [e] using hx2
    · exact le_trans hobj_le2' hobj_le1
  ·
    have hwnz : ∀ i, w i ≠ 0 := by
      intro i
      by_contra hi
      exact hzero ⟨i, hi⟩
    rcases
        exists_affineIndependent_convexCombination_obj_le (n := n) (k := k) (p := p) (w := w)
          (x := x) (a := a) hw hwnz hx with
      ⟨m, hm, e, w', hw', _hwnz', hx', _hAff', hobj_le⟩
    refine ⟨m, hm, e, w', hw', ?_, hobj_le⟩
    simpa using hx'

/-- Corollary 17.1.5. Let `f : ℝⁿ → (-∞, +∞]` be any function (modeled here as
`f : (Fin n → ℝ) → EReal` together with the side condition `∀ x, f x ≠ ⊥`). Then
\[
(\text{conv } f)(x) = \inf \Bigl\{ \sum_{i=1}^{n+1} \lambda_i f(x_i) \,\Bigm|\,
  \sum_{i=1}^{n+1} \lambda_i x_i = x \Bigr\},
\]
where the infimum is taken over all expressions of `x` as a convex combination of `n + 1`
points. (The same formula holds if one restricts to convex combinations in which the `n + 1`
points are affinely independent.) -/
theorem convexHullFunction_eq_sInf_convexCombination_add_one {n : Nat}
    {f : (Fin n → Real) → EReal} (h_not_bot : ∀ x, f x ≠ (⊥ : EReal)) :
    ∀ x : Fin n → Real,
      convexHullFunction f x =
        sInf { z : EReal |
          ∃ (x' : Fin (n + 1) → Fin n → Real) (w : Fin (n + 1) → Real),
            IsConvexWeights (n + 1) w ∧
              x = convexCombination n (n + 1) x' w ∧
              z = ∑ i, ((w i : Real) : EReal) * f (x' i) } := by
  classical
  intro x
  let B0 : Set EReal :=
    { z : EReal |
      ∃ (m : Nat) (lam : Fin m → Real) (x' : Fin m → (Fin n → Real)),
        (∀ i, 0 ≤ lam i) ∧
        (Finset.univ.sum (fun i => lam i) = 1) ∧
        (Finset.univ.sum (fun i => lam i • x' i) = x) ∧
        z = Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f (x' i)) }
  let B1 : Set EReal :=
    { z : EReal |
      ∃ m : Nat, m ≤ n + 1 ∧
        ∃ (x' : Fin m → Fin n → Real) (w : Fin m → Real),
          IsConvexWeights m w ∧
            x = convexCombination n m x' w ∧
            z = ∑ i, ((w i : Real) : EReal) * f (x' i) }
  let B2 : Set EReal :=
    { z : EReal |
      ∃ (x' : Fin (n + 1) → Fin n → Real) (w : Fin (n + 1) → Real),
        IsConvexWeights (n + 1) w ∧
          x = convexCombination n (n + 1) x' w ∧
          z = ∑ i, ((w i : Real) : EReal) * f (x' i) }
  have hconv :
      convexHullFunction f x = sInf B0 := by
    simpa [B0] using
      (convexHullFunction_eq_sInf_convexCombination (g := f) h_not_bot x)
  have B1_to_B0 : ∀ {z}, z ∈ B1 → z ∈ B0 := by
    intro z hz
    rcases hz with ⟨m, _hm, x', w, hw, hxcomb, hz⟩
    rcases hw with ⟨hw_nonneg, hw_sum⟩
    refine ⟨m, w, x', hw_nonneg, ?_, ?_, ?_⟩
    · simpa using hw_sum
    · simpa [convexCombination] using hxcomb.symm
    · simp [hz]
  have B0_to_B1_exists_le :
      ∀ {z}, z ∈ B0 → ∃ z1, z1 ∈ B1 ∧ z1 ≤ z := by
    intro z hz
    rcases hz with ⟨m, lam, x', h0, hsum1, hsumx, hz⟩
    have hw : IsConvexWeights m lam := ⟨h0, by simpa using hsum1⟩
    have hxcomb : x = convexCombination n m x' lam := by
      simpa [convexCombination] using hsumx.symm
    by_cases hz_top : z = ⊤
    ·
      let x1 : Fin 1 → Fin n → Real := fun _ => x
      let w1 : Fin 1 → Real := fun _ => 1
      have hw1 : IsConvexWeights 1 w1 := by
        refine ⟨?_, ?_⟩
        · intro i
          simp [w1]
        · simp [w1]
      have hx1 : x = convexCombination n 1 x1 w1 := by
        simp [convexCombination, x1, w1]
      have hm1 : (1 : Nat) ≤ n + 1 := by
        exact Nat.succ_le_succ (Nat.zero_le n)
      refine ⟨f x, ?_, ?_⟩
      · refine ⟨1, hm1, x1, w1, hw1, hx1, ?_⟩
        simp [x1, w1]
      · simp [hz_top]
    ·
      rcases
          toReal_objective_of_sum_ne_top_for_weights (h_not_bot := h_not_bot) (x := x)
            (x' := x') (w := lam) (z := z) hw hxcomb hz hz_top with
        ⟨x'', hx'', hnot_top, hz_coe⟩
      let a : Fin m → Real := fun i => (f (x'' i)).toReal
      rcases
          reduce_convexCombo_objective_to_le_add_one (n := n) (k := m) (p := x'') (w := lam)
            (x := x) (a := a) hw hx'' with
        ⟨m', hm', e, w', hw', hx', hobj_le⟩
      let z1 : EReal := ∑ j, ((w' j : Real) : EReal) * f (x'' (e j))
      have hz1_mem : z1 ∈ B1 := by
        refine ⟨m', hm', (fun j => x'' (e j)), w', hw', ?_, rfl⟩
        simpa using hx'
      have hz1_coe :
          z1 = ((∑ j, w' j * a (e j) : Real) : EReal) := by
        have hsum' :
            ∑ j, ((w' j : Real) : EReal) * f (x'' (e j)) =
              ∑ j, ((w' j * a (e j) : Real) : EReal) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have htop : f (x'' (e j)) ≠ ⊤ := hnot_top (e j)
          have hbot : f (x'' (e j)) ≠ ⊥ := h_not_bot (x'' (e j))
          have hcoe : (a (e j) : EReal) = f (x'' (e j)) := by
            simpa [a] using (EReal.coe_toReal htop hbot)
          calc
            ((w' j : Real) : EReal) * f (x'' (e j))
                = ((w' j : Real) : EReal) * (a (e j) : EReal) := by simp [hcoe]
            _ = ((w' j * a (e j) : Real) : EReal) := by simp [EReal.coe_mul]
        have hsum'' :
            ∑ j, ((w' j * a (e j) : Real) : EReal) =
              ((∑ j, w' j * a (e j) : Real) : EReal) := by
          simpa using (ereal_coe_sum (s := Finset.univ) (f := fun j => w' j * a (e j)))
        calc
          z1 = ∑ j, ((w' j : Real) : EReal) * f (x'' (e j)) := rfl
          _ = ((∑ j, w' j * a (e j) : Real) : EReal) := by exact hsum'.trans hsum''
      have hz1_le : z1 ≤ z := by
        have hobj_le' :
            ((∑ j, w' j * a (e j) : Real) : EReal) ≤
              ((∑ i, lam i * a i : Real) : EReal) :=
          (EReal.coe_le_coe_iff).2 hobj_le
        simpa [a, hz1_coe, hz_coe] using hobj_le'
      exact ⟨z1, hz1_mem, hz1_le⟩
  have B2_to_B1 : ∀ {z}, z ∈ B2 → z ∈ B1 := by
    intro z hz
    rcases hz with ⟨x', w, hw, hxcomb, hz⟩
    refine ⟨n + 1, le_rfl, x', w, hw, hxcomb, hz⟩
  have B1_to_B2_exists_le :
      ∀ {z}, z ∈ B1 → ∃ z2, z2 ∈ B2 ∧ z2 ≤ z := by
    intro z hz
    rcases hz with ⟨m, hm, x', w, hw, hxcomb, hz⟩
    rcases
        pad_convexCombination_to_fin_add_one (f := f) (n := n) (m := m) hm (x' := x') (w := w) hw with
      ⟨x'', w'', hw'', hx'', hz''⟩
    have hxcomb' : x = convexCombination n (n + 1) x'' w'' := by
      calc
        x = convexCombination n m x' w := hxcomb
        _ = convexCombination n (n + 1) x'' w'' := by symm; exact hx''
    refine ⟨z, ?_, le_rfl⟩
    refine ⟨x'', w'', hw'', hxcomb', ?_⟩
    calc
      z = ∑ i, ((w i : Real) : EReal) * f (x' i) := hz
      _ = ∑ i, ((w'' i : Real) : EReal) * f (x'' i) := by symm; exact hz''
  have hle01 : sInf B0 ≤ sInf B1 := by
    refine le_sInf ?_
    intro z hz
    exact sInf_le (B1_to_B0 hz)
  have hge01 : sInf B1 ≤ sInf B0 := by
    refine le_sInf ?_
    intro z hz
    rcases B0_to_B1_exists_le hz with ⟨z1, hz1, hz1le⟩
    exact le_trans (sInf_le hz1) hz1le
  have hEq01 : sInf B0 = sInf B1 := le_antisymm hle01 hge01
  have hle12 : sInf B1 ≤ sInf B2 := by
    refine le_sInf ?_
    intro z hz
    exact sInf_le (B2_to_B1 hz)
  have hge12 : sInf B2 ≤ sInf B1 := by
    refine le_sInf ?_
    intro z hz
    rcases B1_to_B2_exists_le hz with ⟨z2, hz2, hz2le⟩
    exact le_trans (sInf_le hz2) hz2le
  have hEq12 : sInf B1 = sInf B2 := le_antisymm hle12 hge12
  calc
    convexHullFunction f x = sInf B0 := hconv
    _ = sInf B1 := hEq01
    _ = sInf B2 := hEq12

end Section17
end Chap04
