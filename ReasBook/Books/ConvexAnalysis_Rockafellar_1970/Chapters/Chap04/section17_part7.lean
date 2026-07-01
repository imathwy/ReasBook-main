/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yunfei Zhang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section17_part6

open scoped BigOperators Pointwise
open Topology

section Chap04
section Section17

/-- If `f` is finite somewhere, then so is `convexHullFunction f`. -/
lemma convexHullFunction_exists_ne_top_of_exists_f_ne_top {n : Nat}
    {f : (Fin n → Real) → EReal} :
    (∃ x, f x ≠ (⊤ : EReal)) → ∃ x, convexHullFunction f x ≠ (⊤ : EReal) := by
  intro h
  rcases h with ⟨x, hx⟩
  rcases (convexHullFunction_greatest_convex_minorant (g := f)) with ⟨_hconv, hle, -⟩
  refine ⟨x, ?_⟩
  intro htop
  have htop_le : (⊤ : EReal) ≤ f x := by
    simpa [htop] using hle x
  have htop_eq : f x = (⊤ : EReal) := (top_le_iff).1 htop_le
  exact hx htop_eq

/-- Positive-scalar infimum representation for `posHomGen` of `convexHullFunction`. -/
lemma posHomGen_convexHullFunction_eq_sInf_pos_rightScalarMultiple {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hfinite : ∃ x, f x ≠ (⊤ : EReal)) :
    ∀ x : Fin n → Real,
      x ≠ 0 →
        positivelyHomogeneousConvexFunctionGenerated (convexHullFunction f) x =
          sInf { z : EReal |
            ∃ lam : Real, 0 < lam ∧
              z = rightScalarMultiple (convexHullFunction f) lam x } := by
  intro x hx
  have hconv :
      ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (convexHullFunction f) := by
    simpa using (convexHullFunction_greatest_convex_minorant (g := f)).1
  have hfinite' :
      ∃ x, convexHullFunction f x ≠ (⊤ : EReal) :=
    convexHullFunction_exists_ne_top_of_exists_f_ne_top (f := f) hfinite
  have hmain :=
    (infimumRepresentation_posHomogeneousHull (n := n)
      (h := convexHullFunction f) hconv hfinite').2
  have hmain' := hmain x (Or.inl hx)
  simpa using hmain'

/-- Expand `rightScalarMultiple` of `convexHullFunction` into scaled convex-combination data. -/
lemma rightScalarMultiple_convexHullFunction_eq_sInf_scaled_convexCombination_add_one
    {n : Nat} {f : (Fin n → Real) → EReal} (h_not_bot : ∀ x, f x ≠ (⊥ : EReal))
    {lam : Real} (hlam : 0 < lam) (x : Fin n → Real) :
    rightScalarMultiple (convexHullFunction f) lam x =
      sInf { z : EReal |
        ∃ (x' : Fin (n + 1) → Fin n → Real) (w : Fin (n + 1) → Real),
          IsConvexWeights (n + 1) w ∧
            x = ∑ i, (lam * w i) • x' i ∧
            z = ∑ i, ((lam * w i : Real) : EReal) * f (x' i) } := by
  classical
  let g := convexHullFunction f
  have hconv :
      ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) g := by
    simpa [g] using (convexHullFunction_greatest_convex_minorant (g := f)).1
  have hpos :
      rightScalarMultiple g lam x = (lam : EReal) * g (lam⁻¹ • x) :=
    rightScalarMultiple_pos (f := g) hconv hlam x
  let B : Set EReal :=
    { z : EReal |
      ∃ (x' : Fin (n + 1) → Fin n → Real) (w : Fin (n + 1) → Real),
        IsConvexWeights (n + 1) w ∧
          lam⁻¹ • x = convexCombination n (n + 1) x' w ∧
          z = ∑ i, ((w i : Real) : EReal) * f (x' i) }
  have hB : g (lam⁻¹ • x) = sInf B := by
    simpa [g, B] using
      (convexHullFunction_eq_sInf_convexCombination_add_one (f := f) (h_not_bot := h_not_bot)
        (x := lam⁻¹ • x))
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
      ∃ (x' : Fin (n + 1) → Fin n → Real) (w : Fin (n + 1) → Real),
        IsConvexWeights (n + 1) w ∧
          x = ∑ i, (lam * w i) • x' i ∧
          z = ∑ i, ((lam * w i : Real) : EReal) * f (x' i) }
  have hC : ((fun z : EReal => (lam : EReal) * z) '' B) = C := by
    ext z
    constructor
    · rintro ⟨z0, hz0, rfl⟩
      rcases hz0 with ⟨x', w, hw, hxcomb, hz0⟩
      refine ⟨x', w, hw, ?_, ?_⟩
      ·
        have hx1 : x = lam • (lam⁻¹ • x) := by
          have hlam_ne : lam ≠ 0 := ne_of_gt hlam
          calc
            x = (1 : Real) • x := by simp
            _ = (lam * lam⁻¹) • x := by simp [hlam_ne]
            _ = lam • (lam⁻¹ • x) := by simp [smul_smul]
        have hx2 : lam • (lam⁻¹ • x) = ∑ i, (lam * w i) • x' i := by
          calc
            lam • (lam⁻¹ • x) = lam • convexCombination n (n + 1) x' w := by
              simp [hxcomb]
            _ = ∑ i, (lam * w i) • x' i := by
              simp [convexCombination, Finset.smul_sum, smul_smul]
        exact hx1.trans hx2
      ·
        calc
          (lam : EReal) * z0 =
              (lam : EReal) * ∑ i, ((w i : Real) : EReal) * f (x' i) := by
                simp [hz0]
          _ = ∑ i, (lam : EReal) * (((w i : Real) : EReal) * f (x' i)) := by
                have hlam_nonneg : (0 : EReal) ≤ (lam : EReal) := by
                  exact_mod_cast (le_of_lt hlam)
                have hlam_ne_top : (lam : EReal) ≠ ⊤ := by simp
                simpa using
                  (ereal_mul_sum (s := (Finset.univ : Finset (Fin (n + 1))))
                    (f := fun i => ((w i : Real) : EReal) * f (x' i))
                    (a := (lam : EReal)) hlam_nonneg hlam_ne_top)
          _ = ∑ i, ((lam * w i : Real) : EReal) * f (x' i) := by
                simp [mul_assoc, EReal.coe_mul]
    · rintro ⟨x', w, hw, hxsum, hz⟩
      refine ⟨∑ i, ((w i : Real) : EReal) * f (x' i), ?_, ?_⟩
      ·
        refine ⟨x', w, hw, ?_, rfl⟩
        have hx1 : lam⁻¹ • x = ∑ i, w i • x' i := by
          have hlam_ne : lam ≠ 0 := ne_of_gt hlam
          have hx2 : lam⁻¹ • x = lam⁻¹ • ∑ i, (lam * w i) • x' i := by
            simp [hxsum]
          calc
            lam⁻¹ • x = lam⁻¹ • ∑ i, (lam * w i) • x' i := hx2
            _ = ∑ i, (lam⁻¹ * (lam * w i)) • x' i := by
                  simp [Finset.smul_sum, smul_smul, mul_comm, mul_assoc]
            _ = ∑ i, w i • x' i := by
                  simp [hlam_ne]
        simpa [convexCombination] using hx1
      ·
        calc
          (lam : EReal) * ∑ i, ((w i : Real) : EReal) * f (x' i) =
              ∑ i, (lam : EReal) * (((w i : Real) : EReal) * f (x' i)) := by
                have hlam_nonneg : (0 : EReal) ≤ (lam : EReal) := by
                  exact_mod_cast (le_of_lt hlam)
                have hlam_ne_top : (lam : EReal) ≠ ⊤ := by simp
                simpa using
                  (ereal_mul_sum (s := (Finset.univ : Finset (Fin (n + 1))))
                    (f := fun i => ((w i : Real) : EReal) * f (x' i))
                    (a := (lam : EReal)) hlam_nonneg hlam_ne_top)
          _ = ∑ i, ((lam * w i : Real) : EReal) * f (x' i) := by
                simp [mul_assoc, EReal.coe_mul]
          _ = z := by simp [hz]
  calc
    rightScalarMultiple g lam x = (lam : EReal) * g (lam⁻¹ • x) := hpos
    _ = (lam : EReal) * sInf B := by simp [hB]
    _ = sInf ((fun z : EReal => (lam : EReal) * z) '' B) := hmap
    _ = sInf C := by simp [hC]

/-- Flatten the positive-scalar infimum into explicit scaled convex-combination data. -/
lemma sInf_pos_rightScalarMultiple_convexHullFunction_eq_sInf_exists_scaled_convexCombination_add_one
    {n : Nat} {f : (Fin n → Real) → EReal} (h_not_bot : ∀ x, f x ≠ (⊥ : EReal))
    (x : Fin n → Real) :
    sInf { z : EReal | ∃ lam : Real, 0 < lam ∧
      z = rightScalarMultiple (convexHullFunction f) lam x } =
      sInf { z : EReal |
        ∃ lam : Real, 0 < lam ∧
          ∃ (x' : Fin (n + 1) → Fin n → Real) (w : Fin (n + 1) → Real),
            IsConvexWeights (n + 1) w ∧
              x = ∑ i, (lam * w i) • x' i ∧
              z = ∑ i, ((lam * w i : Real) : EReal) * f (x' i) } := by
  classical
  let g := convexHullFunction f
  let B : {lam : Real // 0 < lam} → Set EReal := fun lam =>
    { z : EReal |
      ∃ (x' : Fin (n + 1) → Fin n → Real) (w : Fin (n + 1) → Real),
        IsConvexWeights (n + 1) w ∧
          x = ∑ i, (lam.1 * w i) • x' i ∧
          z = ∑ i, ((lam.1 * w i : Real) : EReal) * f (x' i) }
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
      (rightScalarMultiple_convexHullFunction_eq_sInf_scaled_convexCombination_add_one
        (f := f) (h_not_bot := h_not_bot) (lam := lam.1) (hlam := lam.2) (x := x))
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
            ∃ (x' : Fin (n + 1) → Fin n → Real) (w : Fin (n + 1) → Real),
              IsConvexWeights (n + 1) w ∧
                x = ∑ i, (lam * w i) • x' i ∧
                z = ∑ i, ((lam * w i : Real) : EReal) * f (x' i) } := by
    ext z
    constructor
    · rintro ⟨lam, hz⟩
      rcases hz with ⟨x', w, hw, hxsum, hz⟩
      exact ⟨lam.1, lam.2, x', w, hw, hxsum, hz⟩
    · rintro ⟨lam, hlam, x', w, hw, hxsum, hz⟩
      exact ⟨⟨lam, hlam⟩, ⟨x', w, hw, hxsum, hz⟩⟩
  calc
    sInf { z : EReal |
        ∃ lam : Real, 0 < lam ∧ z = rightScalarMultiple g lam x } =
        ⨅ lam : {lam : Real // 0 < lam}, sInf (B lam) := hS
    _ = sInf {z : EReal | ∃ lam : {lam : Real // 0 < lam}, z ∈ B lam} := hflat
    _ = sInf { z : EReal |
        ∃ lam : Real, 0 < lam ∧
          ∃ (x' : Fin (n + 1) → Fin n → Real) (w : Fin (n + 1) → Real),
            IsConvexWeights (n + 1) w ∧
              x = ∑ i, (lam * w i) • x' i ∧
              z = ∑ i, ((lam * w i : Real) : EReal) * f (x' i) } := by
        exact congrArg sInf hBset

/-- Replace scaled convex weights by nonnegative coefficients (allowing zeros). -/
lemma scaled_convexCombination_add_one_witness_iff_nonneg_coeff_witness
    {n : Nat} {f : (Fin n → Real) → EReal} {x : Fin n → Real} (hx : x ≠ 0) :
    sInf { z : EReal |
      ∃ lam : Real, 0 < lam ∧
        ∃ (x' : Fin (n + 1) → Fin n → Real) (w : Fin (n + 1) → Real),
          IsConvexWeights (n + 1) w ∧
            x = ∑ i, (lam * w i) • x' i ∧
            z = ∑ i, ((lam * w i : Real) : EReal) * f (x' i) } =
      sInf { z : EReal |
        ∃ (x' : Fin (n + 1) → Fin n → Real) (c : Fin (n + 1) → Real),
          (∀ i, 0 ≤ c i) ∧
            x = ∑ i, c i • x' i ∧
            z = ∑ i, ((c i : Real) : EReal) * f (x' i) } := by
  classical
  let S1 : Set EReal :=
    { z : EReal |
      ∃ lam : Real, 0 < lam ∧
        ∃ (x' : Fin (n + 1) → Fin n → Real) (w : Fin (n + 1) → Real),
          IsConvexWeights (n + 1) w ∧
            x = ∑ i, (lam * w i) • x' i ∧
            z = ∑ i, ((lam * w i : Real) : EReal) * f (x' i) }
  let S2 : Set EReal :=
    { z : EReal |
      ∃ (x' : Fin (n + 1) → Fin n → Real) (c : Fin (n + 1) → Real),
        (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • x' i ∧
          z = ∑ i, ((c i : Real) : EReal) * f (x' i) }
  have hset : S1 = S2 := by
    ext z
    constructor
    · rintro ⟨lam, hlam, x', w, hw, hxsum, hz⟩
      let c : Fin (n + 1) → Real := fun i => lam * w i
      have hc : ∀ i, 0 ≤ c i := by
        intro i
        exact mul_nonneg (le_of_lt hlam) (hw.1 i)
      refine ⟨x', c, hc, ?_, ?_⟩
      · simpa [c] using hxsum
      · simpa [c] using hz
    · rintro ⟨x', c, hc, hxsum, hz⟩
      have hsum_pos : 0 < ∑ i, c i := by
        by_contra hpos
        have hle : ∑ i, c i ≤ 0 := le_of_not_gt hpos
        have hge : 0 ≤ ∑ i, c i := by
          refine Finset.sum_nonneg ?_
          intro i hi
          exact hc i
        have hsum0 : ∑ i, c i = 0 := le_antisymm hle hge
        have hzero : ∀ i, c i = 0 := by
          have hzero' :
              ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))), c i = 0 :=
            (Finset.sum_eq_zero_iff_of_nonneg
              (s := (Finset.univ : Finset (Fin (n + 1))))
              (f := fun i => c i)
              (by intro i hi; exact hc i)).1 hsum0
          intro i
          exact hzero' i (by simp)
        have hx0 : x = 0 := by
          simpa [hzero] using hxsum
        exact (hx hx0).elim
      let lam : Real := ∑ i, c i
      have hlam : 0 < lam := by simpa [lam] using hsum_pos
      let w : Fin (n + 1) → Real := fun i => c i / lam
      have hw_nonneg : ∀ i, 0 ≤ w i := by
        intro i
        exact div_nonneg (hc i) (le_of_lt hlam)
      have hsum_w : ∑ i, w i = 1 := by
        have hlam_ne : lam ≠ 0 := ne_of_gt hlam
        calc
          ∑ i, w i = ∑ i, c i * lam⁻¹ := by
            simp [w, div_eq_mul_inv]
          _ = (∑ i, c i) * lam⁻¹ := by
            symm
            simpa using
              (Finset.sum_mul (s := (Finset.univ : Finset (Fin (n + 1))))
                (f := fun i => c i) (a := lam⁻¹))
          _ = lam⁻¹ * ∑ i, c i := by
            simp [mul_comm]
          _ = 1 := by
            simp [lam, inv_mul_cancel₀ (a := lam) hlam_ne]
      have hw : IsConvexWeights (n + 1) w := ⟨hw_nonneg, hsum_w⟩
      have hmul : ∀ i, lam * w i = c i := by
        intro i
        have hlam_ne : lam ≠ 0 := ne_of_gt hlam
        calc
          lam * w i = lam * (c i / lam) := by rfl
          _ = (lam * c i) / lam := by
                simpa using (mul_div_assoc lam (c i) lam).symm
          _ = c i := by
                simpa [mul_comm] using (mul_div_cancel_left₀ (b := c i) (a := lam) hlam_ne)
      have hxsum' : x = ∑ i, (lam * w i) • x' i := by
        have hsum_eq :
            ∑ i, (lam * w i) • x' i = ∑ i, c i • x' i := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simp [hmul]
        simpa [hsum_eq] using hxsum
      have hz' :
          z = ∑ i, ((lam * w i : Real) : EReal) * f (x' i) := by
        have hsum_eq :
            ∑ i, ((c i : Real) : EReal) * f (x' i) =
              ∑ i, ((lam * w i : Real) : EReal) * f (x' i) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simp [hmul]
        simpa [hsum_eq, EReal.coe_mul, mul_assoc] using hz
      exact ⟨lam, hlam, x', w, hw, hxsum', hz'⟩
  exact congrArg sInf hset

/-- Convert an `EReal` objective into a real sum for nonnegative coefficients. -/
lemma toReal_objective_of_sum_ne_top_for_nonnegCoeffs {n m : Nat}
    {f : (Fin n → Real) → EReal} (h_not_bot : ∀ x, f x ≠ (⊥ : EReal))
    {x' : Fin m → Fin n → Real} {c : Fin m → Real} {x : Fin n → Real} {z : EReal}
    (hc : ∀ i, 0 ≤ c i) (hx : x = ∑ i, c i • x' i) (hx_ne : x ≠ 0)
    (hz : z = ∑ i, ((c i : Real) : EReal) * f (x' i)) (hz_top : z ≠ ⊤) :
    ∃ x'' : Fin m → Fin n → Real,
      x = ∑ i, c i • x'' i ∧
      (∀ i, f (x'' i) ≠ ⊤) ∧
      z = ((∑ i, c i * (f (x'' i)).toReal : Real) : EReal) := by
  classical
  have hpos_exists : ∃ i, 0 < c i := by
    by_contra hpos
    have hzero : ∀ i, c i = 0 := by
      intro i
      have hle : c i ≤ 0 := le_of_not_gt ((not_exists.mp hpos) i)
      exact le_antisymm hle (hc i)
    have hx0 : x = 0 := by
      simpa [hzero] using hx
    exact (hx_ne hx0).elim
  have hnot_top_pos : ∀ i, 0 < c i → f (x' i) ≠ ⊤ := by
    intro i hi
    by_contra htop
    have hposE : (0 : EReal) < (c i : EReal) := (EReal.coe_pos).2 hi
    have hterm_top :
        ((c i : Real) : EReal) * f (x' i) = ⊤ := by
      simpa [htop] using (EReal.mul_top_of_pos (x := (c i : EReal)) hposE)
    have hsum_ne_bot :
        (Finset.univ.erase i).sum
            (fun j => ((c j : Real) : EReal) * f (x' j)) ≠ ⊥ := by
      refine
        sum_ne_bot_of_ne_bot (s := Finset.univ.erase i)
          (f := fun j => ((c j : Real) : EReal) * f (x' j)) ?_
      intro j hj
      have hne_bot : f (x' j) ≠ ⊥ := h_not_bot (x' j)
      refine (EReal.mul_ne_bot ((c j : Real) : EReal) (f (x' j))).2 ?_
      refine ⟨?_, ?_, ?_, ?_⟩
      · left
        exact EReal.coe_ne_bot _
      · right
        exact hne_bot
      · left
        exact EReal.coe_ne_top _
      · left
        exact (EReal.coe_nonneg).2 (hc j)
    have hsum_top :
        (∑ j, ((c j : Real) : EReal) * f (x' j)) = ⊤ := by
      have hsum :=
        (Finset.add_sum_erase (s := Finset.univ)
          (f := fun j => ((c j : Real) : EReal) * f (x' j))
          (a := i) (h := by simp))
      calc
        (∑ j, ((c j : Real) : EReal) * f (x' j)) =
            ((c i : Real) : EReal) * f (x' i) +
              (Finset.univ.erase i).sum
                (fun j => ((c j : Real) : EReal) * f (x' j)) := by
          simpa using hsum.symm
        _ = ⊤ := by
          simpa [hterm_top] using (EReal.top_add_of_ne_bot hsum_ne_bot)
    have hz' : z = ⊤ := by
      simpa [hz] using hsum_top
    exact hz_top hz'
  obtain ⟨i0, hi0pos⟩ := hpos_exists
  have hi0top : f (x' i0) ≠ ⊤ := hnot_top_pos i0 hi0pos
  let x'' : Fin m → Fin n → Real := fun i => if c i = 0 then x' i0 else x' i
  have hsumx' :
      ∑ i, c i • x'' i = ∑ i, c i • x' i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hci : c i = 0
    · simp [x'', hci]
    · simp [x'', hci]
  have hx' : x = ∑ i, c i • x'' i := by
    calc
      x = ∑ i, c i • x' i := hx
      _ = ∑ i, c i • x'' i := by symm; exact hsumx'
  have hnot_top : ∀ i, f (x'' i) ≠ ⊤ := by
    intro i
    by_cases hci : c i = 0
    · simp [x'', hci, hi0top]
    · have hpos : 0 < c i := lt_of_le_of_ne (hc i) (Ne.symm hci)
      have hnot : f (x' i) ≠ ⊤ := hnot_top_pos i hpos
      simp [x'', hci, hnot]
  have hsum_x'' :
      ∑ i, ((c i : Real) : EReal) * f (x'' i) =
        ∑ i, ((c i : Real) : EReal) * f (x' i) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hci : c i = 0
    · simp [x'', hci]
    · simp [x'', hci]
  have hz' : z = ∑ i, ((c i : Real) : EReal) * f (x'' i) := by
    calc
      z = ∑ i, ((c i : Real) : EReal) * f (x' i) := hz
      _ = ∑ i, ((c i : Real) : EReal) * f (x'' i) := by symm; exact hsum_x''
  let a : Fin m → Real := fun i => (f (x'' i)).toReal
  have hsum' :
      ∑ i, ((c i : Real) : EReal) * f (x'' i) =
        ∑ i, ((c i * a i : Real) : EReal) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have htop : f (x'' i) ≠ ⊤ := hnot_top i
    have hbot : f (x'' i) ≠ ⊥ := h_not_bot (x'' i)
    have hcoe : (a i : EReal) = f (x'' i) := by
      simpa [a] using (EReal.coe_toReal htop hbot)
    calc
      ((c i : Real) : EReal) * f (x'' i)
          = ((c i : Real) : EReal) * (a i : EReal) := by simp [hcoe]
      _ = ((c i * a i : Real) : EReal) := by simp [EReal.coe_mul]
  have hsum'' :
      ∑ i, ((c i * a i : Real) : EReal) =
        ((∑ i, c i * a i : Real) : EReal) := by
    simpa using (ereal_coe_sum (s := Finset.univ) (f := fun i => c i * a i))
  refine ⟨x'', hx', hnot_top, ?_⟩
  calc
    z = ∑ i, ((c i : Real) : EReal) * f (x'' i) := hz'
    _ = ((∑ i, c i * a i : Real) : EReal) := by exact hsum'.trans hsum''

/-- Eliminate one generator from a positive conic combination without increasing a linear
objective, assuming the coefficients are objective-minimal among feasible ones. -/
lemma conic_elim_one_generator_pos_obj_to_shorter_fin {n m : Nat}
    {x : Fin n → Real}
    (v : Fin (m + 1) → Fin n → Real) (c : Fin (m + 1) → Real)
    (a : Fin (m + 1) → Real)
    (hcpos : ∀ i, 0 < c i) (hx : x = ∑ i, c i • v i)
    (hlin : ¬ LinearIndependent ℝ v)
    (hmin :
      ∀ c1 : Fin (m + 1) → Real, (∀ i, 0 ≤ c1 i) →
        x = ∑ i, c1 i • v i →
          (∑ i, c i * a i) ≤ ∑ i, c1 i * a i) :
    ∃ e : Fin m ↪ Fin (m + 1), ∃ c' : Fin m → Real,
      (∀ j, 0 ≤ c' j) ∧
        x = ∑ j, c' j • v (e j) ∧
        (∑ j, c' j * a (e j) ≤ ∑ i, c i * a i) := by
  classical
  obtain ⟨μ, hμsum, hμpos⟩ :=
    exists_linear_relation_sum_smul_eq_zero_exists_pos (s := v) hlin
  have hobj : 0 ≤ ∑ i, μ i * a i := by
    have hexists_t : ∃ t > 0, ∀ i, 0 ≤ c i + t * μ i := by
      let Pneg : Finset (Fin (m + 1)) := Finset.univ.filter (fun i => μ i < 0)
      by_cases hPneg : Pneg.Nonempty
      ·
        obtain ⟨i0, hi0P, hmin⟩ :=
          Finset.exists_min_image Pneg (fun i => c i / (- μ i)) hPneg
        have hμneg : μ i0 < 0 := (Finset.mem_filter.mp hi0P).2
        have hpos_ratio : 0 < c i0 / (- μ i0) := by
          have hpos : 0 < - μ i0 := by linarith
          exact div_pos (hcpos i0) hpos
        let t : Real := (c i0 / (- μ i0)) / 2
        have ht_pos : 0 < t := by
          have htwo : (0 : Real) < 2 := by norm_num
          simpa [t] using (div_pos hpos_ratio htwo)
        refine ⟨t, ht_pos, ?_⟩
        intro i
        by_cases hμi : μ i < 0
        ·
          have hi : i ∈ Pneg := by simp [Pneg, hμi]
          have hmin_i : c i0 / (- μ i0) ≤ c i / (- μ i) := hmin i hi
          have ht_le : t ≤ c i / (- μ i) := by
            have ht_le' : t ≤ c i0 / (- μ i0) := by
              have : (c i0 / (- μ i0)) / 2 ≤ c i0 / (- μ i0) := by
                nlinarith [hpos_ratio]
              simpa [t] using this
            exact le_trans ht_le' hmin_i
          have hpos : 0 < - μ i := by linarith
          have hle' : t * (- μ i) ≤ c i := by
            have hle' :=
              (mul_le_mul_of_nonneg_right ht_le (le_of_lt hpos))
            have hne : - μ i ≠ 0 := by linarith
            have hcalc : (c i / (- μ i)) * (- μ i) = c i := by
              have hne' : μ i ≠ 0 := by
                intro hmu
                apply hne
                simp [hmu]
              field_simp [hne, hne']
            simpa [hcalc] using hle'
          have hnonneg : 0 ≤ c i - t * (- μ i) := sub_nonneg.mpr hle'
          simpa [sub_eq_add_neg, mul_neg] using hnonneg
        ·
          have hmu_ge : 0 ≤ μ i := le_of_not_gt hμi
          have hc_ge : 0 ≤ c i := le_of_lt (hcpos i)
          have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
          have hterm : 0 ≤ t * μ i := mul_nonneg ht_nonneg hmu_ge
          exact add_nonneg hc_ge hterm
      ·
        refine ⟨1, by norm_num, ?_⟩
        intro i
        have hmu_ge : 0 ≤ μ i := by
          have hnot : ¬ μ i < 0 := by
            intro hlt
            have : i ∈ Pneg := by simp [Pneg, hlt]
            exact hPneg ⟨i, this⟩
          exact le_of_not_gt hnot
        have hc_ge : 0 ≤ c i := le_of_lt (hcpos i)
        linarith
    rcases hexists_t with ⟨t, ht_pos, hc1⟩
    let c1 : Fin (m + 1) → Real := fun i => c i + t * μ i
    have hc1' : ∀ i, 0 ≤ c1 i := by
      intro i
      simpa [c1] using hc1 i
    have hx1 : x = ∑ i, c1 i • v i := by
      have hsum_expand :
          ∑ i, c1 i • v i =
            ∑ i, c i • v i + t • ∑ i, μ i • v i := by
        calc
          ∑ i, c1 i • v i = ∑ i, (c i + t * μ i) • v i := by rfl
          _ = ∑ i, (c i • v i + (t * μ i) • v i) := by
                refine Finset.sum_congr rfl ?_
                intro i _hi
                simp [add_smul]
          _ = ∑ i, c i • v i + ∑ i, (t * μ i) • v i := by
                simp [Finset.sum_add_distrib]
          _ = ∑ i, c i • v i + t • ∑ i, μ i • v i := by
                have hmul :
                    ∑ i, (t * μ i) • v i = t • ∑ i, μ i • v i := by
                  calc
                    ∑ i, (t * μ i) • v i = ∑ i, t • (μ i • v i) := by
                      refine Finset.sum_congr rfl ?_
                      intro i _hi
                      simp [mul_smul]
                    _ = t • ∑ i, μ i • v i := by
                      simp [Finset.smul_sum]
                simp [hmul]
      calc
        x = ∑ i, c i • v i := hx
        _ = ∑ i, c1 i • v i := by
              calc
                ∑ i, c i • v i =
                    ∑ i, c i • v i + t • ∑ i, μ i • v i := by
                      simp [hμsum]
                _ = ∑ i, c1 i • v i := by
                      symm
                      exact hsum_expand
    have hmin_le : (∑ i, c i * a i) ≤ ∑ i, c1 i * a i := hmin c1 hc1' hx1
    have hsum_obj :
        ∑ i, c1 i * a i = ∑ i, c i * a i + t * ∑ i, μ i * a i := by
      calc
        ∑ i, c1 i * a i = ∑ i, (c i + t * μ i) * a i := by rfl
        _ = ∑ i, (c i * a i + (t * μ i) * a i) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              ring
        _ = ∑ i, c i * a i + ∑ i, (t * μ i) * a i := by
              simp [Finset.sum_add_distrib]
        _ = ∑ i, c i * a i + t * ∑ i, μ i * a i := by
              have hsum_mul :
                  ∑ i, (t * μ i) * a i = t * ∑ i, μ i * a i := by
                have :
                    ∑ i, t * (μ i * a i) = t * ∑ i, μ i * a i := by
                  simpa using
                    (Finset.mul_sum (s := (Finset.univ : Finset (Fin (m + 1))))
                      (f := fun i => μ i * a i) (a := t)).symm
                simpa [mul_assoc] using this
              simp [hsum_mul]
    have hnonneg : 0 ≤ t * ∑ i, μ i * a i := by
      have : ∑ i, c i * a i ≤ ∑ i, c i * a i + t * ∑ i, μ i * a i := by
        simpa [hsum_obj] using hmin_le
      linarith
    nlinarith [hnonneg, ht_pos]
  let P : Finset (Fin (m + 1)) := Finset.univ.filter (fun i => 0 < μ i)
  have hPne : P.Nonempty := by
    rcases hμpos with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simp [P, hi]
  obtain ⟨i0, hi0P, hmin⟩ := Finset.exists_min_image P (fun i => c i / μ i) hPne
  have hμi0 : 0 < μ i0 := (Finset.mem_filter.mp hi0P).2
  have hμi0_ne : μ i0 ≠ 0 := ne_of_gt hμi0
  let lam : Real := c i0 / μ i0
  let c1 : Fin (m + 1) → Real := fun i => c i - lam * μ i
  have hlamnonneg : 0 ≤ lam := by
    exact div_nonneg (le_of_lt (hcpos i0)) (le_of_lt hμi0)
  have hci0 : c1 i0 = 0 := by
    have hmul : (c i0 / μ i0) * μ i0 = c i0 := by
      field_simp [hμi0_ne]
    have hmul' : lam * μ i0 = c i0 := by
      simpa [lam] using hmul
    simp [c1, hmul']
  have hc1 : ∀ i, 0 ≤ c1 i := by
    intro i
    by_cases hμpos_i : 0 < μ i
    · have hi : i ∈ P := by
        simp [P, hμpos_i]
      have hmin_i : lam ≤ c i / μ i := hmin i hi
      have hle : lam * μ i ≤ c i := (le_div_iff₀ hμpos_i).1 hmin_i
      exact sub_nonneg_of_le hle
    · have hμle : μ i ≤ 0 := le_of_not_gt hμpos_i
      have hterm : 0 ≤ -lam * μ i := by
        have : 0 ≤ lam * (-μ i) := mul_nonneg hlamnonneg (neg_nonneg.mpr hμle)
        simpa [mul_comm, mul_left_comm, mul_assoc, mul_neg, neg_mul] using this
      have hc_nonneg : 0 ≤ c i := le_of_lt (hcpos i)
      have : 0 ≤ c i + (-lam * μ i) := add_nonneg hc_nonneg hterm
      simpa [c1, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using this
  have hsum_c1 : x = ∑ i, c1 i • v i := by
    have hsum_expand :
        ∑ i, c i • v i = ∑ i, c1 i • v i + lam • ∑ i, μ i • v i := by
      calc
        ∑ i, c i • v i = ∑ i, (c1 i + lam * μ i) • v i := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simp [c1, sub_eq_add_neg, add_comm, add_left_comm]
        _ = ∑ i, c1 i • v i + ∑ i, (lam * μ i) • v i := by
          simp [add_smul, Finset.sum_add_distrib]
        _ = ∑ i, c1 i • v i + lam • ∑ i, μ i • v i := by
          have hmul :
              ∑ i, (lam * μ i) • v i = lam • ∑ i, μ i • v i := by
            calc
              ∑ i, (lam * μ i) • v i = ∑ i, lam • (μ i • v i) := by
                refine Finset.sum_congr rfl ?_
                intro i _hi
                simp [mul_smul]
              _ = lam • ∑ i, μ i • v i := by
                simp [Finset.smul_sum]
          simp [hmul]
    calc
      x = ∑ i, c i • v i := hx
      _ = ∑ i, c1 i • v i + lam • ∑ i, μ i • v i := hsum_expand
      _ = ∑ i, c1 i • v i := by
        simp [hμsum]
  have hobj_le :
      ∑ i, c1 i * a i ≤ ∑ i, c i * a i := by
    have hsum_obj :
        ∑ i, c1 i * a i = ∑ i, c i * a i - lam * ∑ i, μ i * a i := by
      calc
        ∑ i, c1 i * a i = ∑ i, (c i - lam * μ i) * a i := rfl
        _ = ∑ i, (c i * a i - (lam * μ i) * a i) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simpa using (sub_mul (c i) (lam * μ i) (a i))
        _ = ∑ i, c i * a i - ∑ i, (lam * μ i) * a i := by
          simp [Finset.sum_sub_distrib]
        _ = ∑ i, c i * a i - lam * ∑ i, μ i * a i := by
          have hsum_mul :
              ∑ i, (lam * μ i) * a i = lam * ∑ i, μ i * a i := by
            have : ∑ i, lam * (μ i * a i) = lam * ∑ i, μ i * a i := by
              simpa using
                (Finset.mul_sum (s := (Finset.univ : Finset (Fin (m + 1))))
                  (f := fun i => μ i * a i) (a := lam)).symm
            simpa [mul_assoc] using this
          simp [hsum_mul]
    have hnonneg : 0 ≤ lam * ∑ i, μ i * a i := by
      exact mul_nonneg hlamnonneg hobj
    have := sub_le_self (∑ i, c i * a i) hnonneg
    simpa [hsum_obj] using this
  rcases
      drop_zero_coeff_sum_smul_and_sum_mul_to_shorter_fin
        (n := n) (m := m) (v := v) (c := c1) (a := a) hc1 hsum_c1 i0 hci0 with
    ⟨e, c', hc', hx', hobj_eq⟩
  have hobj_le' :
      ∑ j, c' j * a (e j) ≤ ∑ i, c i * a i := by
    have hobj_eq' : ∑ j, c' j * a (e j) = ∑ i, c1 i * a i := hobj_eq
    exact hobj_eq'.le.trans hobj_le
  exact ⟨e, c', hc', hx', hobj_le'⟩

/- Existence of an objective-minimizing nonnegative coefficient vector for fixed generators. -/
-- TODO: requires an attainment or ε-minimizer argument.

/- Reduce a `Fin (n + 1)` witness to a `Fin n` witness with no larger objective
when the objective is finite. -/

/- Reduce `n + 1` generators to `n` for the conic objective. -/

end Section17
end Chap04
