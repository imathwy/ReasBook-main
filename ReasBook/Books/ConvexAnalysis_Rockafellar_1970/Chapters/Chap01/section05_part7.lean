/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yifan Bai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part6

section Chap01
section Section05

/-- Text 5.5.4: `conv(g)(x) = inf { λ_1 g(x_1) + ... + λ_m g(x_m) | λ_1 x_1 + ... + λ_m x_m = x }`,
where the infimum is taken over all convex combinations of points of `ℝ^n`, assuming `g`
never takes the value `-∞`. -/
theorem convexHullFunction_eq_sInf_convexCombination {n : Nat}
    {g : (Fin n → Real) → EReal} (h_not_bot : ∀ x, g x ≠ (⊥ : EReal)) :
    ∀ x : Fin n → Real,
      convexHullFunction g x =
        sInf { z : EReal |
          ∃ (m : Nat) (lam : Fin m → Real) (x' : Fin m → (Fin n → Real)),
            (∀ i, 0 ≤ lam i) ∧
            (Finset.univ.sum (fun i => lam i) = 1) ∧
            (Finset.univ.sum (fun i => lam i • x' i) = x) ∧
            z = Finset.univ.sum (fun i => ((lam i : Real) : EReal) * g (x' i)) } := by
  classical
  intro x
  let A : Set ℝ :=
    { μ : ℝ |
      (x, μ) ∈ convexHull ℝ (epigraph (S := (Set.univ : Set (Fin n → Real))) g) }
  let A' : Set EReal := (fun μ : ℝ => (μ : EReal)) '' A
  let B : Set EReal :=
    { z : EReal |
      ∃ (m : Nat) (lam : Fin m → Real) (x' : Fin m → (Fin n → Real)),
        (∀ i, 0 ≤ lam i) ∧
        (Finset.univ.sum (fun i => lam i) = 1) ∧
        (Finset.univ.sum (fun i => lam i • x' i) = x) ∧
        z = Finset.univ.sum (fun i => ((lam i : Real) : EReal) * g (x' i)) }
  have hle : sInf B ≤ sInf A' := by
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨μ, hμ, rfl⟩
    rcases
        (mem_convexHull_epigraph_iff_fin_combo (g := g) (x := x) (μ := μ)).1 hμ with
      ⟨m, lam, x', μ', h0, hsum1, hsumx, hsumμ, hleμ⟩
    let b : EReal :=
      Finset.univ.sum (fun i => ((lam i : Real) : EReal) * g (x' i))
    have hbmem : b ∈ B := by
      refine ⟨m, lam, x', h0, hsum1, hsumx, rfl⟩
    have hb : sInf B ≤ b := sInf_le hbmem
    have hsum_le :
        b ≤
          Finset.univ.sum (fun i => ((lam i : Real) : EReal) * (μ' i : EReal)) := by
      simpa [b] using
        (sum_ereal_mul_le_sum_of_le (g := g) (lam := lam) (x' := x') (μ' := μ') h0 hleμ)
    have hsumμE :
        Finset.univ.sum (fun i => ((lam i : Real) : EReal) * (μ' i : EReal)) = (μ : EReal) := by
      have hsum' :
          Finset.univ.sum (fun i => ((lam i : Real) : EReal) * (μ' i : EReal)) =
            Finset.univ.sum (fun i => ((lam i * μ' i : Real) : EReal)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [EReal.coe_mul]
      have hsum'' :
          Finset.univ.sum (fun i => ((lam i * μ' i : Real) : EReal)) =
            ((Finset.univ.sum (fun i => lam i * μ' i) : ℝ) : EReal) := by
        simpa using (ereal_coe_sum (s := Finset.univ) (f := fun i => lam i * μ' i))
      calc
        Finset.univ.sum (fun i => ((lam i : Real) : EReal) * (μ' i : EReal))
            = ((Finset.univ.sum (fun i => lam i * μ' i) : ℝ) : EReal) := by
                exact hsum'.trans hsum''
        _ = (μ : EReal) := by simp [hsumμ]
    exact le_trans hb (by simpa [hsumμE] using hsum_le)
  have hge : sInf A' ≤ sInf B := by
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨m, lam, x', h0, hsum1, hsumx, rfl⟩
    by_cases hztop :
        (Finset.univ.sum (fun i => ((lam i : Real) : EReal) * g (x' i)) = ⊤)
    · simp [hztop]
    · have hpos_exists : ∃ i, 0 < lam i := by
        by_contra hpos
        have h0' : ∀ i, lam i = 0 := by
          intro i
          have hle : lam i ≤ 0 := le_of_not_gt ((not_exists.mp hpos) i)
          exact le_antisymm hle (h0 i)
        have hsum0 : Finset.univ.sum (fun i => lam i) = 0 := by
          simp [h0']
        have hsum1' : (0 : Real) = 1 := by
          have hsum1'' := hsum1
          simp [hsum0] at hsum1''
        exact (one_ne_zero (α := Real)) hsum1'.symm
      have hnot_top_pos : ∀ i, 0 < lam i → g (x' i) ≠ ⊤ := by
        intro i hi
        by_contra htop
        have hposE : (0 : EReal) < (lam i : EReal) := (EReal.coe_pos).2 hi
        have hterm_top :
            ((lam i : Real) : EReal) * g (x' i) = ⊤ := by
          simpa [htop] using (EReal.mul_top_of_pos (x := (lam i : EReal)) hposE)
        have hsum_top :
            Finset.univ.sum (fun i => ((lam i : Real) : EReal) * g (x' i)) = ⊤ := by
          have hsum :=
            (Finset.add_sum_erase (s := Finset.univ)
              (f := fun i => ((lam i : Real) : EReal) * g (x' i))
              (a := i) (h := Finset.mem_univ i))
          have hsum_ne_bot :
              (Finset.univ.erase i).sum (fun i => ((lam i : Real) : EReal) * g (x' i)) ≠ ⊥ := by
            refine
              sum_ne_bot_of_ne_bot (s := Finset.univ.erase i)
                (f := fun i => ((lam i : Real) : EReal) * g (x' i)) ?_
            intro j hj
            have hne_bot : g (x' j) ≠ ⊥ := h_not_bot (x' j)
            refine (EReal.mul_ne_bot ((lam j : Real) : EReal) (g (x' j))).2 ?_
            refine ⟨?_, ?_, ?_, ?_⟩
            · left
              exact EReal.coe_ne_bot _
            · right
              exact hne_bot
            · left
              exact EReal.coe_ne_top _
            · left
              exact (EReal.coe_nonneg).2 (h0 j)
          calc
            Finset.univ.sum (fun i => ((lam i : Real) : EReal) * g (x' i))
                = ((lam i : Real) : EReal) * g (x' i) +
                    (Finset.univ.erase i).sum (fun i =>
                      ((lam i : Real) : EReal) * g (x' i)) := by
                  simpa using hsum.symm
            _ = ⊤ := by
                  simpa [hterm_top] using (EReal.top_add_of_ne_bot hsum_ne_bot)
        exact hztop hsum_top
      obtain ⟨i0, hi0pos⟩ := hpos_exists
      have hi0top : g (x' i0) ≠ ⊤ := hnot_top_pos i0 hi0pos
      let x'' : Fin m → (Fin n → Real) :=
        fun i => if lam i = 0 then x' i0 else x' i
      have hsumx' :
          Finset.univ.sum (fun i => lam i • x'' i) = x := by
        have hsum_eq :
            Finset.univ.sum (fun i => lam i • x'' i) =
              Finset.univ.sum (fun i => lam i • x' i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          by_cases hli : lam i = 0
          · simp [x'', hli]
          · simp [x'', hli]
        simpa [hsum_eq] using hsumx
      have hnot_top : ∀ i, g (x'' i) ≠ ⊤ := by
        intro i
        by_cases hli : lam i = 0
        · simp [x'', hli, hi0top]
        · have hpos : 0 < lam i := lt_of_le_of_ne (h0 i) (Ne.symm hli)
          have hnot : g (x' i) ≠ ⊤ := hnot_top_pos i hpos
          simp [x'', hli, hnot]
      let μ' : Fin m → Real := fun i => (g (x'' i)).toReal
      have hleμ' : ∀ i, g (x'' i) ≤ (μ' i : EReal) := by
        intro i
        have htop : g (x'' i) ≠ ⊤ := hnot_top i
        have hbot : g (x'' i) ≠ ⊥ := h_not_bot (x'' i)
        have hcoe : ((g (x'' i)).toReal : EReal) = g (x'' i) :=
          EReal.coe_toReal htop hbot
        simp [μ', hcoe]
      let μ : Real := Finset.univ.sum (fun i => lam i * μ' i)
      have hmem :
          (x, μ) ∈ convexHull ℝ (epigraph (S := (Set.univ : Set (Fin n → Real))) g) := by
        refine (mem_convexHull_epigraph_iff_fin_combo (g := g) (x := x) (μ := μ)).2 ?_
        refine ⟨m, lam, x'', μ', h0, hsum1, hsumx', rfl, hleμ'⟩
      have hmem' : (μ : EReal) ∈ A' := by
        refine ⟨μ, ?_, rfl⟩
        simpa [A] using hmem
      have hleA : sInf A' ≤ (μ : EReal) := sInf_le hmem'
      have hsum_x'' :
          Finset.univ.sum (fun i => ((lam i : Real) : EReal) * g (x'' i)) =
            Finset.univ.sum (fun i => ((lam i : Real) : EReal) * g (x' i)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases hli : lam i = 0
        · simp [x'', hli]
        · simp [x'', hli]
      have hsum_toReal :
          Finset.univ.sum (fun i => ((lam i : Real) : EReal) * g (x'' i)) = (μ : EReal) := by
        have hsum' :
            Finset.univ.sum (fun i => ((lam i : Real) : EReal) * g (x'' i)) =
              Finset.univ.sum (fun i => ((lam i * μ' i : Real) : EReal)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have htop : g (x'' i) ≠ ⊤ := hnot_top i
          have hbot : g (x'' i) ≠ ⊥ := h_not_bot (x'' i)
          have hcoe :
              (μ' i : EReal) = g (x'' i) := by
            simpa [μ'] using (EReal.coe_toReal htop hbot)
          calc
            ((lam i : Real) : EReal) * g (x'' i)
                = ((lam i : Real) : EReal) * (μ' i : EReal) := by
                    simp [hcoe]
            _ = ((lam i * μ' i : Real) : EReal) := by simp [EReal.coe_mul]
        have hsum'' :
            Finset.univ.sum (fun i => ((lam i * μ' i : Real) : EReal)) =
              ((Finset.univ.sum (fun i => lam i * μ' i) : ℝ) : EReal) := by
          simpa using
            (ereal_coe_sum (s := Finset.univ) (f := fun i => lam i * μ' i))
        have hsumμ : ((Finset.univ.sum (fun i => lam i * μ' i) : ℝ) : EReal) = (μ : EReal) := by
          rfl
        calc
          Finset.univ.sum (fun i => ((lam i : Real) : EReal) * g (x'' i))
              = ((Finset.univ.sum (fun i => lam i * μ' i) : ℝ) : EReal) := by
                  exact hsum'.trans hsum''
          _ = (μ : EReal) := hsumμ
      have hz_eq :
          (μ : EReal) =
            Finset.univ.sum (fun i => ((lam i : Real) : EReal) * g (x' i)) := by
        exact hsum_toReal.symm.trans hsum_x''
      simpa [hz_eq] using hleA
  have hEq : sInf A' = sInf B := le_antisymm hge hle
  simpa [convexHullFunction_eq_inf_section, A, A', B] using hEq

/-- Text 5.5.5: The convex hull of an arbitrary collection of functions `{f_i | i ∈ I}` on
`ℝ^n` is denoted `conv {f_i | i ∈ I}`. It is the function obtained via Theorem 5.3 from
the convex hull of the union of the epigraphs of the `f_i`. -/
noncomputable def convexHullFunctionFamily {n : Nat} {ι : Sort _}
    (f : ι → (Fin n → Real) → EReal) : (Fin n → Real) → EReal :=
  fun x =>
    sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ |
      (x, μ) ∈
        convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)) })
end Section05
end Chap01
