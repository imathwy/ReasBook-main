/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yifan Bai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part8

section Chap01
section Section05

/-- The `sInf` formula for indicator-plus-constant functions reduces to coefficients of `alpha`. -/
lemma sInf_convexCombination_indicator_eq {n : Nat} {ι : Sort _}
    (a : ι → Fin n → Real) (alpha : ι → Real) (x : Fin n → Real) :
    sInf { z : EReal |
      ∃ (s : Finset ι) (lam : ι → Real) (x' : ι → (Fin n → Real)),
        (∀ i, 0 ≤ lam i) ∧
        (∀ i, i ∉ s → lam i = 0) ∧
        (s.sum (fun i => lam i) = 1) ∧
        (s.sum (fun i => lam i • x' i) = x) ∧
        z = s.sum (fun i => ((lam i : Real) : EReal) *
          (indicatorFunction ({a i} : Set (Fin n → Real)) (x' i) + (alpha i : EReal))) }
      =
    sInf { z : EReal |
      ∃ (s : Finset ι) (lam : ι → Real),
        (∀ i, 0 ≤ lam i) ∧
        (∀ i, i ∉ s → lam i = 0) ∧
        (s.sum (fun i => lam i) = 1) ∧
        (s.sum (fun i => lam i • a i) = x) ∧
        z = s.sum (fun i => ((lam i : Real) : EReal) * (alpha i : EReal)) } := by
  classical
  let B : Set EReal :=
    { z : EReal |
      ∃ (s : Finset ι) (lam : ι → Real) (x' : ι → (Fin n → Real)),
        (∀ i, 0 ≤ lam i) ∧
        (∀ i, i ∉ s → lam i = 0) ∧
        (s.sum (fun i => lam i) = 1) ∧
        (s.sum (fun i => lam i • x' i) = x) ∧
        z = s.sum (fun i => ((lam i : Real) : EReal) *
          (indicatorFunction ({a i} : Set (Fin n → Real)) (x' i) + (alpha i : EReal))) }
  let B' : Set EReal :=
    { z : EReal |
      ∃ (s : Finset ι) (lam : ι → Real),
        (∀ i, 0 ≤ lam i) ∧
        (∀ i, i ∉ s → lam i = 0) ∧
        (s.sum (fun i => lam i) = 1) ∧
        (s.sum (fun i => lam i • a i) = x) ∧
        z = s.sum (fun i => ((lam i : Real) : EReal) * (alpha i : EReal)) }
  have hle : sInf B ≤ sInf B' := by
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨s, lam, h0, hzero, hsum1, hsumx, rfl⟩
    refine sInf_le ?_
    refine ⟨s, lam, (fun i => a i), h0, hzero, hsum1, ?_, ?_⟩
    · simpa using hsumx
    · simp [indicatorFunction_singleton_simp]
  have hge : sInf B' ≤ sInf B := by
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨s, lam, x', h0, hzero, hsum1, hsumx, rfl⟩
    by_cases hztop :
        s.sum (fun i => ((lam i : Real) : EReal) *
          (indicatorFunction ({a i} : Set (Fin n → Real)) (x' i) + (alpha i : EReal))) = ⊤
    · simp [hztop]
    · have hxa : ∀ i ∈ s, lam i ≠ 0 → x' i = a i := by
        intro i hi hne
        by_contra hneq
        have hpos : 0 < lam i := lt_of_le_of_ne (h0 i) (Ne.symm hne)
        have hposE : (0 : EReal) < (lam i : EReal) := (EReal.coe_pos).2 hpos
        have htop :
            indicatorFunction ({a i} : Set (Fin n → Real)) (x' i) + (alpha i : EReal) = ⊤ := by
          calc
            indicatorFunction ({a i} : Set (Fin n → Real)) (x' i) + (alpha i : EReal)
                = (⊤ : EReal) + (alpha i : EReal) := by
                    simp [indicatorFunction_singleton_simp, hneq]
            _ = ⊤ := EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)
        have hterm_top :
            ((lam i : Real) : EReal) *
              (indicatorFunction ({a i} : Set (Fin n → Real)) (x' i) + (alpha i : EReal)) = ⊤ := by
          simpa [htop] using (EReal.mul_top_of_pos (x := (lam i : EReal)) hposE)
        have hbot :
            ∀ j ∈ s,
              ((lam j : Real) : EReal) *
                (indicatorFunction ({a j} : Set (Fin n → Real)) (x' j)
                  + (alpha j : EReal)) ≠ ⊥ := by
          intro j hj
          have hne_bot :
              indicatorFunction ({a j} : Set (Fin n → Real)) (x' j) + (alpha j : EReal) ≠ ⊥ := by
            by_cases hxj : x' j = a j
            · simp [indicatorFunction_singleton_simp, hxj]
            · have htop' :
                  indicatorFunction ({a j} : Set (Fin n → Real)) (x' j)
                    + (alpha j : EReal) = ⊤ := by
                calc
                  indicatorFunction ({a j} : Set (Fin n → Real)) (x' j) + (alpha j : EReal)
                      = (⊤ : EReal) + (alpha j : EReal) := by
                          simp [indicatorFunction_singleton_simp, hxj]
                  _ = ⊤ := EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)
              simp [htop']
          refine
            (EReal.mul_ne_bot ((lam j : Real) : EReal)
              (indicatorFunction ({a j} : Set (Fin n → Real)) (x' j) + (alpha j : EReal))).2 ?_
          refine ⟨?_, ?_, ?_, ?_⟩
          · left
            exact EReal.coe_ne_bot _
          · right
            exact hne_bot
          · left
            exact EReal.coe_ne_top _
          · left
            exact (EReal.coe_nonneg).2 (h0 j)
        have hsum_top :
            s.sum (fun i => ((lam i : Real) : EReal) *
              (indicatorFunction ({a i} : Set (Fin n → Real)) (x' i) + (alpha i : EReal))) = ⊤ := by
          exact
            sum_eq_top_of_term_top (s := s)
              (f := fun i => ((lam i : Real) : EReal) *
                (indicatorFunction ({a i} : Set (Fin n → Real)) (x' i) + (alpha i : EReal)))
              (i := i) hi hterm_top hbot
        exact hztop hsum_top
      have hsumx' : s.sum (fun i => lam i • a i) = x := by
        have hsumx'' :
            s.sum (fun i => lam i • a i) =
              s.sum (fun i => lam i • x' i) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          by_cases hli : lam i = 0
          · simp [hli]
          · have hxa' : x' i = a i := hxa i hi hli
            simp [hxa']
        exact hsumx''.trans hsumx
      have hsum_alpha :
          s.sum (fun i => ((lam i : Real) : EReal) *
            (indicatorFunction ({a i} : Set (Fin n → Real)) (x' i) + (alpha i : EReal))) =
            s.sum (fun i => ((lam i : Real) : EReal) * (alpha i : EReal)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases hli : lam i = 0
        · simp [hli]
        · have hxa' : x' i = a i := hxa i hi hli
          simp [indicatorFunction_singleton_simp, hxa']
      have hzmem :
          s.sum (fun i => ((lam i : Real) : EReal) *
            (indicatorFunction ({a i} : Set (Fin n → Real)) (x' i) + (alpha i : EReal))) ∈ B' := by
        refine ⟨s, lam, h0, hzero, hsum1, hsumx', ?_⟩
        simp [hsum_alpha]
      exact sInf_le hzmem
  have hEq : sInf B = sInf B' := le_antisymm hle hge
  simpa [B, B'] using hEq

/-- Text 5.6.1: Suppose `f_i(x) = δ(x | a_i) + alpha_i`, so `f_i(x) = alpha_i` when
`x = a_i` and `f_i(x) = +∞` otherwise. Let `f` be the convex hull of `{f_i}`. Then `f`
is the greatest convex function with `f(a_i) ≤ alpha_i` for all `i`, and
`f(x) = inf { Σ_i lambda_i alpha_i | Σ_i lambda_i a_i = x }`, where the infimum ranges
over convex combinations with only finitely many nonzero coefficients. -/
theorem convexHullFunctionFamily_indicator_add_const {n : Nat} {ι : Sort _}
    (a : ι → Fin n → Real) (alpha : ι → Real) :
    let f : (Fin n → Real) → EReal :=
      convexHullFunctionFamily
        (fun i x =>
          indicatorFunction ({a i} : Set (Fin n → Real)) x + (alpha i : EReal));
    (ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f ∧
      (∀ i, f (a i) ≤ (alpha i : EReal)) ∧
      ∀ h : (Fin n → Real) → EReal,
        ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) h →
        (∀ i, h (a i) ≤ (alpha i : EReal)) →
        h ≤ f)
    ∧
    (∀ x : Fin n → Real,
      f x =
        sInf { z : EReal |
          ∃ (s : Finset ι) (lam : ι → Real),
            (∀ i, 0 ≤ lam i) ∧
            (∀ i, i ∉ s → lam i = 0) ∧
            (s.sum (fun i => lam i) = 1) ∧
            (s.sum (fun i => lam i • a i) = x) ∧
            z = s.sum (fun i => ((lam i : Real) : EReal) * (alpha i : EReal)) }) := by
  classical
  let fi : ι → (Fin n → Real) → EReal :=
    fun i x => indicatorFunction ({a i} : Set (Fin n → Real)) x + (alpha i : EReal)
  let f : (Fin n → Real) → EReal := convexHullFunctionFamily fi
  have hmain :
      (ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f ∧
        (∀ i, f (a i) ≤ (alpha i : EReal)) ∧
        ∀ h : (Fin n → Real) → EReal,
          ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) h →
          (∀ i, h (a i) ≤ (alpha i : EReal)) →
          h ≤ f)
      ∧
      (∀ x : Fin n → Real,
        f x =
          sInf { z : EReal |
            ∃ (s : Finset ι) (lam : ι → Real),
              (∀ i, 0 ≤ lam i) ∧
              (∀ i, i ∉ s → lam i = 0) ∧
              (s.sum (fun i => lam i) = 1) ∧
              (s.sum (fun i => lam i • a i) = x) ∧
              z = s.sum (fun i => ((lam i : Real) : EReal) * (alpha i : EReal)) }) := by
    have hgreat :
        ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f ∧
          (∀ i, f ≤ fi i) ∧
          ∀ h : (Fin n → Real) → EReal,
            ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) h →
            (∀ i, h ≤ fi i) →
            h ≤ f := by
      simpa [f] using (convexHullFunctionFamily_greatest_convex_minorant (f := fi))
    have hconv : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f := hgreat.1
    have hle : ∀ i, f ≤ fi i := hgreat.2.1
    have hmax :
        ∀ h : (Fin n → Real) → EReal,
          ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) h →
          (∀ i, h ≤ fi i) →
          h ≤ f := hgreat.2.2
    refine And.intro ?_ ?_
    · refine And.intro hconv ?_
      refine And.intro ?_ ?_
      · intro i
        have hle_ai : f (a i) ≤ fi i (a i) := (hle i) (a i)
        simpa [fi, indicator_add_const_at_point] using hle_ai
      · intro h hh hle_at
        have hle_fi : ∀ i, h ≤ fi i := by
          intro i
          exact
            le_indicator_add_const_of_le_at (h := h) (a := a i) (c := alpha i) (ha := hle_at i)
        exact hmax h hh hle_fi
    · intro x
      have hproper :
          ∀ i, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (fi i) := by
        intro i
        exact properConvexFunctionOn_indicator_add_const_singleton (a := a i) (c := alpha i)
      have hformula :
          f x =
            sInf { z : EReal |
              ∃ (s : Finset ι) (lam : ι → Real) (x' : ι → (Fin n → Real)),
                (∀ i, 0 ≤ lam i) ∧
                (∀ i, i ∉ s → lam i = 0) ∧
                (s.sum (fun i => lam i) = 1) ∧
                (s.sum (fun i => lam i • x' i) = x) ∧
                z = s.sum (fun i => ((lam i : Real) : EReal) * (fi i (x' i))) } := by
        simpa [f] using
          (convexHullFunctionFamily_eq_sInf_convexCombination (f := fi) hproper x)
      have hformula' :
          f x =
            sInf { z : EReal |
              ∃ (s : Finset ι) (lam : ι → Real) (x' : ι → (Fin n → Real)),
                (∀ i, 0 ≤ lam i) ∧
                (∀ i, i ∉ s → lam i = 0) ∧
                (s.sum (fun i => lam i) = 1) ∧
                (s.sum (fun i => lam i • x' i) = x) ∧
                z = s.sum (fun i => ((lam i : Real) : EReal) *
                  (indicatorFunction ({a i} : Set (Fin n → Real)) (x' i)
                    + (alpha i : EReal))) } := by
        simpa [fi] using hformula
      calc
        f x =
            sInf { z : EReal |
              ∃ (s : Finset ι) (lam : ι → Real) (x' : ι → (Fin n → Real)),
                (∀ i, 0 ≤ lam i) ∧
                (∀ i, i ∉ s → lam i = 0) ∧
                (s.sum (fun i => lam i) = 1) ∧
                (s.sum (fun i => lam i • x' i) = x) ∧
                z = s.sum (fun i => ((lam i : Real) : EReal) *
                  (indicatorFunction ({a i} : Set (Fin n → Real)) (x' i)
                    + (alpha i : EReal))) } := by
            exact hformula'
        _ =
            sInf { z : EReal |
              ∃ (s : Finset ι) (lam : ι → Real),
                (∀ i, 0 ≤ lam i) ∧
                (∀ i, i ∉ s → lam i = 0) ∧
                (s.sum (fun i => lam i) = 1) ∧
                (s.sum (fun i => lam i • a i) = x) ∧
                z = s.sum (fun i => ((lam i : Real) : EReal) * (alpha i : EReal)) } := by
            simpa using (sInf_convexCombination_indicator_eq (a := a) (alpha := alpha) (x := x))
  simpa [f, fi] using hmain

/-- Specialize the convex-combination formula to `Fin m` by using `Finset.univ`. -/
lemma convexHullFunctionFamily_eq_sInf_convexCombination_univ {n m : Nat}
    {f : Fin m → (Fin n → Real) → EReal}
    (hf : ∀ i, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (f i)) :
    ∀ x : Fin n → Real,
      convexHullFunctionFamily f x =
        sInf { z : EReal |
          ∃ (lam : Fin m → Real) (x' : Fin m → (Fin n → Real)),
            (∀ i, 0 ≤ lam i) ∧
            (Finset.univ.sum (fun i => lam i) = 1) ∧
            (Finset.univ.sum (fun i => lam i • x' i) = x) ∧
            z = Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) } := by
  classical
  intro x
  let B : Set EReal :=
    { z : EReal |
      ∃ (s : Finset (Fin m)) (lam : Fin m → Real) (x' : Fin m → (Fin n → Real)),
        (∀ i, 0 ≤ lam i) ∧
        (∀ i, i ∉ s → lam i = 0) ∧
        (s.sum (fun i => lam i) = 1) ∧
        (s.sum (fun i => lam i • x' i) = x) ∧
        z = s.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) }
  let B' : Set EReal :=
    { z : EReal |
      ∃ (lam : Fin m → Real) (x' : Fin m → (Fin n → Real)),
        (∀ i, 0 ≤ lam i) ∧
        (Finset.univ.sum (fun i => lam i) = 1) ∧
        (Finset.univ.sum (fun i => lam i • x' i) = x) ∧
        z = Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) }
  have hle : sInf B ≤ sInf B' := by
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨lam, x', h0, hsum1, hsumx, rfl⟩
    refine sInf_le ?_
    refine ⟨Finset.univ, lam, x', h0, ?_, ?_, ?_, rfl⟩
    · intro i hi
      exfalso
      simp at hi
    · simpa using hsum1
    · simpa using hsumx
  have hge : sInf B' ≤ sInf B := by
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨s, lam, x', h0, hzero, hsum1, hsumx, rfl⟩
    have hsum1' :
        s.sum (fun i => lam i) = Finset.univ.sum (fun i => lam i) := by
      refine Finset.sum_subset (s₁ := s) (s₂ := Finset.univ) ?_ ?_
      · intro i hi
        exact Finset.mem_univ i
      · intro i hi hnot
        simp [hzero i hnot]
    have hsum1'' : Finset.univ.sum (fun i => lam i) = 1 := by
      simpa [hsum1'] using hsum1
    have hsumx' :
        s.sum (fun i => lam i • x' i) =
          Finset.univ.sum (fun i => lam i • x' i) := by
      refine Finset.sum_subset (s₁ := s) (s₂ := Finset.univ) ?_ ?_
      · intro i hi
        exact Finset.mem_univ i
      · intro i hi hnot
        simp [hzero i hnot]
    have hsumx'' : Finset.univ.sum (fun i => lam i • x' i) = x := by
      simpa [hsumx'] using hsumx
    have hsumz' :
        s.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) =
          Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) := by
      refine Finset.sum_subset (s₁ := s) (s₂ := Finset.univ) ?_ ?_
      · intro i hi
        exact Finset.mem_univ i
      · intro i hi hnot
        simp [hzero i hnot]
    refine sInf_le ?_
    refine ⟨lam, x', h0, hsum1'', hsumx'', ?_⟩
    simp [hsumz']
  have hEq : sInf B = sInf B' := le_antisymm hle hge
  have hmain := convexHullFunctionFamily_eq_sInf_convexCombination (f := f) hf x
  simpa [B, B'] using hmain.trans hEq

/-- Right scalar multiple at a scaled point for a nonnegative coefficient. -/
lemma rightScalarMultiple_smul_eq {n m : Nat}
    {f : Fin m → (Fin n → Real) → EReal} {lam : Fin m → Real}
    (hf : ∀ i, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (f i))
    {i : Fin m} {x : Fin n → Real} (hlam : 0 ≤ lam i) :
    rightScalarMultiple (f i) (lam i) (lam i • x) =
      ((lam i : Real) : EReal) * f i x := by
  classical
  by_cases hzero : lam i = 0
  · have hne :
        Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) (f i)) := (hf i).2.1
    have hval := rightScalarMultiple_zero_eval (f := f i) hne (0 • x)
    simpa [hzero] using hval
  · have hpos : 0 < lam i := lt_of_le_of_ne hlam (Ne.symm hzero)
    have hval :=
      rightScalarMultiple_pos (f := f i) (lam := lam i) (_hf := (hf i).1) (hlam := hpos)
        (x := lam i • x)
    have hsmul : (lam i)⁻¹ • (lam i • x) = x := by
      simp [smul_smul, hzero]
    simpa [hsmul] using hval

/-- Change of variables for infimal convolution of right scalar multiples. -/
lemma infimalConvolutionFamily_rightScalarMultiple_eq_sInf {n m : Nat}
    {f : Fin m → (Fin n → Real) → EReal} {lam : Fin m → Real}
    (hf : ∀ i, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (f i))
    (hlam : ∀ i, 0 ≤ lam i) :
    ∀ x : Fin n → Real,
      infimalConvolutionFamily (fun i => rightScalarMultiple (f i) (lam i)) x =
        sInf { z : EReal |
          ∃ x' : Fin m → (Fin n → Real),
            (Finset.univ.sum (fun i => lam i • x' i) = x) ∧
            z = Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) } := by
  classical
  intro x
  let A : Set EReal :=
    { z : EReal |
      ∃ y : Fin m → (Fin n → Real),
        (Finset.univ.sum (fun i => y i) = x) ∧
        z = Finset.univ.sum (fun i => rightScalarMultiple (f i) (lam i) (y i)) }
  let B : Set EReal :=
    { z : EReal |
      ∃ x' : Fin m → (Fin n → Real),
        (Finset.univ.sum (fun i => lam i • x' i) = x) ∧
        z = Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) }
  have hle : sInf A ≤ sInf B := by
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨x', hsumx, rfl⟩
    refine sInf_le ?_
    refine ⟨fun i => lam i • x' i, ?_, ?_⟩
    · simpa using hsumx
    · refine Finset.sum_congr rfl ?_
      intro i hi
      simpa using
        (rightScalarMultiple_smul_eq (hf := hf) (lam := lam) (i := i) (x := x' i)
          (hlam := hlam i)).symm
  have hge : sInf B ≤ sInf A := by
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨y, hsumy, rfl⟩
    by_cases hztop :
        Finset.univ.sum (fun i => rightScalarMultiple (f i) (lam i) (y i)) = ⊤
    · simp [hztop]
    · have hy_zero : ∀ i, lam i = 0 → y i = 0 := by
        intro i hli
        by_contra hne
        have hne_epi :
            Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) (f i)) := (hf i).2.1
        have hval := rightScalarMultiple_zero_eval (f := f i) hne_epi (y i)
        have htop_term :
            rightScalarMultiple (f i) (lam i) (y i) = ⊤ := by
          simp [hli, hne, hval]
        have hbot :
            ∀ j ∈ Finset.univ,
              rightScalarMultiple (f j) (lam j) (y j) ≠ ⊥ := by
          intro j hj
          by_cases hlj : lam j = 0
          · have hne_epi :
              Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) (f j)) := (hf j).2.1
            by_cases hy : y j = 0
            · simp [hlj, hy, rightScalarMultiple_zero_eval (f := f j) hne_epi]
            · simp [hlj, hy, rightScalarMultiple_zero_eval (f := f j) hne_epi]
          · have hpos : 0 < lam j := lt_of_le_of_ne (hlam j) (Ne.symm hlj)
            have hval :=
              rightScalarMultiple_pos (f := f j) (lam := lam j) (_hf := (hf j).1)
                (hlam := hpos) (x := y j)
            have hnotbot :
                f j ((lam j)⁻¹ • y j) ≠ ⊥ := (hf j).2.2 _ (by simp)
            have hmul :
                ((lam j : Real) : EReal) * f j ((lam j)⁻¹ • y j) ≠ ⊥ :=
              ereal_mul_ne_bot_of_pos hpos hnotbot
            simpa [hval] using hmul
        have hsum_top :
            Finset.univ.sum (fun j => rightScalarMultiple (f j) (lam j) (y j)) = ⊤ := by
          exact
            sum_eq_top_of_term_top (s := Finset.univ)
              (f := fun j => rightScalarMultiple (f j) (lam j) (y j))
              (i := i) (by simp) htop_term hbot
        exact hztop hsum_top
      let x' : Fin m → (Fin n → Real) := fun i =>
        if h : lam i = 0 then 0 else (lam i)⁻¹ • y i
      have hsumx' :
          Finset.univ.sum (fun i => lam i • x' i) =
            Finset.univ.sum (fun i => y i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases hli : lam i = 0
        · have hy : y i = 0 := hy_zero i hli
          simp [x', hli, hy]
        · simp [x', hli, smul_smul]
      have hsumx : Finset.univ.sum (fun i => lam i • x' i) = x := by
        simpa [hsumx'] using hsumy
      have hsumz :
          Finset.univ.sum (fun i => rightScalarMultiple (f i) (lam i) (y i)) =
            Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases hli : lam i = 0
        · have hy : y i = 0 := hy_zero i hli
          have hne_epi :
              Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) (f i)) := (hf i).2.1
          simp [x', hli, hy, rightScalarMultiple_zero_eval (f := f i) hne_epi]
        · have hy : y i = lam i • x' i := by
            simp [x', hli, smul_smul]
          have hterm :=
            rightScalarMultiple_smul_eq (hf := hf) (lam := lam) (i := i) (x := x' i)
              (hlam := hlam i)
          simpa [hy] using hterm
      have hzmem :
          Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) ∈ B := by
        refine ⟨x', hsumx, rfl⟩
      have hzle :
          sInf B ≤
            Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) := by
        exact sInf_le hzmem
      simpa [hsumz] using hzle
  have hEq : sInf A = sInf B := le_antisymm hle hge
  simpa [infimalConvolutionFamily, A, B] using hEq

/-- Text 5.6.2: Assume `I = {1, ..., m}` and `f_1, ..., f_m` are proper convex functions.
Let `f = conv {f_1, ..., f_m}`. Then
`f(x) = inf { (f_1 λ_1 □ ... □ f_m λ_m)(x) | λ_i ≥ 0, Σ_i λ_i = 1 }`, where
`f_i λ_i` denotes the right scalar multiple and `□` is infimal convolution. -/
theorem convexHullFunctionFamily_eq_sInf_infimalConvolution_rightScalarMultiple
    {n m : Nat} {f : Fin m → (Fin n → Real) → EReal}
    (hf : ∀ i, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (f i)) :
    ∀ x : Fin n → Real,
      convexHullFunctionFamily f x =
        sInf { z : EReal |
          ∃ lam : Fin m → Real,
            (∀ i, 0 ≤ lam i) ∧
            (Finset.univ.sum (fun i => lam i) = 1) ∧
            z = infimalConvolutionFamily (fun i => rightScalarMultiple (f i) (lam i)) x } := by
  classical
  intro x
  let A : Set EReal :=
    { z : EReal |
      ∃ lam : Fin m → Real,
        (∀ i, 0 ≤ lam i) ∧
        (Finset.univ.sum (fun i => lam i) = 1) ∧
        z = infimalConvolutionFamily (fun i => rightScalarMultiple (f i) (lam i)) x }
  let B : Set EReal :=
    { z : EReal |
      ∃ (lam : Fin m → Real) (x' : Fin m → (Fin n → Real)),
        (∀ i, 0 ≤ lam i) ∧
        (Finset.univ.sum (fun i => lam i) = 1) ∧
        (Finset.univ.sum (fun i => lam i • x' i) = x) ∧
        z = Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) }
  let Blam : (Fin m → Real) → Set EReal := fun lam =>
    { z : EReal |
      ∃ x' : Fin m → (Fin n → Real),
        (Finset.univ.sum (fun i => lam i • x' i) = x) ∧
        z = Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) }
  have hconv :
      convexHullFunctionFamily f x = sInf B := by
    simpa [B] using
      (convexHullFunctionFamily_eq_sInf_convexCombination_univ (f := f) hf x)
  have hBA : sInf B = sInf A := by
    apply le_antisymm
    · refine le_sInf ?_
      intro z hz
      rcases hz with ⟨lam, hlam, hsum1, rfl⟩
      have hconv_lam :
          infimalConvolutionFamily (fun i => rightScalarMultiple (f i) (lam i)) x =
            sInf (Blam lam) := by
        simpa [Blam] using
          (infimalConvolutionFamily_rightScalarMultiple_eq_sInf (f := f) (lam := lam) (hf := hf)
            hlam x)
      have hle : sInf B ≤ sInf (Blam lam) := by
        refine le_sInf ?_
        intro z hz
        refine sInf_le ?_
        rcases hz with ⟨x', hsumx, rfl⟩
        exact ⟨lam, x', hlam, hsum1, hsumx, rfl⟩
      simpa [hconv_lam] using hle
    · refine le_sInf ?_
      intro z hz
      rcases hz with ⟨lam, x', hlam, hsum1, hsumx, rfl⟩
      have hconv_lam :
          infimalConvolutionFamily (fun i => rightScalarMultiple (f i) (lam i)) x =
            sInf (Blam lam) := by
        simpa [Blam] using
          (infimalConvolutionFamily_rightScalarMultiple_eq_sInf (f := f) (lam := lam) (hf := hf)
            hlam x)
      have hA_le : sInf A ≤ sInf (Blam lam) := by
        refine sInf_le ?_
        refine ⟨lam, hlam, hsum1, ?_⟩
        simp [hconv_lam]
      have hle :
          sInf (Blam lam) ≤
            Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i (x' i)) := by
        refine sInf_le ?_
        exact ⟨x', hsumx, rfl⟩
      exact le_trans hA_le hle
  calc
    convexHullFunctionFamily f x = sInf B := hconv
    _ = sInf A := hBA

end Section05
end Chap01
