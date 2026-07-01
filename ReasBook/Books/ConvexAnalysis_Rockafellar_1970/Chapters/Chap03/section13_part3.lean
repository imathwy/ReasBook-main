/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Siyuan Shao, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section13_part2

open scoped Pointwise

section Chap03
section Section13

/-- A crude upper bound for the dot product in terms of the `sup` norm. -/
lemma section13_dotProduct_le_norm_mul_sum_abs {n : Nat} (x y : Fin n → Real) :
    dotProduct x y ≤ ‖x‖ * (Finset.univ.sum fun i : Fin n => |y i|) := by
  classical
  have habs : |dotProduct x y| ≤ ‖x‖ * (Finset.univ.sum fun i : Fin n => |y i|) := by
    have hsum : |dotProduct x y| ≤ Finset.univ.sum (fun i : Fin n => |x i * y i|) := by
      simpa [dotProduct] using
        (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun i : Fin n => x i * y i))
    have hterm :
        (Finset.univ.sum (fun i : Fin n => |x i * y i|)) ≤
          Finset.univ.sum (fun i : Fin n => ‖x‖ * |y i|) := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      have hxi : |x i| ≤ ‖x‖ := by
        have : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm (f := x) (i := i)
        simpa [Real.norm_eq_abs] using this
      calc
        |x i * y i| = |x i| * |y i| := by simp [abs_mul]
        _ ≤ ‖x‖ * |y i| := by
            exact mul_le_mul_of_nonneg_right hxi (abs_nonneg (y i))
    have hconst :
        Finset.univ.sum (fun i : Fin n => ‖x‖ * |y i|) =
          ‖x‖ * (Finset.univ.sum fun i : Fin n => |y i|) := by
      exact
        (Finset.mul_sum (a := ‖x‖) (s := Finset.univ) (f := fun i : Fin n => |y i|)).symm
    have hmid :
        |dotProduct x y| ≤ Finset.univ.sum (fun i : Fin n => ‖x‖ * |y i|) :=
      le_trans hsum hterm
    simpa [hconst] using hmid
  exact le_trans (le_abs_self (dotProduct x y)) habs

/-- A nonempty set has a support function that never takes the value `⊥`. -/
lemma section13_supportFunctionEReal_ne_bot_of_nonempty {n : Nat} {C : Set (Fin n → Real)}
    (hCne : Set.Nonempty C) (xStar : Fin n → Real) :
    supportFunctionEReal C xStar ≠ (⊥ : EReal) := by
  classical
  rcases hCne with ⟨x0, hx0C⟩
  have hxmem :
      ((dotProduct x0 xStar : Real) : EReal) ∈
        {z : EReal | ∃ x ∈ C, z = ((dotProduct x xStar : Real) : EReal)} :=
    ⟨x0, hx0C, rfl⟩
  have hle :
      ((dotProduct x0 xStar : Real) : EReal) ≤ supportFunctionEReal C xStar := by
    simpa [supportFunctionEReal] using (le_sSup hxmem)
  intro hbot
  rw [hbot] at hle
  have : ((dotProduct x0 xStar : Real) : EReal) = (⊥ : EReal) := (le_bot_iff).1 hle
  exact (EReal.coe_ne_bot (dotProduct x0 xStar : Real)) this

/-- A bounded set has a support function that never takes the value `⊤`. -/
lemma section13_supportFunctionEReal_ne_top_of_isBounded {n : Nat} {C : Set (Fin n → Real)}
    (hCbd : Bornology.IsBounded C) (xStar : Fin n → Real) :
    supportFunctionEReal C xStar ≠ (⊤ : EReal) := by
  classical
  rcases hCbd.exists_pos_norm_le with ⟨R, _hRpos, hR⟩
  set U : Real := R * (Finset.univ.sum fun i : Fin n => |xStar i|)
  have hle : supportFunctionEReal C xStar ≤ (U : EReal) := by
    unfold supportFunctionEReal
    refine sSup_le ?_
    intro z hz
    rcases hz with ⟨x, hxC, rfl⟩
    apply (EReal.coe_le_coe_iff).2
    have hdot :
        dotProduct x xStar ≤ ‖x‖ * (Finset.univ.sum fun i : Fin n => |xStar i|) :=
      section13_dotProduct_le_norm_mul_sum_abs (x := x) (y := xStar)
    have hsum_nonneg : 0 ≤ (Finset.univ.sum fun i : Fin n => |xStar i|) := by
      exact Finset.sum_nonneg (fun i _hi => abs_nonneg (xStar i))
    have hmul :
        ‖x‖ * (Finset.univ.sum fun i : Fin n => |xStar i|) ≤
          R * (Finset.univ.sum fun i : Fin n => |xStar i|) :=
      mul_le_mul_of_nonneg_right (hR x hxC) hsum_nonneg
    simpa [U] using le_trans hdot hmul
  intro htop
  rw [htop] at hle
  exact (EReal.coe_ne_top U) ((top_le_iff).1 hle)

/-- If the support function of a nonempty set is finite everywhere, then the set is bounded. -/
lemma section13_isBounded_of_supportFunctionEReal_finite {n : Nat} {C : Set (Fin n → Real)}
    (hfinite :
      ∀ xStar,
        supportFunctionEReal C xStar ≠ (⊤ : EReal) ∧ supportFunctionEReal C xStar ≠ (⊥ : EReal)) :
    Bornology.IsBounded C := by
  classical
  have h_eval : ∀ i : Fin n, Bornology.IsBounded (Function.eval i '' C) := by
    intro i
    set epos : Fin n → Real := Pi.single i 1
    set eneg : Fin n → Real := Pi.single i (-1 : Real)
    have hpos_ne_top : supportFunctionEReal C epos ≠ (⊤ : EReal) := (hfinite epos).1
    have hneg_ne_top : supportFunctionEReal C eneg ≠ (⊤ : EReal) := (hfinite eneg).1
    set U : Real := (supportFunctionEReal C epos).toReal
    set V : Real := (supportFunctionEReal C eneg).toReal
    refine (isBounded_iff_forall_norm_le (s := Function.eval i '' C)).2 ?_
    refine ⟨max |U| |V|, ?_⟩
    rintro _y ⟨x, hxC, rfl⟩
    have hxU : x i ≤ U := by
      have hxmem :
          ((dotProduct x epos : Real) : EReal) ∈
            {z : EReal | ∃ x ∈ C, z = ((dotProduct x epos : Real) : EReal)} :=
        ⟨x, hxC, rfl⟩
      have hxle :
          ((dotProduct x epos : Real) : EReal) ≤ supportFunctionEReal C epos := by
        simpa [supportFunctionEReal] using (le_sSup hxmem)
      have hsup : supportFunctionEReal C epos ≤ (U : EReal) := by
        simpa [U] using (EReal.le_coe_toReal (x := supportFunctionEReal C epos) hpos_ne_top)
      have : ((dotProduct x epos : Real) : EReal) ≤ (U : EReal) := le_trans hxle hsup
      have : dotProduct x epos ≤ U := (EReal.coe_le_coe_iff).1 this
      have hdot : dotProduct x epos = x i := by
        simp [epos]
      simpa [hdot] using this
    have hxV : -x i ≤ V := by
      have hxmem :
          ((dotProduct x eneg : Real) : EReal) ∈
            {z : EReal | ∃ x ∈ C, z = ((dotProduct x eneg : Real) : EReal)} :=
        ⟨x, hxC, rfl⟩
      have hxle :
          ((dotProduct x eneg : Real) : EReal) ≤ supportFunctionEReal C eneg := by
        simpa [supportFunctionEReal] using (le_sSup hxmem)
      have hsup : supportFunctionEReal C eneg ≤ (V : EReal) := by
        simpa [V] using (EReal.le_coe_toReal (x := supportFunctionEReal C eneg) hneg_ne_top)
      have : ((dotProduct x eneg : Real) : EReal) ≤ (V : EReal) := le_trans hxle hsup
      have : dotProduct x eneg ≤ V := (EReal.coe_le_coe_iff).1 this
      have hdot : dotProduct x eneg = -x i := by
        simp [eneg]
      simpa [hdot] using this
    have hleR : x i ≤ max |U| |V| :=
      le_trans (le_trans hxU (le_abs_self U)) (le_max_left _ _)
    have hlowV : (-V) ≤ x i := by
      have := neg_le_neg hxV
      simpa [neg_neg] using this
    have hlowR : -(max |U| |V|) ≤ x i := by
      have hVle : V ≤ |V| := le_abs_self V
      have hneg_abs_le : -|V| ≤ -V := by
        exact neg_le_neg hVle
      have hmaxV : |V| ≤ max |U| |V| := le_max_right _ _
      have hneg_max_le : -(max |U| |V|) ≤ -|V| := by
        exact neg_le_neg hmaxV
      exact le_trans (le_trans hneg_max_le hneg_abs_le) hlowV
    have habs : |x i| ≤ max |U| |V| := (abs_le).2 ⟨hlowR, hleR⟩
    simpa [Real.norm_eq_abs] using habs
  exact (Bornology.forall_isBounded_image_eval_iff (s := C)).1 h_eval

/-- A convex function finite everywhere is automatically closed and proper. -/
lemma section13_closedProper_of_convex_finite {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ConvexFunction f) (hfinite : ∀ x, f x ≠ ⊤ ∧ f x ≠ ⊥) :
    ClosedConvexFunction f ∧ ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
  have hf_convOn : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
    simpa [ConvexFunction] using hf
  have hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
    refine ⟨hf_convOn, ?_, ?_⟩
    · refine ⟨(0, (f 0).toReal), ?_⟩
      refine (mem_epigraph_univ_iff (f := f) (x := (0 : Fin n → Real)) (μ := (f 0).toReal)).2 ?_
      exact EReal.le_coe_toReal (hfinite 0).1
    · intro x hxuniv
      exact (hfinite x).2
  have hdom_univ : effectiveDomain (Set.univ : Set (Fin n → Real)) f = Set.univ := by
    ext x
    have hxlt : f x < (⊤ : EReal) := (lt_top_iff_ne_top).2 (hfinite x).1
    simp [effectiveDomain_eq, hxlt]
  have haff : IsAffineSet n (effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
    have : IsAffineSet n (Set.univ : Set (Fin n → Real)) := by
      intro x y _hx _hy r
      trivial
    simpa [hdom_univ] using this
  have hf_closed : ClosedConvexFunction f :=
    properConvexFunction_closed_of_affine_effectiveDomain (n := n) (f := f) hf_proper haff
  exact ⟨hf_closed, hf_proper⟩

/-- Corollary 13.2.2. The support functions of the non-empty bounded convex sets are the finite
positively homogeneous convex functions. -/
theorem exists_supportFunctionEReal_iff_boundedConvex_posHom_finite {n : Nat}
    (f : (Fin n → Real) → EReal) :
    (∃ C : Set (Fin n → Real),
        Set.Nonempty C ∧ Convex ℝ C ∧ Bornology.IsBounded C ∧ f = supportFunctionEReal C) ↔
      (ConvexFunction f ∧ PositivelyHomogeneous f ∧ ∀ x : Fin n → Real, f x ≠ ⊤ ∧ f x ≠ ⊥) := by
  classical
  constructor
  · rintro ⟨C, hCne, hCconv, hCbd, rfl⟩
    have hchar :
        ClosedConvexFunction (supportFunctionEReal C) ∧
          ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (supportFunctionEReal C) ∧
            PositivelyHomogeneous (supportFunctionEReal C) :=
      (exists_supportFunctionEReal_iff_closedProperConvex_posHom (n := n) (f := supportFunctionEReal C)).1
        ⟨C, hCne, hCconv, rfl⟩
    refine ⟨hchar.1.1, hchar.2.2, ?_⟩
    intro xStar
    refine ⟨?_, ?_⟩
    · exact section13_supportFunctionEReal_ne_top_of_isBounded (C := C) hCbd xStar
    · exact section13_supportFunctionEReal_ne_bot_of_nonempty (C := C) hCne xStar
  · rintro ⟨hf_conv, hf_pos, hfinite⟩
    have hcp := section13_closedProper_of_convex_finite (f := f) hf_conv hfinite
    rcases
        (exists_supportFunctionEReal_iff_closedProperConvex_posHom (n := n) (f := f)).2
          ⟨hcp.1, hcp.2, hf_pos⟩ with
      ⟨C, hCne, hCconv, hfeq⟩
    have hCbd : Bornology.IsBounded C := by
      refine section13_isBounded_of_supportFunctionEReal_finite (C := C) ?_
      intro xStar
      simpa [hfeq] using hfinite xStar
    exact ⟨C, hCne, hCconv, hCbd, hfeq⟩
end Section13
end Chap03
