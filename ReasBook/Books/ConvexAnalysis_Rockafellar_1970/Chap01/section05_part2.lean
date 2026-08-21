/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yifan Bai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section05_part1

section Chap01
section Section05

/-- From a strict upper bound on the infimum of a fiber, pick a point below it. -/
lemma exists_fiber_lt_of_sInf_lt {n : Nat} {F : Set ((Fin n → Real) × Real)}
    {x : Fin n → Real} {α : Real}
    (h : sInf { μ : ℝ | (x, μ) ∈ F } < α)
    (hne : Set.Nonempty { μ : ℝ | (x, μ) ∈ F }) :
    ∃ μ, (x, μ) ∈ F ∧ μ < α := by
  rcases exists_lt_of_csInf_lt (s := { μ : ℝ | (x, μ) ∈ F }) hne h with ⟨μ, hμ, hμlt⟩
  exact ⟨μ, hμ, hμlt⟩

/-- If every fiber is nonempty and bounded below, the inf-section is convex. -/
lemma convexOn_inf_section_of_convex_of_nonempty_bddBelow {n : Nat}
    {F : Set ((Fin n → Real) × Real)} (hF : Convex ℝ F)
    (hne : ∀ x, Set.Nonempty { μ : ℝ | (x, μ) ∈ F })
    (hbdd : ∀ x, BddBelow { μ : ℝ | (x, μ) ∈ F }) :
    ConvexOn ℝ (Set.univ : Set (Fin n → Real))
      (fun x => sInf { μ : ℝ | (x, μ) ∈ F }) := by
  classical
  refine (convexOn_iff_forall_pos).2 ?_
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  refine le_of_forall_pos_lt_add ?_
  intro ε hε
  set Fx : Set ℝ := { μ : ℝ | (x, μ) ∈ F }
  set Fy : Set ℝ := { μ : ℝ | (y, μ) ∈ F }
  set Fxy : Set ℝ := { μ : ℝ | (a • x + b • y, μ) ∈ F }
  have hneFx : Fx.Nonempty := by simpa [Fx] using hne x
  have hneFy : Fy.Nonempty := by simpa [Fy] using hne y
  have hμexists :
      ∃ μ, (x, μ) ∈ F ∧ μ < sInf Fx + ε := by
    have hlt : sInf Fx < sInf Fx + ε := lt_add_of_pos_right _ hε
    simpa [Fx] using (exists_fiber_lt_of_sInf_lt (F := F) (x := x) (α := sInf Fx + ε) hlt hneFx)
  have hνexists :
      ∃ ν, (y, ν) ∈ F ∧ ν < sInf Fy + ε := by
    have hlt : sInf Fy < sInf Fy + ε := lt_add_of_pos_right _ hε
    simpa [Fy] using (exists_fiber_lt_of_sInf_lt (F := F) (x := y) (α := sInf Fy + ε) hlt hneFy)
  rcases hμexists with ⟨μ, hμF, hμlt⟩
  rcases hνexists with ⟨ν, hνF, hνlt⟩
  have hcombo : (a • (x, μ) + b • (y, ν)) ∈ F := hF hμF hνF ha.le hb.le hab
  have hcombo' : (a • x + b • y, a * μ + b * ν) ∈ F := by
    simpa [smul_eq_mul] using hcombo
  have hcombo'' : a * μ + b * ν ∈ Fxy := by
    simpa [Fxy] using hcombo'
  have hle : sInf Fxy ≤ a * μ + b * ν := by
    have hbdd' : BddBelow Fxy := by
      simpa [Fxy] using hbdd (a • x + b • y)
    exact csInf_le hbdd' hcombo''
  have hμlt' : a * μ < a * (sInf Fx + ε) := by
    exact mul_lt_mul_of_pos_left hμlt ha
  have hνlt' : b * ν < b * (sInf Fy + ε) := by
    exact mul_lt_mul_of_pos_left hνlt hb
  have hlt_sum : a * μ + b * ν < a * (sInf Fx + ε) + b * (sInf Fy + ε) := by
    exact add_lt_add hμlt' hνlt'
  have hlt_sum' :
      a * (sInf Fx + ε) + b * (sInf Fy + ε) =
        a * sInf Fx + b * sInf Fy + ε := by
    calc
      a * (sInf Fx + ε) + b * (sInf Fy + ε) =
          a * sInf Fx + b * sInf Fy + (a + b) * ε := by ring
      _ = a * sInf Fx + b * sInf Fy + ε := by simp [hab]
  have hlt : a * μ + b * ν < a * sInf Fx + b * sInf Fy + ε := by
    simpa [hlt_sum'] using hlt_sum
  have hlt' : sInf Fxy < a * sInf Fx + b * sInf Fy + ε := lt_of_le_of_lt hle hlt
  simpa [Fx, Fy, Fxy] using hlt'

/-- From a strict upper bound on the `EReal`-infimum of a fiber, pick a real point below it. -/
lemma exists_fiber_lt_of_sInf_lt_ereal {n : Nat} {F : Set ((Fin n → Real) × Real)}
    {x : Fin n → Real} {α : Real}
    (h :
      sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ | (x, μ) ∈ F }) < (α : EReal)) :
    ∃ μ, (x, μ) ∈ F ∧ (μ : EReal) < (α : EReal) := by
  classical
  set S : Set ℝ := { μ : ℝ | (x, μ) ∈ F }
  set T : Set EReal := (fun μ : ℝ => (μ : EReal)) '' S
  have hne : T.Nonempty := by
    by_contra hne
    have hT : T = ∅ := (Set.not_nonempty_iff_eq_empty).1 hne
    have htop : (⊤ : EReal) < (α : EReal) := by
      have h' := h
      simp [T, hT, sInf_empty] at h'
    exact (not_lt_of_ge le_top) htop
  rcases exists_lt_of_csInf_lt (s := T) hne (by simpa [T] using h) with ⟨z, hzT, hzlt⟩
  rcases hzT with ⟨μ, hμS, rfl⟩
  refine ⟨μ, ?_, hzlt⟩
  simpa [S] using hμS

/-- Convexity of `F` gives closure under convex combinations. -/
lemma convex_combo_mem_F {n : Nat} {F : Set ((Fin n → Real) × Real)} (hF : Convex ℝ F)
    {x y : Fin n → Real} {μ ν : Real} {a b : Real}
    (hx : (x, μ) ∈ F) (hy : (y, ν) ∈ F)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • x + b • y, a * μ + b * ν) ∈ F := by
  have hcombo : a • (x, μ) + b • (y, ν) ∈ F := hF hx hy ha hb hab
  simpa [smul_eq_mul] using hcombo

/-- Strict inequality for the inf-section in the `EReal` setting. -/
lemma strict_ineq_inf_section_ereal {n : Nat} {F : Set ((Fin n → Real) × Real)}
    (hF : Convex ℝ F) {x y : Fin n → Real} {α β t : Real}
    (hfx :
      sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ | (x, μ) ∈ F }) < (α : EReal))
    (hfy :
      sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ | (y, μ) ∈ F }) < (β : EReal))
    (ht0 : 0 < t) (ht1 : t < 1) :
    sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ | ((1 - t) • x + t • y, μ) ∈ F }) <
      ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal) := by
  classical
  rcases exists_fiber_lt_of_sInf_lt_ereal (F := F) (x := x) (α := α) hfx with
    ⟨μ, hμF, hμltE⟩
  rcases exists_fiber_lt_of_sInf_lt_ereal (F := F) (x := y) (α := β) hfy with
    ⟨ν, hνF, hνltE⟩
  have ha : 0 ≤ 1 - t := sub_nonneg.mpr (le_of_lt ht1)
  have hb : 0 ≤ t := le_of_lt ht0
  have hcombo :
      ((1 - t) • x + t • y, (1 - t) * μ + t * ν) ∈ F := by
    exact convex_combo_mem_F (hF := hF) hμF hνF ha hb (by linarith)
  have hmem :
      ((1 - t) * μ + t * ν : EReal) ∈
        (fun μ : ℝ => (μ : EReal)) '' { μ : ℝ | ((1 - t) • x + t • y, μ) ∈ F } := by
    refine ⟨(1 - t) * μ + t * ν, ?_, rfl⟩
    exact hcombo
  have hle :
      sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ | ((1 - t) • x + t • y, μ) ∈ F }) ≤
        ((1 - t) * μ + t * ν : EReal) := sInf_le hmem
  have hμlt : μ < α := (EReal.coe_lt_coe_iff).1 hμltE
  have hνlt : ν < β := (EReal.coe_lt_coe_iff).1 hνltE
  have hμlt' : (1 - t) * μ < (1 - t) * α :=
    mul_lt_mul_of_pos_left hμlt (sub_pos.mpr ht1)
  have hνlt' : t * ν < t * β := mul_lt_mul_of_pos_left hνlt ht0
  have hlt_real : (1 - t) * μ + t * ν < (1 - t) * α + t * β :=
    add_lt_add hμlt' hνlt'
  have hlt_ereal :
      ((1 - t) * μ + t * ν : EReal) <
        ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal) := by
    have hlt_ereal' :
        ((1 - t) * μ + t * ν : EReal) <
          ((1 - t) * α + t * β : EReal) :=
      (EReal.coe_lt_coe_iff).2 hlt_real
    simpa [EReal.coe_add, EReal.coe_mul] using hlt_ereal'
  exact lt_of_le_of_lt hle hlt_ereal

/-- Theorem 5.3: Let `F` be a convex set in `R^{n+1}`, and define
`f x = inf { μ | (x, μ) ∈ F }`, interpreted in `EReal` so empty fibers give `+∞`.
Then `f` is convex on `R^n`. -/
theorem convexOn_inf_section_of_convex {n : Nat} {F : Set ((Fin n → Real) × Real)}
    (hF : Convex ℝ F) :
    ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real)))
      (fun x => sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ | (x, μ) ∈ F })) := by
  classical
  refine
    (convexFunctionOn_univ_iff_strict_inequality
        (f := fun x =>
          sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ | (x, μ) ∈ F }))).2 ?_
  intro x y α β t hfx hfy ht0 ht1
  simpa using
    (strict_ineq_inf_section_ereal (hF := hF) (x := x) (y := y) (α := α) (β := β)
      (t := t) hfx hfy ht0 ht1)

/-- Theorem 5.4: Let `f_1, ..., f_m` be proper convex functions on `R^n`, and define
`f x = inf { f_1 x_1 + ... + f_m x_m | x_i ∈ R^n, x_1 + ... + x_m = x }`.
Then `f` is a convex function on `R^n`. -/
theorem convexFunctionOn_inf_sum_of_proper {n m : Nat}
    {f : Fin m → (Fin n → Real) → EReal}
    (hf : ∀ i, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (f i)) :
    ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real)))
      (fun x =>
        sInf { z : EReal |
          ∃ x' : Fin m → (Fin n → Real),
            (Finset.univ.sum (fun i => x' i) = x) ∧
              z = Finset.univ.sum (fun i => f i (x' i)) }) := by
  classical
  refine
    (convexFunctionOn_univ_iff_strict_inequality
        (f := fun x =>
          sInf { z : EReal |
            ∃ x' : Fin m → (Fin n → Real),
              (Finset.univ.sum (fun i => x' i) = x) ∧
                z = Finset.univ.sum (fun i => f i (x' i)) })).2 ?_
  intro x y α β t hfx hfy ht0 ht1
  set Sx : Set EReal :=
    { z : EReal |
      ∃ x' : Fin m → (Fin n → Real),
        (Finset.univ.sum (fun i => x' i) = x) ∧
          z = Finset.univ.sum (fun i => f i (x' i)) }
  set Sy : Set EReal :=
    { z : EReal |
      ∃ x' : Fin m → (Fin n → Real),
        (Finset.univ.sum (fun i => x' i) = y) ∧
          z = Finset.univ.sum (fun i => f i (x' i)) }
  set Sxy : Set EReal :=
    { z : EReal |
      ∃ x' : Fin m → (Fin n → Real),
        (Finset.univ.sum (fun i => x' i) = (1 - t) • x + t • y) ∧
          z = Finset.univ.sum (fun i => f i (x' i)) }
  have hneSx : Sx.Nonempty := by
    by_contra hne
    have hSx : Sx = ∅ := (Set.not_nonempty_iff_eq_empty).1 hne
    have hfx' := hfx
    simp [Sx, hSx, sInf_empty] at hfx'
  have hneSy : Sy.Nonempty := by
    by_contra hne
    have hSy : Sy = ∅ := (Set.not_nonempty_iff_eq_empty).1 hne
    have hfy' := hfy
    simp [Sy, hSy, sInf_empty] at hfy'
  rcases exists_lt_of_csInf_lt (s := Sx) hneSx (by simpa [Sx] using hfx) with
    ⟨zx, hxSx, hxlt⟩
  rcases exists_lt_of_csInf_lt (s := Sy) hneSy (by simpa [Sy] using hfy) with
    ⟨zy, hySy, hylt⟩
  rcases hxSx with ⟨x', hxsum, rfl⟩
  rcases hySy with ⟨y', hysum, rfl⟩
  let w : Fin m → (Fin n → Real) := fun i => (1 - t) • x' i + t • y' i
  have hsum_w :
      Finset.univ.sum (fun i => w i) = (1 - t) • x + t • y := by
    have hsumx :
        Finset.univ.sum (fun i => (1 - t) • x' i) =
          (1 - t) • Finset.univ.sum (fun i => x' i) := by
      symm
      simpa using
        (Finset.smul_sum (s := Finset.univ) (f := fun i => x' i) (r := (1 - t)))
    have hsumy :
        Finset.univ.sum (fun i => t • y' i) =
          t • Finset.univ.sum (fun i => y' i) := by
      symm
      simpa using
        (Finset.smul_sum (s := Finset.univ) (f := fun i => y' i) (r := t))
    calc
      Finset.univ.sum (fun i => w i) =
          Finset.univ.sum (fun i => (1 - t) • x' i + t • y' i) := by
            simp [w]
      _ = Finset.univ.sum (fun i => (1 - t) • x' i) +
            Finset.univ.sum (fun i => t • y' i) := by
            simp [Finset.sum_add_distrib]
      _ = (1 - t) • Finset.univ.sum (fun i => x' i) +
            t • Finset.univ.sum (fun i => y' i) := by
            simp [hsumx, hsumy]
      _ = (1 - t) • x + t • y := by
            simp [hxsum, hysum]
  have hseg :
      ∀ i,
        f i (w i) ≤
          ((1 - t : Real) : EReal) * f i (x' i) + ((t : Real) : EReal) * f i (y' i) := by
    intro i
    have hfconv : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (f i) :=
      (hf i).1
    have hfnotbot : ∀ x, f i x ≠ ⊥ := by
      intro x
      exact (hf i).2.2 x (by simp)
    simpa [w] using
      (segment_inequality_f_univ (hf := hfconv) (hnotbot := hfnotbot) (x' i) (y' i) t ht0 ht1)
  have hsum_le :
      Finset.univ.sum (fun i => f i (w i)) ≤
        Finset.univ.sum
          (fun i =>
            ((1 - t : Real) : EReal) * f i (x' i) + ((t : Real) : EReal) * f i (y' i)) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hseg i
  have ha : 0 ≤ ((1 - t : Real) : EReal) := by
    exact le_of_lt ((EReal.coe_pos).2 (sub_pos.mpr ht1))
  have hb : 0 ≤ ((t : Real) : EReal) := by
    exact le_of_lt ((EReal.coe_pos).2 ht0)
  have ha_top : ((1 - t : Real) : EReal) ≠ ⊤ := by
    exact EReal.coe_ne_top (1 - t)
  have hb_top : ((t : Real) : EReal) ≠ ⊤ := by
    exact EReal.coe_ne_top t
  have hsum_eq :
      Finset.univ.sum
          (fun i =>
            ((1 - t : Real) : EReal) * f i (x' i) + ((t : Real) : EReal) * f i (y' i)) =
        ((1 - t : Real) : EReal) * Finset.univ.sum (fun i => f i (x' i)) +
          ((t : Real) : EReal) * Finset.univ.sum (fun i => f i (y' i)) := by
    have hsumx' :
        Finset.univ.sum (fun i => ((1 - t : Real) : EReal) * f i (x' i)) =
          ((1 - t : Real) : EReal) * Finset.univ.sum (fun i => f i (x' i)) := by
      symm
      exact
        EReal.mul_sum_of_nonneg_of_ne_top (s := Finset.univ) (a := ((1 - t : Real) : EReal))
          ha ha_top (fun i => f i (x' i))
    have hsumy' :
        Finset.univ.sum (fun i => ((t : Real) : EReal) * f i (y' i)) =
          ((t : Real) : EReal) * Finset.univ.sum (fun i => f i (y' i)) := by
      symm
      exact
        EReal.mul_sum_of_nonneg_of_ne_top (s := Finset.univ) (a := ((t : Real) : EReal))
          hb hb_top (fun i => f i (y' i))
    calc
      Finset.univ.sum
            (fun i =>
              ((1 - t : Real) : EReal) * f i (x' i) + ((t : Real) : EReal) * f i (y' i)) =
          Finset.univ.sum (fun i => ((1 - t : Real) : EReal) * f i (x' i)) +
            Finset.univ.sum (fun i => ((t : Real) : EReal) * f i (y' i)) := by
              exact Finset.sum_add_distrib
      _ = ((1 - t : Real) : EReal) * Finset.univ.sum (fun i => f i (x' i)) +
            ((t : Real) : EReal) * Finset.univ.sum (fun i => f i (y' i)) := by
              rw [hsumx', hsumy']
  have hsum_le' :
      Finset.univ.sum (fun i => f i (w i)) ≤
        ((1 - t : Real) : EReal) * Finset.univ.sum (fun i => f i (x' i)) +
          ((t : Real) : EReal) * Finset.univ.sum (fun i => f i (y' i)) := by
    have hsum_le' := hsum_le
    rw [hsum_eq] at hsum_le'
    exact hsum_le'
  have hnotbot_sum :
      ∀ x' : Fin m → (Fin n → Real),
        (Finset.univ.sum (fun i => f i (x' i))) ≠ (⊥ : EReal) := by
    intro x'
    classical
    refine Finset.induction_on (s := Finset.univ) ?_ ?_
    · simp
    · intro i s hi hs
      have hi_nebot : f i (x' i) ≠ ⊥ := (hf i).2.2 (x' i) (by simp)
      have hsum : f i (x' i) + Finset.sum s (fun j => f j (x' j)) ≠ ⊥ := by
        exact (EReal.add_ne_bot_iff).2 ⟨hi_nebot, hs⟩
      simpa [Finset.sum_insert, hi] using hsum
  have hzx_ne_bot :
      Finset.univ.sum (fun i => f i (x' i)) ≠ (⊥ : EReal) := hnotbot_sum x'
  have hzy_ne_bot :
      Finset.univ.sum (fun i => f i (y' i)) ≠ (⊥ : EReal) := hnotbot_sum y'
  have hzx_ne_top :
      Finset.univ.sum (fun i => f i (x' i)) ≠ (⊤ : EReal) := ne_top_of_lt hxlt
  have hzy_ne_top :
      Finset.univ.sum (fun i => f i (y' i)) ≠ (⊤ : EReal) := ne_top_of_lt hylt
  have hzx_coe :
      ((Finset.univ.sum (fun i => f i (x' i))).toReal : EReal) =
        Finset.univ.sum (fun i => f i (x' i)) :=
    EReal.coe_toReal hzx_ne_top hzx_ne_bot
  have hzy_coe :
      ((Finset.univ.sum (fun i => f i (y' i))).toReal : EReal) =
        Finset.univ.sum (fun i => f i (y' i)) :=
    EReal.coe_toReal hzy_ne_top hzy_ne_bot
  have hzx_lt_real :
      (Finset.univ.sum (fun i => f i (x' i))).toReal < α := by
    have hlt :
        ((Finset.univ.sum (fun i => f i (x' i))).toReal : EReal) < (α : EReal) := by
      simpa [hzx_coe] using hxlt
    exact (EReal.coe_lt_coe_iff).1 hlt
  have hzy_lt_real :
      (Finset.univ.sum (fun i => f i (y' i))).toReal < β := by
    have hlt :
        ((Finset.univ.sum (fun i => f i (y' i))).toReal : EReal) < (β : EReal) := by
      simpa [hzy_coe] using hylt
    exact (EReal.coe_lt_coe_iff).1 hlt
  have hcombo_lt :
      ((1 - t : Real) : EReal) *
            ((Finset.univ.sum (fun i => f i (x' i))).toReal : EReal) +
          ((t : Real) : EReal) *
            ((Finset.univ.sum (fun i => f i (y' i))).toReal : EReal) <
        ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal) :=
    ereal_convex_combo_lt_of_lt hzx_lt_real hzy_lt_real ht0 ht1
  have hcombo_lt' :
      ((1 - t : Real) : EReal) * Finset.univ.sum (fun i => f i (x' i)) +
          ((t : Real) : EReal) * Finset.univ.sum (fun i => f i (y' i)) <
        ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal) := by
    simpa [hzx_coe, hzy_coe] using hcombo_lt
  have hmem : Finset.univ.sum (fun i => f i (w i)) ∈ Sxy := by
    refine ⟨w, hsum_w, rfl⟩
  have hle :
      sInf Sxy ≤ Finset.univ.sum (fun i => f i (w i)) := by
    exact sInf_le hmem
  have hlt :
      sInf Sxy <
        ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal) := by
    exact lt_of_le_of_lt hle (lt_of_le_of_lt hsum_le' hcombo_lt')
  simpa [Sxy] using hlt

/-- Text 5.4.0 (Infimal convolution of two functions): Let `f, g : R^n -> R union {+infty}`
be proper convex functions. Their infimal convolution `f square g` is the function
`(f square g)(x) = inf { f x1 + g x2 | x1, x2 in R^n, x1 + x2 = x }`, equivalently
`(f square g)(x) = inf_{y in R^n} { f y + g (x - y) }`. -/
noncomputable def infimalConvolution {n : Nat} (f g : (Fin n → Real) → EReal) :
    (Fin n → Real) → EReal :=
  fun x =>
    sInf { z : EReal |
      ∃ x1 x2 : Fin n → Real, x1 + x2 = x ∧ z = f x1 + g x2 }

/-- Text 5.4.1: Let `f_1, ..., f_m` be proper convex functions on `R^n`, and let
`f x = inf { f_1 x_1 + ... + f_m x_m | x_i ∈ R^n, x_1 + ... + x_m = x }`. The
function `f` is denoted by `f_1 square f_2 square ... square f_m`; the operation
`square` is called infimal convolution. -/
noncomputable def infimalConvolutionFamily {n m : Nat}
    (f : Fin m → (Fin n → Real) → EReal) : (Fin n → Real) → EReal :=
  fun x =>
    sInf { z : EReal |
      ∃ x' : Fin m → (Fin n → Real),
        (Finset.univ.sum (fun i => x' i) = x) ∧
          z = Finset.univ.sum (fun i => f i (x' i)) }

/-- The two-function infimal convolution matches the family version on `Fin 2`. -/
lemma infimalConvolution_eq_infimalConvolutionFamily_two {n : Nat}
    (f g : (Fin n → Real) → EReal) :
    infimalConvolution f g =
      infimalConvolutionFamily (fun i : Fin 2 => if i = 0 then f else g) := by
  classical
  funext x
  have hset :
      { z : EReal | ∃ x1 x2 : Fin n → Real, x1 + x2 = x ∧ z = f x1 + g x2 } =
        { z : EReal |
          ∃ x' : Fin 2 → (Fin n → Real),
            (Finset.univ.sum (fun i => x' i) = x) ∧
              z = Finset.univ.sum (fun i => (if i = 0 then f else g) (x' i)) } := by
    ext z
    constructor
    · rintro ⟨x1, x2, hsum, rfl⟩
      refine ⟨fun i => if i = 0 then x1 else x2, ?_, ?_⟩
      · simp [Fin.sum_univ_two, hsum]
      · simp [Fin.sum_univ_two]
    · rintro ⟨x', hsum, rfl⟩
      refine ⟨x' 0, x' 1, ?_, ?_⟩
      · simpa [Fin.sum_univ_two] using hsum
      · simp [Fin.sum_univ_two]
  simp [infimalConvolution, infimalConvolutionFamily, hset]

/-- The indicator of a singleton is `0` at the point and `⊤` elsewhere. -/
lemma indicatorFunction_singleton_simp {n : Nat} (a x : Fin n → Real) :
    indicatorFunction ({a} : Set (Fin n → Real)) x =
      (if x = a then (0 : EReal) else ⊤) := by
  classical
  simp [indicatorFunction, Set.mem_singleton_iff]

/-- The infimal convolution is bounded above by the translate `f (x - a)`. -/
lemma infimalConvolution_indicator_singleton_le {n : Nat} (f : (Fin n → Real) → EReal)
    (a : Fin n → Real) :
    ∀ x, infimalConvolution f (indicatorFunction ({a} : Set (Fin n → Real))) x ≤ f (x - a) := by
  classical
  intro x
  refine sInf_le ?_
  refine ⟨x - a, a, ?_, ?_⟩
  · simp
  · simp [indicatorFunction, Set.mem_singleton_iff]

/-- The translate `f (x - a)` is a lower bound when `f` never takes the value `⊥`. -/
lemma infimalConvolution_indicator_singleton_ge {n : Nat} (f : (Fin n → Real) → EReal)
    (a : Fin n → Real) (hf : ∀ x, f x ≠ (⊥ : EReal)) :
    ∀ x, f (x - a) ≤ infimalConvolution f (indicatorFunction ({a} : Set (Fin n → Real))) x := by
  classical
  intro x
  refine le_sInf ?_
  intro z hz
  rcases hz with ⟨x1, x2, hsum, rfl⟩
  by_cases hx2 : x2 = a
  · have hsum' : x1 + a = x := by simpa [hx2] using hsum
    have hx1 : x1 = x - a := by
      have h := congrArg (fun t => t - a) hsum'
      simpa using h
    simp [hx1, hx2, indicatorFunction, Set.mem_singleton_iff]
  · have htop : f x1 + (⊤ : EReal) = ⊤ := EReal.add_top_of_ne_bot (hf x1)
    simp [indicatorFunction, Set.mem_singleton_iff, hx2, htop]

/-- Text 5.4.1.1: If `g = δ(· | a)` for a point `a ∈ R^n` (where `δ(x | a) = +infty` for
`x ≠ a` and `δ(a | a) = 0`), then `(f square g)(x) = f (x - a)`. -/
lemma infimalConvolution_indicator_singleton {n : Nat} (f : (Fin n → Real) → EReal)
    (a : Fin n → Real) (hf : ∀ x, f x ≠ (⊥ : EReal)) :
    infimalConvolution f (indicatorFunction ({a} : Set (Fin n → Real))) =
      (fun x => f (x - a)) := by
  classical
  funext x
  apply le_antisymm
  · exact infimalConvolution_indicator_singleton_le (f := f) (a := a) x
  · exact infimalConvolution_indicator_singleton_ge (f := f) (a := a) hf x

/-- Reparametrize the defining set in `infimalConvolution`. -/
lemma infimalConvolution_eq_sInf_param {n : Nat} (f g : (Fin n → Real) → EReal) :
    ∀ x : Fin n → Real,
      infimalConvolution f g x =
        sInf { r : EReal | ∃ z : Fin n → Real, r = g z + f (x - z) } := by
  classical
  intro x
  have hset :
      { z : EReal |
          ∃ x1 x2 : Fin n → Real, x1 + x2 = x ∧ z = f x1 + g x2 } =
        { r : EReal | ∃ z : Fin n → Real, r = g z + f (x - z) } := by
    ext r
    constructor
    · rintro ⟨x1, x2, hsum, rfl⟩
      refine ⟨x2, ?_⟩
      have hx1 : x1 = x - x2 := by
        have h := congrArg (fun t => t - x2) hsum
        simpa [add_sub_cancel] using h
      simp [hx1, add_comm]
    · rintro ⟨z, rfl⟩
      refine ⟨x - z, z, ?_, ?_⟩
      · simp
      · simp [add_comm]
  simp [infimalConvolution, hset]

/-- The singleton indicator collapses the reflected infimal convolution. -/
lemma infimalConvolution_reflection_indicator_inner {n : Nat}
    (f : (Fin n → Real) → EReal) (x z : Fin n → Real)
    (hf : ∀ y, f y ≠ (⊥ : EReal)) :
    infimalConvolution (fun y => f (-y))
        (indicatorFunction ({x} : Set (Fin n → Real))) z =
      f (x - z) := by
  classical
  have hf' : ∀ y, (fun y => f (-y)) y ≠ (⊥ : EReal) := by
    intro y
    simpa using hf (-y)
  have h :=
    infimalConvolution_indicator_singleton (f := fun y => f (-y)) (a := x) (hf := hf')
  have hz := congrArg (fun hfun => hfun z) h
  simpa [neg_sub] using hz

/-- Replace the inner infimal convolution using the singleton indicator formula. -/
lemma infimalConvolution_reflection_indicator_finalize {n : Nat}
    (f g : (Fin n → Real) → EReal) (hf : ∀ y, f y ≠ (⊥ : EReal)) :
    ∀ x : Fin n → Real,
      sInf { r : EReal |
        ∃ z : Fin n → Real,
          r = g z +
            infimalConvolution (fun y => f (-y))
              (indicatorFunction ({x} : Set (Fin n → Real))) z } =
        sInf { r : EReal | ∃ z : Fin n → Real, r = g z + f (x - z) } := by
  classical
  intro x
  have hset :
      { r : EReal |
          ∃ z : Fin n → Real,
            r = g z +
              infimalConvolution (fun y => f (-y))
                (indicatorFunction ({x} : Set (Fin n → Real))) z } =
        { r : EReal | ∃ z : Fin n → Real, r = g z + f (x - z) } := by
    ext r
    constructor
    · rintro ⟨z, rfl⟩
      have hz := infimalConvolution_reflection_indicator_inner (f := f) (x := x) (z := z) hf
      refine ⟨z, ?_⟩
      simp [hz]
    · rintro ⟨z, rfl⟩
      have hz := infimalConvolution_reflection_indicator_inner (f := f) (x := x) (z := z) hf
      refine ⟨z, ?_⟩
      simp [hz]
  simp [hset]

/-- Text 5.4.1.2: Let `f, g : ℝ^n → ℝ ∪ {+∞}` and define the reflection `h(y) = f(-y)`.
Then for every `x ∈ ℝ^n`, `(f □ g)(x) = inf_{z ∈ ℝ^n} { g(z) + (h □ δ(· | x))(z) }`. -/
theorem infimalConvolution_reflection_indicator {n : Nat}
    (f g : (Fin n → Real) → EReal) (hf : ∀ y, f y ≠ (⊥ : EReal)) :
    ∀ x : Fin n → Real,
      infimalConvolution f g x =
        sInf { r : EReal |
          ∃ z : Fin n → Real,
            r = g z +
              infimalConvolution (fun y => f (-y))
                (indicatorFunction ({x} : Set (Fin n → Real))) z } := by
  intro x
  calc
    infimalConvolution f g x =
        sInf { r : EReal | ∃ z : Fin n → Real, r = g z + f (x - z) } := by
          simpa using (infimalConvolution_eq_sInf_param (f := f) (g := g) x)
    _ = sInf { r : EReal |
          ∃ z : Fin n → Real,
            r = g z +
              infimalConvolution (fun y => f (-y))
                (indicatorFunction ({x} : Set (Fin n → Real))) z } := by
          symm
          simpa using
            (infimalConvolution_reflection_indicator_finalize (f := f) (g := g) (hf := hf) x)

/-- Points in the effective domain of the infimal convolution decompose into points in each
effective domain, assuming no `⊥` values. -/
lemma effectiveDomain_infimalConvolution_subset_sum {n : Nat}
    (f g : (Fin n → Real) → EReal)
    (hf : ∀ x, f x ≠ (⊥ : EReal)) (hg : ∀ x, g x ≠ (⊥ : EReal)) :
    ∀ x,
      x ∈ effectiveDomain Set.univ (infimalConvolution f g) →
        x ∈ Set.image2 (fun x y => x + y)
          (effectiveDomain Set.univ f) (effectiveDomain Set.univ g) := by
  classical
  intro x hx
  have hx' : infimalConvolution f g x < (⊤ : EReal) := by
    have hx'' : x ∈ Set.univ ∧ infimalConvolution f g x < (⊤ : EReal) := by
      simpa [effectiveDomain_eq] using hx
    exact hx''.2
  have hx'' :
      sInf { r : EReal | ∃ z : Fin n → Real, r = g z + f (x - z) } < (⊤ : EReal) := by
    simpa [infimalConvolution_eq_sInf_param (f := f) (g := g) x] using hx'
  rcases (sInf_lt_iff).1 hx'' with ⟨r, hr, hrlt⟩
  rcases hr with ⟨z, rfl⟩
  have hgz_ne_top : g z ≠ (⊤ : EReal) := by
    intro htop
    have hsum : g z + f (x - z) = (⊤ : EReal) := by
      simpa [htop] using (EReal.top_add_of_ne_bot (x := f (x - z)) (hf (x - z)))
    exact (ne_of_lt hrlt) hsum
  have hfx_ne_top : f (x - z) ≠ (⊤ : EReal) := by
    intro htop
    have hsum : g z + f (x - z) = (⊤ : EReal) := by
      simpa [htop] using (EReal.add_top_of_ne_bot (x := g z) (hg z))
    exact (ne_of_lt hrlt) hsum
  have hgz_lt : g z < (⊤ : EReal) := (lt_top_iff_ne_top).2 hgz_ne_top
  have hfx_lt : f (x - z) < (⊤ : EReal) := (lt_top_iff_ne_top).2 hfx_ne_top
  have hdomf : x - z ∈ effectiveDomain Set.univ f := by
    have : x - z ∈ Set.univ ∧ f (x - z) < (⊤ : EReal) := by
      exact ⟨by simp, hfx_lt⟩
    simpa [effectiveDomain_eq] using this
  have hdomg : z ∈ effectiveDomain Set.univ g := by
    have : z ∈ Set.univ ∧ g z < (⊤ : EReal) := by
      exact ⟨by simp, hgz_lt⟩
    simpa [effectiveDomain_eq] using this
  refine ⟨x - z, hdomf, z, hdomg, ?_⟩
  simp [sub_add_cancel]

/-- Any sum of points from the effective domains lies in the effective domain of `f □ g`. -/
lemma effectiveDomain_sum_subset_infimalConvolution {n : Nat}
    (f g : (Fin n → Real) → EReal) :
    ∀ x,
      x ∈ Set.image2 (fun x y => x + y)
        (effectiveDomain Set.univ f) (effectiveDomain Set.univ g) →
      x ∈ effectiveDomain Set.univ (infimalConvolution f g) := by
  classical
  intro x hx
  rcases hx with ⟨u, hu, v, hv, rfl⟩
  have hfu : f u < (⊤ : EReal) := by
    have : u ∈ Set.univ ∧ f u < (⊤ : EReal) := by
      simpa [effectiveDomain_eq] using hu
    exact this.2
  have hgv : g v < (⊤ : EReal) := by
    have : v ∈ Set.univ ∧ g v < (⊤ : EReal) := by
      simpa [effectiveDomain_eq] using hv
    exact this.2
  have hsum_lt : g v + f u < (⊤ : EReal) := by
    exact EReal.add_lt_top (lt_top_iff_ne_top.1 hgv) (lt_top_iff_ne_top.1 hfu)
  have hle :
      sInf { r : EReal | ∃ z : Fin n → Real, r = g z + f ((u + v) - z) } ≤
        g v + f u := by
    refine sInf_le ?_
    refine ⟨v, ?_⟩
    have : (u + v) - v = u := by
      simp
    simp [this]
  have hlt :
      sInf { r : EReal | ∃ z : Fin n → Real, r = g z + f ((u + v) - z) } < (⊤ : EReal) := by
    exact lt_of_le_of_lt hle hsum_lt
  have hlt' : infimalConvolution f g (u + v) < (⊤ : EReal) := by
    simpa [infimalConvolution_eq_sInf_param (f := f) (g := g) (u + v)] using hlt
  have : u + v ∈ Set.univ ∧ infimalConvolution f g (u + v) < (⊤ : EReal) := by
    exact ⟨by simp, hlt'⟩
  simpa [effectiveDomain_eq] using this

/-- Text 5.4.1.3: The effective domain of `f □ g` is the sum of `dom f` and `dom g`. -/
lemma effectiveDomain_infimalConvolution_eq_sum {n : Nat}
    (f g : (Fin n → Real) → EReal)
    (hf : ∀ x, f x ≠ (⊥ : EReal)) (hg : ∀ x, g x ≠ (⊥ : EReal)) :
    effectiveDomain Set.univ (infimalConvolution f g) =
      Set.image2 (fun x y => x + y)
        (effectiveDomain Set.univ f) (effectiveDomain Set.univ g) := by
  ext x
  constructor
  · exact effectiveDomain_infimalConvolution_subset_sum (f := f) (g := g) hf hg x
  · exact effectiveDomain_sum_subset_infimalConvolution (f := f) (g := g) x

/-- Adding the indicator yields the norm on `C` and `⊤` outside. -/
lemma indicator_add_norm_eq_if {n : Nat} {C : Set (Fin n → Real)}
    (x z : Fin n → Real) :
    indicatorFunction C z + ((‖x - z‖ : Real) : EReal) =
      (by
        classical
        exact if z ∈ C then ((‖x - z‖ : Real) : EReal) else (⊤ : EReal)) := by
  classical
  simpa [add_comm] using
    (add_indicatorFunction_eq (f := fun y : Fin n → Real => ‖x - y‖) (C := C) z)

/-- Rewriting the infimal convolution with an indicator as an infimum over `C`. -/
lemma infimalConvolution_norm_indicator_eq_sInf_range {n : Nat} {C : Set (Fin n → Real)} :
    ∀ x : Fin n → Real,
      infimalConvolution (fun y => ((‖y‖ : Real) : EReal)) (indicatorFunction C) x =
        sInf (Set.range (fun z : C => ((‖x - z‖ : Real) : EReal))) := by
  classical
  intro x
  set S : Set EReal :=
    { r : EReal |
      ∃ z : Fin n → Real,
        r = indicatorFunction C z + ((‖x - z‖ : Real) : EReal) }
  have hS :
      infimalConvolution (fun y => ((‖y‖ : Real) : EReal)) (indicatorFunction C) x = sInf S := by
    simp [S, infimalConvolution_eq_sInf_param]
  have hsubset1 :
      Set.range (fun z : C => ((‖x - z‖ : Real) : EReal)) ⊆ S := by
    intro r hr
    rcases hr with ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    have hz : (z : Fin n → Real) ∈ C := z.property
    simp [indicatorFunction, hz]
  have hsubset2 :
      S ⊆ insert ⊤ (Set.range (fun z : C => ((‖x - z‖ : Real) : EReal))) := by
    intro r hr
    rcases hr with ⟨z, rfl⟩
    by_cases hz : z ∈ C
    · have hrange :
          ((‖x - z‖ : Real) : EReal) ∈
            Set.range (fun z : C => ((‖x - z‖ : Real) : EReal)) := ⟨⟨z, hz⟩, rfl⟩
      have hr :
          indicatorFunction C z + ((‖x - z‖ : Real) : EReal) =
            ((‖x - z‖ : Real) : EReal) := by
        simp [indicatorFunction, hz]
      apply (Set.mem_insert_iff).2
      right
      simpa [hr] using hrange
    · have hr :
          indicatorFunction C z + ((‖x - z‖ : Real) : EReal) = (⊤ : EReal) := by
        simp [indicator_add_norm_eq_if, hz]
      apply (Set.mem_insert_iff).2
      left
      simp [hr]
  calc
    infimalConvolution (fun y => ((‖y‖ : Real) : EReal)) (indicatorFunction C) x = sInf S := hS
    _ = sInf (Set.range (fun z : C => ((‖x - z‖ : Real) : EReal))) := by
      exact le_antisymm (sInf_le_sInf hsubset1) (sInf_le_sInf_of_subset_insert_top hsubset2)

/-- The infimum of norms over a nonempty set gives the distance. -/
lemma sInf_range_norm_eq_infDist {n : Nat} {C : Set (Fin n → Real)} (hCne : C.Nonempty) :
    ∀ x : Fin n → Real,
      sInf (Set.range (fun z : C => ((‖x - z‖ : Real) : EReal))) =
        ((Metric.infDist x C : Real) : EReal) := by
  classical
  intro x
  set S : Set EReal := Set.range (fun z : C => ((‖x - z‖ : Real) : EReal))
  have hle : ((Metric.infDist x C : Real) : EReal) ≤ sInf S := by
    refine le_sInf ?_
    intro r hr
    rcases hr with ⟨z, rfl⟩
    have hle' : Metric.infDist x C ≤ dist x z :=
      Metric.infDist_le_dist_of_mem z.property
    have hle'' :
        ((Metric.infDist x C : Real) : EReal) ≤ ((dist x z : Real) : EReal) :=
      (EReal.coe_le_coe_iff).2 hle'
    simpa [dist_eq_norm, S] using hle''
  have hle' : sInf S ≤ ((Metric.infDist x C : Real) : EReal) := by
    refine (EReal.le_of_forall_lt_iff_le).1 ?_
    intro z hz
    have hz' : Metric.infDist x C < z := (EReal.coe_lt_coe_iff).1 (by simpa using hz)
    rcases (Metric.infDist_lt_iff (x := x) (s := C) hCne).1 hz' with ⟨y, hyC, hdist⟩
    have hmem : ((‖x - y‖ : Real) : EReal) ∈ S := by
      exact ⟨⟨y, hyC⟩, rfl⟩
    have hle_s : sInf S ≤ ((‖x - y‖ : Real) : EReal) := sInf_le hmem
    have hlt : ((‖x - y‖ : Real) : EReal) < (z : EReal) := by
      have hdist' : ‖x - y‖ < z := by
        simpa [dist_eq_norm] using hdist
      exact (EReal.coe_lt_coe_iff).2 hdist'
    exact hle_s.trans hlt.le
  exact le_antisymm hle' hle

/-- Text 5.4.1.4: Taking `f` to be the Euclidean norm and `g` to be the indicator
function of a convex set `C`, we get `(f □ g)(x) = d(x, C)`, where `d(x, C)` denotes
the distance between `x` and `C`. -/
lemma infimalConvolution_norm_indicator_eq_infDist {n : Nat} {C : Set (Fin n → Real)}
    (hCne : C.Nonempty) :
    ∀ x : Fin n → Real,
      infimalConvolution (fun y => ((‖y‖ : Real) : EReal)) (indicatorFunction C) x =
        ((Metric.infDist x C : Real) : EReal) := by
  intro x
  calc
    infimalConvolution (fun y => ((‖y‖ : Real) : EReal)) (indicatorFunction C) x =
        sInf (Set.range (fun z : C => ((‖x - z‖ : Real) : EReal))) := by
          simpa using (infimalConvolution_norm_indicator_eq_sInf_range (C := C) x)
    _ = ((Metric.infDist x C : Real) : EReal) := by
          simpa using (sInf_range_norm_eq_infDist (C := C) hCne x)

/-- The Euclidean norm is a proper convex function on `Set.univ`. -/
lemma properConvexFunctionOn_norm {n : Nat} :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
      (fun x => ((‖x‖ : Real) : EReal)) := by
  have hconv_real :
      ConvexOn ℝ (Set.univ : Set (Fin n → Real)) (fun x => ‖x‖) := by
    simpa using
      (convexOn_univ_norm : ConvexOn ℝ (Set.univ : Set (Fin n → Real)) (norm))
  have hconv :
      ConvexFunctionOn (Set.univ : Set (Fin n → Real))
        (fun x => ((‖x‖ : Real) : EReal)) :=
    convexFunctionOn_of_convexOn_real (S := (Set.univ : Set (Fin n → Real))) hconv_real
  have hne :
      Set.Nonempty
        (epigraph (Set.univ : Set (Fin n → Real))
          (fun x => ((‖x‖ : Real) : EReal))) := by
    refine ⟨((0 : Fin n → Real), 0), ?_⟩
    have hle : ((‖(0 : Fin n → Real)‖ : Real) : EReal) ≤ (0 : EReal) := by
      simp
    exact (mem_epigraph_univ_iff (f := fun x => ((‖x‖ : Real) : EReal))).2 hle
  have hnotbot :
      ∀ x ∈ (Set.univ : Set (Fin n → Real)),
        ((‖x‖ : Real) : EReal) ≠ (⊥ : EReal) := by
    intro x hx
    exact EReal.coe_ne_bot (‖x‖)
  exact ⟨hconv, hne, hnotbot⟩

/-- The indicator of a nonempty convex set is a proper convex function. -/
lemma properConvexFunctionOn_indicator_of_convex_of_nonempty {n : Nat} {C : Set (Fin n → Real)}
    (hC : Convex ℝ C) (hCne : C.Nonempty) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (indicatorFunction C) := by
  classical
  have hconv' : ConvexFunction (indicatorFunction C) :=
    convexFunction_indicator_of_convex (C := C) hC
  have hconv :
      ConvexFunctionOn (Set.univ : Set (Fin n → Real)) (indicatorFunction C) := by
    simpa [ConvexFunction] using hconv'
  rcases hCne with ⟨x, hxC⟩
  have hne :
      Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) (indicatorFunction C)) := by
    refine ⟨(x, 0), ?_⟩
    have hle : indicatorFunction C x ≤ (0 : EReal) := by
      simp [indicatorFunction, hxC]
    exact (mem_epigraph_univ_iff (f := indicatorFunction C)).2 hle
  have hnotbot :
      ∀ x ∈ (Set.univ : Set (Fin n → Real)),
        indicatorFunction C x ≠ (⊥ : EReal) := by
    intro x hx
    by_cases hxC : x ∈ C
    · simp [indicatorFunction, hxC]
    · simp [indicatorFunction, hxC]
  exact ⟨hconv, hne, hnotbot⟩

/-- The infimal convolution of two proper convex functions is convex. -/
lemma convexFunctionOn_infimalConvolution_of_proper {n : Nat}
    {f g : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f)
    (hg : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) g) :
    ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (infimalConvolution f g) := by
  have hconv :
      ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real)))
        (infimalConvolutionFamily (fun i : Fin 2 => if i = 0 then f else g)) := by
    refine
      convexFunctionOn_inf_sum_of_proper (f := fun i : Fin 2 => if i = 0 then f else g) ?_
    intro i
    fin_cases i
    · simpa using hf
    · simpa using hg
  simpa [infimalConvolution_eq_infimalConvolutionFamily_two (f := f) (g := g)] using hconv

/-- Text 5.4.1.5: For a convex set `C`, let `d(x, C)` denote the distance between `x`
and `C`. Then the function `d(·, C)` is convex on `ℝ^n`. -/
lemma convexOn_infDist_of_convex {n : Nat} {C : Set (Fin n → Real)}
    (hC : Convex ℝ C) :
    ConvexOn ℝ (Set.univ : Set (Fin n → Real)) (fun x => Metric.infDist x C) := by
  classical
  by_cases hCne : C.Nonempty
  · have hproper_norm :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
          (fun x => ((‖x‖ : Real) : EReal)) :=
      properConvexFunctionOn_norm (n := n)
    have hproper_indicator :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (indicatorFunction C) :=
      properConvexFunctionOn_indicator_of_convex_of_nonempty (C := C) hC hCne
    have hconv_ereal :
        ConvexFunctionOn (Set.univ : Set (Fin n → Real))
          (infimalConvolution (fun y => ((‖y‖ : Real) : EReal)) (indicatorFunction C)) := by
      exact
        convexFunctionOn_infimalConvolution_of_proper
          (f := fun y => ((‖y‖ : Real) : EReal))
          (g := indicatorFunction C) hproper_norm hproper_indicator
    have hconv_ereal' :
        ConvexFunctionOn (Set.univ : Set (Fin n → Real))
          (fun x => ((Metric.infDist x C : Real) : EReal)) := by
      have hEq :
          infimalConvolution (fun y => ((‖y‖ : Real) : EReal)) (indicatorFunction C) =
            fun x => ((Metric.infDist x C : Real) : EReal) := by
        funext x
        simpa using (infimalConvolution_norm_indicator_eq_infDist (C := C) hCne x)
      simpa [hEq] using hconv_ereal
    have hnotbot :
        ∀ x ∈ (Set.univ : Set (Fin n → Real)),
          ((Metric.infDist x C : Real) : EReal) ≠ (⊥ : EReal) := by
      intro x hx
      exact EReal.coe_ne_bot (Metric.infDist x C)
    have hseg :=
      (convexFunctionOn_iff_segment_inequality (C := (Set.univ : Set (Fin n → Real)))
          (f := fun x => ((Metric.infDist x C : Real) : EReal))
          (hC := convex_univ)
          (hnotbot := hnotbot)).1 hconv_ereal'
    refine (convexOn_iff_forall_pos).2 ?_
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      subst ha0
      subst hb1
      simp
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by linarith
      subst hb0
      subst ha1
      simp
    have ha_pos : 0 < a := ha
    have hb_pos : 0 < b := hb
    have hb1 : b < 1 := by linarith [hab, ha_pos]
    have ha_eq : a = 1 - b := by linarith [hab]
    have hseg' := hseg x (by simp) y (by simp) b hb_pos hb1
    have hseg'' :
        ((Metric.infDist (a • x + b • y) C : Real) : EReal) ≤
          ((a : Real) : EReal) * ((Metric.infDist x C : Real) : EReal) +
            ((b : Real) : EReal) * ((Metric.infDist y C : Real) : EReal) := by
      simpa [ha_eq] using hseg'
    have hseg_real :
        Metric.infDist (a • x + b • y) C ≤
          a * Metric.infDist x C + b * Metric.infDist y C := by
      exact (EReal.coe_le_coe_iff).1
        (by simpa [EReal.coe_add, EReal.coe_mul] using hseg'')
    exact hseg_real
  · have hCempty : C = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using hCne
    subst hCempty
    simpa using
      (convexOn_const (s := (Set.univ : Set (Fin n → Real)))
        (𝕜 := ℝ) (c := (0 : ℝ)) (hs := convex_univ))

end Section05
end Chap01
