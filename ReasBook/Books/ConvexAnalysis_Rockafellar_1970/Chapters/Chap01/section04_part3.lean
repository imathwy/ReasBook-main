/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xuran Sun, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section04_part2

open Matrix
open scoped BigOperators
open scoped Topology

section Chap01
section Section04
open scoped BigOperators

/-- Left distributivity for multiplication by `⊥` under a non-forbidden sum. -/
lemma ereal_bot_mul_add_of_no_forbidden {x1 x2 : EReal}
    (h : ¬ ERealForbiddenSum ((⊥ : EReal) * x1) ((⊥ : EReal) * x2)) :
    (⊥ : EReal) * (x1 + x2) = (⊥ : EReal) * x1 + (⊥ : EReal) * x2 := by
  have h' : ¬ ERealForbiddenSum ((-(⊤ : EReal)) * x1) ((-(⊤ : EReal)) * x2) := by
    simpa using h
  have h_neg :
      ¬ ERealForbiddenSum (-((⊤ : EReal) * x1)) (-((⊤ : EReal) * x2)) := by
    simpa [← EReal.neg_mul] using h'
  have h_top :
      ¬ ERealForbiddenSum ((⊤ : EReal) * x1) ((⊤ : EReal) * x2) := by
    intro hforb
    apply h_neg
    exact (ereal_forbiddenSum_neg_iff (a := (⊤ : EReal) * x1) (b := (⊤ : EReal) * x2)).2 hforb
  have hdistrib :
      (⊤ : EReal) * (x1 + x2) = (⊤ : EReal) * x1 + (⊤ : EReal) * x2 :=
    ereal_top_mul_add_of_no_forbidden (x1 := x1) (x2 := x2) h_top
  have hdisj := ereal_no_forbidden_neg_add h_top
  calc
    (⊥ : EReal) * (x1 + x2) = -((⊤ : EReal) * (x1 + x2)) := by
      simpa using (EReal.neg_mul (⊤ : EReal) (x1 + x2))
    _ = -((⊤ : EReal) * x1 + (⊤ : EReal) * x2) := by simp [hdistrib]
    _ = -((⊤ : EReal) * x1) - (⊤ : EReal) * x2 := by
      simpa [sub_eq_add_neg] using (EReal.neg_add hdisj.1 hdisj.2)
    _ = (-((⊤ : EReal) * x1) + -((⊤ : EReal) * x2)) := by simp [sub_eq_add_neg]
    _ = (-(⊤ : EReal)) * x1 + (-(⊤ : EReal)) * x2 := by
      rw [← EReal.neg_mul, ← EReal.neg_mul]
    _ = (⊥ : EReal) * x1 + (⊥ : EReal) * x2 := by simp

/-- Left distributivity under a non-forbidden sum. -/
lemma ereal_mul_add_of_no_forbidden {α x1 x2 : EReal}
    (hα : ¬ ERealForbiddenSum (α * x1) (α * x2)) :
    α * (x1 + x2) = α * x1 + α * x2 := by
  cases α using EReal.rec
  · simpa using (ereal_bot_mul_add_of_no_forbidden (x1 := x1) (x2 := x2) hα)
  · rename_i a
    by_cases hnonneg : 0 ≤ a
    · have hE : (0 : EReal) ≤ (a : EReal) := (EReal.coe_nonneg).2 hnonneg
      have hne : (a : EReal) ≠ ⊤ := EReal.coe_ne_top a
      simpa using (EReal.left_distrib_of_nonneg_of_ne_top hE hne x1 x2)
    · have ha_neg : a < 0 := lt_of_not_ge hnonneg
      let b : ℝ := -a
      have hb_nonneg : (0 : EReal) ≤ (b : EReal) := by
        have hb : 0 ≤ b := by linarith
        exact (EReal.coe_nonneg).2 hb
      have hb_ne_top : (b : EReal) ≠ ⊤ := EReal.coe_ne_top b
      have hdistrib :
          (b : EReal) * (x1 + x2) = (b : EReal) * x1 + (b : EReal) * x2 :=
        EReal.left_distrib_of_nonneg_of_ne_top hb_nonneg hb_ne_top x1 x2
      have h_neg :
          ¬ ERealForbiddenSum (-((b : EReal) * x1)) (-((b : EReal) * x2)) := by
        simpa [b, EReal.neg_mul] using hα
      have h_forbid :
          ¬ ERealForbiddenSum ((b : EReal) * x1) ((b : EReal) * x2) := by
        intro hforb
        apply h_neg
        exact (ereal_forbiddenSum_neg_iff (a := (b : EReal) * x1) (b := (b : EReal) * x2)).2
          hforb
      have hdisj := ereal_no_forbidden_neg_add h_forbid
      calc
        (a : EReal) * (x1 + x2) = (-(b : EReal)) * (x1 + x2) := by simp [b]
        _ = -((b : EReal) * (x1 + x2)) := by
          simp
        _ = -((b : EReal) * x1 + (b : EReal) * x2) := by simp [hdistrib]
        _ = -((b : EReal) * x1) - (b : EReal) * x2 := by
          simpa [sub_eq_add_neg] using (EReal.neg_add hdisj.1 hdisj.2)
        _ = -((b : EReal) * x1) + -((b : EReal) * x2) := by simp [sub_eq_add_neg]
        _ = (-(b : EReal)) * x1 + (-(b : EReal)) * x2 := by
          rw [← EReal.neg_mul, ← EReal.neg_mul]
        _ = (a : EReal) * x1 + (a : EReal) * x2 := by simp [b]
  · simpa using (ereal_top_mul_add_of_no_forbidden (x1 := x1) (x2 := x2) hα)

/-- Defintion 4.4.6: Under these conventions, the usual arithmetic laws remain valid
as long as none of the indicated binary sums is forbidden. -/
lemma ereal_arithmetic_laws_of_no_forbidden {x1 x2 x3 α : EReal}
    (_h12 : ¬ ERealForbiddenSum x1 x2)
    (_h23 : ¬ ERealForbiddenSum x2 x3)
    (_h123 : ¬ ERealForbiddenSum (x1 + x2) x3)
    (_h123' : ¬ ERealForbiddenSum x1 (x2 + x3))
    (hα : ¬ ERealForbiddenSum (α * x1) (α * x2)) :
    x1 + x2 = x2 + x1 ∧ (x1 + x2) + x3 = x1 + (x2 + x3) ∧
      x1 * x2 = x2 * x1 ∧ (x1 * x2) * x3 = x1 * (x2 * x3) ∧
      α * (x1 + x2) = α * x1 + α * x2 := by
  refine ⟨add_comm _ _, ?_⟩
  refine ⟨add_assoc _ _ _, ?_⟩
  refine ⟨mul_comm _ _, ?_⟩
  refine ⟨mul_assoc _ _ _, ?_⟩
  exact ereal_mul_add_of_no_forbidden (α := α) (x1 := x1) (x2 := x2) hα

/-- Remark 4.4.7: In this book, a “convex function” means an `EReal`-valued convex
function defined on all of `ℝ^n`, unless otherwise specified; this convention lets
the effective domain be determined implicitly by where `f x` is or is not `⊤`. -/
def ConvexFunction {n : Nat} (f : (Fin n -> Real) -> EReal) : Prop :=
  ConvexFunctionOn (Set.univ) f

/-
Remark 4.5.0: In the multidimensional case, every function of the form
`f x = ⟪x, a⟫ + α` with `a ∈ ℝ^n` and `α ∈ ℝ` is convex on `ℝ^n`, in fact affine.
Every affine function on `ℝ^n` is of this form (Theorem 1.5).
-/
/-- Convex combinations preserve linear-plus-constant forms. -/
lemma inner_add_const_combo_eq {n : Nat} (a : Fin n → Real) (α t : Real)
    (x y : Fin n → Real) :
    ((Finset.univ.sum (fun i => ((1 - t) • x + t • y) i * a i) + α : Real) : EReal)
      = ((1 - t : Real) : EReal) * ((Finset.univ.sum (fun i => x i * a i) + α : Real) : EReal)
        + ((t : Real) : EReal) * ((Finset.univ.sum (fun i => y i * a i) + α : Real) : EReal) := by
  classical
  have hsum :
      Finset.univ.sum (fun i => ((1 - t) • x + t • y) i * a i)
        = (1 - t) * Finset.univ.sum (fun i => x i * a i)
          + t * Finset.univ.sum (fun i => y i * a i) := by
    classical
    calc
      Finset.univ.sum (fun i => ((1 - t) • x + t • y) i * a i)
          = Finset.univ.sum (fun i => ((1 - t) * x i + t * y i) * a i) := by
              simp [Pi.add_apply, Pi.smul_apply]
      _ = Finset.univ.sum (fun i => ((1 - t) * x i) * a i + (t * y i) * a i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
      _ = Finset.univ.sum (fun i => ((1 - t) * x i) * a i)
            + Finset.univ.sum (fun i => (t * y i) * a i) := by
              simp [Finset.sum_add_distrib]
      _ = (1 - t) * Finset.univ.sum (fun i => x i * a i)
            + t * Finset.univ.sum (fun i => y i * a i) := by
              have h1 :
                  Finset.univ.sum (fun i => ((1 - t) * x i) * a i)
                    = (1 - t) * Finset.univ.sum (fun i => x i * a i) := by
                  calc
                    Finset.univ.sum (fun i => ((1 - t) * x i) * a i)
                        = Finset.univ.sum (fun i => (1 - t) * (x i * a i)) := by
                            refine Finset.sum_congr rfl ?_
                            intro i hi
                            ring
                    _ = (1 - t) * Finset.univ.sum (fun i => x i * a i) := by
                            simpa using (Finset.mul_sum (s := Finset.univ)
                              (f := fun i => x i * a i) (a := (1 - t))).symm
              have h2 :
                  Finset.univ.sum (fun i => (t * y i) * a i)
                    = t * Finset.univ.sum (fun i => y i * a i) := by
                  calc
                    Finset.univ.sum (fun i => (t * y i) * a i)
                        = Finset.univ.sum (fun i => t * (y i * a i)) := by
                            refine Finset.sum_congr rfl ?_
                            intro i hi
                            ring
                    _ = t * Finset.univ.sum (fun i => y i * a i) := by
                            simpa using (Finset.mul_sum (s := Finset.univ)
                              (f := fun i => y i * a i) (a := t)).symm
              simp [h1, h2]
  have hreal :
      Finset.univ.sum (fun i => ((1 - t) • x + t • y) i * a i) + α
        = (1 - t) * (Finset.univ.sum (fun i => x i * a i) + α)
          + t * (Finset.univ.sum (fun i => y i * a i) + α) := by
    calc
      Finset.univ.sum (fun i => ((1 - t) • x + t • y) i * a i) + α
          = ((1 - t) * Finset.univ.sum (fun i => x i * a i)
              + t * Finset.univ.sum (fun i => y i * a i)) + α := by
                simpa using congrArg (fun r => r + α) hsum
      _ = (1 - t) * (Finset.univ.sum (fun i => x i * a i) + α)
            + t * (Finset.univ.sum (fun i => y i * a i) + α) := by
              ring
  have hcoe :
      ((Finset.univ.sum (fun i => ((1 - t) • x + t • y) i * a i) + α : Real) : EReal)
        = (( (1 - t) * (Finset.univ.sum (fun i => x i * a i) + α)
              + t * (Finset.univ.sum (fun i => y i * a i) + α) : Real) : EReal) := by
      simpa using congrArg (fun r : Real => (r : EReal)) hreal
  calc
    ((Finset.univ.sum (fun i => ((1 - t) • x + t • y) i * a i) + α : Real) : EReal)
        = (( (1 - t) * (Finset.univ.sum (fun i => x i * a i) + α)
              + t * (Finset.univ.sum (fun i => y i * a i) + α) : Real) : EReal) := hcoe
    _ = ((1 - t : Real) : EReal) * ((Finset.univ.sum (fun i => x i * a i) + α : Real) : EReal)
          + ((t : Real) : EReal) * ((Finset.univ.sum (fun i => y i * a i) + α : Real) : EReal) := by
        simp

lemma affineFunctionOn_univ_inner_add_const {n : Nat} (a : Fin n → Real) (α : Real) :
    AffineFunctionOn (Set.univ) (fun x : Fin n → Real =>
      ((Finset.univ.sum (fun i => x i * a i) + α : Real) : EReal)) := by
  classical
  let f : (Fin n → Real) → EReal := fun x =>
    ((Finset.univ.sum (fun i => x i * a i) + α : Real) : EReal)
  refine ⟨?finite, ?convex, ?hypo⟩
  · intro x hx
    constructor
    · simp
    · have h' :
          (↑(Finset.univ.sum (fun i => x i * a i)) + (↑α : EReal)) ≠ ⊤ := by
        exact EReal.add_ne_top (by simp) (by simp)
      simpa [f] using h'
  · rw [convexFunctionOn_iff_segment_inequality (C := Set.univ) (f := f) (hC := convex_univ)]
    · intro x hx y hy t ht0 ht1
      have hEq :
          f ((1 - t) • x + t • y)
            = ((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y := by
        simpa [f] using (inner_add_const_combo_eq (a := a) (α := α) (t := t) (x := x) (y := y))
      exact le_of_eq hEq
    intro x hx
    simp [f]
  · refine (convex_iff_forall_pos).2 ?_
    intro p hp q hq s t hs ht hst
    have hp' : (p.2 : EReal) ≤ f p.1 := by
      have hp'' : p.1 ∈ (Set.univ : Set (Fin n → Real)) ∧ (p.2 : EReal) ≤ f p.1 := by
        simpa using hp
      exact hp''.2
    have hq' : (q.2 : EReal) ≤ f q.1 := by
      have hq'' : q.1 ∈ (Set.univ : Set (Fin n → Real)) ∧ (q.2 : EReal) ≤ f q.1 := by
        simpa using hq
      exact hq''.2
    have hp_real : p.2 ≤ Finset.univ.sum (fun i => p.1 i * a i) + α := by
      have hp'' :
          (p.2 : EReal)
            ≤ ((Finset.univ.sum (fun i => p.1 i * a i) + α : Real) : EReal) := by
        simpa [f, -EReal.coe_add] using hp'
      exact (EReal.coe_le_coe_iff.mp hp'')
    have hq_real : q.2 ≤ Finset.univ.sum (fun i => q.1 i * a i) + α := by
      have hq'' :
          (q.2 : EReal)
            ≤ ((Finset.univ.sum (fun i => q.1 i * a i) + α : Real) : EReal) := by
        simpa [f, -EReal.coe_add] using hq'
      exact (EReal.coe_le_coe_iff.mp hq'')
    have hs' : s = 1 - t := by linarith
    have hineq_real :
        s * p.2 + t * q.2 ≤ (1 - t) * (Finset.univ.sum (fun i => p.1 i * a i) + α)
          + t * (Finset.univ.sum (fun i => q.1 i * a i) + α) := by
      have h1 : s * p.2 ≤ s * (Finset.univ.sum (fun i => p.1 i * a i) + α) := by
        exact mul_le_mul_of_nonneg_left hp_real hs.le
      have h2 : t * q.2 ≤ t * (Finset.univ.sum (fun i => q.1 i * a i) + α) := by
        exact mul_le_mul_of_nonneg_left hq_real ht.le
      have h := add_le_add h1 h2
      simpa [hs'] using h
    have hineq_E :
        ((s * p.2 + t * q.2 : Real) : EReal)
          ≤ ((1 - t : Real) : EReal)
              * ((Finset.univ.sum (fun i => p.1 i * a i) + α : Real) : EReal)
            + ((t : Real) : EReal)
              * ((Finset.univ.sum (fun i => q.1 i * a i) + α : Real) : EReal) := by
      have hineq_E' :
          ((s * p.2 + t * q.2 : Real) : EReal)
            ≤ (( (1 - t) * (Finset.univ.sum (fun i => p.1 i * a i) + α)
                  + t * (Finset.univ.sum (fun i => q.1 i * a i) + α) : Real) : EReal) := by
        exact (EReal.coe_le_coe_iff).2 hineq_real
      simpa [f] using hineq_E'
    have hEq :
        f (s • p.1 + t • q.1)
          = ((1 - t : Real) : EReal) * f p.1 + ((t : Real) : EReal) * f q.1 := by
      simpa [f, hs'] using
        (inner_add_const_combo_eq (a := a) (α := α) (t := t) (x := p.1) (y := q.1))
    have hineq_E' : ((s • p + t • q).2 : EReal) ≤ f ((s • p + t • q).1) := by
      calc
        ((s • p + t • q).2 : EReal) = ((s * p.2 + t * q.2 : Real) : EReal) := by
          simp [smul_eq_mul]
        _ ≤ ((1 - t : Real) : EReal) * f p.1 + ((t : Real) : EReal) * f q.1 := hineq_E
        _ = f ((s • p + t • q).1) := by
          simpa using hEq.symm
    simpa [Set.mem_univ] using hineq_E'

/-- Affine functions on `Set.univ` agree with convex combinations. -/
lemma affineFunctionOn_univ_eq_combo {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : AffineFunctionOn (Set.univ) f) :
    ∀ x y t, 0 ≤ t → t ≤ 1 →
      f ((1 - t) • x + t • y) =
        ((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y := by
  intro x y t ht0 ht1
  set g : (Fin n → Real) → Real := fun z => (f z).toReal
  have hfin : ∀ z, f z ≠ ⊥ ∧ f z ≠ ⊤ := by
    intro z
    simpa [Set.mem_univ] using (hf.1 z (by simp))
  have ht1' : 0 ≤ 1 - t := by linarith
  have hsum : (1 - t) + t = (1 : Real) := by ring
  have hx_epi : (x, g x) ∈ epigraph (Set.univ) f := by
    refine And.intro (by simpa using (Set.mem_univ x)) ?_
    simpa [g] using (EReal.le_coe_toReal (x := f x) (h := (hfin x).2))
  have hy_epi : (y, g y) ∈ epigraph (Set.univ) f := by
    refine And.intro (by simpa using (Set.mem_univ y)) ?_
    simpa [g] using (EReal.le_coe_toReal (x := f y) (h := (hfin y).2))
  have hconv_epi : Convex ℝ (epigraph (Set.univ) f) := by
    simpa [ConvexFunctionOn] using hf.2.1
  have hmem_epi :
      (1 - t) • (x, g x) + t • (y, g y) ∈ epigraph (Set.univ) f :=
    hconv_epi hx_epi hy_epi ht1' ht0 hsum
  rcases (by simpa [epigraph] using hmem_epi) with ⟨_, hmem_epi'⟩
  have hineq_epi :
      f ((1 - t) • x + t • y) ≤ ((1 - t) * g x + t * g y : Real) := by
    simpa [g, smul_eq_mul] using hmem_epi'
  let H :
      Set (Prod (Fin n → Real) Real) :=
        {p | p.1 ∈ (Set.univ : Set (Fin n → Real)) ∧ ((p.2 : EReal) ≤ f p.1)}
  have hx_hypo : (x, g x) ∈ H := by
    refine And.intro (by simp) ?_
    simpa [g] using (EReal.coe_toReal_le (x := f x) (h := (hfin x).1))
  have hy_hypo : (y, g y) ∈ H := by
    refine And.intro (by simp) ?_
    simpa [g] using (EReal.coe_toReal_le (x := f y) (h := (hfin y).1))
  have hconv_hypo : Convex ℝ H := by
    simpa [H] using hf.2.2
  have hmem_hypo :
      (1 - t) • (x, g x) + t • (y, g y) ∈ H :=
    hconv_hypo hx_hypo hy_hypo ht1' ht0 hsum
  have hmem_hypo' :
      ((1 - t) • (x, g x) + t • (y, g y)).1 ∈ Set.univ ∧
        (( ((1 - t) • (x, g x) + t • (y, g y)).2 : Real) : EReal) ≤
          f ((1 - t) • (x, g x) + t • (y, g y)).1 := by
    simpa [H] using hmem_hypo
  have hineq_hypo :
      ((1 - t) * g x + t * g y : Real) ≤ f ((1 - t) • x + t • y) := by
    simpa [g, smul_eq_mul] using hmem_hypo'.2
  have hcomb :
      f ((1 - t) • x + t • y) =
        (( (1 - t) * g x + t * g y : Real) : EReal) := by
    exact le_antisymm hineq_epi hineq_hypo
  have hx_coe : (g x : EReal) = f x := by
    simpa [g] using (EReal.coe_toReal (x := f x) (hx := (hfin x).2) (h'x := (hfin x).1))
  have hy_coe : (g y : EReal) = f y := by
    simpa [g] using (EReal.coe_toReal (x := f y) (hx := (hfin y).2) (h'x := (hfin y).1))
  calc
    f ((1 - t) • x + t • y)
        = (( (1 - t) * g x + t * g y : Real) : EReal) := hcomb
    _ =
        ((1 - t : Real) : EReal) * (g x : EReal) +
          ((t : Real) : EReal) * (g y : EReal) := by
        simp [EReal.coe_add, EReal.coe_mul]
    _ = ((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y := by
        simp [hx_coe, hy_coe]

/-- Subtracting the value at `0` gives a linear map for an affine function. -/
lemma affineFunctionOn_univ_toReal_linearMap {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : AffineFunctionOn (Set.univ) f) :
    ∃ A : (Fin n → Real) →ₗ[Real] Real, ∀ x, (f x).toReal = A x + (f 0).toReal := by
  classical
  let g : (Fin n → Real) → Real := fun x => (f x).toReal
  have hfin : ∀ z, f z ≠ ⊥ ∧ f z ≠ ⊤ := by
    intro z
    simpa [Set.mem_univ] using (hf.1 z (by simp))
  have hcombo :
      ∀ x y t, 0 ≤ t → t ≤ 1 →
        g ((1 - t) • x + t • y) = (1 - t) * g x + t * g y := by
    intro x y t ht0 ht1
    have hE :=
      affineFunctionOn_univ_eq_combo (f := f) hf x y t ht0 ht1
    have hx_coe : (g x : EReal) = f x := by
      simpa [g] using (EReal.coe_toReal (x := f x) (hx := (hfin x).2) (h'x := (hfin x).1))
    have hy_coe : (g y : EReal) = f y := by
      simpa [g] using (EReal.coe_toReal (x := f y) (hx := (hfin y).2) (h'x := (hfin y).1))
    have hE' :
        f ((1 - t) • x + t • y) =
          (( (1 - t) * g x + t * g y : Real) : EReal) := by
      calc
        f ((1 - t) • x + t • y)
            = ((1 - t : Real) : EReal) * (g x : EReal) +
                ((t : Real) : EReal) * (g y : EReal) := by
            simpa [hx_coe, hy_coe] using hE
        _ = (( (1 - t) * g x + t * g y : Real) : EReal) := by
            simp [EReal.coe_add, EReal.coe_mul]
    simpa [g] using congrArg EReal.toReal hE'
  let h : (Fin n → Real) → Real := fun x => g x - g 0
  have h_zero : h 0 = 0 := by simp [h]
  have hsmul_unit : ∀ t x, 0 ≤ t → t ≤ 1 → h (t • x) = t * h x := by
    intro t x ht0 ht1
    have h0 := hcombo 0 x t ht0 ht1
    have h0' : g (t • x) = (1 - t) * g 0 + t * g x := by
      simpa [smul_eq_mul] using h0
    calc
      h (t • x) = g (t • x) - g 0 := by simp [h]
      _ = (1 - t) * g 0 + t * g x - g 0 := by simp [h0']
      _ = t * (g x - g 0) := by ring
      _ = t * h x := by simp [h]
  have hadd : ∀ x y, h (x + y) = h x + h y := by
    intro x y
    have hhalf : (1 - (2⁻¹ : Real)) = (2⁻¹ : Real) := by norm_num
    have hxy :
        g ((2⁻¹ : Real) • x + (2⁻¹ : Real) • y)
          = (2⁻¹ : Real) * g x + (2⁻¹ : Real) * g y := by
      have hxy0 :=
        hcombo x y (2⁻¹ : Real) (by norm_num) (by norm_num)
      simpa [hhalf] using hxy0
    have hxy' :
        g ((2⁻¹ : Real) • x + (2⁻¹ : Real) • y)
          = (2⁻¹ : Real) * g (x + y) + (2⁻¹ : Real) * g 0 := by
      have hxy0 :=
        hcombo (x + y) 0 (2⁻¹ : Real) (by norm_num) (by norm_num)
      simpa [hhalf, smul_add, add_smul, smul_eq_mul] using hxy0
    have hsum :
        (2⁻¹ : Real) * g x + (2⁻¹ : Real) * g y
          = (2⁻¹ : Real) * g (x + y) + (2⁻¹ : Real) * g 0 := by
      exact hxy.symm.trans hxy'
    have hsum' : g (x + y) = g x + g y - g 0 := by
      linarith [hsum]
    simp [h, hsum', sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hsmul_nonneg : ∀ t x, 0 ≤ t → h (t • x) = t * h x := by
    intro t x ht0
    by_cases ht : t = 0
    · simp [ht, h]
    obtain ⟨n, hn⟩ := exists_nat_ge t
    have hn0' : n ≠ 0 := by
      intro hn0'
      have : t ≤ (0 : Real) := by simpa [hn0'] using hn
      exact ht (le_antisymm this ht0)
    have hn0 : (n : Real) ≠ 0 := by exact_mod_cast hn0'
    have hnpos : 0 < (n : Real) := by
      exact_mod_cast (Nat.pos_of_ne_zero hn0')
    have hs0 : 0 ≤ t / n := by
      have hn0' : 0 ≤ (n : Real) := by exact_mod_cast (Nat.zero_le n)
      exact div_nonneg ht0 hn0'
    have hs1 : t / n ≤ 1 := by
      have h : t ≤ (n : Real) := by simpa using hn
      exact (div_le_one (a := t) (b := (n : Real)) hnpos).2 h
    have hsn : (n : Real) * (t / n) = t := by
      simpa using (mul_div_cancel₀ t hn0)
    have hnat : ∀ n : Nat, ∀ x, h ((n : Real) • x) = (n : Real) * h x := by
      intro n x
      have hnat' : h (n • x) = (n : Real) * h x := by
        induction n with
        | zero =>
            simp [h_zero]
        | succ n ih =>
            calc
              h ((Nat.succ n) • x) = h (n • x + x) := by
                simp [Nat.succ_eq_add_one, add_smul]
              _ = h (n • x) + h x := hadd _ _
              _ = (n : Real) * h x + h x := by rw [ih]
              _ = (Nat.succ n : Real) * h x := by
                simp [Nat.cast_succ, add_mul, add_comm]
      simpa [Nat.cast_smul_eq_nsmul] using hnat'
    have htdecomp : t • x = (n : Real) • ((t / n) • x) := by
      have htdecomp' :
          (n : Real) • ((t / n) • x) = t • x := by
        calc
          (n : Real) • ((t / n) • x) = ((n : Real) * (t / n)) • x := by
            simp [smul_smul]
          _ = t • x := by simp [hsn]
      simpa using htdecomp'.symm
    calc
      h (t • x) = h ((n : Real) • ((t / n) • x)) := by
        simp [htdecomp]
      _ = (n : Real) * h ((t / n) • x) := hnat n _
      _ = (n : Real) * ((t / n) * h x) := by
        simp [hsmul_unit, hs0, hs1]
      _ = ((n : Real) * (t / n)) * h x := by ring
      _ = t * h x := by simp [hsn]
  have hsmul : ∀ t x, h (t • x) = t * h x := by
    intro t x
    by_cases ht0 : 0 ≤ t
    · exact hsmul_nonneg t x ht0
    · have ht0' : 0 ≤ -t := by linarith
      have hneg : h (-x) = -h x := by
        have hsum := hadd x (-x)
        have hsum' : h x + h (-x) = 0 := by
          simpa [h_zero] using hsum.symm
        linarith [hsum']
      calc
        h (t • x) = h ((-t) • (-x)) := by
          simp [smul_neg, neg_smul]
        _ = (-t) * h (-x) := hsmul_nonneg (-t) (-x) ht0'
        _ = t * h x := by
          simp [hneg]
  refine ⟨
    { toFun := h
      map_add' := hadd
      map_smul' := hsmul }, ?_⟩
  intro x
  simp [h, g]

/-- A linear functional on `Fin n → ℝ` is determined by its values on the standard basis. -/
lemma linearMap_apply_eq_sum_mul_basis {n : Nat} (A : (Fin n → Real) →ₗ[Real] Real)
    (x : Fin n → Real) :
    A x = ∑ i, x i * A (fun j => if j = i then 1 else 0) := by
  classical
  let e : Fin n → Fin n → Real := fun i j => if j = i then 1 else 0
  have hx : x = ∑ i, x i • e i := by
    ext j
    have hsum : ∑ i, x i * (if j = i then (1 : Real) else 0) = x j := by
      simp
    simp [e, smul_eq_mul]
  calc
    A x = A (∑ i, x i • e i) := by
        exact congrArg A hx
    _ = ∑ i, A (x i • e i) := by
        exact (map_sum A (f := fun i => x i • e i) (s := Finset.univ))
    _ = ∑ i, x i * A (e i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [smul_eq_mul]
    _ = ∑ i, x i * A (fun j => if j = i then 1 else 0) := by
        rfl

/-- Remark 4.5.0: Every affine function on `ℝ^n` is of the form
`x ↦ ⟪x, a⟫ + α` for some `a ∈ ℝ^n` and `α ∈ ℝ` (Theorem 1.5). -/
lemma affineFunctionOn_univ_exists_inner_add_const {n : Nat}
    {f : (Fin n → Real) → EReal} (hf : AffineFunctionOn (Set.univ) f) :
    ∃ a : Fin n → Real, ∃ α : Real, ∀ x,
      f x = ((Finset.univ.sum (fun i => x i * a i) + α : Real) : EReal) := by
  classical
  rcases affineFunctionOn_univ_toReal_linearMap (f := f) hf with ⟨A, hA⟩
  let a : Fin n → Real := fun i => A (fun j => if j = i then 1 else 0)
  let α : Real := (f 0).toReal
  refine ⟨a, α, ?_⟩
  intro x
  have hAx : (f x).toReal = A x + α := by
    simpa [α] using hA x
  have hAx' : A x = ∑ i, x i * a i := by
    simpa [a] using (linearMap_apply_eq_sum_mul_basis (A := A) (x := x))
  have hfin : f x ≠ ⊥ ∧ f x ≠ ⊤ := by
    simpa [Set.mem_univ] using (hf.1 x (by simp))
  have hx_coe : ((f x).toReal : EReal) = f x := by
    simpa using (EReal.coe_toReal (x := f x) (hx := hfin.2) (h'x := hfin.1))
  have hAx_coe :
      ((f x).toReal : EReal) =
        ((Finset.univ.sum (fun i => x i * a i) + α : Real) : EReal) := by
    have hAx'' : (f x).toReal = Finset.univ.sum (fun i => x i * a i) + α := by
      simpa [hAx'] using hAx
    simpa using congrArg (fun r : Real => (r : EReal)) hAx''
  simpa [hx_coe] using hAx_coe

/-- Definition 4.5: The dimension of the effective domain of `f` is called the
dimension of `f`. -/
noncomputable def functionDimension {n : Nat} (S : Set (Fin n -> Real))
    (f : (Fin n -> Real) -> EReal) :
    Nat :=
  Module.finrank ℝ (affineSpan ℝ (effectiveDomain S f)).direction

/-- If `x ∈ S` and `f x ≤ μ`, then `(x, μ)` is in the epigraph. -/
lemma epigraph_mem_of_le {n : Nat} {S : Set (Fin n → Real)}
    {f : (Fin n → Real) → EReal} {x : Fin n → Real} {μ : Real}
    (hx : x ∈ S) (hμ : f x ≤ (μ : EReal)) : (x, μ) ∈ epigraph S f := by
  exact And.intro hx hμ

/-- Convexity of the epigraph yields convex combinations of points in it. -/
lemma convex_combo_mem_epigraph {n : Nat} {S : Set (Fin n → Real)}
    {f : (Fin n → Real) → EReal} {x y : Fin n → Real} {μ v t : Real}
    (hconv : Convex ℝ (epigraph S f))
    (hx : (x, μ) ∈ epigraph S f) (hy : (y, v) ∈ epigraph S f)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) • (x, μ) + t • (y, v) ∈ epigraph S f := by
  have ht1' : 0 ≤ (1 - t) := by linarith
  have hsum : (1 - t) + t = (1 : Real) := by ring
  simpa using hconv hx hy ht1' ht0 hsum

/-- Unpack epigraph membership of a convex combination. -/
lemma epigraph_combo_proj {n : Nat} {S : Set (Fin n → Real)}
    {f : (Fin n → Real) → EReal} {x y : Fin n → Real} {μ v t : Real} :
    ((1 - t) • (x, μ) + t • (y, v)) ∈ epigraph S f →
      ((1 - t) • x + t • y) ∈ S ∧
        f ((1 - t) • x + t • y) ≤
          (((1 - t) * μ + t * v : Real) : EReal) := by
  intro hmem
  have hmem' :
      S ((1 - t) • (x, μ) + t • (y, v)).1 ∧
        f ((1 - t) • (x, μ) + t • (y, v)).1 ≤
          (((1 - t) • (x, μ) + t • (y, v)).2 : EReal) := by
    simpa [epigraph] using hmem
  rcases hmem' with ⟨hS, hle⟩
  refine ⟨?_, ?_⟩
  · simpa using hS
  · simpa [smul_eq_mul] using hle

/-- Remark 4.5.1: For convexity of the epigraph, one requires that for any `x, y ∈ S`,
any `μ, v ∈ ℝ` with `f x ≤ μ` and `f y ≤ v`, and any `0 ≤ λ ≤ 1`, the point
`(1 - λ) x + λ y` lies in `S` and satisfies
`f ((1 - λ) x + λ y) ≤ (1 - λ) μ + λ v`; this condition admits several equivalent
formulations. -/
lemma convexFunctionOn_epigraph_condition {n : Nat} {S : Set (Fin n -> Real)}
    {f : (Fin n -> Real) -> EReal} (hf : ConvexFunctionOn S f) :
    ∀ x ∈ S, ∀ y ∈ S, ∀ μ v : Real,
      f x ≤ (μ : EReal) → f y ≤ (v : EReal) →
      ∀ t : Real, 0 ≤ t → t ≤ 1 →
        ((1 - t) • x + t • y) ∈ S ∧
          f ((1 - t) • x + t • y) ≤
            (((1 - t) * μ + t * v : Real) : EReal) := by
  intro x hx y hy μ v hμ hv t ht0 ht1
  have hconv : Convex ℝ (epigraph S f) := by
    simpa [ConvexFunctionOn] using hf
  have hx_epi : (x, μ) ∈ epigraph S f := epigraph_mem_of_le (x := x) (μ := μ) hx hμ
  have hy_epi : (y, v) ∈ epigraph S f := epigraph_mem_of_le (x := y) (μ := v) hy hv
  have hmem :
      (1 - t) • (x, μ) + t • (y, v) ∈ epigraph S f :=
    convex_combo_mem_epigraph (x := x) (y := y) (μ := μ) (v := v) (t := t)
      hconv hx_epi hy_epi ht0 ht1
  exact epigraph_combo_proj (x := x) (y := y) (μ := μ) (v := v) (t := t) hmem

/-- Expansion of the quadratic form on a linear combination. -/
lemma quadratic_combo_expansion {n : Nat} {Q : Matrix (Fin n) (Fin n) ℝ}
    (x y : Fin n → ℝ) (t u : ℝ) :
    dotProduct (t • x + u • y) (Q.mulVec (t • x + u • y)) =
      t ^ 2 * dotProduct x (Q.mulVec x) + u ^ 2 * dotProduct y (Q.mulVec y) +
        t * u * (dotProduct x (Q.mulVec y) + dotProduct y (Q.mulVec x)) := by
  simp [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, pow_two]
  ring

/-- Quadratic form of a difference expressed via cross terms. -/
lemma quadratic_sub_cross {n : Nat} {Q : Matrix (Fin n) (Fin n) ℝ}
    (x y : Fin n → ℝ) :
    dotProduct (x - y) (Q.mulVec (x - y)) =
      dotProduct x (Q.mulVec x) + dotProduct y (Q.mulVec y) -
        (dotProduct x (Q.mulVec y) + dotProduct y (Q.mulVec x)) := by
  simpa [sub_eq_add_neg, pow_two] using
    (quadratic_combo_expansion (Q := Q) x y (1 : ℝ) (-1 : ℝ))

/-- Convexity of the quadratic function forces its quadratic form to be nonnegative. -/
lemma convexity_implies_quadratic_nonneg {n : Nat}
    {Q : Matrix (Fin n) (Fin n) ℝ} {a : Fin n → ℝ} {α : ℝ}
    (hconv : ConvexOn ℝ (Set.univ) (fun x : Fin n → ℝ =>
      (1 / 2 : ℝ) * dotProduct x (Q.mulVec x) + dotProduct x a + α)) :
    ∀ x, 0 ≤ dotProduct x (Q.mulVec x) := by
  classical
  let q : (Fin n → ℝ) → ℝ := fun x => dotProduct x (Q.mulVec x)
  let f : (Fin n → ℝ) → ℝ := fun x => (1 / 2 : ℝ) * q x + dotProduct x a + α
  intro x
  have hineq :=
    hconv.2 (by simp : x ∈ Set.univ) (by simp : -x ∈ Set.univ)
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1)
  have hzero : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (-x) = 0 := by
    ext i
    simp [smul_eq_mul]
  have hineq' :
      α ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) * q x + dotProduct x a + α) +
        (1 / 2 : ℝ) * ((1 / 2 : ℝ) * q x - dotProduct x a + α) := by
    have hineq'' :
        α ≤ (1 / 2 : ℝ) * f x + (1 / 2 : ℝ) * f (-x) := by
      simpa [f, q, hzero, mulVec_neg, neg_dotProduct, neg_dotProduct_neg,
        smul_eq_mul, sub_eq_add_neg] using hineq
    simpa [f, q, mulVec_neg, neg_dotProduct, neg_dotProduct_neg, smul_eq_mul,
      sub_eq_add_neg] using hineq''
  have hineq'' : α ≤ (1 / 2 : ℝ) * q x + α := by
    nlinarith [hineq']
  nlinarith [hineq'']

/-- Positive semidefinite quadratic form yields convexity of the quadratic function. -/
lemma posSemidef_implies_convexity_quadratic {n : Nat}
    {Q : Matrix (Fin n) (Fin n) ℝ} {a : Fin n → ℝ} {α : ℝ}
    (hpos : Matrix.PosSemidef Q) :
    ConvexOn ℝ (Set.univ) (fun x : Fin n → ℝ =>
      (1 / 2 : ℝ) * dotProduct x (Q.mulVec x) + dotProduct x a + α) := by
  classical
  let q : (Fin n → ℝ) → ℝ := fun x => dotProduct x (Q.mulVec x)
  have hpos' := (posSemidef_iff_real (M := Q)).1 hpos
  have hnonneg : ∀ x, 0 ≤ q x := by
    intro x
    simpa [q] using hpos'.2 x
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy t u ht hu htu
  let s : Fin n → ℝ := t • x + u • y
  have hcross :
      dotProduct x (Q.mulVec y) + dotProduct y (Q.mulVec x) =
        q x + q y - q (x - y) := by
    have hsub := quadratic_sub_cross (Q := Q) x y
    linarith [hsub]
  have hq_combo' :
      q s = t * q x + u * q y - t * u * q (x - y) := by
    have h1 : t ^ 2 + t * u = t := by
      calc
        t ^ 2 + t * u = t * (t + u) := by ring
        _ = t := by simp [htu]
    have h2 : u ^ 2 + t * u = u := by
      calc
        u ^ 2 + t * u = u * (t + u) := by ring
        _ = u := by simp [htu]
    calc
      q s =
          t ^ 2 * q x + u ^ 2 * q y +
            t * u * (dotProduct x (Q.mulVec y) + dotProduct y (Q.mulVec x)) := by
            simpa [q, s] using (quadratic_combo_expansion (Q := Q) x y t u)
      _ = t ^ 2 * q x + u ^ 2 * q y + t * u * (q x + q y - q (x - y)) := by
            simp [hcross]
      _ = (t ^ 2 + t * u) * q x + (u ^ 2 + t * u) * q y - t * u * q (x - y) := by
            ring
      _ = t * q x + u * q y - t * u * q (x - y) := by
            simp [h1, h2]
  have hlin :
      dotProduct s a = t * dotProduct x a + u * dotProduct y a := by
    simp [s, add_dotProduct, smul_dotProduct, smul_eq_mul]
  have hsub_nonneg : 0 ≤ (1 / 2 : ℝ) * (t * u * q (x - y)) := by
    have htu_nonneg : 0 ≤ t * u := mul_nonneg ht hu
    have htuq_nonneg : 0 ≤ t * u * q (x - y) :=
      mul_nonneg htu_nonneg (hnonneg (x - y))
    have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
    exact mul_nonneg hhalf htuq_nonneg
  have hineq_base :
      (1 / 2 : ℝ) * q s + dotProduct s a + α ≤
        t * ((1 / 2 : ℝ) * q x) + u * ((1 / 2 : ℝ) * q y) +
          t * dotProduct x a + u * dotProduct y a + α := by
    have hcalc :
        (1 / 2 : ℝ) * q s + dotProduct s a + α =
          t * ((1 / 2 : ℝ) * q x) + u * ((1 / 2 : ℝ) * q y) +
            t * dotProduct x a + u * dotProduct y a + α -
            (1 / 2 : ℝ) * (t * u * q (x - y)) := by
      simp [hq_combo', hlin, mul_add, sub_eq_add_neg]
      ring
    calc
      (1 / 2 : ℝ) * q s + dotProduct s a + α
          =
          t * ((1 / 2 : ℝ) * q x) + u * ((1 / 2 : ℝ) * q y) +
            t * dotProduct x a + u * dotProduct y a + α -
            (1 / 2 : ℝ) * (t * u * q (x - y)) := hcalc
      _ ≤
          t * ((1 / 2 : ℝ) * q x) + u * ((1 / 2 : ℝ) * q y) +
            t * dotProduct x a + u * dotProduct y a + α := by
          exact sub_le_self _ hsub_nonneg
  have hmul :
      t * ((1 / 2 : ℝ) * q x + dotProduct x a) +
          u * ((1 / 2 : ℝ) * q y + dotProduct y a) + α =
        t * ((1 / 2 : ℝ) * q x) + u * ((1 / 2 : ℝ) * q y) +
          t * dotProduct x a + u * dotProduct y a + α := by
    ring
  have hineq :
      (1 / 2 : ℝ) * q s + dotProduct s a + α ≤
        t * ((1 / 2 : ℝ) * q x + dotProduct x a) +
          u * ((1 / 2 : ℝ) * q y + dotProduct y a) + α := by
    rw [hmul]
    exact hineq_base
  have hRHS :
      t * ((1 / 2 : ℝ) * q x + dotProduct x a + α) +
          u * ((1 / 2 : ℝ) * q y + dotProduct y a + α) =
        t * ((1 / 2 : ℝ) * q x + dotProduct x a) +
          u * ((1 / 2 : ℝ) * q y + dotProduct y a) + (t + u) * α := by
    ring
  have hRHS' :
      t * ((1 / 2 : ℝ) * q x + dotProduct x a + α) +
          u * ((1 / 2 : ℝ) * q y + dotProduct y a + α) =
        t * ((1 / 2 : ℝ) * q x + dotProduct x a) +
          u * ((1 / 2 : ℝ) * q y + dotProduct y a) + α := by
    simpa [htu] using hRHS
  have hineq' :
      (1 / 2 : ℝ) * q s + dotProduct s a + α ≤
        t * ((1 / 2 : ℝ) * q x + dotProduct x a + α) +
          u * ((1 / 2 : ℝ) * q y + dotProduct y a + α) := by
    rw [hRHS']
    exact hineq
  simpa [q, s, smul_eq_mul] using hineq'

/-- Remark 4.5.1: A quadratic function
`f x = (1/2) ⟪x, Q x⟫ + ⟪x, a⟫ + α`, where `Q` is a symmetric `n × n` matrix,
is convex on `ℝ^n` iff `Q` is positive semidefinite, i.e.
`⟪z, Q z⟫ ≥ 0` for every `z ∈ ℝ^n`. -/
lemma convexOn_quadratic_iff_posSemidef {n : Nat}
    {Q : Matrix (Fin n) (Fin n) ℝ} {a : Fin n → ℝ} {α : ℝ}
    (hQ : Matrix.IsSymm Q) :
    ConvexOn ℝ (Set.univ) (fun x : Fin n → ℝ =>
      ((1 / 2 : ℝ) * dotProduct x (Q.mulVec x) + dotProduct x a + α)) ↔
      Matrix.PosSemidef Q := by
  classical
  constructor
  · intro hconv
    have hnonneg : ∀ x, 0 ≤ dotProduct x (Q.mulVec x) :=
      convexity_implies_quadratic_nonneg (Q := Q) (a := a) (α := α) hconv
    refine (posSemidef_iff_real (M := Q)).2 ?_
    refine ⟨?_, ?_⟩
    · simpa [Matrix.IsHermitian, Matrix.IsSymm, conjTranspose_eq_transpose_of_trivial] using hQ
    · intro x
      simpa using hnonneg x
  · intro hpos
    exact posSemidef_implies_convexity_quadratic (Q := Q) (a := a) (α := α) hpos

/- Remark 4.5.2: An interesting function on `ℝ^n` whose convexity may be verified by
Theorem 4.5 is the negative geometric mean:
`f(x) = -(xi_1 * xi_2 * ... * xi_n)^(1/n)` if `xi_1 ≥ 0, ..., xi_n ≥ 0`, and
`f(x) = +∞` otherwise. -/
/-- Cauchy-Schwarz for `Fin n`: the square of the sum is bounded by `n` times the sum of squares. -/
lemma sum_sq_le_n_mul_sum_sq {n : Nat} (u : Fin n → Real) :
    (Finset.univ.sum u) ^ 2 ≤ (n : Real) * Finset.univ.sum (fun i => (u i) ^ 2) := by
  classical
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset (Fin n)))
      (f := u) (g := fun _ => (1 : Real)))

/-- The closure of the positive orthant is the nonnegative orthant. -/
lemma closure_posOrthant_eq_nonneg {n : Nat} :
    closure {x : Fin n → Real | ∀ i, 0 < x i} = {x | ∀ i, 0 ≤ x i} := by
  classical
  have hpos :
      ({x : Fin n → Real | ∀ i, 0 < x i} : Set (Fin n → Real)) =
        Set.pi (Set.univ : Set (Fin n)) (fun _ => Set.Ioi (0 : Real)) := by
    ext x; simp
  have hnonneg :
      ({x : Fin n → Real | ∀ i, 0 ≤ x i} : Set (Fin n → Real)) =
        Set.pi (Set.univ : Set (Fin n)) (fun _ => Set.Ici (0 : Real)) := by
    ext x; simp [Pi.le_def]
  have hclosure :=
    (closure_pi_set (I := (Set.univ : Set (Fin n)))
      (s := fun _ => Set.Ioi (0 : Real)))
  simpa [hpos, hnonneg, closure_Ioi] using hclosure

/-- The positive orthant is open. -/
lemma isOpen_posOrthant {n : Nat} : IsOpen {x : Fin n → Real | ∀ i, 0 < x i} := by
  classical
  have hpos :
      ({x : Fin n → Real | ∀ i, 0 < x i} : Set (Fin n → Real)) =
        Set.pi (Set.univ : Set (Fin n)) (fun _ => Set.Ioi (0 : Real)) := by
    ext x; simp
  have hopen :
      IsOpen (Set.pi (Set.univ : Set (Fin n)) (fun _ => Set.Ioi (0 : Real))) := by
    refine isOpen_set_pi (i := (Set.univ : Set (Fin n)))
      (s := fun _ => Set.Ioi (0 : Real)) (hi := (Set.finite_univ)) ?_
    intro i hi
    simpa using isOpen_Ioi
  simpa [hpos] using hopen

/-- The positive orthant is convex. -/
lemma convex_posOrthant {n : Nat} : Convex ℝ {x : Fin n → Real | ∀ i, 0 < x i} := by
  classical
  have hpos :
      ({x : Fin n → Real | ∀ i, 0 < x i} : Set (Fin n → Real)) =
        Set.pi (Set.univ : Set (Fin n)) (fun _ => Set.Ioi (0 : Real)) := by
    ext x; simp
  have hconv :
      Convex ℝ (Set.pi (Set.univ : Set (Fin n)) (fun _ => Set.Ioi (0 : Real))) := by
    refine convex_pi ?_
    intro i hi
    simpa using (convex_Ioi (𝕜 := ℝ) (β := ℝ) (r := (0 : Real)))
  simpa [hpos] using hconv

/-- The coordinate product is `C^2` on any set. -/
lemma contDiffOn_prod_coord {n : Nat} {C : Set (Fin n → Real)} :
    ContDiffOn ℝ 2 (fun x : Fin n → Real => ∏ i, x i) C := by
  classical
  refine contDiffOn_prod (t := (Finset.univ : Finset (Fin n))) (s := C)
    (f := fun i x => x i) ?_
  intro i hi
  simpa using (contDiff_apply (𝕜 := ℝ) (E := ℝ) (n := 2) i).contDiffOn

/-- The coordinate product is nonzero on the positive orthant. -/
lemma prod_ne_zero_of_pos {n : Nat} {x : Fin n → Real} (hx : ∀ i, 0 < x i) :
    (Finset.univ.prod (fun i => x i)) ≠ 0 := by
  classical
  have hpos : 0 < Finset.univ.prod (fun i => x i) := by
    refine Finset.prod_pos ?_
    intro i hi
    exact hx i
  exact ne_of_gt hpos

/-- The negative geometric mean is `C^2` on the positive orthant. -/
lemma contDiffOn_negGeomMean_pos {n : Nat} :
    ContDiffOn ℝ 2 (fun x : Fin n → Real =>
      -(Real.rpow (Finset.univ.prod (fun i => x i)) (1 / (n : Real))))
      {x | ∀ i, 0 < x i} := by
  classical
  have hprod :
      ContDiffOn ℝ 2 (fun x : Fin n → Real => Finset.univ.prod (fun i => x i))
        {x | ∀ i, 0 < x i} := contDiffOn_prod_coord
  have hprod_ne :
      ∀ x ∈ {x : Fin n → Real | ∀ i, 0 < x i},
        Finset.univ.prod (fun i => x i) ≠ 0 := by
    intro x hx
    exact prod_ne_zero_of_pos (x := x) hx
  have hpow :
      ContDiffOn ℝ 2 (fun x : Fin n → Real =>
        (Finset.univ.prod (fun i => x i)) ^ (1 / (n : Real)))
        {x | ∀ i, 0 < x i} :=
    (ContDiffOn.rpow_const_of_ne (p := (1 / (n : Real))) hprod hprod_ne)
  simpa using hpow.neg

/-- Product over `Finset.univ` with two entries removed. -/
lemma prod_erase_erase_eq_div {n : Nat} (x : Fin n → Real) (hx : ∀ i, x i ≠ 0) {i j : Fin n}
    (hj : j ∈ (Finset.univ.erase i)) :
    ((Finset.univ.erase i).erase j).prod (fun k => x k) =
      (Finset.univ.prod (fun k => x k)) / x i / x j := by
  classical
  have h1 :
      (Finset.univ.erase i).prod (fun k => x k) =
        (Finset.univ.prod (fun k => x k)) / x i := by
    have hx_i : x i ≠ 0 := hx i
    have hmul :
        x i * (Finset.univ.erase i).prod (fun k => x k) =
          Finset.univ.prod (fun k => x k) := by
      simpa using
        (Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin n)))
          (f := fun k => x k) (a := i) (h := Finset.mem_univ i))
    field_simp [hx_i]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have h2 :
      ((Finset.univ.erase i).erase j).prod (fun k => x k) =
        (Finset.univ.erase i).prod (fun k => x k) / x j := by
    have hx_j : x j ≠ 0 := hx j
    have hmul :
        x j * ((Finset.univ.erase i).erase j).prod (fun k => x k) =
          (Finset.univ.erase i).prod (fun k => x k) := by
      simpa using
        (Finset.mul_prod_erase (s := (Finset.univ.erase i))
          (f := fun k => x k) (a := j) (h := hj))
    field_simp [hx_j]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  calc
    ((Finset.univ.erase i).erase j).prod (fun k => x k) =
        (Finset.univ.erase i).prod (fun k => x k) / x j := h2
    _ = (Finset.univ.prod (fun k => x k)) / x i / x j := by
          simp [h1, div_eq_mul_inv, mul_assoc]

/-- Off-diagonal double sum identity. -/
lemma sum_erase_mul_sum_eq_sum_sq_sub_sum_sq {n : Nat} (u : Fin n → Real) :
    (∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j => u i * u j))) =
      (Finset.univ.sum u) ^ 2 - Finset.univ.sum (fun i => (u i) ^ 2) := by
  classical
  have hsplit :
      ∑ i, (u i * u i + Finset.sum (s := (Finset.univ.erase i)) (fun j => u i * u j)) =
        ∑ i, (Finset.sum (s := (Finset.univ : Finset (Fin n))) (fun j => u i * u j)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp
  have hsum_add :
      (∑ i, (u i * u i + Finset.sum (s := (Finset.univ.erase i)) (fun j => u i * u j))) =
        (∑ i, u i * u i) +
          ∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j => u i * u j)) := by
    exact
      (Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin n)))
        (f := fun i => u i * u i)
        (g := fun i => Finset.sum (s := (Finset.univ.erase i)) (fun j => u i * u j)))
  have hsplit' :
      (∑ i, u i * u i) + ∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j => u i * u j)) =
        ∑ i, (Finset.sum (s := (Finset.univ : Finset (Fin n))) (fun j => u i * u j)) := by
    calc
      (∑ i, u i * u i) +
          ∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j => u i * u j)) =
          ∑ i, (u i * u i + Finset.sum (s := (Finset.univ.erase i)) (fun j => u i * u j)) :=
        hsum_add.symm
      _ =
          ∑ i, (Finset.sum (s := (Finset.univ : Finset (Fin n))) (fun j => u i * u j)) :=
        hsplit
  have hsum_off :
      (∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j => u i * u j))) =
        ∑ i, (Finset.sum (s := (Finset.univ : Finset (Fin n))) (fun j => u i * u j)) -
          ∑ i, u i * u i := by
    refine (eq_sub_iff_add_eq).2 ?_
    calc
      (∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j => u i * u j))) + ∑ i, u i * u i =
          (∑ i, u i * u i) +
            ∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j => u i * u j)) := by
        ac_rfl
      _ =
          ∑ i, (Finset.sum (s := (Finset.univ : Finset (Fin n))) (fun j => u i * u j)) :=
        hsplit'
  have hsum_sq :
      (Finset.univ.sum u) ^ 2 =
        ∑ i, (Finset.sum (s := (Finset.univ : Finset (Fin n))) (fun j => u i * u j)) := by
    simpa [pow_two] using
      (Finset.sum_mul_sum (s := (Finset.univ : Finset (Fin n)))
        (t := (Finset.univ : Finset (Fin n))) (f := u) (g := u))
  have hdiag : ∑ i, u i ^ 2 = ∑ i, u i * u i := by
    simp [pow_two]
  calc
    ∑ i, (Finset.sum (s := (Finset.univ.erase i)) (fun j => u i * u j))
        = ∑ i, (Finset.sum (s := (Finset.univ : Finset (Fin n))) (fun j => u i * u j)) -
            ∑ i, u i * u i := hsum_off
    _ = (Finset.univ.sum u) ^ 2 - Finset.univ.sum (fun i => (u i) ^ 2) := by
          simp [hsum_sq, hdiag]

end Section04
end Chap01
