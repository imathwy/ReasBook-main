/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section15_part19

section Chap03
section Section15

open scoped BigOperators
open scoped Pointwise
open scoped Topology

/-- The cone `P` is the closure of its `μ > 0` slice. -/
lemma P_eq_closure_P_inter_mu_pos {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0) :
    let h : ℝ → (Fin n → ℝ) → EReal :=
      fun t x =>
        if 0 < t then
          (t : EReal) * f ((t⁻¹) • x)
        else if t = 0 then
          recessionFunction f x
        else
          ⊤
    let P : Set ((ℝ × (Fin n → ℝ)) × ℝ) := {q | h q.1.1 q.1.2 ≤ (q.2 : EReal)}
    P = closure (P ∩ {q | 0 < q.2}) := by
  classical
  intro h P
  refine subset_antisymm ?_ ?_
  · intro q hq
    rcases q with ⟨⟨lam, x⟩, μ⟩
    by_cases hμpos : 0 < μ
    · exact subset_closure ⟨hq, hμpos⟩
    · have hμle : μ ≤ 0 := le_of_not_gt hμpos
      have hlamnonneg : 0 ≤ lam := by
        have hq' : ((lam, x), μ) ∈ P := hq
        simpa [h, P] using (mem_P_imp_lam_nonneg (f := f) (q := ((lam, x), μ)) hq')
      have hnonneg : (0 : EReal) ≤ h lam x := by
        simpa [h] using
          (h_nonneg_of_lam_nonneg (f := f) hf_nonneg hf0 (lam := lam) (x := x) hlamnonneg)
      have hle : h lam x ≤ (μ : EReal) := by simpa [P] using hq
      have hμnonneg' : (0 : EReal) ≤ (μ : EReal) := le_trans hnonneg hle
      have hμnonneg : 0 ≤ μ := (EReal.coe_le_coe_iff).1 hμnonneg'
      have hμzero : μ = 0 := le_antisymm hμle hμnonneg
      refine (mem_closure_iff_seq_limit).2 ?_
      refine ⟨fun n : ℕ => ((lam, x), (1 / (n + 1 : ℝ))), ?_, ?_⟩
      · intro n
        have hpos : 0 < (1 / (n + 1 : ℝ)) := by
          have : 0 < (n + 1 : ℝ) := by exact_mod_cast (Nat.succ_pos n)
          exact one_div_pos.mpr this
        have hle0 : h lam x ≤ (0 : EReal) := by
          simpa [hμzero] using hle
        have hle' : h lam x ≤ (1 / (n + 1 : ℝ) : EReal) := by
          have hnonneg' :
              (0 : EReal) ≤ (1 / (n + 1 : ℝ) : EReal) :=
            (EReal.coe_le_coe_iff).2 (le_of_lt hpos)
          exact le_trans hle0 hnonneg'
        have hmemP : ((lam, x), (1 / (n + 1 : ℝ))) ∈ P := by
          simpa [P] using hle'
        exact ⟨hmemP, hpos⟩
      · have hμtend :
            Filter.Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ))) Filter.atTop (𝓝 (0 : ℝ)) := by
          have h :=
            (tendsto_one_div_add_atTop_nhds_zero_nat : Filter.Tendsto
              (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (𝓝 (0 : ℝ)))
          simpa [one_div, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using h
        have hconst :
            Filter.Tendsto (fun n : ℕ => (lam, x)) Filter.atTop (𝓝 (lam, x)) := by
          exact tendsto_const_nhds
        have hprod :
            Filter.Tendsto (fun n : ℕ => ((lam, x), (1 / (n + 1 : ℝ))))
              Filter.atTop (𝓝 ((lam, x), (0 : ℝ))) := by
          have hprod' :
              Filter.Tendsto (fun n : ℕ => ((lam, x), (1 / (n + 1 : ℝ))))
                Filter.atTop (𝓝 (lam, x) ×ˢ 𝓝 (0 : ℝ)) :=
            hconst.prodMk hμtend
          simpa [nhds_prod_eq] using hprod'
        simpa [hμzero] using hprod
  ·
    have hclosed : IsClosed P := by
      simpa [h, P] using (isClosed_P (f := f) hf_nonneg hf_closed hf0)
    exact closure_minimal Set.inter_subset_left hclosed

/-- Any closed convex cone containing the obverse points contains `P`. -/
lemma P_subset_any_closed_convexCone_containing_obverse_points {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0) :
    let g : (Fin n → ℝ) → EReal := obverseConvex f
    let h : ℝ → (Fin n → ℝ) → EReal :=
      fun t x =>
        if 0 < t then
          (t : EReal) * f ((t⁻¹) • x)
        else if t = 0 then
          recessionFunction f x
        else
          ⊤
    let P : Set ((ℝ × (Fin n → ℝ)) × ℝ) := {q | h q.1.1 q.1.2 ≤ (q.2 : EReal)}
    ∀ K : ConvexCone ℝ ((ℝ × (Fin n → ℝ)) × ℝ),
      IsClosed (K : Set ((ℝ × (Fin n → ℝ)) × ℝ)) →
        (∀ (lam : ℝ) (x : Fin n → ℝ),
            g x ≤ (lam : EReal) →
              ((lam, x), (1 : ℝ)) ∈ (K : Set ((ℝ × (Fin n → ℝ)) × ℝ))) →
          P ⊆ (K : Set ((ℝ × (Fin n → ℝ)) × ℝ)) := by
  classical
  intro g h P K hKclosed hK
  have hsubset_pos : P ∩ {q | 0 < q.2} ⊆ (K : Set ((ℝ × (Fin n → ℝ)) × ℝ)) := by
    intro q hq
    rcases hq with ⟨hqP, hqμpos⟩
    rcases q with ⟨⟨lam, x⟩, μ⟩
    have hle : h lam x ≤ (μ : EReal) := by simpa [P] using hqP
    have hle1 : h (lam / μ) ((μ⁻¹) • x) ≤ (1 : EReal) := by
      simpa [h] using
        (h_div_mu_le_one_of_h_le_mu (f := f) hf_nonneg hf_closed hf0
          (lam := lam) (μ := μ) (x := x) hqμpos hle)
    have hmem' :
        ((μ⁻¹) • x, lam / μ) ∈
          epigraph (S := (Set.univ : Set (Fin n → ℝ))) g := by
      have hEq :
          {p : (Fin n → ℝ) × ℝ | h p.2 p.1 ≤ (1 : EReal)} =
            epigraph (S := (Set.univ : Set (Fin n → ℝ))) g := by
        simpa [g, h] using
          (sublevel_h_one_eq_epigraph_obverseConvex (f := f) hf_nonneg hf_closed hf0)
      have hmem : ((μ⁻¹) • x, lam / μ) ∈ {p : (Fin n → ℝ) × ℝ | h p.2 p.1 ≤ (1 : EReal)} := by
        simpa using hle1
      simpa [hEq] using hmem
    have hgle : g ((μ⁻¹) • x) ≤ (lam / μ : EReal) := by
      simpa [mem_epigraph_univ_iff] using hmem'
    have hq' :
        ((lam / μ, (μ⁻¹) • x), (1 : ℝ)) ∈
          (K : Set ((ℝ × (Fin n → ℝ)) × ℝ)) := hK (lam / μ) ((μ⁻¹) • x) hgle
    have hμne : μ ≠ 0 := ne_of_gt hqμpos
    have hscale :
        (μ : ℝ) • ((lam / μ, (μ⁻¹) • x), (1 : ℝ)) = ((lam, x), μ) := by
      apply Prod.ext
      · apply Prod.ext
        ·
          have h1 : (μ : ℝ) * (lam / μ) = lam := by
            field_simp [hμne]
          simpa [Prod.smul_mk, smul_eq_mul] using h1
        ·
          ext i
          simp [Prod.smul_mk, smul_eq_mul, smul_smul, hμne]
      · simp [Prod.smul_mk, smul_eq_mul]
    have hsmul : (μ : ℝ) • ((lam / μ, (μ⁻¹) • x), (1 : ℝ)) ∈
        (K : Set ((ℝ × (Fin n → ℝ)) × ℝ)) :=
      K.smul_mem hqμpos hq'
    simpa [hscale] using hsmul
  have hcl :
      closure (P ∩ {q | 0 < q.2}) ⊆ (K : Set ((ℝ × (Fin n → ℝ)) × ℝ)) :=
    closure_minimal hsubset_pos hKclosed
  have hPcl : P = closure (P ∩ {q | 0 < q.2}) := by
    simpa [h, P] using (P_eq_closure_P_inter_mu_pos (f := f) hf_nonneg hf_closed hf0)
  rw [hPcl]
  exact hcl

/-- Text 15.0.35: Let `P ⊆ ℝ^{n+2}` be the closed convex cone `P = epi h` from Text 15.0.34, where
`h` is built from `f` as in Text 15.0.33 and `g` is the obverse of `f`.

Assuming `f ≥ 0`, the set `P` is the closure of its intersection with the open half-space `μ > 0`.
Moreover, `P` is the smallest closed convex cone containing all points `(λ, x, 1)` such that
`λ ≥ g(x)`. Thus `f` and `g` determine the same closed convex cone in `ℝ^{n+2}`, with the roles of
`λ` and `μ` reversed when passing between the two descriptions. -/
lemma epigraph_h_min_closedConvexCone_containing_obverse_points {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_closed : ClosedConvexFunction f) (hf0 : f 0 = 0) :
    let g : (Fin n → ℝ) → EReal := obverseConvex f
    let h : ℝ → (Fin n → ℝ) → EReal :=
      fun t x =>
        if 0 < t then
          (t : EReal) * f ((t⁻¹) • x)
        else if t = 0 then
          recessionFunction f x
        else
          ⊤
    let P : Set ((ℝ × (Fin n → ℝ)) × ℝ) := {q | h q.1.1 q.1.2 ≤ (q.2 : EReal)}
    (P = closure (P ∩ {q | 0 < q.2})) ∧
      (∀ K : ConvexCone ℝ ((ℝ × (Fin n → ℝ)) × ℝ),
          IsClosed (K : Set ((ℝ × (Fin n → ℝ)) × ℝ)) →
            (∀ (lam : ℝ) (x : Fin n → ℝ),
                g x ≤ (lam : EReal) →
                  ((lam, x), (1 : ℝ)) ∈ (K : Set ((ℝ × (Fin n → ℝ)) × ℝ))) →
              P ⊆ (K : Set ((ℝ × (Fin n → ℝ)) × ℝ))) := by
  classical
  intro g h P
  refine ⟨?_, ?_⟩
  · simpa [h, P] using (P_eq_closure_P_inter_mu_pos (f := f) hf_nonneg hf_closed hf0)
  · intro K hKclosed hK
    simpa [g, h, P] using
      (P_subset_any_closed_convexCone_containing_obverse_points (f := f) hf_nonneg hf_closed hf0
        (K := K) hKclosed hK)

/- Theorem 15.4: Let `f` be a nonnegative convex function on `ℝⁿ` such that `f 0 = 0`.
Then its polar `fᵒ` is a nonnegative closed convex function with `fᵒ 0 = 0`, and the bipolar
satisfies `fᵒᵒ = cl f`.

In this development, the polar `fᵒ` is `polarConvex f` (Text 15.0.29) and `cl f` is
`convexFunctionClosure f`. -/
/-- The polar convex function is nonnegative. -/
lemma polarConvex_nonneg {n : ℕ} (f : (Fin n → ℝ) → EReal) (xStar : Fin n → ℝ) :
    (0 : EReal) ≤ polarConvex f xStar := by
  unfold polarConvex
  refine le_sInf ?_
  intro μ hμ
  exact hμ.1

/-- The polar convex function vanishes at the origin. -/
lemma polarConvex_zero {n : ℕ} (f : (Fin n → ℝ) → EReal) :
    polarConvex f (0 : Fin n → ℝ) = 0 := by
  have hle : polarConvex f (0 : Fin n → ℝ) ≤ 0 := by
    unfold polarConvex
    refine sInf_le ?_
    refine ⟨le_rfl, ?_⟩
    intro x
    simp
  have hge : (0 : EReal) ≤ polarConvex f (0 : Fin n → ℝ) :=
    polarConvex_nonneg f (0 : Fin n → ℝ)
  exact le_antisymm hle hge

/-- Vertical reflection in the last coordinate. -/
def vertReflect {n : ℕ} (p : (Fin n → ℝ) × ℝ) : (Fin n → ℝ) × ℝ :=
  (p.1, -p.2)

/-- The vertical reflection is an involution. -/
lemma vertReflect_involutive {n : ℕ} : Function.Involutive (vertReflect (n := n)) := by
  intro p
  cases p with
  | mk x μ =>
      simp [vertReflect]

/-- Product-space polar set using the dot-product-plus-scalar pairing. -/
def polarSetProd {n : ℕ} (C : Set ((Fin n → ℝ) × ℝ)) : Set ((Fin n → ℝ) × ℝ) :=
  {y | ∀ x ∈ C, (x.1 ⬝ᵥ y.1 : ℝ) + x.2 * y.2 ≤ 1}

/-- `polarSetProd` is closed and convex as an intersection of closed halfspaces. -/
lemma polarSetProd_isClosed_and_convex {n : ℕ} (C : Set ((Fin n → ℝ) × ℝ)) :
    IsClosed (polarSetProd (n := n) C) ∧ Convex ℝ (polarSetProd (n := n) C) := by
  classical
  have hclosed_half :
      ∀ x : (Fin n → ℝ) × ℝ,
        IsClosed {y : (Fin n → ℝ) × ℝ | (x.1 ⬝ᵥ y.1 : ℝ) + x.2 * y.2 ≤ 1} := by
    intro x
    have hcont1 :
        Continuous fun y : (Fin n → ℝ) × ℝ => (x.1 ⬝ᵥ y.1 : ℝ) := by
      simpa using (continuous_dotProduct_const (x := x.1)).comp continuous_fst
    have hcont2 : Continuous fun y : (Fin n → ℝ) × ℝ => x.2 * y.2 := by
      simpa using (continuous_const.mul continuous_snd)
    have hcont :
        Continuous fun y : (Fin n → ℝ) × ℝ =>
          (x.1 ⬝ᵥ y.1 : ℝ) + x.2 * y.2 := hcont1.add hcont2
    simpa [Set.preimage, Set.mem_Iic] using (isClosed_Iic.preimage hcont)
  have hconv_half :
      ∀ x : (Fin n → ℝ) × ℝ,
        Convex ℝ {y : (Fin n → ℝ) × ℝ | (x.1 ⬝ᵥ y.1 : ℝ) + x.2 * y.2 ≤ 1} := by
    intro x y1 hy1 y2 hy2 a b ha hb hab
    have hdot :
        (x.1 ⬝ᵥ (a • y1 + b • y2).1 : ℝ) =
          a * (x.1 ⬝ᵥ y1.1 : ℝ) + b * (x.1 ⬝ᵥ y2.1 : ℝ) := by
      simp [dotProduct_add, dotProduct_smul, smul_eq_mul]
    have hmul :
        x.2 * (a • y1 + b • y2).2 =
          a * (x.2 * y1.2) + b * (x.2 * y2.2) := by
      have hmul' :
          x.2 * (a * y1.2 + b * y2.2) =
            a * (x.2 * y1.2) + b * (x.2 * y2.2) := by
        ring
      calc
        x.2 * (a • y1 + b • y2).2 =
            x.2 * (a * y1.2 + b * y2.2) := by
              simp [smul_eq_mul]
        _ = a * (x.2 * y1.2) + b * (x.2 * y2.2) := hmul'
    have hsum :
        (x.1 ⬝ᵥ (a • y1 + b • y2).1 : ℝ) + x.2 * (a • y1 + b • y2).2 =
          a * ((x.1 ⬝ᵥ y1.1 : ℝ) + x.2 * y1.2) +
            b * ((x.1 ⬝ᵥ y2.1 : ℝ) + x.2 * y2.2) := by
      calc
        (x.1 ⬝ᵥ (a • y1 + b • y2).1 : ℝ) + x.2 * (a • y1 + b • y2).2
            =
            (a * (x.1 ⬝ᵥ y1.1 : ℝ) + b * (x.1 ⬝ᵥ y2.1 : ℝ)) +
              (a * (x.2 * y1.2) + b * (x.2 * y2.2)) := by
                rw [hdot, hmul]
        _ =
            a * ((x.1 ⬝ᵥ y1.1 : ℝ) + x.2 * y1.2) +
              b * ((x.1 ⬝ᵥ y2.1 : ℝ) + x.2 * y2.2) := by
                ring
    have hle1 :
        a * ((x.1 ⬝ᵥ y1.1 : ℝ) + x.2 * y1.2) ≤ a * 1 :=
      mul_le_mul_of_nonneg_left hy1 ha
    have hle2 :
        b * ((x.1 ⬝ᵥ y2.1 : ℝ) + x.2 * y2.2) ≤ b * 1 :=
      mul_le_mul_of_nonneg_left hy2 hb
    have hle :
        a * ((x.1 ⬝ᵥ y1.1 : ℝ) + x.2 * y1.2) +
            b * ((x.1 ⬝ᵥ y2.1 : ℝ) + x.2 * y2.2) ≤
          a * 1 + b * 1 :=
      add_le_add hle1 hle2
    have hsum1 : a + b = (1 : ℝ) := by
      simpa using hab
    have hle' :
        (x.1 ⬝ᵥ (a • y1 + b • y2).1 : ℝ) + x.2 * (a • y1 + b • y2).2 ≤ a + b := by
      simpa [mul_one, hsum.symm] using hle
    simpa [hsum1] using hle'
  have hclosed :
      IsClosed (polarSetProd (n := n) C) := by
    simp [polarSetProd, Set.setOf_forall]
    refine isClosed_iInter ?_
    intro i
    refine isClosed_iInter ?_
    intro i_1
    refine isClosed_iInter ?_
    intro hi
    exact hclosed_half (i, i_1)
  have hconv :
      Convex ℝ (polarSetProd (n := n) C) := by
    simp [polarSetProd, Set.setOf_forall]
    refine convex_iInter ?_
    intro i
    refine convex_iInter ?_
    intro i_1
    refine convex_iInter ?_
    intro hi
    exact hconv_half (i, i_1)
  exact ⟨hclosed, hconv⟩

/-- `polarSetProd` is unchanged by taking the closure of the set. -/
lemma polarSetProd_closure_eq {n : ℕ} (C : Set ((Fin n → ℝ) × ℝ)) :
    polarSetProd (n := n) (closure C) = polarSetProd (n := n) C := by
  classical
  ext y
  constructor
  · intro hy x hx
    exact hy x (subset_closure hx)
  · intro hy x hx
    let H : Set ((Fin n → ℝ) × ℝ) :=
      {x : (Fin n → ℝ) × ℝ | (x.1 ⬝ᵥ y.1 : ℝ) + x.2 * y.2 ≤ 1}
    have hsubset : C ⊆ H := by
      intro x hxC
      exact hy x hxC
    have hclosed : IsClosed H := by
      have hcont1 :
          Continuous fun x : (Fin n → ℝ) × ℝ => (x.1 ⬝ᵥ y.1 : ℝ) := by
        have hcont :
            Continuous fun x : (Fin n → ℝ) × ℝ => (y.1 ⬝ᵥ x.1 : ℝ) := by
          simpa using (continuous_dotProduct_const (x := y.1)).comp continuous_fst
        simpa [dotProduct_comm] using hcont
      have hcont2 : Continuous fun x : (Fin n → ℝ) × ℝ => x.2 * y.2 := by
        simpa using (continuous_snd.mul continuous_const)
      have hcont :
          Continuous fun x : (Fin n → ℝ) × ℝ =>
            (x.1 ⬝ᵥ y.1 : ℝ) + x.2 * y.2 := hcont1.add hcont2
      simpa [H, Set.preimage, Set.mem_Iic] using (isClosed_Iic.preimage hcont)
    have hcl : closure C ⊆ H := closure_minimal hsubset hclosed
    exact hcl hx

/-- `polarSetProd` commutes with vertical reflection preimages. -/
lemma polarSetProd_preimage_vertReflect {n : ℕ} (C : Set ((Fin n → ℝ) × ℝ)) :
    polarSetProd (n := n) ((vertReflect (n := n)) ⁻¹' C) =
      (vertReflect (n := n)) ⁻¹' (polarSetProd (n := n) C) := by
  classical
  ext y
  constructor
  · intro hy
    have hy' : vertReflect (n := n) y ∈ polarSetProd (n := n) C := by
      intro x hx
      have hx' : vertReflect (n := n) x ∈ (vertReflect (n := n)) ⁻¹' C := by
        simpa [Set.preimage, vertReflect] using hx
      have hineq := hy (vertReflect (n := n) x) hx'
      have hrewrite :
          (x.1 ⬝ᵥ y.1 : ℝ) + x.2 * (-y.2) =
            (x.1 ⬝ᵥ y.1 : ℝ) + (-x.2) * y.2 := by
        ring
      simpa [Set.preimage, vertReflect, hrewrite] using hineq
    exact hy'
  · intro hy x hx
    have hx' : vertReflect (n := n) x ∈ C := by
      simpa [Set.preimage, vertReflect] using hx
    have hineq := hy (vertReflect (n := n) x) hx'
    simpa [vertReflect, mul_comm, mul_left_comm, mul_assoc] using hineq

/-- A linear functional on the product splits into a dot product and a scalar part. -/
lemma linearMap_eq_dotProduct_add_mul_prod {n : ℕ}
    (φ : ((Fin n → ℝ) × ℝ) →ₗ[ℝ] ℝ) :
    ∀ p : (Fin n → ℝ) × ℝ,
      φ p = (p.1 ⬝ᵥ fun i => φ (Pi.single i 1, (0 : ℝ)) : ℝ) + p.2 * φ (0, 1) := by
  classical
  intro p
  let φ0 : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => φ (x, (0 : ℝ))
      map_add' := by
        intro x y
        simpa using (map_add φ (x, (0 : ℝ)) (y, (0 : ℝ)))
      map_smul' := by
        intro c x
        simpa [Prod.smul_mk, smul_eq_mul] using (map_smul φ c (x, (0 : ℝ))) }
  have hφx :
      φ (p.1, (0 : ℝ)) =
        (p.1 ⬝ᵥ fun i => φ (Pi.single i 1, (0 : ℝ)) : ℝ) := by
    simpa [φ0] using (linearMap_eq_dotProduct_piSingle (f := φ0) p.1)
  have hφμ :
      φ ((0 : Fin n → ℝ), p.2) = p.2 * φ ((0 : Fin n → ℝ), (1 : ℝ)) := by
    have hsmul := map_smul φ p.2 ((0 : Fin n → ℝ), (1 : ℝ))
    have hprod :
        (p.2 : ℝ) • ((0 : Fin n → ℝ), (1 : ℝ)) = ((0 : Fin n → ℝ), p.2) := by
      ext <;> simp [Prod.smul_mk, smul_eq_mul]
    simpa [hprod] using hsmul
  have hdecomp : p = (p.1, (0 : ℝ)) + ((0 : Fin n → ℝ), p.2) := by
    ext <;> simp
  calc
    φ p = φ ((p.1, (0 : ℝ)) + ((0 : Fin n → ℝ), p.2)) := by
      exact congrArg φ hdecomp
    _ = φ (p.1, (0 : ℝ)) + φ ((0 : Fin n → ℝ), p.2) := by
      simpa using (map_add φ (p.1, (0 : ℝ)) ((0 : Fin n → ℝ), p.2))
    _ = (p.1 ⬝ᵥ fun i => φ (Pi.single i 1, (0 : ℝ)) : ℝ) + p.2 * φ (0, 1) := by
      simp [hφx, hφμ]

/-- The dual bipolar set matches the `polarSetProd` bipolar. -/
lemma bipolar_dualSet_eq_polarSetProd_polarSetProd {n : ℕ}
    (C : Set ((Fin n → ℝ) × ℝ)) :
    {x : (Fin n → ℝ) × ℝ |
        ∀ φ ∈ polar (E := (Fin n → ℝ) × ℝ) C, φ x ≤ (1 : ℝ)} =
      polarSetProd (n := n) (polarSetProd (n := n) C) := by
  classical
  ext x
  constructor
  · intro hx y hy
    let φ : ((Fin n → ℝ) × ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun p => (p.1 ⬝ᵥ y.1 : ℝ) + p.2 * y.2
        map_add' := by
          intro p q
          simp [add_mul, add_left_comm, add_assoc]
        map_smul' := by
          intro a p
          simp [smul_eq_mul, mul_add, mul_left_comm, mul_comm] }
    have hφ : φ ∈ polar (E := (Fin n → ℝ) × ℝ) C := by
      refine (mem_polar_iff (E := (Fin n → ℝ) × ℝ) (C := C) (φ := φ)).2 ?_
      intro z hz
      have hineq := hy z hz
      simpa [φ] using hineq
    have hx' : φ x ≤ 1 := hx φ hφ
    simpa [φ, dotProduct_comm, mul_comm, mul_left_comm, mul_assoc] using hx'
  · intro hx φ hφ
    let y : (Fin n → ℝ) × ℝ :=
      (fun i => φ (Pi.single i 1, (0 : ℝ)), φ (0, 1))
    have hy : y ∈ polarSetProd (n := n) C := by
      intro z hz
      have hφz :
          φ z ≤ 1 :=
        (mem_polar_iff (E := (Fin n → ℝ) × ℝ) (C := C) (φ := φ)).1 hφ z hz
      have hrepr :
          φ z = (z.1 ⬝ᵥ y.1 : ℝ) + z.2 * y.2 := by
        simpa [y] using (linearMap_eq_dotProduct_add_mul_prod (n := n) φ z)
      simpa [hrepr] using hφz
    have hx' : (x.1 ⬝ᵥ y.1 : ℝ) + x.2 * y.2 ≤ 1 := by
      simpa [dotProduct_comm, mul_comm, mul_left_comm, mul_assoc] using hx y hy
    have hreprx :
        φ x = (x.1 ⬝ᵥ y.1 : ℝ) + x.2 * y.2 := by
      simpa [y] using (linearMap_eq_dotProduct_add_mul_prod (n := n) φ x)
    simpa [hreprx] using hx'


end Section15
end Chap03
