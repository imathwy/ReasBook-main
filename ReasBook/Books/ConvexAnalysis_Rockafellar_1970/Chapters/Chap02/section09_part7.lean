/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part6

noncomputable section
open scoped Pointwise
open scoped BigOperators
open scoped Topology
open scoped RealInnerProductSpace

section Chap02
section Section09

/-- The recession cone of the block-sum epigraph is the epigraph of the block-sum recession. -/
lemma recessionCone_epigraph_sum_block {n m : Nat}
    {f f0_plus : Fin m → (Fin n → Real) → EReal}
    (hnotbot : ∀ i : Fin m, ∀ x, f i x ≠ (⊥ : EReal))
    (hnotbot0 : ∀ i : Fin m, ∀ x, f0_plus i x ≠ (⊥ : EReal))
    (hconv_i :
      ∀ i : Fin m,
        Convex Real (epigraph (Set.univ : Set (Fin n → Real)) (f i)))
    (hrec_i :
      ∀ i : Fin m,
        Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) (f i)) =
          epigraph (Set.univ : Set (Fin n → Real)) (f0_plus i)) :
    let e := blockEquivFun (n := n) (m := m)
    let h : (Fin (m * n) → Real) → EReal :=
      fun x => Finset.univ.sum (fun i => f i ((e x) i))
    let h0_plus : (Fin (m * n) → Real) → EReal :=
      fun x => Finset.univ.sum (fun i => f0_plus i ((e x) i))
    Set.recessionCone (epigraph (Set.univ : Set (Fin (m * n) → Real)) h) =
      epigraph (Set.univ : Set (Fin (m * n) → Real)) h0_plus := by
  classical
  intro e h h0_plus
  let g : (Fin m → (Fin n → Real)) → EReal :=
    fun x => Finset.univ.sum (fun i => f i (x i))
  let g0_plus : (Fin m → (Fin n → Real)) → EReal :=
    fun x => Finset.univ.sum (fun i => f0_plus i (x i))
  let eprod : ((Fin (m * n) → Real) × Real) ≃ₗ[Real]
      ((Fin m → (Fin n → Real)) × Real) :=
    LinearEquiv.prodCongr (e : (Fin (m * n) → Real) ≃ₗ[Real] (Fin m → (Fin n → Real)))
      (LinearEquiv.refl (R := Real) (M := Real))
  have hEpi :
      eprod '' epigraph (Set.univ : Set (Fin (m * n) → Real)) h =
        {p : (Fin m → (Fin n → Real)) × Real | g p.1 ≤ (p.2 : EReal)} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hle : h q.1 ≤ (q.2 : EReal) := (mem_epigraph_univ_iff (f := h)).1 hq
      have hle' : g (e q.1) ≤ (q.2 : EReal) := by
        simpa [g, h] using hle
      simpa [eprod] using hle'
    · intro hp
      refine ⟨eprod.symm p, ?_, ?_⟩
      · have hle : h (e.symm p.1) ≤ (p.2 : EReal) := by
          simpa [g, h] using hp
        exact (mem_epigraph_univ_iff (f := h)).2 hle
      · simp [eprod]
  have hEpi0 :
      eprod '' epigraph (Set.univ : Set (Fin (m * n) → Real)) h0_plus =
        {p : (Fin m → (Fin n → Real)) × Real | g0_plus p.1 ≤ (p.2 : EReal)} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hle : h0_plus q.1 ≤ (q.2 : EReal) :=
        (mem_epigraph_univ_iff (f := h0_plus)).1 hq
      have hle' : g0_plus (e q.1) ≤ (q.2 : EReal) := by
        simpa [g0_plus, h0_plus] using hle
      simpa [eprod] using hle'
    · intro hp
      refine ⟨eprod.symm p, ?_, ?_⟩
      · have hle : h0_plus (e.symm p.1) ≤ (p.2 : EReal) := by
          simpa [g0_plus, h0_plus] using hp
        exact (mem_epigraph_univ_iff (f := h0_plus)).2 hle
      · simp [eprod]
  have hrec_prod :
      Set.recessionCone
          (eprod '' epigraph (Set.univ : Set (Fin (m * n) → Real)) h) =
        eprod '' epigraph (Set.univ : Set (Fin (m * n) → Real)) h0_plus := by
    calc
      Set.recessionCone
          (eprod '' epigraph (Set.univ : Set (Fin (m * n) → Real)) h) =
        Set.recessionCone
          {p : (Fin m → (Fin n → Real)) × Real | g p.1 ≤ (p.2 : EReal)} := by
        simp [hEpi]
      _ =
        {p : (Fin m → (Fin n → Real)) × Real | g0_plus p.1 ≤ (p.2 : EReal)} := by
        simpa [g, g0_plus] using
          (recessionCone_sum_epigraph_prod (n := n) (m := m) (f := f) (f0_plus := f0_plus)
            hnotbot hnotbot0 hconv_i hrec_i)
      _ =
        eprod '' epigraph (Set.univ : Set (Fin (m * n) → Real)) h0_plus := by
        simp [hEpi0]
  have hrec_symm :=
    (recessionCone_image_linearEquiv (e := eprod.symm)
      (C := eprod '' epigraph (Set.univ : Set (Fin (m * n) → Real)) h))
  have hpre :
      eprod.symm '' (eprod '' epigraph (Set.univ : Set (Fin (m * n) → Real)) h) =
        epigraph (Set.univ : Set (Fin (m * n) → Real)) h := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with ⟨r, hr, rfl⟩
      have hr' : eprod.symm (e r.1, r.2) = r := by
        simpa [eprod] using (eprod.symm_apply_apply r)
      simpa [hr'] using hr
    · intro hp
      refine ⟨eprod p, ?_, by
        simpa [eprod] using (eprod.symm_apply_apply p)⟩
      exact ⟨p, hp, rfl⟩
  have hrec_symm' :
      Set.recessionCone (epigraph (Set.univ : Set (Fin (m * n) → Real)) h) =
        eprod.symm '' Set.recessionCone
          (eprod '' epigraph (Set.univ : Set (Fin (m * n) → Real)) h) := by
    simpa [hpre] using hrec_symm
  calc
    Set.recessionCone (epigraph (Set.univ : Set (Fin (m * n) → Real)) h) =
        eprod.symm '' Set.recessionCone
          (eprod '' epigraph (Set.univ : Set (Fin (m * n) → Real)) h) := hrec_symm'
    _ = eprod.symm '' (eprod '' epigraph (Set.univ : Set (Fin (m * n) → Real)) h0_plus) := by
      simp [hrec_prod]
    _ = epigraph (Set.univ : Set (Fin (m * n) → Real)) h0_plus := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        rcases hq with ⟨r, hr, rfl⟩
        have hr' : eprod.symm (e r.1, r.2) = r := by
          simpa [eprod] using (eprod.symm_apply_apply r)
        simpa [hr'] using hr
      · intro hp
        refine ⟨eprod p, ?_, by
          simpa [eprod] using (eprod.symm_apply_apply p)⟩
        exact ⟨p, hp, rfl⟩

/-- The block-sum `h0_plus` is positively homogeneous and proper under componentwise assumptions. -/
lemma h0_plus_sum_posHom_proper {n m : Nat}
    {f0_plus : Fin m → (Fin n → Real) → EReal}
    (hpos_i : ∀ i : Fin m, PositivelyHomogeneous (f0_plus i))
    (hproper_i :
      ∀ i : Fin m,
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (f0_plus i)) :
    let e := blockEquivFun (n := n) (m := m)
    let h0_plus : (Fin (m * n) → Real) → EReal :=
      fun x => Finset.univ.sum (fun i => f0_plus i ((e x) i))
    PositivelyHomogeneous h0_plus ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin (m * n) → Real)) h0_plus := by
  classical
  intro e h0_plus
  have hpos : PositivelyHomogeneous h0_plus := by
    intro x t ht
    have he : e (t • x) = t • e x := by
      exact
        (map_smul
          (f := (e : (Fin (m * n) → Real) →ₗ[Real] (Fin m → (Fin n → Real)))) t x)
    have hmul_sum :
        Finset.univ.sum (fun i => (t : EReal) * f0_plus i ((e x) i)) =
          (t : EReal) * Finset.univ.sum (fun i => f0_plus i ((e x) i)) := by
      classical
      let f : Fin m → EReal := fun i => f0_plus i ((e x) i)
      have hnotbot_f : ∀ i, f i ≠ (⊥ : EReal) := by
        intro i
        simpa [f] using (hproper_i i).2.2 ((e x) i) (by simp)
      have hsum :
          ∀ s : Finset (Fin m),
            s.sum (fun i => (t : EReal) * f i) = (t : EReal) * s.sum f := by
        intro s
        refine Finset.induction_on s ?_ ?_
        · simp
        · intro a s ha hs
          have hnotbot_a : f a ≠ (⊥ : EReal) := hnotbot_f a
          have hsum_notbot : s.sum f ≠ (⊥ : EReal) := by
            refine sum_ne_bot_of_ne_bot (s := s) (f := f) ?_
            intro i hi
            exact hnotbot_f i
          have hnotbot_a' : ((t : EReal) * f a) ≠ (⊥ : EReal) :=
            ereal_mul_ne_bot_of_pos (r := t) ht hnotbot_a
          have hnotbot_s' : ((t : EReal) * s.sum f) ≠ (⊥ : EReal) :=
            ereal_mul_ne_bot_of_pos (r := t) ht hsum_notbot
          have hforb :
              ¬ ERealForbiddenSum ((t : EReal) * f a) ((t : EReal) * s.sum f) := by
            intro hforb
            rcases hforb with hforb | hforb
            · exact hnotbot_s' hforb.2
            · exact hnotbot_a' hforb.1
          have hdistrib :
              (t : EReal) * (f a + s.sum f) =
                (t : EReal) * f a + (t : EReal) * s.sum f :=
            ereal_mul_add_of_no_forbidden (α := (t : EReal)) (x1 := f a) (x2 := s.sum f) hforb
          simp [Finset.sum_insert, ha, hs, hdistrib]
      simpa [f] using hsum Finset.univ
    calc
      h0_plus (t • x) =
          Finset.univ.sum (fun i => f0_plus i ((e (t • x)) i)) := by
        simp [h0_plus]
      _ = Finset.univ.sum (fun i => f0_plus i (t • (e x) i)) := by
        simp [he]
      _ = Finset.univ.sum (fun i => (t : EReal) * f0_plus i ((e x) i)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa using (hpos_i i ((e x) i) t ht)
      _ = (t : EReal) * Finset.univ.sum (fun i => f0_plus i ((e x) i)) := by
        simpa using hmul_sum
      _ = (t : EReal) * h0_plus x := by
        simp [h0_plus]
  have hgi_proper :
      ∀ i : Fin m,
        ProperConvexFunctionOn (Set.univ : Set (Fin (m * n) → Real))
          (fun x => f0_plus i ((e x) i)) := by
    intro i
    let A_i :
        (Fin (m * n) → Real) →ₗ[Real] (Fin n → Real) :=
      (LinearMap.proj i).comp
        (e : (Fin (m * n) → Real) ≃ₗ[Real] (Fin m → (Fin n → Real))).toLinearMap
    have hA_i : Function.Surjective A_i := by
      intro y
      refine ⟨e.symm (fun j => if j = i then y else 0), ?_⟩
      simp [A_i, LinearMap.comp_apply, LinearMap.proj_apply]
    have hA_i' :
        ProperConvexFunctionOn (Set.univ : Set (Fin (m * n) → Real))
          (fun x => f0_plus i (A_i x)) :=
      properConvexFunctionOn_precomp_linearMap_surjective (A := A_i) (hA := hA_i)
        (f := f0_plus i) (hproper_i i)
    simpa [A_i, LinearMap.comp_apply, LinearMap.proj_apply] using hA_i'
  have hconv_on :
      ConvexFunctionOn (Set.univ : Set (Fin (m * n) → Real)) h0_plus := by
    have hconv :=
      convexFunctionOn_linearCombination_of_proper (n := m * n) (m := m)
        (f := fun i => fun x => f0_plus i ((e x) i)) (lam := fun _ => (1 : Real))
        (hlam := by intro i; exact zero_le_one) (hf := hgi_proper)
    simpa [h0_plus, one_mul] using hconv
  have hnotbot_term :
      ∀ i : Fin m, ∀ x, f0_plus i ((e x) i) ≠ (⊥ : EReal) := by
    intro i x
    exact (hproper_i i).2.2 _ (by simp)
  have hnotbot_sum' :
      ∀ s : Finset (Fin m), ∀ x,
        s.sum (fun i => f0_plus i ((e x) i)) ≠ (⊥ : EReal) := by
    intro s x
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha hs
      have hterm : f0_plus a ((e x) a) ≠ (⊥ : EReal) := hnotbot_term a x
      have hsum : s.sum (fun i => f0_plus i ((e x) i)) ≠ (⊥ : EReal) := hs
      simpa [Finset.sum_insert, ha] using add_ne_bot_of_notbot hterm hsum
  have hnotbot :
      ∀ x ∈ (Set.univ : Set (Fin (m * n) → Real)), h0_plus x ≠ (⊥ : EReal) := by
    intro x hx
    simpa [h0_plus] using hnotbot_sum' (Finset.univ : Finset (Fin m)) x
  have hdom_ne :
      ∀ i : Fin m,
        Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → Real)) (f0_plus i)) := by
    intro i
    have h :=
      (properConvexFunctionOn_iff_effectiveDomain_nonempty_finite
        (S := (Set.univ : Set (Fin n → Real))) (f := f0_plus i)).1 (hproper_i i)
    exact h.2.1
  classical
  choose x0 hx0 using hdom_ne
  have hnot_top_term : ∀ i : Fin m, f0_plus i (x0 i) ≠ (⊤ : EReal) := by
    intro i
    exact mem_effectiveDomain_imp_ne_top
      (S := (Set.univ : Set (Fin n → Real))) (f := f0_plus i) (x := x0 i) (hx0 i)
  have hnot_top_sum' :
      ∀ s : Finset (Fin m), s.sum (fun i => f0_plus i (x0 i)) ≠ (⊤ : EReal) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha hs
      have hterm : f0_plus a (x0 a) ≠ (⊤ : EReal) := hnot_top_term a
      have hsum : s.sum (fun i => f0_plus i (x0 i)) ≠ (⊤ : EReal) := hs
      simpa [Finset.sum_insert, ha] using EReal.add_ne_top hterm hsum
  have hnot_top : h0_plus (e.symm x0) ≠ (⊤ : EReal) := by
    simpa [h0_plus] using hnot_top_sum' (Finset.univ : Finset (Fin m))
  have hne_epi :
      Set.Nonempty (epigraph (Set.univ : Set (Fin (m * n) → Real)) h0_plus) := by
    refine ⟨(e.symm x0, (h0_plus (e.symm x0)).toReal), ?_⟩
    have hle :
        h0_plus (e.symm x0) ≤ ((h0_plus (e.symm x0)).toReal : EReal) :=
      EReal.le_coe_toReal hnot_top
    exact (mem_epigraph_univ_iff (f := h0_plus)).2 hle
  have hproper0 :
      ProperConvexFunctionOn (Set.univ : Set (Fin (m * n) → Real)) h0_plus := by
    exact ⟨hconv_on, hne_epi, hnotbot⟩
  exact ⟨hpos, hproper0⟩

/-- Attainment in the `⊤` case for infimal convolution families when `m > 0`. -/
lemma attainment_top_case_infimalConvolutionFamily {n m : Nat}
    (hm : 0 < m) {f : Fin m → (Fin n → Real) → EReal} :
    let fInf : (Fin n → Real) → EReal := infimalConvolutionFamily f
    ∀ x : Fin n → Real, fInf x = (⊤ : EReal) →
      ∃ x' : Fin m → (Fin n → Real),
        Finset.univ.sum (fun i => x' i) = x ∧
          fInf x = Finset.univ.sum (fun i => f i (x' i)) := by
  classical
  intro fInf x htop
  let i0 : Fin m := ⟨0, hm⟩
  let x' : Fin m → (Fin n → Real) := fun i => if i = i0 then x else 0
  have hsum' : Finset.univ.sum (fun i => x' i) = x' i0 := by
    refine Finset.sum_eq_single i0 ?_ ?_
    · intro i hi hne
      simp [x', hne]
    · simp [x']
  have hsum : Finset.univ.sum (fun i => x' i) = x := by
    have hx : x' i0 = x := by
      simp [x', i0]
    calc
      Finset.univ.sum (fun i => x' i) = x' i0 := hsum'
      _ = x := by simp [hx]
  have hmem :
      Finset.univ.sum (fun i => f i (x' i)) ∈
        { z : EReal |
          ∃ x'' : Fin m → (Fin n → Real),
            Finset.univ.sum (fun i => x'' i) = x ∧
              z = Finset.univ.sum (fun i => f i (x'' i)) } := by
    exact ⟨x', hsum, rfl⟩
  have hle : fInf x ≤ Finset.univ.sum (fun i => f i (x' i)) := by
    simpa [fInf, infimalConvolutionFamily] using (sInf_le hmem)
  have htop_le :
      (⊤ : EReal) ≤ Finset.univ.sum (fun i => f i (x' i)) := by
    simpa [htop] using hle
  have hsum_top : Finset.univ.sum (fun i => f i (x' i)) = (⊤ : EReal) :=
    (top_le_iff.mp htop_le)
  refine ⟨x', hsum, ?_⟩
  simp [htop, hsum_top]

/-- Corollary 9.2.1. Let `f₁, …, fₘ` be closed proper convex functions on `ℝ^n`. Assume that
`z₁ + … + zₘ ≠ 0` for every choice of vectors `z₁, …, zₘ` such that
`(f₁ 0+)(z₁) + … + (fₘ 0+)(zₘ) ≤ 0` and `(f₁ 0+)(-z₁) + … + (fₘ 0+)(-zₘ) > 0`. Then the
infimal convolute `f₁ □ … □ fₘ` is a closed proper convex function on `ℝ^n`, and the infimum
in the definition of `(f₁ □ … □ fₘ)(x)` is attained for each `x`. Moreover,
`(f₁ □ … □ fₘ)0+ = f₁ 0+ □ … □ fₘ 0+`. -/
theorem infimalConvolutionFamily_closed_proper_convex_recession
    {n m : Nat}
    {f f0_plus : Fin m → (Fin n → Real) → EReal}
    (hclosed : ∀ i : Fin m, ClosedConvexFunction (f i))
    (hproper : ∀ i : Fin m, ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (f i))
    (hrec_i :
      ∀ i : Fin m,
        Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) (f i)) =
          epigraph (Set.univ : Set (Fin n → Real)) (f0_plus i))
    (hpos_i : ∀ i : Fin m, PositivelyHomogeneous (f0_plus i))
    (hproper0_i :
      ∀ i : Fin m,
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (f0_plus i))
    (hzero :
      ∀ z : Fin m → (Fin n → Real),
        (Finset.univ.sum (fun i => f0_plus i (z i)) ≤ (0 : EReal)) →
        (Finset.univ.sum (fun i => f0_plus i (-(z i))) > (0 : EReal)) →
        (Finset.univ.sum (fun i => z i) ≠ (0 : Fin n → Real)))
    (hm : 0 < m) :
    let fInf : (Fin n → Real) → EReal := infimalConvolutionFamily f
    let fInf0_plus : (Fin n → Real) → EReal := infimalConvolutionFamily f0_plus
    ClosedConvexFunction fInf ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) fInf ∧
      (∀ x : Fin n → Real,
        ∃ x' : Fin m → (Fin n → Real),
          Finset.univ.sum (fun i => x' i) = x ∧
            fInf x = Finset.univ.sum (fun i => f i (x' i))) ∧
  fInf0_plus = infimalConvolutionFamily f0_plus := by
  classical
  let fInf : (Fin n → Real) → EReal := infimalConvolutionFamily f
  let fInf0_plus : (Fin n → Real) → EReal := infimalConvolutionFamily f0_plus
  let e := blockEquivFun (n := n) (m := m)
  let A := (sumLinearMapFun (n := n) (m := m)).comp e.toLinearMap
  let h : (Fin (m * n) → Real) → EReal :=
    fun x => Finset.univ.sum (fun i => f i ((e x) i))
  let h0_plus : (Fin (m * n) → Real) → EReal :=
    fun x => Finset.univ.sum (fun i => f0_plus i ((e x) i))
  let Ah : (Fin n → Real) → EReal :=
    fun y => sInf { z : EReal | ∃ x : Fin (m * n) → Real, A x = y ∧ z = h x }
  let Ah0_plus : (Fin n → Real) → EReal :=
    fun y => sInf { z : EReal | ∃ x : Fin (m * n) → Real, A x = y ∧ z = h0_plus x }
  have hgi_proper :
      ∀ i : Fin m,
        ProperConvexFunctionOn (Set.univ : Set (Fin (m * n) → Real))
          (fun x => f i ((e x) i)) := by
    intro i
    let A_i :
        (Fin (m * n) → Real) →ₗ[Real] (Fin n → Real) :=
      (LinearMap.proj i).comp
        (e : (Fin (m * n) → Real) ≃ₗ[Real] (Fin m → (Fin n → Real))).toLinearMap
    have hA_i : Function.Surjective A_i := by
      intro y
      refine ⟨e.symm (fun j => if j = i then y else 0), ?_⟩
      simp [A_i, LinearMap.comp_apply, LinearMap.proj_apply]
    have hA_i' :
        ProperConvexFunctionOn (Set.univ : Set (Fin (m * n) → Real))
          (fun x => f i (A_i x)) :=
      properConvexFunctionOn_precomp_linearMap_surjective (A := A_i) (hA := hA_i)
        (f := f i) (hproper i)
    simpa [A_i, LinearMap.comp_apply, LinearMap.proj_apply] using hA_i'
  have hconv_on :
      ConvexFunctionOn (Set.univ : Set (Fin (m * n) → Real)) h := by
    classical
    have hconv :=
      convexFunctionOn_linearCombination_of_proper (n := m * n) (m := m)
        (f := fun i => fun x => f i ((e x) i)) (lam := fun _ => (1 : Real))
        (hlam := by intro i; exact zero_le_one) (hf := hgi_proper)
    simpa [h, one_mul] using hconv
  have hconv : ConvexFunction h := by
    simpa [ConvexFunction] using hconv_on
  have hls_term :
      ∀ i : Fin m, LowerSemicontinuous (fun x => f i ((e x) i)) := by
    intro i
    have hls_f : LowerSemicontinuous (f i) := (hclosed i).2
    have hcont_e :
        Continuous (e :
          (Fin (m * n) → Real) → (Fin m → (Fin n → Real))) :=
      (e.toContinuousLinearEquiv.continuous)
    have hcont_i :
        Continuous (fun x : Fin (m * n) → Real => (e x) i) :=
      (continuous_apply i).comp hcont_e
    exact hls_f.comp_continuous hcont_i
  have hnotbot_term :
      ∀ i : Fin m, ∀ x, f i ((e x) i) ≠ (⊥ : EReal) := by
    intro i x
    exact (hproper i).2.2 _ (by simp)
  have hnotbot_sum' :
      ∀ s : Finset (Fin m), ∀ x,
        s.sum (fun i => f i ((e x) i)) ≠ (⊥ : EReal) := by
    intro s x
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha hs
      have hterm : f a ((e x) a) ≠ (⊥ : EReal) := hnotbot_term a x
      have hsum : s.sum (fun i => f i ((e x) i)) ≠ (⊥ : EReal) := hs
      simpa [Finset.sum_insert, ha] using add_ne_bot_of_notbot hterm hsum
  have hls : LowerSemicontinuous h := by
    classical
    have hls' :
        LowerSemicontinuous
          (fun x => (Finset.univ.sum (fun i => f i ((e x) i)))) := by
      refine Finset.induction_on (s := (Finset.univ : Finset (Fin m))) ?_ ?_
      · simpa using
          (lowerSemicontinuous_const :
            LowerSemicontinuous (fun _ : Fin (m * n) → Real => (0 : EReal)))
      · intro a s ha hs
        have hls_a : LowerSemicontinuous (fun x => f a ((e x) a)) := hls_term a
        have hcont :
            ∀ x,
              ContinuousAt (fun p : EReal × EReal => p.1 + p.2)
                (f a ((e x) a), s.sum (fun i => f i ((e x) i))) := by
          intro x
          have hnotbot_a : f a ((e x) a) ≠ (⊥ : EReal) := hnotbot_term a x
          have hnotbot_s :
              s.sum (fun i => f i ((e x) i)) ≠ (⊥ : EReal) := hnotbot_sum' s x
          exact EReal.continuousAt_add (h := Or.inr hnotbot_s) (h' := Or.inl hnotbot_a)
        have hls_add :
            LowerSemicontinuous
              (fun x => f a ((e x) a) + s.sum (fun i => f i ((e x) i))) :=
          LowerSemicontinuous.add' hls_a hs hcont
        simpa [Finset.sum_insert, ha] using hls_add
    simpa [h] using hls'
  have hclosed_block : ClosedConvexFunction h := by
    exact ⟨hconv, hls⟩
  have hnotbot :
      ∀ x ∈ (Set.univ : Set (Fin (m * n) → Real)), h x ≠ (⊥ : EReal) := by
    intro x hx
    simpa [h] using hnotbot_sum' (Finset.univ : Finset (Fin m)) x
  have hdom_ne :
      ∀ i : Fin m,
        Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → Real)) (f i)) := by
    intro i
    have h :=
      (properConvexFunctionOn_iff_effectiveDomain_nonempty_finite
        (S := (Set.univ : Set (Fin n → Real))) (f := f i)).1 (hproper i)
    exact h.2.1
  classical
  choose x0 hx0 using hdom_ne
  have hnot_top_term : ∀ i : Fin m, f i (x0 i) ≠ (⊤ : EReal) := by
    intro i
    exact mem_effectiveDomain_imp_ne_top
      (S := (Set.univ : Set (Fin n → Real))) (f := f i) (x := x0 i) (hx0 i)
  have hnot_top_sum' :
      ∀ s : Finset (Fin m), s.sum (fun i => f i (x0 i)) ≠ (⊤ : EReal) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha hs
      have hterm : f a (x0 a) ≠ (⊤ : EReal) := hnot_top_term a
      have hsum : s.sum (fun i => f i (x0 i)) ≠ (⊤ : EReal) := hs
      simpa [Finset.sum_insert, ha] using EReal.add_ne_top hterm hsum
  have hnot_top : h (e.symm x0) ≠ (⊤ : EReal) := by
    simpa [h] using hnot_top_sum' (Finset.univ : Finset (Fin m))
  have hne_epi :
      Set.Nonempty (epigraph (Set.univ : Set (Fin (m * n) → Real)) h) := by
    refine ⟨(e.symm x0, (h (e.symm x0)).toReal), ?_⟩
    have hle :
        h (e.symm x0) ≤ ((h (e.symm x0)).toReal : EReal) :=
      EReal.le_coe_toReal hnot_top
    exact (mem_epigraph_univ_iff (f := h)).2 hle
  have hproper_block :
      ProperConvexFunctionOn (Set.univ : Set (Fin (m * n) → Real)) h := by
    exact ⟨hconv_on, hne_epi, hnotbot⟩
  have hnotbot_f : ∀ i : Fin m, ∀ x, f i x ≠ (⊥ : EReal) := by
    intro i x
    exact (hproper i).2.2 _ (by simp)
  have hconv_i :
      ∀ i : Fin m,
        Convex Real (epigraph (Set.univ : Set (Fin n → Real)) (f i)) := by
    intro i
    exact convex_epigraph_of_convexFunctionOn (hf := (hproper i).1)
  have hnotbot0 : ∀ i : Fin m, ∀ x, f0_plus i x ≠ (⊥ : EReal) := by
    intro i x
    exact (hproper0_i i).2.2 _ (by simp)
  have hrec :
      Set.recessionCone (epigraph (Set.univ : Set (Fin (m * n) → Real)) h) =
        epigraph (Set.univ : Set (Fin (m * n) → Real)) h0_plus := by
    simpa [e, h, h0_plus] using
      (recessionCone_epigraph_sum_block (n := n) (m := m) (f := f) (f0_plus := f0_plus)
        hnotbot_f hnotbot0 hconv_i hrec_i)
  have hpos : PositivelyHomogeneous h0_plus := by
    have hpos' :
        PositivelyHomogeneous h0_plus ∧
          ProperConvexFunctionOn (Set.univ : Set (Fin (m * n) → Real)) h0_plus := by
      simpa [e, h0_plus] using
        (h0_plus_sum_posHom_proper (n := n) (m := m) (f0_plus := f0_plus) hpos_i hproper0_i)
    exact hpos'.1
  have hproper0 :
      ProperConvexFunctionOn (Set.univ : Set (Fin (m * n) → Real)) h0_plus := by
    have hpos' :
        PositivelyHomogeneous h0_plus ∧
          ProperConvexFunctionOn (Set.univ : Set (Fin (m * n) → Real)) h0_plus := by
      simpa [e, h0_plus] using
        (h0_plus_sum_posHom_proper (n := n) (m := m) (f0_plus := f0_plus) hpos_i hproper0_i)
    exact hpos'.2
  have hA :
      ∀ z : Fin (m * n) → Real,
        h0_plus z ≤ (0 : EReal) → h0_plus (-z) > (0 : EReal) → A z ≠ 0 := by
    simpa [e, A, h0_plus] using
      (hA_from_hzero (n := n) (m := m) (f0_plus := f0_plus) hzero)
  have hmain :=
    (linearMap_infimum_closed_proper_convex_recession
      (h := h) (h0_plus := h0_plus) (hclosed := hclosed_block) (hproper := hproper_block)
      (hrec := hrec) (hpos := hpos) (hproper0 := hproper0) (A := A) (hA := hA))
  have hmain' :
      ClosedConvexFunction Ah ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) Ah ∧
        Ah0_plus =
          (fun y =>
            sInf { z : EReal | ∃ x : Fin (m * n) → Real, A x = y ∧ z = h0_plus x }) ∧
        (∀ y : Fin n → Real, Ah y ≠ (⊤ : EReal) →
          ∃ x : Fin (m * n) → Real, A x = y ∧ Ah y = h x) := by
    simpa [Ah, Ah0_plus] using hmain
  have hAh_eq : Ah = infimalConvolutionFamily f := by
    simpa [e, A, h, Ah] using
      (infimalConvolutionFamily_eq_Ah (n := n) (m := m) (f := f))
  have hAh0_eq : Ah0_plus = infimalConvolutionFamily f0_plus := by
    simpa [e, A, h0_plus, Ah0_plus] using
      (infimalConvolutionFamily_eq_Ah (n := n) (m := m) (f := f0_plus))
  have hclosedInf : ClosedConvexFunction fInf := by
    simpa [fInf, hAh_eq] using hmain'.1
  have hproperInf :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) fInf := by
    simpa [fInf, hAh_eq] using hmain'.2.1
  have hAttain :
      ∀ x : Fin n → Real,
        ∃ x' : Fin m → (Fin n → Real),
          Finset.univ.sum (fun i => x' i) = x ∧
            fInf x = Finset.univ.sum (fun i => f i (x' i)) := by
    intro x
    by_cases htop : fInf x = (⊤ : EReal)
    · -- TODO: handle the `⊤` case by exhibiting a trivial attainer.
      simpa [fInf] using
        (attainment_top_case_infimalConvolutionFamily (n := n) (m := m) (f := f) hm x htop)
    · have hne : Ah x ≠ (⊤ : EReal) := by
        simpa [fInf, hAh_eq] using htop
      rcases (hmain'.2.2.2 x hne) with ⟨x0, hx0A, hx0Eq⟩
      refine ⟨e x0, ?_, ?_⟩
      · simpa [A, sumLinearMapFun] using hx0A
      · have hx0Eq' : fInf x = h x0 := by
          simpa [fInf, hAh_eq] using hx0Eq
        simpa [h] using hx0Eq'
  refine ⟨hclosedInf, hproperInf, hAttain, ?_⟩
  simp

end Section09
end Chap02
