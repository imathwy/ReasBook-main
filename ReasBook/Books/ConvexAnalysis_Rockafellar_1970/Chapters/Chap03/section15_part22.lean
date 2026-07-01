/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part21
section Chap03
section Section15

open scoped BigOperators
open scoped Pointwise


/-- Epigraph points of the polar map to the product polar via vertical reflection. -/
lemma epigraph_polarConvex_subset_vertReflect_preimage_polarSetProd_epigraph {n : ℕ}
    {f : (Fin n → ℝ) → EReal} (hf_nonneg : ∀ x, 0 ≤ f x) :
    epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarConvex f) ⊆
      (vertReflect (n := n)) ⁻¹'
        polarSetProd (n := n) (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) := by
  intro p hp
  rcases p with ⟨xStar, μ⟩
  intro x hx
  have hμ :
      polarConvex f xStar ≤ (μ : EReal) :=
    (mem_epigraph_univ_iff (f := polarConvex f) (x := xStar) (μ := μ)).1 hp
  have hx_le : f x.1 ≤ (x.2 : EReal) :=
    (mem_epigraph_univ_iff (f := f) (x := x.1) (μ := x.2)).1 hx
  have hx_not_top : f x.1 ≠ ⊤ := by
    intro htop
    have htop_le : (⊤ : EReal) ≤ (x.2 : EReal) := by
      have hx_le' := hx_le
      simp [htop] at hx_le'
    exact (not_top_le_coe x.2 htop_le).elim
  have hxStar_not_top : polarConvex f xStar ≠ ⊤ := by
    intro htop
    have htop_le : (⊤ : EReal) ≤ (μ : EReal) := by
      have hμ' := hμ
      simp [htop] at hμ'
    exact (not_top_le_coe μ htop_le).elim
  have hinner :
      ((x.1 ⬝ᵥ xStar : ℝ) : EReal) ≤
        (1 : EReal) + f x.1 * polarConvex f xStar :=
    inner_le_one_add_mul_polarConvex (f := f) (x := x.1) (xStar := xStar)
      hx_not_top hxStar_not_top
  have hμ_nonneg : (0 : EReal) ≤ (μ : EReal) := by
    have h0 : (0 : EReal) ≤ polarConvex f xStar := polarConvex_nonneg f xStar
    exact le_trans h0 hμ
  have hx_nonneg : (0 : EReal) ≤ f x.1 := hf_nonneg x.1
  have hmul1 : f x.1 * polarConvex f xStar ≤ f x.1 * (μ : EReal) :=
    mul_le_mul_of_nonneg_left hμ hx_nonneg
  have hmul2 : f x.1 * (μ : EReal) ≤ (x.2 : EReal) * (μ : EReal) :=
    mul_le_mul_of_nonneg_right hx_le hμ_nonneg
  have hmul := add_le_add_left (le_trans hmul1 hmul2) (1 : EReal)
  have hineqE :
      ((x.1 ⬝ᵥ xStar : ℝ) : EReal) ≤
        (1 : EReal) + (x.2 : EReal) * (μ : EReal) :=
    le_trans hinner (by
      simpa [add_comm, add_left_comm, add_assoc] using hmul)
  have hineqR :
      (x.1 ⬝ᵥ xStar : ℝ) ≤ 1 + x.2 * μ := by
    have hineqR' :
        ((x.1 ⬝ᵥ xStar : ℝ) : EReal) ≤ ((1 + x.2 * μ : ℝ) : EReal) := by
      simpa [EReal.coe_add, EReal.coe_mul, mul_comm, mul_left_comm, mul_assoc] using hineqE
    exact (EReal.coe_le_coe_iff).1 hineqR'
  have hineq :
      (x.1 ⬝ᵥ xStar : ℝ) + x.2 * (-μ) ≤ 1 := by
    nlinarith
  simpa [vertReflect, mul_comm, mul_left_comm, mul_assoc] using hineq

/-- Reflected product-polar points are in the epigraph of the polar. -/
lemma vertReflect_preimage_polarSetProd_epigraph_subset_epigraph_polarConvex {n : ℕ}
    {f : (Fin n → ℝ) → EReal} (hf_nonneg : ∀ x, 0 ≤ f x) (hf0 : f 0 = 0) :
    (vertReflect (n := n)) ⁻¹'
        polarSetProd (n := n) (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) ⊆
      epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarConvex f) := by
  intro p hp
  rcases p with ⟨xStar, μ⟩
  have hp' :
      vertReflect (n := n) (xStar, μ) ∈
        polarSetProd (n := n) (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) := by
    simpa [Set.preimage] using hp
  have hμ_nonneg : 0 ≤ μ :=
    mu_nonneg_of_vertReflect_mem_polarSetProd_epigraph (n := n) (f := f) hf0 hp'
  have hμ_nonnegE : (0 : EReal) ≤ (μ : EReal) := by exact_mod_cast hμ_nonneg
  have hle_pos :
      ∀ ε : ℝ, ε > 0 → polarConvex f xStar ≤ ((μ + ε : ℝ) : EReal) := by
    intro ε hε
    refine sInf_le ?_
    refine ⟨?_, ?_⟩
    · exact_mod_cast (by linarith [hμ_nonneg, hε])
    · intro x
      by_cases hfx : f x = ⊤
      · have hpos : 0 < μ + ε := by linarith [hμ_nonneg, hε]
        have hmul_top : ((μ + ε : ℝ) : EReal) * (⊤ : EReal) = ⊤ := by
          simpa using (EReal.coe_mul_top_of_pos hpos)
        have htop : (1 : EReal) + ((μ + ε : ℝ) : EReal) * (⊤ : EReal) = ⊤ := by
          have hadd : (1 : EReal) + (⊤ : EReal) = ⊤ := by
            have hne : (1 : EReal) ≠ (⊥ : EReal) := EReal.coe_ne_bot (1 : ℝ)
            exact (EReal.add_top_iff_ne_bot (x := (1 : EReal))).2 hne
          calc
            (1 : EReal) + ((μ + ε : ℝ) : EReal) * (⊤ : EReal) =
                (1 : EReal) + (⊤ : EReal) := by
                  rw [hmul_top]
            _ = ⊤ := hadd
        have hle_top :
            ((x ⬝ᵥ xStar : ℝ) : EReal) ≤
              (1 : EReal) + ((μ + ε : ℝ) : EReal) * (⊤ : EReal) := by
          calc
            ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ (⊤ : EReal) := le_top
            _ = (1 : EReal) + ((μ + ε : ℝ) : EReal) * (⊤ : EReal) := by
                  symm
                  exact htop
        simpa [hfx] using hle_top
      · cases hfx' : f x using EReal.rec with
        | bot =>
            have hbot : f x = (⊥ : EReal) := hfx'
            have hcontra : (0 : EReal) ≤ (⊥ : EReal) := by
              simpa [hbot] using (hf_nonneg x)
            have h0eq : (0 : EReal) = (⊥ : EReal) := (le_bot_iff).1 hcontra
            simp at h0eq
        | top =>
            exact (False.elim (hfx hfx'))
        | coe r =>
            have hr0 : 0 ≤ r := by
              have : (0 : EReal) ≤ (r : EReal) := by
                simpa [hfx'] using (hf_nonneg x)
              exact (EReal.coe_le_coe_iff).1 this
            have hmem_epi :
                (x, r) ∈
                  epigraph (S := (Set.univ : Set (Fin n → ℝ))) f := by
              have hle : f x ≤ (r : EReal) := by simp [hfx']
              simpa [mem_epigraph_univ_iff] using hle
            have hineq := hp' (x, r) hmem_epi
            have hineq' : (x ⬝ᵥ xStar : ℝ) ≤ 1 + r * μ := by
              have hineq'' : (x ⬝ᵥ xStar : ℝ) - r * μ ≤ 1 := by
                simpa [vertReflect, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hineq
              linarith
            have hineqE :
                ((x ⬝ᵥ xStar : ℝ) : EReal) ≤
                  (1 : EReal) + (r : EReal) * (μ : EReal) := by
              have hineqE' :
                  ((x ⬝ᵥ xStar : ℝ) : EReal) ≤ ((1 + r * μ : ℝ) : EReal) := by
                exact_mod_cast hineq'
              simpa [EReal.coe_add, EReal.coe_mul, mul_comm, mul_left_comm, mul_assoc] using hineqE'
            have hmul :
                (r : EReal) * (μ : EReal) ≤ (r : EReal) * ((μ + ε : ℝ) : EReal) := by
              have hμle : (μ : EReal) ≤ ((μ + ε : ℝ) : EReal) := by
                exact_mod_cast (by linarith)
              have hr0E : (0 : EReal) ≤ (r : EReal) := by exact_mod_cast hr0
              exact mul_le_mul_of_nonneg_left hμle hr0E
            have hineqE' :
                ((x ⬝ᵥ xStar : ℝ) : EReal) ≤
                  (1 : EReal) + (r : EReal) * ((μ + ε : ℝ) : EReal) :=
              le_trans hineqE (by
                simpa [add_comm, add_left_comm, add_assoc] using
                  (add_le_add_left hmul (1 : EReal)))
            simpa [hfx', mul_comm, mul_left_comm, mul_assoc] using hineqE'
  have hleμ : polarConvex f xStar ≤ (μ : EReal) := by
    by_cases htop : polarConvex f xStar = ⊤
    · have h := hle_pos 1 (by norm_num)
      have htop_le : (⊤ : EReal) ≤ ((μ + 1 : ℝ) : EReal) := by
        simpa [htop] using h
      exact (False.elim (not_top_le_coe (μ + 1) htop_le))
    · cases hpolar : polarConvex f xStar using EReal.rec with
      | bot =>
          have hbot : polarConvex f xStar = (⊥ : EReal) := hpolar
          have h0le : (0 : EReal) ≤ (⊥ : EReal) := by
            simpa [hbot] using (polarConvex_nonneg f xStar)
          have h0eq : (0 : EReal) = (⊥ : EReal) := (le_bot_iff).1 h0le
          simp at h0eq
      | top =>
          exact (False.elim (htop hpolar))
      | coe r =>
          have hle_r : ∀ ε : ℝ, ε > 0 → r ≤ μ + ε := by
            intro ε hε
            have hle' : (r : EReal) ≤ ((μ + ε : ℝ) : EReal) := by
              simpa [hpolar] using hle_pos ε hε
            exact (EReal.coe_le_coe_iff).1 hle'
          have hle_rμ : r ≤ μ := by
            refine le_of_forall_pos_le_add ?_
            intro ε hε
            simpa [add_comm, add_left_comm, add_assoc] using (hle_r ε hε)
          simpa [hpolar] using (EReal.coe_le_coe_iff).2 hle_rμ
  exact (mem_epigraph_univ_iff (f := polarConvex f) (x := xStar) (μ := μ)).2 hleμ

/-- Epigraph identity for the polar convex function. -/
lemma epigraph_polarConvex_mem_iff_vertReflect_mem_polarSetProd_epigraph {n : ℕ}
    {f : (Fin n → ℝ) → EReal} (hf_nonneg : ∀ x, 0 ≤ f x) (hf0 : f 0 = 0)
    (p : (Fin n → ℝ) × ℝ) :
    p ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarConvex f) ↔
      vertReflect (n := n) p ∈
        polarSetProd (n := n) (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) := by
  constructor
  · intro hp
    exact
      epigraph_polarConvex_subset_vertReflect_preimage_polarSetProd_epigraph (n := n)
        (f := f) hf_nonneg hp
  · intro hp
    have hp' :
        p ∈
          (vertReflect (n := n)) ⁻¹'
            polarSetProd (n := n) (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) := by
      simpa [Set.preimage] using hp
    exact
      vertReflect_preimage_polarSetProd_epigraph_subset_epigraph_polarConvex (n := n)
        (f := f) hf_nonneg hf0 hp'

/-- Bipolar epigraph of the polar convex function. -/
lemma epigraph_bipolar_polarConvex_eq_closure_epigraph {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf_conv : ConvexFunctionOn (S := (Set.univ : Set (Fin n → ℝ))) f)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf0 : f 0 = 0) :
    epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarConvex (polarConvex f)) =
      closure (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) := by
  classical
  have hconv_epi : Convex ℝ (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) := by
    simpa [ConvexFunctionOn] using hf_conv
  have h0_epi :
      (0 : (Fin n → ℝ) × ℝ) ∈
        epigraph (S := (Set.univ : Set (Fin n → ℝ))) f := by
    have hle : f (0 : Fin n → ℝ) ≤ (0 : EReal) := by
      simp [hf0]
    exact (mem_epigraph_univ_iff (f := f) (x := (0 : Fin n → ℝ)) (μ := (0 : ℝ))).2 hle
  have hpolar_epi :
      epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarConvex (polarConvex f)) =
        (vertReflect (n := n)) ⁻¹'
          polarSetProd (n := n)
            (epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarConvex f)) := by
    ext p
    simpa using
      (epigraph_polarConvex_mem_iff_vertReflect_mem_polarSetProd_epigraph (n := n)
        (f := polarConvex f) (fun x => polarConvex_nonneg f x) (polarConvex_zero f) p)
  have hpolar_epi_f :
      epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarConvex f) =
        (vertReflect (n := n)) ⁻¹'
          polarSetProd (n := n) (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) := by
    ext p
    simpa using
      (epigraph_polarConvex_mem_iff_vertReflect_mem_polarSetProd_epigraph (n := n)
        (f := f) hf_nonneg hf0 p)
  have hpolar_epi' :
      epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarConvex (polarConvex f)) =
        (vertReflect (n := n)) ⁻¹'
          polarSetProd (n := n)
            ((vertReflect (n := n)) ⁻¹'
              polarSetProd (n := n)
                (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f)) := by
    simpa [hpolar_epi_f] using hpolar_epi
  have hcancel :
      (vertReflect (n := n)) ⁻¹'
          polarSetProd (n := n)
            ((vertReflect (n := n)) ⁻¹'
              polarSetProd (n := n)
                (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f)) =
        polarSetProd (n := n)
          (polarSetProd (n := n)
            (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f)) := by
    calc
      (vertReflect (n := n)) ⁻¹'
          polarSetProd (n := n)
            ((vertReflect (n := n)) ⁻¹'
              polarSetProd (n := n)
                (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f))
          =
          (vertReflect (n := n)) ⁻¹'
            ((vertReflect (n := n)) ⁻¹'
              polarSetProd (n := n)
                (polarSetProd (n := n)
                  (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f))) := by
            have hpre :
                polarSetProd (n := n)
                    ((vertReflect (n := n)) ⁻¹'
                      polarSetProd (n := n)
                        (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f)) =
                  (vertReflect (n := n)) ⁻¹'
                    polarSetProd (n := n)
                      (polarSetProd (n := n)
                        (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f)) := by
              simpa using
                (polarSetProd_preimage_vertReflect (n := n)
                  (C := polarSetProd (n := n)
                    (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f)))
            simp [hpre]
      _ =
          polarSetProd (n := n)
            (polarSetProd (n := n)
              (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f)) := by
            ext p
            have hσ : vertReflect (n := n) (vertReflect (n := n) p) = p := by
              simpa using (vertReflect_involutive (n := n) p)
            constructor
            · intro hp
              have hp' :
                  vertReflect (n := n) (vertReflect (n := n) p) ∈
                    polarSetProd (n := n)
                      (polarSetProd (n := n)
                        (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f)) := by
                simpa [Set.preimage] using hp
              simpa [hσ] using hp'
            · intro hp
              have hp' :
                  vertReflect (n := n) (vertReflect (n := n) p) ∈
                    polarSetProd (n := n)
                      (polarSetProd (n := n)
                        (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f)) := by
                simpa [hσ] using hp
              simpa [Set.preimage] using hp'
  calc
    epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarConvex (polarConvex f)) =
        polarSetProd (n := n)
          (polarSetProd (n := n)
            (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f)) := by
      simpa [hpolar_epi'] using hcancel
    _ = closure (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) := by
      exact polarSetProd_bipolar_eq_closure_of_convex_zeroMem (n := n)
        (C := epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) hconv_epi h0_epi

theorem polarConvex_nonneg_closedConvex_and_bipolar_eq_convexFunctionClosure {n : ℕ}
    {f : (Fin n → ℝ) → EReal}
    (hf_conv : ConvexFunctionOn (S := (Set.univ : Set (Fin n → ℝ))) f)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf0 : f 0 = 0) :
    let fPolar : (Fin n → ℝ) → EReal := polarConvex f
    (∀ xStar, 0 ≤ fPolar xStar) ∧
      ClosedConvexFunction fPolar ∧
        fPolar 0 = 0 ∧
          polarConvex fPolar = convexFunctionClosure f := by
  classical
  dsimp
  refine ⟨?_, ?_⟩
  · intro xStar
    exact polarConvex_nonneg f xStar
  · refine ⟨?_, ?_⟩
    · have hpolar_epi :
          epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarConvex f) =
            (vertReflect (n := n)) ⁻¹'
              polarSetProd (n := n)
                (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) := by
        ext p
        simpa using
          (epigraph_polarConvex_mem_iff_vertReflect_mem_polarSetProd_epigraph (n := n)
            (f := f) hf_nonneg hf0 p)
      have hclosed_polar :
          IsClosed
            (polarSetProd (n := n)
              (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f)) :=
        (polarSetProd_isClosed_and_convex (n := n)
          (C := epigraph (S := (Set.univ : Set (Fin n → ℝ))) f)).1
      have hconv_polar :
          Convex ℝ
            (polarSetProd (n := n)
              (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f)) :=
        (polarSetProd_isClosed_and_convex (n := n)
          (C := epigraph (S := (Set.univ : Set (Fin n → ℝ))) f)).2
      have hcont : Continuous (vertReflect (n := n)) := by
        have hfst : Continuous (fun p : (Fin n → ℝ) × ℝ => p.1) := continuous_fst
        have hsnd : Continuous (fun p : (Fin n → ℝ) × ℝ => -p.2) := by
          simpa using
            (continuous_snd.neg :
              Continuous (fun p : (Fin n → ℝ) × ℝ => -p.2))
        change Continuous (fun p : (Fin n → ℝ) × ℝ => (p.1, -p.2))
        exact hfst.prodMk hsnd
      have hclosed_epi :
          IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarConvex f)) := by
        simpa [hpolar_epi] using hclosed_polar.preimage hcont
      have hconv_epi :
          Convex ℝ (epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarConvex f)) := by
        have hlin : IsLinearMap ℝ (vertReflect (n := n)) := by
          refine ⟨?_, ?_⟩
          · intro p q
            cases p with
            | mk x μ =>
                cases q with
                | mk y ν =>
                    simp [vertReflect, add_comm]
          · intro a p
            cases p with
            | mk x μ =>
                simp [vertReflect, smul_eq_mul]
        have hconv_pre :
            Convex ℝ
              ((vertReflect (n := n)) ⁻¹'
                polarSetProd (n := n)
                  (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f)) :=
          (Convex.is_linear_preimage (s := polarSetProd (n := n)
              (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f)) hconv_polar hlin)
        simpa [hpolar_epi] using hconv_pre
      have hls : LowerSemicontinuous (polarConvex f) := by
        have hiff :=
          lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph (f := polarConvex f)
        have hsub :
            ∀ α : ℝ, IsClosed {x | polarConvex f x ≤ (α : EReal)} :=
          (hiff.2).2 hclosed_epi
        exact (hiff.1).2 hsub
      have hconv : ConvexFunction (polarConvex f) := by
        simpa [ConvexFunction, ConvexFunctionOn] using hconv_epi
      exact ⟨hconv, hls⟩
    · refine ⟨?_, ?_⟩
      · simpa using (polarConvex_zero f)
      · have hbot : ∀ x, f x ≠ (⊥ : EReal) := hbot_of_nonneg (f := f) hf_nonneg
        have hbot_polar :
            ∀ x, polarConvex (polarConvex f) x ≠ (⊥ : EReal) :=
          hbot_of_nonneg (f := polarConvex (polarConvex f))
            (fun x => polarConvex_nonneg (polarConvex f) x)
        have hcl_epi :
            epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarConvex (polarConvex f)) =
              closure (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) :=
          epigraph_bipolar_polarConvex_eq_closure_epigraph (n := n) (f := f) hf_conv hf_nonneg hf0
        have hcl :
            closure (epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarConvex (polarConvex f))) =
              closure (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) := by
          calc
            closure (epigraph (S := (Set.univ : Set (Fin n → ℝ)))
                (polarConvex (polarConvex f))) =
                closure (closure (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f)) := by
                  simp [hcl_epi]
            _ = closure (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) := by
                  simp
        have hcl_eq :
            convexFunctionClosure (polarConvex (polarConvex f)) =
              convexFunctionClosure f :=
          convexFunctionClosure_eq_of_epigraph_closure_eq (n := n)
            (f := polarConvex (polarConvex f)) (g := f) hbot_polar hbot hcl
        have hconv_epi_f :
            Convex ℝ (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f) := by
          simpa [ConvexFunctionOn] using hf_conv
        have hconv_epi_polar :
            Convex ℝ
              (epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarConvex (polarConvex f))) := by
          have hconv_cl : Convex ℝ (closure (epigraph (S := (Set.univ : Set (Fin n → ℝ))) f)) :=
            hconv_epi_f.closure
          simpa [hcl_epi] using hconv_cl
        have hclosed_epi_polar :
            IsClosed
              (epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarConvex (polarConvex f))) := by
          simp [hcl_epi]
        have hls_polar : LowerSemicontinuous (polarConvex (polarConvex f)) := by
          have hiff :=
            lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph
              (f := polarConvex (polarConvex f))
          have hsub :
              ∀ α : ℝ,
                IsClosed {x | polarConvex (polarConvex f) x ≤ (α : EReal)} :=
            (hiff.2).2 hclosed_epi_polar
          exact (hiff.1).2 hsub
        have hconv_polar : ConvexFunction (polarConvex (polarConvex f)) := by
          simpa [ConvexFunction, ConvexFunctionOn] using hconv_epi_polar
        have hclosed_polar : ClosedConvexFunction (polarConvex (polarConvex f)) :=
          ⟨hconv_polar, hls_polar⟩
        have hclosure_polar :
            convexFunctionClosure (polarConvex (polarConvex f)) =
              polarConvex (polarConvex f) :=
          convexFunctionClosure_eq_of_closedConvexFunction (n := n) hclosed_polar hbot_polar
        calc
          polarConvex (polarConvex f) =
              convexFunctionClosure (polarConvex (polarConvex f)) := by
                symm
                exact hclosure_polar
          _ = convexFunctionClosure f := hcl_eq

/-- A closed convex function is convex on `univ`. -/
lemma convexFunctionOn_univ_of_closedConvexFunction {n : ℕ}
    {f : (Fin n → ℝ) → EReal} (hf_closed : ClosedConvexFunction f) :
    ConvexFunctionOn (S := (Set.univ : Set (Fin n → ℝ))) f := by
  simpa [ConvexFunction] using hf_closed.1

/-- `polarConvex` preserves nonnegativity, closed convexity, and vanishing at `0` on the subtype. -/
lemma polarConvex_mem_subtype_nonneg_closedConvex_zero {n : ℕ}
    (f : {g : (Fin n → ℝ) → EReal //
        (∀ x, 0 ≤ g x) ∧ ClosedConvexFunction g ∧ g 0 = 0}) :
    (∀ x, 0 ≤ polarConvex f.1 x) ∧
      ClosedConvexFunction (polarConvex f.1) ∧
        polarConvex f.1 0 = 0 := by
  have hf_conv :
      ConvexFunctionOn (S := (Set.univ : Set (Fin n → ℝ))) f.1 :=
    convexFunctionOn_univ_of_closedConvexFunction (n := n) f.property.2.1
  have h :=
    polarConvex_nonneg_closedConvex_and_bipolar_eq_convexFunctionClosure (n := n)
      (f := f.1) hf_conv f.property.1 f.property.2.2
  dsimp at h
  rcases h with ⟨h_nonneg, h_closed, h_zero, _⟩
  exact ⟨h_nonneg, h_closed, h_zero⟩

/-- `polarConvex` is involutive on the nonnegative closed convex subclass with `f 0 = 0`. -/
lemma polarConvex_involutive_on_subtype {n : ℕ}
    (f : {g : (Fin n → ℝ) → EReal //
        (∀ x, 0 ≤ g x) ∧ ClosedConvexFunction g ∧ g 0 = 0}) :
    polarConvex (polarConvex f.1) = f.1 := by
  have hf_conv :
      ConvexFunctionOn (S := (Set.univ : Set (Fin n → ℝ))) f.1 :=
    convexFunctionOn_univ_of_closedConvexFunction (n := n) f.property.2.1
  have h :=
    polarConvex_nonneg_closedConvex_and_bipolar_eq_convexFunctionClosure (n := n)
      (f := f.1) hf_conv f.property.1 f.property.2.2
  dsimp at h
  have hbot : ∀ x, f.1 x ≠ (⊥ : EReal) :=
    hbot_of_nonneg (f := f.1) f.property.1
  have hclosure :
      convexFunctionClosure f.1 = f.1 :=
    convexFunctionClosure_eq_of_closedConvexFunction (n := n) f.property.2.1 hbot
  calc
    polarConvex (polarConvex f.1) = convexFunctionClosure f.1 := h.2.2.2
    _ = f.1 := hclosure

end Section15
end Chap03
