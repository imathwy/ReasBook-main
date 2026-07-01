/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section08_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section10_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section12_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section13_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section14_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part5

section Chap03
section Section15

open scoped BigOperators
open scoped Pointwise

/-- The gauge of a closed convex absorbing set containing `0` is a gauge. -/
lemma gaugeFunctionEReal_isGauge_of_closed_convex_zeroMem_absorbing {n : ℕ} {C : Set (Fin n → ℝ)}
    (hC_closed : IsClosed C) (hC_conv : Convex ℝ C) (hC0 : (0 : Fin n → ℝ) ∈ C)
    (hCabs : ∀ x : Fin n → ℝ, ∃ lam : ℝ, 0 ≤ lam ∧ x ∈ (fun y => lam • y) '' C) :
    IsGauge (fun x => (gaugeFunction C x : EReal)) := by
  let S : (Fin n → ℝ) → Set ℝ :=
    fun x => {r : ℝ | 0 ≤ r ∧ ∃ y ∈ C, x = r • y}
  have hS_nonempty : ∀ x, (S x).Nonempty := by
    intro x
    rcases hCabs x with ⟨r, hr0, hxmem⟩
    rcases hxmem with ⟨y, hyC, hxy⟩
    exact ⟨r, ⟨hr0, y, hyC, hxy.symm⟩⟩
  have hS_bdd : ∀ x, BddBelow (S x) := by
    intro x
    refine ⟨0, ?_⟩
    intro r hr
    exact hr.1
  have hS_eq : ∀ x, gaugeFunction C x = sInf (S x) := by
    intro x
    simp [gaugeFunction, S]
  have hclosed :
      ClosedConvexFunction (fun x => (gaugeFunction C x : EReal)) :=
    (gaugeFunction_closed_and_level_sets (C := C) hC_closed hC_conv hC0 hCabs).1
  have hconv : ConvexFunction (fun x => (gaugeFunction C x : EReal)) := hclosed.1
  have hconv_on :
      ConvexFunctionOn (S := (Set.univ : Set (Fin n → ℝ)))
        (fun x => (gaugeFunction C x : EReal)) := by
    simpa [ConvexFunction] using hconv
  have hnonneg : ∀ x, (0 : EReal) ≤ (gaugeFunction C x : EReal) := by
    intro x
    have hle : 0 ≤ sInf (S x) :=
      le_csInf (hS_nonempty x) (by intro r hr; exact hr.1)
    have hle' : (0 : EReal) ≤ ((sInf (S x) : ℝ) : EReal) := by exact_mod_cast hle
    simpa [hS_eq x] using hle'
  have hzero_real : gaugeFunction C (0 : Fin n → ℝ) = 0 := by
    have hmem : (0 : ℝ) ∈ S (0 : Fin n → ℝ) := by
      refine ⟨le_rfl, 0, hC0, ?_⟩
      simp
    have hle : sInf (S (0 : Fin n → ℝ)) ≤ 0 := csInf_le (hS_bdd _) hmem
    have hge : 0 ≤ sInf (S (0 : Fin n → ℝ)) :=
      le_csInf (hS_nonempty _) (by intro r hr; exact hr.1)
    have hEq : sInf (S (0 : Fin n → ℝ)) = 0 := le_antisymm hle hge
    simp [hS_eq (0 : Fin n → ℝ), hEq]
  have hzero : (gaugeFunction C (0 : Fin n → ℝ) : EReal) = 0 := by
    exact_mod_cast hzero_real
  have hhom_real :
      ∀ x r, 0 ≤ r → gaugeFunction C (r • x) = r * gaugeFunction C x := by
    intro x r hr
    by_cases hr0 : r = 0
    · subst hr0
      simp [hzero_real]
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      have hle :
          gaugeFunction C (r • x) ≤ r * gaugeFunction C x := by
        refine _root_.le_of_forall_pos_le_add ?_
        intro ε hε
        have hx_lt : sInf (S x) < sInf (S x) + ε / r := by
          have hpos : 0 < ε / r := by exact div_pos hε hrpos
          linarith
        rcases exists_lt_of_csInf_lt (hS_nonempty x) hx_lt with ⟨s, hs, hslt⟩
        rcases hs with ⟨hs0, y, hyC, hxy⟩
        have hrs : r * s ∈ S (r • x) := by
          refine ⟨mul_nonneg hr hs0, y, hyC, ?_⟩
          calc
            r • x = r • (s • y) := by simp [hxy]
            _ = (r * s) • y := by simp [smul_smul]
        have hle_s : sInf (S (r • x)) ≤ r * s :=
          csInf_le (hS_bdd (r • x)) hrs
        have hslt' : r * s < r * (sInf (S x) + ε / r) :=
          mul_lt_mul_of_pos_left hslt hrpos
        have hslt'' :
            r * (sInf (S x) + ε / r) = r * sInf (S x) + ε := by
          have hrne : r ≠ 0 := ne_of_gt hrpos
          calc
            r * (sInf (S x) + ε / r) = r * sInf (S x) + r * (ε / r) := by ring
            _ = r * sInf (S x) + ε := by
              field_simp [hrne]
        have hle' : sInf (S (r • x)) ≤ r * sInf (S x) + ε :=
          le_trans hle_s (le_of_lt (by simpa [hslt''] using hslt'))
        simpa [hS_eq (r • x), hS_eq x] using hle'
      have hge :
          r * gaugeFunction C x ≤ gaugeFunction C (r • x) := by
        refine le_csInf (hS_nonempty (r • x)) ?_
        intro s hs
        rcases hs with ⟨hs0, y, hyC, hxy⟩
        have hs' : s / r ∈ S x := by
          refine ⟨div_nonneg hs0 hr, y, hyC, ?_⟩
          have hrne : r ≠ 0 := ne_of_gt hrpos
          calc
            x = (1 / r) • (r • x) := by
              simp [smul_smul, hrne]
            _ = (1 / r) • (s • y) := by simp [hxy]
            _ = (s / r) • y := by
              simp [smul_smul, div_eq_mul_inv, mul_comm]
        have hle_s : sInf (S x) ≤ s / r := csInf_le (hS_bdd x) hs'
        have hle_s' : r * sInf (S x) ≤ r * (s / r) :=
          mul_le_mul_of_nonneg_left hle_s hr
        have hle_s'' : r * (s / r) = s := by
          have hrne : r ≠ 0 := ne_of_gt hrpos
          field_simp [hrne]
        have hle_s''' : r * sInf (S x) ≤ s := by simpa [hle_s''] using hle_s'
        simpa [hS_eq x] using hle_s'''
      exact le_antisymm hle hge
  have hhom :
      ∀ x (r : ℝ), 0 ≤ r →
        (gaugeFunction C (r • x) : EReal) = (r : EReal) * (gaugeFunction C x : EReal) := by
    intro x r hr
    have hhom' : (gaugeFunction C (r • x) : EReal) =
        ((r * gaugeFunction C x : ℝ) : EReal) := by
      exact_mod_cast (hhom_real x r hr)
    simpa [EReal.coe_mul] using hhom'
  refine ⟨hconv_on, hnonneg, hhom, ?_⟩
  exact hzero

/-- The gauge function of a closed convex absorbing set has closed epigraph. -/
lemma isClosed_epigraph_gaugeFunctionEReal_of_closed_convex_zeroMem_absorbing
    {n : ℕ} {C : Set (Fin n → ℝ)} (hC_closed : IsClosed C) (hC_conv : Convex ℝ C)
    (hC0 : (0 : Fin n → ℝ) ∈ C)
    (hCabs : ∀ x : Fin n → ℝ, ∃ lam : ℝ, 0 ≤ lam ∧ x ∈ (fun y => lam • y) '' C) :
    IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ)))
      (fun x => (gaugeFunction C x : EReal))) := by
  have hclosed :
      ClosedConvexFunction (fun x => (gaugeFunction C x : EReal)) :=
    (gaugeFunction_closed_and_level_sets (C := C) hC_closed hC_conv hC0 hCabs).1
  have hlsc : LowerSemicontinuous (fun x => (gaugeFunction C x : EReal)) := hclosed.2
  exact isClosed_epigraph_univ_of_lowerSemicontinuous (hf := hlsc)

/-- The polar gauge of the support function agrees with the gauge of the set. -/
lemma polarGauge_supportFunctionEReal_eq_gaugeFunctionEReal {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCne : C.Nonempty)
    (hCabs : ∀ x : Fin n → ℝ, ∃ lam : ℝ, 0 ≤ lam ∧ x ∈ (fun y => lam • y) '' C)
    (hγ : IsGauge (fun x => (gaugeFunction C x : EReal)))
    (hγclosed :
      IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ)))
        (fun x => (gaugeFunction C x : EReal)))) :
    polarGauge (supportFunctionEReal C) = (fun x => (gaugeFunction C x : EReal)) := by
  have hpol :
      polarGauge (fun x => (gaugeFunction C x : EReal)) = supportFunctionEReal C :=
    polarGauge_gaugeFunction_eq_supportFunctionEReal (C := C) hCne hCabs
  calc
    polarGauge (supportFunctionEReal C) =
        polarGauge (polarGauge (fun x => (gaugeFunction C x : EReal))) := by
          simp [hpol]
    _ = (fun x => (gaugeFunction C x : EReal)) :=
      polarGauge_involutive_of_isGauge_isClosed_epigraph hγ hγclosed

/-- Corollary 15.1.2: If `C ⊆ ℝ^n` is a closed convex set containing `0`, then the gauge
`γ(· | C)` and the support function `δ^*(· | C)` are closed gauges polar to each other.

In this development, `γ(· | C)` is `fun x => (gaugeFunction C x : EReal)`, the support function
is `supportFunctionEReal C`, "closed" is expressed as `IsClosed (epigraph univ ·)`, and polarity
of gauges is given by `polarGauge`. We additionally assume `C` is absorbing. -/
theorem gaugeFunction_and_supportFunctionEReal_closedGauges_polar {n : ℕ} {C : Set (Fin n → ℝ)}
    (hC_closed : IsClosed C) (hC_conv : Convex ℝ C) (hC0 : (0 : Fin n → ℝ) ∈ C)
    (hCabs : ∀ x : Fin n → ℝ, ∃ lam : ℝ, 0 ≤ lam ∧ x ∈ (fun y => lam • y) '' C) :
    let γ : (Fin n → ℝ) → EReal := fun x => (gaugeFunction C x : EReal)
    let δ : (Fin n → ℝ) → EReal := supportFunctionEReal C
    (IsGauge γ ∧ IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ))) γ)) ∧
      (IsGauge δ ∧ IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ))) δ)) ∧
        polarGauge γ = δ ∧ polarGauge δ = γ := by
  dsimp
  have hCne : C.Nonempty := ⟨0, hC0⟩
  have hγ : IsGauge (fun x => (gaugeFunction C x : EReal)) :=
    gaugeFunctionEReal_isGauge_of_closed_convex_zeroMem_absorbing
      (C := C) hC_closed hC_conv hC0 hCabs
  have hγclosed :
      IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ)))
        (fun x => (gaugeFunction C x : EReal))) :=
    isClosed_epigraph_gaugeFunctionEReal_of_closed_convex_zeroMem_absorbing
      (C := C) hC_closed hC_conv hC0 hCabs
  have hpol :
      polarGauge (fun x => (gaugeFunction C x : EReal)) = supportFunctionEReal C :=
    polarGauge_gaugeFunction_eq_supportFunctionEReal (C := C) hCne hCabs
  have hδ :
      IsGauge (supportFunctionEReal C) ∧
        IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ))) (supportFunctionEReal C)) := by
    have hmap :=
      (polarGauge_mapsTo_closedGauges (k := fun x => (gaugeFunction C x : EReal))
        ⟨hγ, hγclosed⟩)
    simpa [hpol] using hmap
  have hpol' :
      polarGauge (supportFunctionEReal C) = (fun x => (gaugeFunction C x : EReal)) :=
    polarGauge_supportFunctionEReal_eq_gaugeFunctionEReal (C := C) hCne hCabs hγ hγclosed
  refine ⟨⟨hγ, hγclosed⟩, ?_⟩
  refine ⟨hδ, ?_⟩
  exact ⟨hpol, hpol'⟩

/-- If `0` lies in the interior of a convex set, then the set is absorbing. -/
lemma absorbing_of_zero_mem_interior {n : ℕ} {C : Set (Fin n → ℝ)} (hCconv : Convex ℝ C)
    (hC0 : (0 : Fin n → ℝ) ∈ interior C) :
    ∀ x : Fin n → ℝ, ∃ lam : ℝ, 0 ≤ lam ∧ x ∈ (fun y => lam • y) '' C := by
  have hscale :
      ∀ y : Fin n → ℝ, ∃ ε : ℝ, 0 < ε ∧ ε • y ∈ C :=
    (section14_zero_mem_interior_iff_forall_exists_pos_smul_mem
      (E := Fin n → ℝ) (C := C) hCconv).1 hC0
  intro x
  rcases hscale x with ⟨ε, hεpos, hεmem⟩
  refine ⟨ε⁻¹, ?_, ?_⟩
  · exact inv_nonneg.mpr (le_of_lt hεpos)
  · refine ⟨ε • x, hεmem, ?_⟩
    have hεne : ε ≠ 0 := ne_of_gt hεpos
    simp [smul_smul, hεne]

/-- A norm gauge is continuous on `ℝ^n`. -/
lemma normGauge_continuous {n : ℕ} {k : (Fin n → ℝ) → EReal} (hk : IsNormGauge k) :
    Continuous k := by
  rcases hk with ⟨hk_gauge, hk_finite, _hk_even, _hk_pos⟩
  have hCsub :
      (Set.univ : Set (Fin n → ℝ)) ⊆
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) k := by
    intro x hx
    have hxlt : k x < (⊤ : EReal) := (lt_top_iff_ne_top).2 (hk_finite x)
    have hx' :
        x ∈ {x | x ∈ (Set.univ : Set (Fin n → ℝ)) ∧ k x < (⊤ : EReal)} := ⟨by simp, hxlt⟩
    simpa [effectiveDomain_eq] using hx'
  have hCrelOpen :
      euclideanRelativelyOpen n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          (Set.univ : Set (Fin n → ℝ))) := by
    simpa using (euclideanRelativelyOpen_univ n)
  have hcontOn :
      ContinuousOn k (Set.univ : Set (Fin n → ℝ)) :=
    convexFunctionOn_continuousOn_of_relOpen_effectiveDomain (n := n) (f := k) hk_gauge.1
      (C := Set.univ) (hCconv := convex_univ) (hCsub := hCsub) (hCrelOpen := hCrelOpen)
  simpa using (continuousOn_univ).1 hcontOn

/-- The unit sublevel set of a norm gauge is closed. -/
lemma normGauge_sublevel_one_closed {n : ℕ} {k : (Fin n → ℝ) → EReal} (hk : IsNormGauge k) :
    IsClosed {x : Fin n → ℝ | k x ≤ (1 : EReal)} := by
  have hcont : Continuous k := normGauge_continuous (k := k) hk
  have hclosed : IsClosed (k ⁻¹' Set.Iic (1 : EReal)) := (isClosed_Iic.preimage hcont)
  simpa [Set.preimage, Set.Iic] using hclosed

/-- The unit sublevel set of a norm gauge contains the origin in its interior. -/
lemma normGauge_sublevel_one_zero_mem_interior {n : ℕ} {k : (Fin n → ℝ) → EReal}
    (hk : IsNormGauge k) :
    (0 : Fin n → ℝ) ∈ interior {x : Fin n → ℝ | k x ≤ (1 : EReal)} := by
  rcases hk with ⟨hk_gauge, hk_finite, _hk_even, hk_pos⟩
  rcases hk_gauge with ⟨hk_conv, hk_nonneg, hk_hom, hk0⟩
  let C : Set (Fin n → ℝ) := {x : Fin n → ℝ | k x ≤ (1 : EReal)}
  have hCconv : Convex ℝ C := IsGauge.convex_sublevel_one (k := k) ⟨hk_conv, hk_nonneg, hk_hom, hk0⟩
  refine
    (section14_zero_mem_interior_iff_forall_exists_pos_smul_mem
      (E := Fin n → ℝ) (C := C) hCconv).2 ?_
  intro x
  by_cases hx0 : x = 0
  · refine ⟨1, by norm_num, ?_⟩
    subst hx0
    have h0le : (0 : EReal) ≤ (1 : EReal) := by
      exact_mod_cast (show (0 : ℝ) ≤ (1 : ℝ) by norm_num)
    simp [C, hk0, h0le]
  · have hxpos : (0 : EReal) < k x := hk_pos x hx0
    have hx_top : k x ≠ ⊤ := hk_finite x
    have hx_bot : k x ≠ (⊥ : EReal) := IsGauge.ne_bot ⟨hk_conv, hk_nonneg, hk_hom, hk0⟩ x
    set r : ℝ := (k x).toReal
    have hrpos : 0 < r := EReal.toReal_pos hxpos hx_top
    have hreq : k x = (r : EReal) := by
      simpa [r] using (EReal.coe_toReal (x := k x) hx_top hx_bot).symm
    refine ⟨r⁻¹, inv_pos.mpr hrpos, ?_⟩
    have hhom : k (r⁻¹ • x) = ((r⁻¹ : ℝ) : EReal) * k x := by
      simpa using hk_hom x r⁻¹ (inv_nonneg.mpr (le_of_lt hrpos))
    have hEq : k (r⁻¹ • x) = (1 : EReal) := by
      calc
        k (r⁻¹ • x) = ((r⁻¹ : ℝ) : EReal) * k x := hhom
        _ = ((r⁻¹ : ℝ) : EReal) * (r : EReal) := by
          exact congrArg (fun z => ((r⁻¹ : ℝ) : EReal) * z) hreq
        _ = (1 : EReal) := by
            have hrne : r ≠ 0 := ne_of_gt hrpos
            have hmul : ((r⁻¹ * r : ℝ)) = 1 := by
              field_simp [hrne]
            calc
              ((r⁻¹ : ℝ) : EReal) * (r : EReal) = ((r⁻¹ * r : ℝ) : EReal) := by
                exact (EReal.coe_mul r⁻¹ r).symm
              _ = (1 : EReal) := by simp [hmul]
    have hle : k (r⁻¹ • x) ≤ (1 : EReal) := by
      exact le_of_eq hEq
    change k (r⁻¹ • x) ≤ (1 : EReal)
    exact hle

/-- The recession cone of the unit sublevel set of a norm gauge is `{0}`. -/
lemma normGauge_sublevel_one_recessionCone_eq_singleton_zero {n : ℕ}
    {k : (Fin n → ℝ) → EReal} (hk : IsNormGauge k) :
    Set.recessionCone {x : Fin n → ℝ | k x ≤ (1 : EReal)} = ({0} : Set (Fin n → ℝ)) := by
  classical
  rcases hk with ⟨hk_gauge, hk_finite, _hk_even, hk_pos⟩
  rcases hk_gauge with ⟨hk_conv, hk_nonneg, hk_hom, hk0⟩
  let C : Set (Fin n → ℝ) := {x : Fin n → ℝ | k x ≤ (1 : EReal)}
  have hC0 : (0 : Fin n → ℝ) ∈ C := by
    have h0le : (0 : EReal) ≤ (1 : EReal) := by
      exact_mod_cast (show (0 : ℝ) ≤ (1 : ℝ) by norm_num)
    simp [C, hk0, h0le]
  have hsubset : Set.recessionCone C ⊆ ({0} : Set (Fin n → ℝ)) := by
    intro y hy
    by_cases hy0 : y = 0
    · simp [hy0]
    · have hypos : (0 : EReal) < k y := hk_pos y hy0
      have hy_top : k y ≠ ⊤ := hk_finite y
      have hy_bot : k y ≠ (⊥ : EReal) := IsGauge.ne_bot ⟨hk_conv, hk_nonneg, hk_hom, hk0⟩ y
      set r : ℝ := (k y).toReal
      have hrpos : 0 < r := EReal.toReal_pos hypos hy_top
      have hreq : k y = (r : EReal) := by
        simpa [r] using (EReal.coe_toReal (x := k y) hy_top hy_bot).symm
      have hmem : ((r / 2)⁻¹) • y ∈ C := by
        have hnonneg : 0 ≤ (r / 2)⁻¹ := by
          have : 0 < r / 2 := by linarith [hrpos]
          exact inv_nonneg.mpr (le_of_lt this)
        have hmem' := hy (x := 0) hC0 (t := (r / 2)⁻¹) hnonneg
        simpa using hmem'
      have hle : k ((r / 2)⁻¹ • y) ≤ (1 : EReal) := by
        simpa [C] using hmem
      have hhom : k ((r / 2)⁻¹ • y) = (((r / 2)⁻¹ : ℝ) : EReal) * k y := by
        have hnonneg : 0 ≤ (r / 2)⁻¹ := by
          have : 0 < r / 2 := by linarith [hrpos]
          exact inv_nonneg.mpr (le_of_lt this)
        simpa using hk_hom y ((r / 2)⁻¹) hnonneg
      have hcalc : k ((r / 2)⁻¹ • y) = (2 : EReal) := by
        have hrne : r ≠ 0 := ne_of_gt hrpos
        have hmul : ((r / 2)⁻¹ * r : ℝ) = 2 := by
          field_simp [hrne]
        calc
          k ((r / 2)⁻¹ • y) = (((r / 2)⁻¹ : ℝ) : EReal) * k y := hhom
          _ = (((r / 2)⁻¹ : ℝ) : EReal) * (r : EReal) := by
            exact congrArg (fun z => (((r / 2)⁻¹ : ℝ) : EReal) * z) hreq
          _ = (2 : EReal) := by
              calc
                (((r / 2)⁻¹ : ℝ) : EReal) * (r : EReal) =
                    (((r / 2)⁻¹ * r : ℝ) : EReal) := by
                    exact (EReal.coe_mul ((r / 2)⁻¹) r).symm
                _ = (2 : EReal) := by
                  simpa using (congrArg (fun t : ℝ => (t : EReal)) hmul)
      have hcontr : (2 : EReal) ≤ (1 : EReal) := by
        have hle' := hle
        rw [hcalc] at hle'
        exact hle'
      have : ¬ ((2 : EReal) ≤ (1 : EReal)) := by
        exact_mod_cast (show ¬ ((2 : ℝ) ≤ (1 : ℝ)) by linarith)
      exact (this hcontr).elim
  have hzero : (0 : Fin n → ℝ) ∈ Set.recessionCone C := by
    intro x hx t ht
    simpa using hx
  ext y
  constructor
  · intro hy
    exact hsubset hy
  · intro hy
    have : y = 0 := by simpa using hy
    subst this
    exact hzero

/-- The unit sublevel set of a norm gauge is bounded. -/
lemma normGauge_sublevel_one_bounded {n : ℕ} {k : (Fin n → ℝ) → EReal} (hk : IsNormGauge k) :
    Bornology.IsBounded {x : Fin n → ℝ | k x ≤ (1 : EReal)} := by
  classical
  let C : Set (Fin n → ℝ) := {x : Fin n → ℝ | k x ≤ (1 : EReal)}
  have hCne : C.Nonempty := IsGauge.sublevel_one_nonempty (k := k) hk.1
  have hCconv : Convex ℝ C := IsGauge.convex_sublevel_one (k := k) hk.1
  have hCclosed : IsClosed C := normGauge_sublevel_one_closed (k := k) hk
  have hRec : Set.recessionCone C = ({0} : Set (Fin n → ℝ)) :=
    normGauge_sublevel_one_recessionCone_eq_singleton_zero (k := k) hk
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] Fin n → ℝ :=
    EuclideanSpace.equiv (Fin n) ℝ
  let C' : Set (EuclideanSpace ℝ (Fin n)) := e ⁻¹' C
  have hCne' : C'.Nonempty := by
    rcases hCne with ⟨x, hx⟩
    refine ⟨e.symm x, ?_⟩
    simpa [C', Set.preimage] using hx
  have hCclosed' : IsClosed C' := by
    simpa [C', Set.preimage] using hCclosed.preimage e.continuous
  have hCconv' : Convex ℝ C' := by
    intro x hx y hy a b ha hb hab
    have hx' : e x ∈ C := by simpa [C', Set.preimage] using hx
    have hy' : e y ∈ C := by simpa [C', Set.preimage] using hy
    have hmem : a • e x + b • e y ∈ C := hCconv hx' hy' ha hb hab
    have : e (a • x + b • y) ∈ C := by
      simpa [map_add, map_smul] using hmem
    simpa [C', Set.preimage] using this
  have hRec' : Set.recessionCone C' = ({0} : Set (EuclideanSpace ℝ (Fin n))) := by
    ext y
    constructor
    · intro hy
      have hy' : e y ∈ Set.recessionCone C := by
        intro x hx t ht
        have hx' : e.symm x ∈ C' := by
          simpa [C', Set.preimage] using hx
        have hmem : e.symm x + t • y ∈ C' := hy hx' ht
        have : e (e.symm x + t • y) ∈ C := by
          simpa [C', Set.preimage] using hmem
        simpa [map_add, map_smul] using this
      have : e y ∈ ({0} : Set (Fin n → ℝ)) := by simpa [hRec] using hy'
      have hy0 : e y = 0 := by simpa using this
      have : y = 0 := by
        exact e.injective (by simpa using hy0)
      simp [this]
    · intro hy
      have hy0 : y = 0 := by simpa using hy
      subst hy0
      intro x hx t ht
      simpa using hx
  have hCbdd' : Bornology.IsBounded C' :=
    (bounded_iff_recessionCone_eq_singleton_zero
      (n := n) (C := C') hCne' hCclosed' hCconv').2 hRec'
  have hCbdd : Bornology.IsBounded (e '' C') := by
    simpa using (e.lipschitz.isBounded_image hCbdd')
  have hCeq : e '' C' = C := by
    simpa [C'] using (Equiv.image_preimage (e := e.toEquiv) C)
  simpa [hCeq] using hCbdd

/-- The unit sublevel set of a norm gauge is symmetric, closed, bounded, convex, and contains `0`
in its interior. -/
lemma normGauge_sublevelOne_symmClosedBoundedConvex {n : ℕ} {k : (Fin n → ℝ) → EReal}
    (hk : IsNormGauge k) :
    let C := {x : Fin n → ℝ | k x ≤ (1 : EReal)};
      IsClosed C ∧
        Convex ℝ C ∧
          Bornology.IsBounded C ∧
            (0 : Fin n → ℝ) ∈ interior C ∧ (∀ x, x ∈ C → -x ∈ C) := by
  classical
  have hk' : IsNormGauge k := hk
  rcases hk with ⟨hk_gauge, _hk_finite, hk_even, _hk_pos⟩
  let C : Set (Fin n → ℝ) := {x : Fin n → ℝ | k x ≤ (1 : EReal)}
  have hCconv : Convex ℝ C := IsGauge.convex_sublevel_one (k := k) hk_gauge
  have hCclosed : IsClosed C := by
    simpa [C] using (normGauge_sublevel_one_closed (k := k) hk')
  have hC0int : (0 : Fin n → ℝ) ∈ interior C := by
    simpa [C] using (normGauge_sublevel_one_zero_mem_interior (k := k) hk')
  have hsymm : ∀ x, x ∈ C → -x ∈ C := by
    intro x hx
    simpa [C, hk_even x] using hx
  have hCbdd : Bornology.IsBounded C := by
    simpa [C] using (normGauge_sublevel_one_bounded (k := k) hk')
  refine ⟨hCclosed, hCconv, hCbdd, hC0int, hsymm⟩

/-- The gauge of a symmetric closed bounded convex set with `0` in its interior is a norm gauge. -/
lemma gaugeFunctionEReal_isNormGauge_of_symmClosedBoundedConvex_zeroInterior {n : ℕ}
    {C : Set (Fin n → ℝ)} (hC_closed : IsClosed C) (hC_conv : Convex ℝ C)
    (hC_bdd : Bornology.IsBounded C) (hC0 : (0 : Fin n → ℝ) ∈ interior C)
    (hC_symm : ∀ x, x ∈ C → -x ∈ C) :
    IsNormGauge (fun x => (gaugeFunction C x : EReal)) := by
  classical
  have hC0mem : (0 : Fin n → ℝ) ∈ C := interior_subset hC0
  have hCabs :
      ∀ x : Fin n → ℝ, ∃ lam : ℝ, 0 ≤ lam ∧ x ∈ (fun y => lam • y) '' C :=
    absorbing_of_zero_mem_interior (C := C) hC_conv hC0
  have hGauge :
      IsGauge (fun x => (gaugeFunction C x : EReal)) :=
    gaugeFunctionEReal_isGauge_of_closed_convex_zeroMem_absorbing
      (C := C) hC_closed hC_conv hC0mem hCabs
  have hfinite : ∀ x, (gaugeFunction C x : EReal) ≠ ⊤ := by
    intro x
    rcases hCabs x with ⟨lam, hlam0, y, hyC, hxy⟩
    have hmem : lam ∈ {r : ℝ | 0 ≤ r ∧ ∃ y ∈ C, x = r • y} := ⟨hlam0, y, hyC, hxy.symm⟩
    have hle : gaugeFunction C x ≤ lam := by
      have hS_bdd : BddBelow {r : ℝ | 0 ≤ r ∧ ∃ y ∈ C, x = r • y} := by
        refine ⟨0, ?_⟩
        intro r hr
        exact hr.1
      exact csInf_le hS_bdd hmem
    have hle' : (gaugeFunction C x : EReal) ≤ (lam : EReal) := by
      exact_mod_cast hle
    intro htop
    have hle'' := hle'
    rw [htop] at hle''
    exact not_top_le_coe lam hle''
  have hsymm : ∀ x, (gaugeFunction C (-x) : EReal) = (gaugeFunction C x : EReal) := by
    intro x
    let S : (Fin n → ℝ) → Set ℝ :=
      fun z => {r : ℝ | 0 ≤ r ∧ ∃ y ∈ C, z = r • y}
    have hS : S (-x) = S x := by
      ext r
      constructor
      · intro hr
        rcases hr with ⟨hr0, y, hyC, hxy⟩
        refine ⟨hr0, -y, hC_symm y hyC, ?_⟩
        calc
          x = -(-x) := by simp
          _ = -(r • y) := by simp [hxy]
          _ = r • (-y) := by simp [smul_neg]
      · intro hr
        rcases hr with ⟨hr0, y, hyC, hxy⟩
        refine ⟨hr0, -y, hC_symm y hyC, ?_⟩
        calc
          -x = -(r • y) := by simp [hxy]
          _ = r • (-y) := by simp [smul_neg]
    simp [gaugeFunction, S, hS]
  have hpos : ∀ x, x ≠ 0 → (0 : EReal) < (gaugeFunction C x : EReal) := by
    rcases hC_bdd.exists_pos_norm_le with ⟨R, hRpos, hR⟩
    intro x hx0
    let S : Set ℝ := {r : ℝ | 0 ≤ r ∧ ∃ y ∈ C, x = r • y}
    have hS_nonempty : S.Nonempty := by
      rcases hCabs x with ⟨r, hr0, y, hyC, hxy⟩
      exact ⟨r, hr0, y, hyC, hxy.symm⟩
    have hS_bdd : BddBelow S := by
      refine ⟨0, ?_⟩
      intro r hr
      exact hr.1
    have hlower : ‖x‖ / R ≤ sInf S := by
      refine le_csInf hS_nonempty ?_
      intro r hr
      rcases hr with ⟨hr0, y, hyC, hxy⟩
      have hybound : ‖y‖ ≤ R := hR y hyC
      have hxnorm : ‖x‖ = r * ‖y‖ := by
        calc
          ‖x‖ = ‖r • y‖ := by simp [hxy]
          _ = |r| * ‖y‖ := by simpa using norm_smul r y
          _ = r * ‖y‖ := by simp [abs_of_nonneg hr0]
      have hxle : ‖x‖ ≤ r * R := by
        calc
          ‖x‖ = r * ‖y‖ := hxnorm
          _ ≤ r * R := mul_le_mul_of_nonneg_left hybound hr0
      have hRne : R ≠ 0 := ne_of_gt hRpos
      have hRinv_nonneg : 0 ≤ (1 / R) := by
        exact one_div_nonneg.mpr (le_of_lt hRpos)
      have hxle' : ‖x‖ / R ≤ r := by
        calc
          ‖x‖ / R = ‖x‖ * (1 / R) := by simp [div_eq_mul_inv]
          _ ≤ r * R * (1 / R) := by
            exact mul_le_mul_of_nonneg_right hxle hRinv_nonneg
          _ = r := by field_simp [hRne, mul_comm, mul_left_comm, mul_assoc]
      exact hxle'
    have hpos_real : 0 < gaugeFunction C x := by
      have hxnorm_pos : 0 < ‖x‖ := by
        exact norm_pos_iff.mpr hx0
      have hdiv_pos : 0 < ‖x‖ / R := by
        exact div_pos hxnorm_pos hRpos
      have hle : ‖x‖ / R ≤ gaugeFunction C x := by
        simpa [gaugeFunction, S] using hlower
      exact lt_of_lt_of_le hdiv_pos hle
    exact_mod_cast hpos_real
  exact ⟨hGauge, hfinite, hsymm, hpos⟩

/-- The support function of a symmetric closed bounded convex set with `0` in its interior is a
norm gauge. -/
lemma supportFunctionEReal_isNormGauge_of_symmClosedBoundedConvex_zeroInterior {n : ℕ}
    {C : Set (Fin n → ℝ)} (hCne : C.Nonempty) (hC_conv : Convex ℝ C)
    (hC_bdd : Bornology.IsBounded C) (hC0 : (0 : Fin n → ℝ) ∈ interior C)
    (hC_symm : ∀ x, x ∈ C → -x ∈ C) :
    IsNormGauge (supportFunctionEReal C) := by
  classical
  have hCabs :
      ∀ x : Fin n → ℝ, ∃ lam : ℝ, 0 ≤ lam ∧ x ∈ (fun y => lam • y) '' C :=
    absorbing_of_zero_mem_interior (C := C) hC_conv hC0
  have hpol :
      polarGauge (fun x => (gaugeFunction C x : EReal)) = supportFunctionEReal C :=
    polarGauge_gaugeFunction_eq_supportFunctionEReal (C := C) hCne hCabs
  have hGauge : IsGauge (supportFunctionEReal C) := by
    simpa [hpol] using (polarGauge_isGauge (k := fun x => (gaugeFunction C x : EReal)))
  have hfinite : ∀ x, supportFunctionEReal C x ≠ ⊤ := by
    intro x
    exact section13_supportFunctionEReal_ne_top_of_isBounded (C := C) hC_bdd x
  have hsymm : ∀ x, supportFunctionEReal C (-x) = supportFunctionEReal C x := by
    intro x
    have hset :
        {z : EReal | ∃ y ∈ C, z = ((dotProduct y (-x) : ℝ) : EReal)} =
          {z : EReal | ∃ y ∈ C, z = ((dotProduct y x : ℝ) : EReal)} := by
      ext z
      constructor
      · rintro ⟨y, hyC, rfl⟩
        refine ⟨-y, hC_symm y hyC, ?_⟩
        simp [dotProduct_neg, neg_dotProduct]
      · rintro ⟨y, hyC, rfl⟩
        refine ⟨-y, hC_symm y hyC, ?_⟩
        simp [dotProduct_neg, neg_dotProduct]
    unfold supportFunctionEReal
    exact congrArg sSup hset
  have hpos : ∀ x, x ≠ 0 → (0 : EReal) < supportFunctionEReal C x := by
    have hpos' :=
      (section13_zero_mem_interior_iff_forall_supportFunctionEReal_pos
        (n := n) (C := C) hC_conv hCne).1 hC0
    intro x hx
    exact hpos' x hx
  exact ⟨hGauge, hfinite, hsymm, hpos⟩

/-- The polar gauge of a norm gauge is the support function of its unit sublevel set. -/
lemma polarGauge_eq_supportFunctionEReal_unitSublevel {n : ℕ} {k : (Fin n → ℝ) → EReal}
    (hk : IsNormGauge k) :
    let C := {x : Fin n → ℝ | k x ≤ (1 : EReal)};
      polarGauge k = supportFunctionEReal C := by
  classical
  intro C
  have hk_finite : ∀ x, k x ≠ ⊤ := hk.2.1
  have hk_pos : ∀ x, x ≠ 0 → (0 : EReal) < k x := hk.2.2.2
  rcases hk.1 with ⟨hk_conv, hk_nonneg, hk_hom, hk0⟩
  have hCne : C.Nonempty := IsGauge.sublevel_one_nonempty (k := k) hk.1
  have hC0 : (0 : Fin n → ℝ) ∈ C := by
    simp [C, hk0]
  have hCabs :
      ∀ x : Fin n → ℝ, ∃ lam : ℝ, 0 ≤ lam ∧ x ∈ (fun y => lam • y) '' C := by
    intro x
    by_cases hx0 : x = 0
    · refine ⟨0, le_rfl, ?_⟩
      refine ⟨0, hC0, by simp [hx0]⟩
    · have hxpos : (0 : EReal) < k x := hk_pos x hx0
      have hx_top : k x ≠ ⊤ := hk_finite x
      have hx_bot : k x ≠ (⊥ : EReal) := IsGauge.ne_bot ⟨hk_conv, hk_nonneg, hk_hom, hk0⟩ x
      set r : ℝ := (k x).toReal
      have hrpos : 0 < r := EReal.toReal_pos hxpos hx_top
      have hreq : k x = (r : EReal) := by
        simpa [r] using (EReal.coe_toReal (x := k x) hx_top hx_bot).symm
      refine ⟨r, le_of_lt hrpos, ?_⟩
      refine ⟨(r⁻¹) • x, ?_, ?_⟩
      · have hhom : k (r⁻¹ • x) = ((r⁻¹ : ℝ) : EReal) * k x := by
          simpa using hk_hom x r⁻¹ (inv_nonneg.mpr (le_of_lt hrpos))
        have hEq : k (r⁻¹ • x) = (1 : EReal) := by
          calc
            k (r⁻¹ • x) = ((r⁻¹ : ℝ) : EReal) * k x := hhom
            _ = ((r⁻¹ : ℝ) : EReal) * (r : EReal) := by
              exact congrArg (fun z => ((r⁻¹ : ℝ) : EReal) * z) hreq
            _ = (1 : EReal) := by
                have hrne : r ≠ 0 := ne_of_gt hrpos
                have hmul : ((r⁻¹ * r : ℝ)) = 1 := by
                  field_simp [hrne]
                calc
                  ((r⁻¹ : ℝ) : EReal) * (r : EReal) = ((r⁻¹ * r : ℝ) : EReal) := by
                    exact (EReal.coe_mul r⁻¹ r).symm
                  _ = (1 : EReal) := by simp [hmul]
        have hle : k (r⁻¹ • x) ≤ (1 : EReal) := by
          exact le_of_eq hEq
        change k (r⁻¹ • x) ≤ (1 : EReal)
        exact hle
      · have hrne : r ≠ 0 := ne_of_gt hrpos
        simp [smul_smul, hrne, r]
  have hk_eq :
      (fun x => (gaugeFunction C x : EReal)) = k :=
    IsGauge.gaugeFunction_sublevel_one_eq (k := k) hk.1 hk_finite
  have hpol :
      polarGauge (fun x => (gaugeFunction C x : EReal)) = supportFunctionEReal C :=
    polarGauge_gaugeFunction_eq_supportFunctionEReal (C := C) hCne hCabs
  simpa [hk_eq] using hpol

/-- Theorem 15.2: The relations `k(x) = γ(x | C)` and `C = {x ∈ ℝ^n | k x ≤ 1}` define a
one-to-one correspondence between norms `k` on `ℝ^n` and symmetric closed bounded convex sets
`C ⊆ ℝ^n` such that `0 ∈ interior C`.

In this development, `ℝ^n` is `Fin n → ℝ`; the unit ball of `k` is `{x | k x ≤ 1}`; and
`γ(x | C)` is represented by `fun x => (gaugeFunction C x : EReal)`. -/
noncomputable def normGaugeEquiv_symmClosedBoundedConvex {n : ℕ} :
    {k : (Fin n → ℝ) → EReal // IsNormGauge k} ≃
      {C : Set (Fin n → ℝ) //
          IsClosed C ∧
            Convex ℝ C ∧
              Bornology.IsBounded C ∧
                (0 : Fin n → ℝ) ∈ interior C ∧ (∀ x, x ∈ C → -x ∈ C)} := by
  classical
  refine
    { toFun := fun k =>
        ⟨{x : Fin n → ℝ | k.1 x ≤ (1 : EReal)}, ?_⟩
      invFun := fun C =>
        ⟨(fun x => (gaugeFunction C.1 x : EReal)),
          gaugeFunctionEReal_isNormGauge_of_symmClosedBoundedConvex_zeroInterior
            (C := C.1) C.2.1 C.2.2.1 C.2.2.2.1 C.2.2.2.2.1
            (by
              intro x hx
              exact C.2.2.2.2.2 x hx)⟩
      left_inv := by
        intro k
        apply Subtype.ext
        funext x
        have hk_eq :
            (fun x => (gaugeFunction {x : Fin n → ℝ | k.1 x ≤ (1 : EReal)} x : EReal)) = k.1 :=
          IsGauge.gaugeFunction_sublevel_one_eq (k := k.1) k.2.1 k.2.2.1
        simpa using congrArg (fun f => f x) hk_eq
      right_inv := by
        intro C
        apply Subtype.ext
        have hCabs :
            ∀ x : Fin n → ℝ, ∃ lam : ℝ, 0 ≤ lam ∧ x ∈ (fun y => lam • y) '' C.1 :=
          absorbing_of_zero_mem_interior (C := C.1) C.2.2.1 C.2.2.2.2.1
        have hC0 : (0 : Fin n → ℝ) ∈ C.1 := interior_subset C.2.2.2.2.1
        have hset :
            C.1 = {x : Fin n → ℝ | (gaugeFunction C.1 x : EReal) ≤ (1 : EReal)} :=
          set_eq_gaugeFunction_sublevel_one (D := C.1) C.2.1 C.2.2.1 hC0 hCabs
        change
          {x : Fin n → ℝ | (gaugeFunction C.1 x : EReal) ≤ (1 : EReal)} = C.1
        exact hset.symm }
  ·
    have h :=
      normGauge_sublevelOne_symmClosedBoundedConvex (k := k.1) k.2
    simpa using h

/-- Theorem 15.2 (polar): Under the norm/set correspondence of Theorem 15.2, the polar of a norm
is a norm. In this development, the polar of `k` is `polarGauge k`. -/
theorem polarGauge_isNormGauge {n : ℕ} {k : (Fin n → ℝ) → EReal} (hk : IsNormGauge k) :
    IsNormGauge (polarGauge k) := by
  classical
  have hC :=
    normGauge_sublevelOne_symmClosedBoundedConvex (k := k) hk
  dsimp at hC
  rcases hC with ⟨hCclosed, hCconv, hCbdd, hC0int, hCsymm⟩
  have hCne : ({x : Fin n → ℝ | k x ≤ (1 : EReal)}).Nonempty := by
    exact IsGauge.sublevel_one_nonempty (k := k) hk.1
  have hpol :
      polarGauge k = supportFunctionEReal {x : Fin n → ℝ | k x ≤ (1 : EReal)} :=
    (polarGauge_eq_supportFunctionEReal_unitSublevel (k := k) hk)
  have hnorm :
      IsNormGauge
        (supportFunctionEReal {x : Fin n → ℝ | k x ≤ (1 : EReal)}) :=
    supportFunctionEReal_isNormGauge_of_symmClosedBoundedConvex_zeroInterior
      (C := {x : Fin n → ℝ | k x ≤ (1 : EReal)}) hCne hCconv hCbdd hC0int hCsymm
  simpa [hpol] using hnorm

/-- Text 15.0.13: Define `k : ℝⁿ → [0, +∞)` by
`k(x) = max {|ξ₁|, …, |ξₙ|}` for `x = (ξ₁, …, ξₙ)`.

Then `k` is a norm, and its polar gauge `k^∘` is the `ℓ₁`-norm:
`k^∘(x⋆) = |ξ₁⋆| + ⋯ + |ξₙ⋆|` for `x⋆ = (ξ₁⋆, …, ξₙ⋆)`.
Consequently, `k` and `k^∘` form a polar pair of norms.

In this development, `ℝⁿ` is `Fin n → ℝ`, and we model real-valued norms as `EReal`-valued
functions via coercion `ℝ → EReal`. -/
noncomputable def linftyNormEReal {n : ℕ} (x : Fin n → ℝ) : EReal :=
  ((‖x‖ : ℝ) : EReal)

noncomputable def l1NormEReal {n : ℕ} (x : Fin n → ℝ) : EReal :=
  ((∑ i, |x i|) : ℝ)

/-- The sign function satisfies `sign r * r = |r|`. -/
lemma real_sign_mul_self_eq_abs (r : ℝ) : Real.sign r * r = |r| := by
  by_cases hr : r = 0
  · simp [hr]
  · rcases lt_or_gt_of_ne hr with hneg | hpos
    · simp [Real.sign_of_neg hneg, abs_of_neg hneg]
    · simp [Real.sign_of_pos hpos, abs_of_pos hpos]

/-- The absolute value of `Real.sign` is bounded by `1`. -/
lemma abs_sign_le_one (r : ℝ) : |Real.sign r| ≤ (1 : ℝ) := by
  rcases Real.sign_apply_eq r with hneg | hzero | hpos
  · simp [hneg]
  · simp [hzero]
  · simp [hpos]

/-- The support function of the `ℓ∞` unit ball is the `ℓ1` norm. -/
lemma supportFunctionEReal_linftyUnitBall_eq_l1NormEReal {n : ℕ} :
    let C : Set (Fin n → ℝ) := {x | (‖x‖ : ℝ) ≤ 1};
    supportFunctionEReal C = l1NormEReal (n := n) := by
  classical
  intro C
  funext xStar
  apply le_antisymm
  ·
    refine (section13_supportFunctionEReal_le_coe_iff (C := C) (y := xStar)
      (μ := ∑ i, |xStar i|)).2 ?_
    intro x hx
    have hxnorm : ‖x‖ ≤ (1 : ℝ) := by
      simpa [C] using hx
    have hxi : ∀ i, |x i| ≤ (1 : ℝ) := by
      have h :=
        (pi_norm_le_iff_of_nonneg (x := x) (r := (1 : ℝ)) (by norm_num)).1 hxnorm
      intro i
      have h' : ‖x i‖ ≤ (1 : ℝ) := h i
      simpa [Real.norm_eq_abs] using h'
    calc
      dotProduct x xStar = ∑ i, x i * xStar i := by simp [dotProduct]
      _ ≤ ∑ i, |x i * xStar i| := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact le_abs_self _
      _ = ∑ i, |x i| * |xStar i| := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [abs_mul]
      _ ≤ ∑ i, |xStar i| := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hxi' : |x i| ≤ 1 := hxi i
        have hnonneg : 0 ≤ |xStar i| := abs_nonneg _
        have hle : |x i| * |xStar i| ≤ (1 : ℝ) * |xStar i| :=
          mul_le_mul_of_nonneg_right hxi' hnonneg
        simpa using hle
  ·
    let x : Fin n → ℝ := fun i => Real.sign (xStar i)
    have hxmem : x ∈ C := by
      have hxcomp : ∀ i, ‖x i‖ ≤ (1 : ℝ) := by
        intro i
        have : |Real.sign (xStar i)| ≤ (1 : ℝ) := abs_sign_le_one (xStar i)
        simpa [x, Real.norm_eq_abs] using this
      have hxnorm : ‖x‖ ≤ (1 : ℝ) :=
        (pi_norm_le_iff_of_nonneg (x := x) (r := (1 : ℝ)) (by norm_num)).2 hxcomp
      simpa [C] using hxnorm
    have hdot : dotProduct x xStar = ∑ i, |xStar i| := by
      simp [dotProduct, x, real_sign_mul_self_eq_abs]
    have hxle : ((∑ i, |xStar i| : ℝ) : EReal) ≤ supportFunctionEReal C xStar := by
      unfold supportFunctionEReal
      refine le_sSup ?_
      exact ⟨x, hxmem, by simp [hdot]⟩
    simpa [l1NormEReal] using hxle

/-- The support function of the `ℓ1` unit ball is the `ℓ∞` norm. -/
lemma supportFunctionEReal_l1UnitBall_eq_linftyNormEReal {n : ℕ} :
    let C : Set (Fin n → ℝ) := {x | (∑ i, |x i|) ≤ 1};
    supportFunctionEReal C = linftyNormEReal (n := n) := by
  classical
  cases n with
  | zero =>
      intro C
      funext xStar
      have hC0 : (0 : Fin 0 → ℝ) ∈ C := by
        simp [C]
      have hsupp : supportFunctionEReal C xStar = (0 : EReal) := by
        apply le_antisymm
        ·
          refine (section13_supportFunctionEReal_le_coe_iff (C := C) (y := xStar) (μ := 0)).2 ?_
          intro x hx
          simp [dotProduct]
        ·
          unfold supportFunctionEReal
          refine le_sSup ?_
          exact ⟨0, hC0, by simp [dotProduct]⟩
      have hnorm : linftyNormEReal (n := 0) xStar = (0 : EReal) := by
        have hx : xStar = 0 := Subsingleton.elim _ _
        simp [linftyNormEReal, hx]
      simp [hsupp, hnorm]
  | succ n =>
      intro C
      funext xStar
      apply le_antisymm
      ·
        refine (section13_supportFunctionEReal_le_coe_iff (C := C) (y := xStar)
          (μ := ‖xStar‖)).2 ?_
        intro x hx
        have hxsum : ∑ i, |x i| ≤ (1 : ℝ) := by
          simpa [C] using hx
        have hxi : ∀ i, |xStar i| ≤ ‖xStar‖ := by
          intro i
          have h := norm_le_pi_norm (f := xStar) i
          simpa [Real.norm_eq_abs] using h
        calc
          dotProduct x xStar = ∑ i, x i * xStar i := by simp [dotProduct]
          _ ≤ ∑ i, |x i * xStar i| := by
            refine Finset.sum_le_sum ?_
            intro i hi
            exact le_abs_self _
          _ = ∑ i, |x i| * |xStar i| := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [abs_mul]
          _ ≤ ∑ i, |x i| * ‖xStar‖ := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have hxi' : |xStar i| ≤ ‖xStar‖ := hxi i
            have hxnonneg : 0 ≤ |x i| := abs_nonneg _
            have hle : |x i| * |xStar i| ≤ |x i| * ‖xStar‖ :=
              mul_le_mul_of_nonneg_left hxi' hxnonneg
            simpa [mul_comm, mul_left_comm, mul_assoc] using hle
          _ = ‖xStar‖ * ∑ i, |x i| := by
            calc
              ∑ i, |x i| * ‖xStar‖ = ∑ i, ‖xStar‖ * |x i| := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                simp [mul_comm]
              _ = ‖xStar‖ * ∑ i, |x i| := by
                symm
                simp [Finset.mul_sum]
          _ ≤ ‖xStar‖ := by
            have hnonneg : 0 ≤ ‖xStar‖ := norm_nonneg _
            have hle : ‖xStar‖ * (∑ i, |x i|) ≤ ‖xStar‖ * 1 :=
              mul_le_mul_of_nonneg_left hxsum hnonneg
            simpa using hle
      ·
        have hne : (Finset.univ : Finset (Fin (Nat.succ n))).Nonempty := by
          exact ⟨0, by simp⟩
        set f : Fin (Nat.succ n) → NNReal := fun i => ‖xStar i‖₊
        rcases Finset.exists_mem_eq_sup (s := (Finset.univ : Finset (Fin (Nat.succ n)))) hne f with
          ⟨i0, hi0, hsup⟩
        have hnorm : ‖xStar‖ = (f i0 : ℝ) := by
          have hnorm0 : ‖xStar‖ = ((Finset.univ.sup f : NNReal) : ℝ) := by
            simpa [f] using (Pi.norm_def (f := xStar))
          simpa [hsup] using hnorm0
        let x : Fin (Nat.succ n) → ℝ := fun i => if i = i0 then Real.sign (xStar i0) else 0
        have hxsum : ∑ i, |x i| = |Real.sign (xStar i0)| := by
          classical
          have hxsum' :
              ∑ i ∈ (Finset.univ : Finset (Fin (Nat.succ n))), |x i| = |x i0| := by
            refine Finset.sum_eq_single i0 ?_ ?_
            · intro i hi hne
              simp [x, hne]
            · intro hne
              exact (hne (Finset.mem_univ i0)).elim
          simp [x, hxsum']
        have hxmem : x ∈ C := by
          have hsign_le : |Real.sign (xStar i0)| ≤ (1 : ℝ) := abs_sign_le_one (xStar i0)
          have hxle : ∑ i, |x i| ≤ (1 : ℝ) := by
            simpa [hxsum] using hsign_le
          simpa [C] using hxle
        have hdot : dotProduct x xStar = |xStar i0| := by
          classical
          have hsum' : ∑ i, x i * xStar i = Real.sign (xStar i0) * xStar i0 := by
            simp [x]
          have hdot' : dotProduct x xStar = Real.sign (xStar i0) * xStar i0 := by
            simpa [dotProduct] using hsum'
          simpa [real_sign_mul_self_eq_abs] using hdot'
        have hnorm' : ‖xStar‖ = |xStar i0| := by
          calc
            ‖xStar‖ = (f i0 : ℝ) := hnorm
            _ = ‖xStar i0‖ := by simp [f]
            _ = |xStar i0| := by simp [Real.norm_eq_abs]
        have hxle : ((‖xStar‖ : ℝ) : EReal) ≤ supportFunctionEReal C xStar := by
          unfold supportFunctionEReal
          refine le_sSup ?_
          exact ⟨x, hxmem, by simp [hdot, hnorm']⟩
        simpa [linftyNormEReal] using hxle

theorem linftyNormEReal_isNormGauge {n : ℕ} : IsNormGauge (linftyNormEReal (n := n)) := by
  have hconv :
      ConvexFunctionOn (S := (Set.univ : Set (Fin n → ℝ))) (linftyNormEReal (n := n)) := by
    have hconv' :
        ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) (fun x : Fin n → ℝ => ‖x‖) := by
      simpa using (convexOn_norm (s := (Set.univ : Set (Fin n → ℝ))) (hs := convex_univ))
    simpa [linftyNormEReal] using (convexFunctionOn_of_convexOn_real (S := Set.univ) hconv')
  have hnonneg : ∀ x, (0 : EReal) ≤ linftyNormEReal (n := n) x := by
    intro x
    simp [linftyNormEReal, norm_nonneg]
  have hhom :
      ∀ x (r : ℝ), 0 ≤ r →
        linftyNormEReal (n := n) (r • x) = (r : EReal) * linftyNormEReal (n := n) x := by
    intro x r hr
    simp [linftyNormEReal, norm_smul, abs_of_nonneg hr, EReal.coe_mul]
  have hzero : linftyNormEReal (n := n) (0 : Fin n → ℝ) = 0 := by
    simp [linftyNormEReal]
  have hGauge : IsGauge (linftyNormEReal (n := n)) := ⟨hconv, hnonneg, hhom, hzero⟩
  refine ⟨hGauge, ?_, ?_, ?_⟩
  · intro x
    simp [linftyNormEReal]
  · intro x
    simp [linftyNormEReal, norm_neg]
  · intro x hx0
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    simpa [linftyNormEReal] using (EReal.coe_lt_coe_iff.2 hxpos)

theorem polarGauge_linftyNormEReal {n : ℕ} :
    polarGauge (linftyNormEReal (n := n)) = l1NormEReal (n := n) := by
  classical
  have hk : IsNormGauge (linftyNormEReal (n := n)) := linftyNormEReal_isNormGauge (n := n)
  have hpol :
      polarGauge (linftyNormEReal (n := n)) =
        supportFunctionEReal {x : Fin n → ℝ | linftyNormEReal (n := n) x ≤ (1 : EReal)} :=
    polarGauge_eq_supportFunctionEReal_unitSublevel (k := linftyNormEReal (n := n)) hk
  have hsupport :
      supportFunctionEReal {x : Fin n → ℝ | linftyNormEReal (n := n) x ≤ (1 : EReal)} =
        l1NormEReal (n := n) := by
    have hset :
        {x : Fin n → ℝ | linftyNormEReal (n := n) x ≤ (1 : EReal)} =
          {x : Fin n → ℝ | ‖x‖ ≤ (1 : ℝ)} := by
      ext x
      change ((‖x‖ : ℝ) : EReal) ≤ ((1 : ℝ) : EReal) ↔ ‖x‖ ≤ (1 : ℝ)
      simpa using
        (EReal.coe_le_coe_iff :
          ((‖x‖ : ℝ) : EReal) ≤ ((1 : ℝ) : EReal) ↔ ‖x‖ ≤ (1 : ℝ))
    simpa [hset] using (supportFunctionEReal_linftyUnitBall_eq_l1NormEReal (n := n))
  simpa [hpol] using hsupport

theorem polarGauge_l1NormEReal {n : ℕ} : polarGauge (l1NormEReal (n := n)) = linftyNormEReal := by
  classical
  have hk : IsNormGauge (linftyNormEReal (n := n)) := linftyNormEReal_isNormGauge (n := n)
  have hl1 : IsNormGauge (l1NormEReal (n := n)) := by
    simpa [polarGauge_linftyNormEReal (n := n)] using
      (polarGauge_isNormGauge (k := linftyNormEReal (n := n)) hk)
  have hpol :
      polarGauge (l1NormEReal (n := n)) =
        supportFunctionEReal {x : Fin n → ℝ | l1NormEReal (n := n) x ≤ (1 : EReal)} :=
    polarGauge_eq_supportFunctionEReal_unitSublevel (k := l1NormEReal (n := n)) hl1
  have hsupport :
      supportFunctionEReal {x : Fin n → ℝ | l1NormEReal (n := n) x ≤ (1 : EReal)} =
        linftyNormEReal (n := n) := by
    have hset :
        {x : Fin n → ℝ | l1NormEReal (n := n) x ≤ (1 : EReal)} =
          {x : Fin n → ℝ | (∑ i, |x i|) ≤ (1 : ℝ)} := by
      ext x
      change ((∑ i, |x i| : ℝ) : EReal) ≤ ((1 : ℝ) : EReal) ↔ ∑ i, |x i| ≤ (1 : ℝ)
      simpa using
        (EReal.coe_le_coe_iff :
          ((∑ i, |x i| : ℝ) : EReal) ≤ ((1 : ℝ) : EReal) ↔ ∑ i, |x i| ≤ (1 : ℝ))
    simpa [hset] using (supportFunctionEReal_l1UnitBall_eq_linftyNormEReal (n := n))
  simpa [hpol] using hsupport

end Section15
end Chap03
