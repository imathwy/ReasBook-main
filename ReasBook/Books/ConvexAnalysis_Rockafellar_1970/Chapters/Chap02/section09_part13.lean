/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part12

noncomputable section
open scoped Pointwise
open scoped BigOperators
open scoped Topology
open scoped RealInnerProductSpace
open Filter

section Chap02
section Section09
/-- Corollary 9.7.1. Let `C` be a closed convex set in `ℝ^n` containing `0`. The gauge function
`gamma(· | C)` of `C` is closed. One has `{x | gamma(x | C) ≤ λ} = λ C` for any `λ > 0`, and
`{x | gamma(x | C) = 0} = 0^+ C`. -/
theorem gaugeFunction_closed_and_level_sets {n : Nat} {C : Set (Fin n → Real)}
    (hCclosed : IsClosed C) (hCconv : Convex Real C) (hC0 : (0 : Fin n → Real) ∈ C)
    (hCabs : ∀ x : Fin n → Real, ∃ lam : Real, 0 ≤ lam ∧ x ∈ (fun y => lam • y) '' C) :
    let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
    let C' : Set (EuclideanSpace Real (Fin n)) := Set.image e.symm C
    let recC : Set (Fin n → Real) := Set.image e (Set.recessionCone C')
    ClosedConvexFunction (fun x => (gaugeFunction C x : EReal)) ∧
      (∀ lam : Real, 0 < lam → {x : Fin n → Real | gaugeFunction C x ≤ lam} = lam • C) ∧
      {x : Fin n → Real | gaugeFunction C x = 0} = recC := by
  classical
  -- Unfold the `let`-bindings for `e`, `C'`, and `recC`.
  simp
  set e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
  set C' : Set (EuclideanSpace Real (Fin n)) := Set.image e.symm C
  set recC : Set (Fin n → Real) := Set.image e (Set.recessionCone C')
  -- Nonempty, closed, and convex hypotheses for the transported set.
  have hCne : Set.Nonempty C := ⟨0, hC0⟩
  have hC'ne : Set.Nonempty C' := by
    refine ⟨e.symm 0, ?_⟩
    exact ⟨0, hC0, by simp⟩
  have hC'closed : IsClosed C' := by
    let hhome := e.symm.toAffineEquiv.toHomeomorphOfFiniteDimensional
    have hclosed' : IsClosed ((hhome : _ → _) '' C) :=
      (hhome.isClosed_image (s := C)).2 hCclosed
    simpa [C', hhome, AffineEquiv.coe_toHomeomorphOfFiniteDimensional] using hclosed'
  have hC'conv : Convex Real C' := by
    simpa [C'] using hCconv.linear_image (e.symm.toLinearMap)
  -- The defining set for the gauge.
  let S : (Fin n → Real) → Set ℝ :=
    fun x => { r : ℝ | 0 ≤ r ∧ ∃ y ∈ C, x = r • y }
  have hS_nonempty : ∀ x, (S x).Nonempty := by
    intro x
    rcases hCabs x with ⟨lam, hlam, hxmem⟩
    rcases hxmem with ⟨y, hyC, rfl⟩
    exact ⟨lam, ⟨hlam, ⟨y, hyC, rfl⟩⟩⟩
  have hS_bdd : ∀ x, BddBelow (S x) := by
    intro x
    refine ⟨0, ?_⟩
    intro r hr
    exact hr.1
  have hgauge_eq : ∀ x, gaugeFunction C x = sInf (S x) := by
    intro x; simp [gaugeFunction, S]
  have hgauge_nonneg : ∀ x, 0 ≤ gaugeFunction C x := by
    intro x
    have hSne := hS_nonempty x
    have hle : 0 ≤ sInf (S x) :=
      le_csInf hSne (by intro r hr; exact hr.1)
    simpa [hgauge_eq x] using hle
  have hgauge_zero : gaugeFunction C (0 : Fin n → Real) = 0 := by
    have hS0 : (0 : ℝ) ∈ S (0 : Fin n → Real) := by
      refine ⟨le_rfl, ?_⟩
      exact ⟨0, hC0, by simp⟩
    have hle : sInf (S (0 : Fin n → Real)) ≤ 0 := csInf_le (hS_bdd _) hS0
    have hge : 0 ≤ sInf (S (0 : Fin n → Real)) :=
      le_csInf (hS_nonempty _) (by intro r hr; exact hr.1)
    have hEq : sInf (S (0 : Fin n → Real)) = 0 := le_antisymm hle hge
    simpa [hgauge_eq] using hEq
  -- `recC` equals the recession cone of `C`.
  have hrecC_eq : recC = Set.recessionCone C := by
    dsimp [recC, C']
    have hrec :
        Set.recessionCone (e.symm '' C) = e.symm '' Set.recessionCone C := by
      simpa using
        (recessionCone_image_linearEquiv (e := e.symm.toLinearEquiv) (C := C))
    calc
      e '' Set.recessionCone (e.symm '' C) = e '' (e.symm '' Set.recessionCone C) := by
        simp [hrec]
      _ = Set.recessionCone C := by
        simp [Set.image_image]
  -- Recession directions belong to every positive scaling.
  have hrec_smul : ∀ {x : Fin n → Real} {lam : Real}, 0 < lam →
      x ∈ recC → x ∈ lam • C := by
    intro x lam hlam hx
    have hx' : x ∈ Set.recessionCone C := by
      simpa [hrecC_eq] using hx
    have hmem : (1 / lam) • x ∈ C := by
      have := hx' (x := (0 : Fin n → Real)) hC0 (t := (1 / lam)) (by positivity)
      simpa using this
    have hlamne : lam ≠ 0 := ne_of_gt hlam
    refine ⟨(1 / lam) • x, hmem, ?_⟩
    simp [smul_smul, hlamne]
  -- `gauge = 0` implies membership in the recession cone.
  have hzero_subset_recC :
      {x : Fin n → Real | gaugeFunction C x = 0} ⊆ recC := by
    intro x hx
    have hSne := hS_nonempty x
    have hSbdd := hS_bdd x
    have hxinf : sInf (S x) = 0 := by
      simpa [hgauge_eq x] using hx
    rcases exists_seq_tendsto_sInf hSne hSbdd with ⟨r, hr_anti, hr_tendsto, hr_mem⟩
    have hr_tendsto0 : Filter.Tendsto r Filter.atTop (𝓝 (0 : ℝ)) := by
      simpa [hxinf] using hr_tendsto
    have hr_mem' : ∀ n, ∃ y ∈ C, x = r n • y := by
      intro n
      rcases hr_mem n with ⟨_, hy⟩
      exact hy
    classical
    choose y hyC hxy using hr_mem'
    have hlim : Filter.Tendsto (fun n => r n • y n) Filter.atTop (𝓝 x) := by
      have : (fun n => r n • y n) = fun _ => x := by
        funext n; simp [hxy n]
      simp [this]
    have hyC' : ∀ n, e.symm (y n) ∈ C' := by
      intro n
      exact ⟨y n, hyC n, by simp⟩
    have hlim' :
        Filter.Tendsto (fun n => r n • e.symm (y n)) Filter.atTop (𝓝 (e.symm x)) := by
      have hlim1 :
          Filter.Tendsto (fun n => e.symm (r n • y n)) Filter.atTop (𝓝 (e.symm x)) :=
        (e.symm.continuous.tendsto _).comp hlim
      simpa using hlim1
    have hxrec' : e.symm x ∈ Set.recessionCone C' := by
      refine seq_limits_subset_recessionCone (C := C') hC'ne hC'closed hC'conv ?_
      exact ⟨fun n => e.symm (y n), r, hyC', hr_anti, hr_tendsto0, hlim'⟩
    have hxrec : x ∈ recC := by
      refine ⟨e.symm x, hxrec', ?_⟩
      simp
    exact hxrec
  -- Recession directions give gauge zero.
  have hrec_subset_zero :
      recC ⊆ {x : Fin n → Real | gaugeFunction C x = 0} := by
    intro x hx
    have hx' : x ∈ Set.recessionCone C := by
      simpa [hrecC_eq] using hx
    have hle : ∀ ε : Real, 0 < ε → gaugeFunction C x ≤ ε := by
      intro ε hε
      have hmem : x ∈ ε • C := by
        have hmem' : (1 / ε) • x ∈ C := by
          have := hx' (x := (0 : Fin n → Real)) hC0 (t := (1 / ε)) (by positivity)
          simpa using this
        have hεne : ε ≠ 0 := ne_of_gt hε
        refine ⟨(1 / ε) • x, hmem', ?_⟩
        simp [smul_smul, hεne]
      rcases hmem with ⟨y, hyC, hxy⟩
      have hxy' : x = ε • y := by
        simpa [eq_comm] using hxy
      have hS : ε ∈ S x := ⟨le_of_lt hε, ⟨y, hyC, hxy'⟩⟩
      have hle' : sInf (S x) ≤ ε := csInf_le (hS_bdd x) hS
      simpa [hgauge_eq x] using hle'
    have hle0 : gaugeFunction C x ≤ 0 := by
      refine le_of_forall_pos_le_add ?_
      intro ε hε
      have hle' := hle ε hε
      simpa [add_comm, add_left_comm, add_assoc] using hle'
    have hge0 : 0 ≤ gaugeFunction C x := hgauge_nonneg x
    exact le_antisymm hle0 hge0
  have hrec_eq : {x : Fin n → Real | gaugeFunction C x = 0} = recC :=
    Set.Subset.antisymm hzero_subset_recC hrec_subset_zero
  -- Positive gauge values are attained.
  have hmem_S_of_pos :
      ∀ {x : Fin n → Real}, 0 < gaugeFunction C x →
        ∃ y ∈ C, x = gaugeFunction C x • y := by
    intro x hxpos
    have hx0 : x ≠ 0 := by
      intro hx0
      have : gaugeFunction C x = 0 := by simpa [hx0] using hgauge_zero
      exact (ne_of_gt hxpos) this
    have hSne := hS_nonempty x
    have hSbdd := hS_bdd x
    rcases exists_seq_tendsto_sInf hSne hSbdd with ⟨r, hr_anti, hr_tendsto, hr_mem⟩
    have hr_tendsto' : Filter.Tendsto r Filter.atTop (𝓝 (gaugeFunction C x)) := by
      simpa [hgauge_eq x] using hr_tendsto
    have hr_mem' : ∀ n, ∃ y ∈ C, x = r n • y := by
      intro n
      rcases hr_mem n with ⟨_, hy⟩
      exact hy
    classical
    choose y hyC hxy using hr_mem'
    have hr_ne : ∀ n, r n ≠ 0 := by
      intro n hzero
      have : x = 0 := by
        have hxy' := hxy n
        simpa [hzero] using hxy'
      exact hx0 this
    have hy_eq : ∀ n, y n = (r n)⁻¹ • x := by
      intro n
      have hrne := hr_ne n
      have hxy' : x = r n • y n := hxy n
      have : (r n)⁻¹ • x = y n := by
        calc
          (r n)⁻¹ • x = (r n)⁻¹ • (r n • y n) := by simp [hxy']
          _ = y n := by simp [smul_smul, hrne]
      simpa [eq_comm] using this
    have htendsto_inv :
        Filter.Tendsto (fun n => (r n)⁻¹) Filter.atTop
          (𝓝 ((gaugeFunction C x)⁻¹)) :=
      (tendsto_inv₀ (x := gaugeFunction C x) (ne_of_gt hxpos)).comp hr_tendsto'
    have htendsto_y :
        Filter.Tendsto y Filter.atTop (𝓝 ((gaugeFunction C x)⁻¹ • x)) := by
      have ht :
          Filter.Tendsto (fun n => (r n)⁻¹ • x) Filter.atTop
            (𝓝 ((gaugeFunction C x)⁻¹ • x)) :=
        htendsto_inv.smul_const x
      have hy_eq' : y = fun n => (r n)⁻¹ • x := by
        funext n
        simp [hy_eq n]
      simpa [hy_eq'] using ht
    have hmem : (gaugeFunction C x)⁻¹ • x ∈ C :=
      hCclosed.mem_of_tendsto htendsto_y (eventually_of_forall hyC)
    refine ⟨(gaugeFunction C x)⁻¹ • x, hmem, ?_⟩
    simp [smul_smul, ne_of_gt hxpos]
  -- Monotonicity of scalings.
  have hsmul_mono :
      ∀ {r lam : Real}, 0 ≤ r → r ≤ lam → 0 < lam →
        r • C ⊆ lam • C := by
    intro r lam hr hrlam hlam x hx
    rcases hx with ⟨y, hyC, rfl⟩
    by_cases hr0 : r = 0
    · subst hr0
      exact ⟨0, hC0, by simp⟩
    · have hratio0 : 0 ≤ r / lam := by
        exact div_nonneg hr (le_of_lt hlam)
      have hratio1 : r / lam ≤ 1 := by
        have hlamne : lam ≠ 0 := ne_of_gt hlam
        have : r ≤ lam := hrlam
        exact (div_le_one (by exact hlam)).2 this
      have hmem : (r / lam) • y ∈ C :=
        hCconv.smul_mem_of_zero_mem hC0 hyC ⟨hratio0, hratio1⟩
      have hlamne : lam ≠ 0 := ne_of_gt hlam
      refine ⟨(r / lam) • y, hmem, ?_⟩
      have hne : lam ≠ 0 := ne_of_gt hlam
      calc
        lam • ((r / lam) • y) = (lam * (r / lam)) • y := by
          simp [smul_smul]
        _ = r • y := by
          field_simp [hne]
  -- Sublevel sets.
  have hlevel :
      ∀ lam : Real, 0 < lam →
        {x : Fin n → Real | gaugeFunction C x ≤ lam} = lam • C := by
    intro lam hlam
    apply Set.Subset.antisymm
    · intro x hx
      by_cases hx0 : gaugeFunction C x = 0
      · have hxrec : x ∈ recC := by
          have : x ∈ {x : Fin n → Real | gaugeFunction C x = 0} := by simp [hx0]
          exact hzero_subset_recC this
        exact hrec_smul hlam hxrec
      · have hpos : 0 < gaugeFunction C x :=
          lt_of_le_of_ne (hgauge_nonneg x) (Ne.symm hx0)
        rcases hmem_S_of_pos hpos with ⟨y, hyC, hxy⟩
        have hxmem : x ∈ gaugeFunction C x • C := ⟨y, hyC, hxy.symm⟩
        exact hsmul_mono (hgauge_nonneg x) hx hlam hxmem
    · intro x hx
      rcases hx with ⟨y, hyC, rfl⟩
      have hS : lam ∈ S (lam • y) := ⟨le_of_lt hlam, ⟨y, hyC, rfl⟩⟩
      have hle : sInf (S (lam • y)) ≤ lam := csInf_le (hS_bdd _) hS
      simpa [hgauge_eq] using hle
  -- Closedness from explicit sublevel sets.
  have hclosed : ClosedConvexFunction (fun x => (gaugeFunction C x : EReal)) := by
    have hconv :
        ConvexFunction (fun x => (gaugeFunction C x : EReal)) := by
      have hnotbot :
          ∀ x ∈ (Set.univ : Set (Fin n → Real)),
            (gaugeFunction C x : EReal) ≠ (⊥ : EReal) := by
        intro x hx; simp
      have hineq :
          ∀ x ∈ (Set.univ : Set (Fin n → Real)),
            ∀ y ∈ (Set.univ : Set (Fin n → Real)),
              ∀ t : Real, 0 < t → t < 1 →
                (gaugeFunction C ((1 - t) • x + t • y) : EReal) ≤
                  ((1 - t : Real) : EReal) * (gaugeFunction C x : EReal) +
                    ((t : Real) : EReal) * (gaugeFunction C y : EReal) := by
        intro x hx y hy t ht0 ht1
        have hineq_real :
            gaugeFunction C ((1 - t) • x + t • y) ≤
              (1 - t) * gaugeFunction C x + t * gaugeFunction C y := by
          refine le_of_forall_pos_le_add ?_
          intro ε hε
          have hxlt :
              sInf (S x) < gaugeFunction C x + ε := by
            have : gaugeFunction C x < gaugeFunction C x + ε := by linarith
            simpa [hgauge_eq x] using this
          rcases (csInf_lt_iff (s := S x) (hb := hS_bdd x) (hs := hS_nonempty x)).1 hxlt with
            ⟨rx, hrxS, hrxlt⟩
          have hylt :
              sInf (S y) < gaugeFunction C y + ε := by
            have : gaugeFunction C y < gaugeFunction C y + ε := by linarith
            simpa [hgauge_eq y] using this
          rcases (csInf_lt_iff (s := S y) (hb := hS_bdd y) (hs := hS_nonempty y)).1 hylt with
            ⟨ry, hryS, hrylt⟩
          rcases hrxS with ⟨hrx0, ⟨ux, huxC, hux⟩⟩
          rcases hryS with ⟨hry0, ⟨uy, huyC, huy⟩⟩
          set r := (1 - t) * rx + t * ry
          have hle_r :
              gaugeFunction C ((1 - t) • x + t • y) ≤ r := by
            by_cases hr0 : r = 0
            · have hrx0' : rx = 0 := by nlinarith [hr0, hrx0, hry0, ht0, ht1]
              have hry0' : ry = 0 := by nlinarith [hr0, hrx0, hry0, ht0, ht1]
              have hx0 : x = 0 := by simp [hux, hrx0']
              have hy0 : y = 0 := by simp [huy, hry0']
              have hxy0 : (1 - t) • x + t • y = 0 := by simp [hx0, hy0]
              have hval : gaugeFunction C ((1 - t) • x + t • y) = 0 := by
                simpa [hxy0] using hgauge_zero
              simp [hr0, hval]
            · have hrpos : 0 < r := by
                have hpos1 : 0 < (1 - t) := sub_pos.mpr ht1
                have hpos2 : 0 < t := ht0
                have hr_nonneg : 0 ≤ r := by
                  have hpos1' : 0 ≤ (1 - t) := le_of_lt hpos1
                  have hpos2' : 0 ≤ t := le_of_lt hpos2
                  exact add_nonneg (mul_nonneg hpos1' hrx0) (mul_nonneg hpos2' hry0)
                exact lt_of_le_of_ne hr_nonneg (Ne.symm hr0)
              set a := (1 - t) * rx / r
              set b := t * ry / r
              have ha : 0 ≤ a := by
                have hnum : 0 ≤ (1 - t) * rx :=
                  mul_nonneg (sub_nonneg.mpr (le_of_lt ht1)) hrx0
                exact div_nonneg hnum (le_of_lt hrpos)
              have hb : 0 ≤ b := by
                have hnum : 0 ≤ t * ry := mul_nonneg (le_of_lt ht0) hry0
                exact div_nonneg hnum (le_of_lt hrpos)
              have hab : a + b = 1 := by
                have hne : r ≠ 0 := ne_of_gt hrpos
                dsimp [a, b]
                field_simp [hne]
                simp [r]
              have hcomb : a • ux + b • uy ∈ C :=
                hCconv huxC huyC ha hb hab
              have hxy :
                  (1 - t) • x + t • y = r • (a • ux + b • uy) := by
                have hmul_a : r * a = (1 - t) * rx := by
                  have hne : r ≠ 0 := ne_of_gt hrpos
                  dsimp [a]
                  field_simp [hne]
                have hmul_b : r * b = t * ry := by
                  have hne : r ≠ 0 := ne_of_gt hrpos
                  dsimp [b]
                  field_simp [hne]
                calc
                  (1 - t) • x + t • y
                      = (1 - t) • (rx • ux) + t • (ry • uy) := by simp [hux, huy]
                  _ = ((1 - t) * rx) • ux + (t * ry) • uy := by
                      simp [smul_smul, mul_comm]
                  _ = r • (a • ux + b • uy) := by
                      simp [smul_add, smul_smul, hmul_a, hmul_b]
              have hmem : (1 - t) • x + t • y ∈ r • C := by
                refine ⟨a • ux + b • uy, hcomb, hxy.symm⟩
              rcases hmem with ⟨z, hzC, hzx⟩
              have hS : r ∈ S ((1 - t) • x + t • y) :=
                ⟨le_of_lt hrpos, ⟨z, hzC, hzx.symm⟩⟩
              have hle : sInf (S ((1 - t) • x + t • y)) ≤ r :=
                csInf_le (hS_bdd _) hS
              simpa [hgauge_eq] using hle
          have hsum :
              r ≤ (1 - t) * gaugeFunction C x + t * gaugeFunction C y + ε := by
            have h1 : (1 - t) * rx ≤ (1 - t) * (gaugeFunction C x + ε) := by
              exact mul_le_mul_of_nonneg_left (le_of_lt hrxlt) (sub_nonneg.mpr (le_of_lt ht1))
            have h2 : t * ry ≤ t * (gaugeFunction C y + ε) := by
              exact mul_le_mul_of_nonneg_left (le_of_lt hrylt) (le_of_lt ht0)
            nlinarith [h1, h2]
          exact (hle_r.trans hsum)
        exact (EReal.coe_le_coe_iff).2 hineq_real
      have hconvOn :=
        (convexFunctionOn_iff_segment_inequality (C := (Set.univ : Set (Fin n → Real)))
          (f := fun x => (gaugeFunction C x : EReal)) (hC := convex_univ) hnotbot).2 hineq
      simp [ConvexFunction, hconvOn]
    have hls :
        LowerSemicontinuous (fun x => (gaugeFunction C x : EReal)) := by
      refine (lowerSemicontinuous_iff_closed_sublevel
        (f := fun x => (gaugeFunction C x : EReal))).2 ?_
      intro α
      by_cases hα : α < 0
      · have hset : {x : Fin n → Real | gaugeFunction C x ≤ α} = (∅ : Set (Fin n → Real)) := by
          ext x
          constructor
          · intro hx
            have hnonneg : 0 ≤ gaugeFunction C x := hgauge_nonneg x
            exact (not_le_of_gt (lt_of_lt_of_le hα hnonneg) hx).elim
          · intro hx
            exact (Set.notMem_empty _ hx).elim
        simp [hset]
      · have hα' : 0 ≤ α := le_of_not_gt hα
        by_cases hα0 : α = 0
        · subst hα0
          have hset0 :
              {x : Fin n → Real | gaugeFunction C x ≤ 0} =
                {x : Fin n → Real | gaugeFunction C x = 0} := by
            ext x
            constructor
            · intro hx
              exact le_antisymm hx (hgauge_nonneg x)
            · intro hx
              exact le_of_eq hx
          have hrec : IsClosed recC := by
            have hrec' : IsClosed (Set.recessionCone C') :=
              recessionCone_isClosed_of_closed (C := C') hC'closed
            have hrec'' : IsClosed recC := by
              let hhome := e.toAffineEquiv.toHomeomorphOfFiniteDimensional
              have hclosed' : IsClosed ((hhome : _ → _) '' Set.recessionCone C') :=
                (hhome.isClosed_image (s := Set.recessionCone C')).2 hrec'
              simpa [recC, hhome, AffineEquiv.coe_toHomeomorphOfFiniteDimensional] using hclosed'
            exact hrec''
          have hclosed0 : IsClosed {x : Fin n → Real | gaugeFunction C x = 0} := by
            simpa [hrec_eq] using hrec
          simpa [hset0] using hclosed0
        · have hpos : 0 < α := lt_of_le_of_ne hα' (Ne.symm hα0)
          have hset : {x : Fin n → Real | gaugeFunction C x ≤ α} = α • C :=
            hlevel α hpos
          have hne : (α : Real) ≠ 0 := ne_of_gt hpos
          simpa [hset] using (hCclosed.smul_of_ne_zero (c := α) hne)
    exact ⟨hconv, hls⟩
  exact ⟨hclosed, hlevel, hrec_eq⟩

end Section09
end Chap02
