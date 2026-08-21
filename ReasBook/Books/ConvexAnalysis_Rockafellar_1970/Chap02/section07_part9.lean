/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xinyi Guo, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section07_part8

noncomputable section
open scoped Topology

section Chap02
section Section07

lemma continuousOn_toReal_on_ri_effectiveDomain {n : Nat} {f : (Fin n → Real) → EReal}
    (hg : ConvexOn ℝ (effectiveDomain (Set.univ : Set (Fin n → Real)) f) (fun x => (f x).toReal)) :
    ContinuousOn (fun x : EuclideanSpace Real (Fin n) => (f x).toReal)
      (euclideanRelativeInterior n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f)) := by
  classical
  set C : Set (EuclideanSpace Real (Fin n)) :=
    (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
      effectiveDomain (Set.univ : Set (Fin n → Real)) f
  let A : EuclideanSpace Real (Fin n) →ₗ[Real] (Fin n → Real) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).toLinearMap
  have hconv' :
      ConvexOn ℝ (A ⁻¹' effectiveDomain (Set.univ : Set (Fin n → Real)) f)
        ((fun x => (f x).toReal) ∘ A) :=
    (ConvexOn.comp_linearMap (hf := hg) A)
  have hconv : ConvexOn ℝ C (fun x : EuclideanSpace Real (Fin n) => (f x).toReal) := by
    simpa [C, A, Function.comp, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using hconv'
  simpa [C] using (convexOn_continuousOn_ri_via_coordinateSubspace (C := C) (g := fun x =>
    (f x).toReal) hconv)

lemma convexFunction_continuousOn_ri_effectiveDomain_of_proper {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    ContinuousOn (fun x : EuclideanSpace Real (Fin n) => f x)
      (euclideanRelativeInterior n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f)) := by
  classical
  -- This is the fundamental continuity theorem for proper convex functions (see §10).
  have hfinite :
      ∀ x ∈
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f),
        f x ≠ (⊥ : EReal) ∧ f x ≠ (⊤ : EReal) :=
    properConvexFunctionOn_ne_top_on_ri_effectiveDomain (f := f) hf
  have hconv_toReal :
      ConvexOn ℝ (effectiveDomain (Set.univ : Set (Fin n → Real)) f) (fun x => (f x).toReal) :=
    convexOn_toReal_on_effectiveDomain (f := f) hf
  have hcont_toReal :
      ContinuousOn (fun x : EuclideanSpace Real (Fin n) => (f x).toReal)
        (euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :=
    continuousOn_toReal_on_ri_effectiveDomain (f := f) hconv_toReal
  exact continuousOn_ereal_of_toReal (f := fun x : EuclideanSpace Real (Fin n) => f x)
    hcont_toReal hfinite

/-- Remark 7.0.24: A convex function is continuous relative to `ri (dom f)`. -/
theorem convexFunction_continuousOn_ri_effectiveDomain {n : Nat}
    {f : (Fin n → Real) → EReal} (hf : ConvexFunction f) :
    ContinuousOn (fun x : EuclideanSpace Real (Fin n) => f x)
      (euclideanRelativeInterior n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f)) := by
  classical
  by_cases hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f
  · simpa using
      (convexFunction_continuousOn_ri_effectiveDomain_of_proper (f := f) hproper)
  · set s :
        Set (EuclideanSpace Real (Fin n)) :=
      euclideanRelativeInterior n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f) with hs
    have hconv : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
      simpa [ConvexFunction] using hf
    have himproper :
        ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := ⟨hconv, hproper⟩
    have hEq : Set.EqOn (fun x : EuclideanSpace Real (Fin n) => f x)
        (fun _ : EuclideanSpace Real (Fin n) => (⊥ : EReal)) s := by
      intro x hx
      have hbot :
          f x = (⊥ : EReal) := by
        simpa [hs] using
          improperConvexFunctionOn_eq_bot_on_ri_effectiveDomain (f := f) himproper x hx
      simp [hbot]
    have hconst :
        ContinuousOn (fun _ : EuclideanSpace Real (Fin n) => (⊥ : EReal)) s :=
      continuousOn_const
    have hcont := hconst.congr hEq
    simpa [hs] using hcont

/-- The segment map tends to its endpoint as `t → 1`. -/
lemma tendsto_segment_to_y {n : Nat} (x y : EuclideanSpace Real (Fin n)) :
    Filter.Tendsto (fun t : Real => (1 - t) • x + t • y) (𝓝 (1 : Real)) (𝓝 y) := by
  have hcont : Continuous (fun t : Real => (1 - t) • x + t • y) := by
    fun_prop
  have h_tendsto := hcont.tendsto (1 : Real)
  simpa using h_tendsto

/-- Liminf along the segment bounds the closure from below. -/
lemma liminf_along_segment_ge_closure {n : Nat} {f : (Fin n → Real) → EReal}
    {x y : EuclideanSpace Real (Fin n)}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    convexFunctionClosure f y ≤
      Filter.liminf (fun t : Real => f ((1 - t) • x + t • y))
        (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) := by
  have hls :
      LowerSemicontinuous (convexFunctionClosure f) :=
    (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri (f := f) hf).1.1.2
  have hle : convexFunctionClosure f ≤ f := convexFunctionClosure_le_self (f := f)
  have hliminf_y :
      convexFunctionClosure f y ≤
        Filter.liminf (fun z : Fin n → Real => f z) (𝓝 (y : Fin n → Real)) :=
    lowerSemicontinuous_le_liminf_of_le (f := f) (g := convexFunctionClosure f) hls hle y
  have h_tendsto :
      Filter.Tendsto (fun t : Real => (1 - t) • x + t • y) (𝓝 (1 : Real)) (𝓝 y) :=
    tendsto_segment_to_y x y
  have h_tendsto_within :
      Filter.Tendsto (fun t : Real => (1 - t) • x + t • y)
        (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) (𝓝 y) :=
    tendsto_nhdsWithin_of_tendsto_nhds h_tendsto
  have h_tendsto_within' :
      Filter.Tendsto (fun t : Real => (1 - t) • x.ofLp + t • y.ofLp)
        (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) (𝓝 y.ofLp) := by
    have hcoe :
        Filter.Tendsto (fun z : EuclideanSpace Real (Fin n) => (z : Fin n → Real)) (𝓝 y)
          (𝓝 y.ofLp) := by
      simpa using (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).continuous.tendsto y
    simpa using (hcoe.comp h_tendsto_within)
  have hnebot_within :
      (nhdsWithin (1 : Real) (Set.Iio (1 : Real))).NeBot := by
    have hclosure : (1 : Real) ∈ closure (Set.Iio (1 : Real)) := by
      simp [closure_Iio]
    exact (mem_closure_iff_nhdsWithin_neBot).1 hclosure
  have hnebot_map :
      (Filter.map (fun t : Real => (1 - t) • x + t • y)
          (nhdsWithin (1 : Real) (Set.Iio (1 : Real)))).NeBot :=
    Filter.NeBot.map hnebot_within _
  have hbound :
      (𝓝 (y : Fin n → Real)).IsBoundedUnder (· ≥ ·) (fun z : Fin n → Real => f z) := by
    refine Filter.isBoundedUnder_of ?_
    refine ⟨(⊥ : EReal), ?_⟩
    intro z
    exact bot_le
  have hbound_map :
      (Filter.map (fun t : Real => (1 - t) • x.ofLp + t • y.ofLp)
          (nhdsWithin (1 : Real) (Set.Iio (1 : Real)))).IsCoboundedUnder (· ≥ ·)
        (fun z : Fin n → Real => f z) := by
    haveI := hnebot_map
    refine Filter.isCoboundedUnder_ge_of_le
      (l := Filter.map (fun t : Real => (1 - t) • x.ofLp + t • y.ofLp)
        (nhdsWithin (1 : Real) (Set.Iio (1 : Real))))
      (f := fun z : Fin n → Real => f z) (x := (⊤ : EReal)) ?_
    intro z
    exact le_top
  have hliminf_map :
      Filter.liminf (fun z : Fin n → Real => f z) (𝓝 (y : Fin n → Real)) ≤
        Filter.liminf (fun z : Fin n → Real => f z)
          (Filter.map (fun t : Real => (1 - t) • x.ofLp + t • y.ofLp)
            (nhdsWithin (1 : Real) (Set.Iio (1 : Real)))) :=
    Filter.liminf_le_liminf_of_le h_tendsto_within' (hf := hbound) (hg := hbound_map)
  have hliminf_seg :
      convexFunctionClosure f y ≤
        Filter.liminf (fun z : Fin n → Real => f z)
          (Filter.map (fun t : Real => (1 - t) • x + t • y)
            (nhdsWithin (1 : Real) (Set.Iio (1 : Real)))) :=
    le_trans hliminf_y hliminf_map
  simpa [Function.comp] using hliminf_seg

/-- Upper bound for the limsup along a segment via the embedded epigraph. -/
lemma limsup_along_segment_le_beta {n : Nat} {f : (Fin n → Real) → EReal}
    {x y : EuclideanSpace Real (Fin n)}
    (hx :
      x ∈ euclideanRelativeInterior n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f))
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) {β : Real}
    (hβ : convexFunctionClosure f y ≤ (β : EReal)) :
    Filter.limsup (fun t : Real => f ((1 - t) • x + t • y))
        (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) ≤ (β : EReal) := by
  classical
  set C :
      Set (EuclideanSpace Real (Fin (n + 1))) :=
    (appendAffineEquiv n 1) ''
      ((fun p : (Fin n → Real) × Real =>
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => p.2))) ''
        epigraph (S := (Set.univ : Set (Fin n → Real))) f) with hC
  have hconv : ConvexFunction f := by
    simpa [ConvexFunction] using hf.1
  have hconv_C : Convex ℝ C := by
    simpa [hC] using (convex_embedded_epigraph (n := n) (f := f) hconv)
  have hbot : ∀ x, f x ≠ (⊥ : EReal) := by
    intro x
    exact hf.2.2 x (by simp)
  have hcl_epi :
      epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f) =
        closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) :=
    (epigraph_convexFunctionClosure_eq_closure_epigraph (f := f) hbot).1
  have hy_closure :
      ((y : Fin n → Real), β) ∈
        closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
    have hy_epi :
        ((y : Fin n → Real), β) ∈
          epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f) :=
      (mem_epigraph_univ_iff (f := convexFunctionClosure f)).2 hβ
    simpa [hcl_epi] using hy_epi
  let g : (Fin n → Real) × Real →
      (EuclideanSpace Real (Fin n) × EuclideanSpace Real (Fin 1)) :=
    fun p =>
      ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
          (fun _ : Fin 1 => p.2))
  let h : (Fin n → Real) × Real → EuclideanSpace Real (Fin (n + 1)) :=
    fun p => appendAffineEquiv n 1 (g p)
  have hcont_g1 :
      Continuous (fun p : (Fin n → Real) × Real =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1) := by
    simpa using
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm.continuous.comp continuous_fst
  have hcont_fun1 : Continuous (fun r : Real => (fun _ : Fin 1 => r)) := by
    refine continuous_pi ?_
    intro i
    simpa using (continuous_id : Continuous fun r : Real => r)
  have hcont_g2 :
      Continuous (fun p : (Fin n → Real) × Real =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => p.2)) := by
    have hcont_fun' :
        Continuous (fun p : (Fin n → Real) × Real => (fun _ : Fin 1 => p.2)) :=
      hcont_fun1.comp continuous_snd
    simpa using
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm.continuous.comp hcont_fun'
  have hcont_g : Continuous g := hcont_g1.prodMk hcont_g2
  have hcont_append :
      Continuous
        (fun q : EuclideanSpace Real (Fin n) × EuclideanSpace Real (Fin 1) =>
          appendAffineEquiv n 1 q) := by
    simpa using (AffineEquiv.continuous_of_finiteDimensional (f := appendAffineEquiv n 1))
  have hcont_h : Continuous h := hcont_append.comp hcont_g
  have hyC :
      h ((y : Fin n → Real), β) ∈ closure C := by
    have hy_image : h ((y : Fin n → Real), β) ∈ h '' closure
        (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
      exact ⟨((y : Fin n → Real), β), hy_closure, rfl⟩
    have hy_closure_image :
        h ((y : Fin n → Real), β) ∈
          closure (h '' epigraph (S := (Set.univ : Set (Fin n → Real))) f) :=
      (image_closure_subset_closure_image hcont_h) hy_image
    simpa [h, g, hC, Set.image_image] using hy_closure_image
  have hxfinite :
      f x ≠ (⊥ : EReal) ∧ f x ≠ (⊤ : EReal) :=
    properConvexFunctionOn_ne_top_on_ri_effectiveDomain (f := f) hf x hx
  have hx_top : f x < (⊤ : EReal) := (lt_top_iff_ne_top).2 hxfinite.2
  rcases EReal.exists_between_coe_real hx_top with ⟨α, hfxα, hαtop⟩
  set p_xα : EuclideanSpace Real (Fin (n + 1)) :=
    appendAffineEquiv n 1
      ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real),
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
          (fun _ : Fin 1 => α)) with hp_xα
  set p_yβ : EuclideanSpace Real (Fin (n + 1)) :=
    appendAffineEquiv n 1
      ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (y : Fin n → Real),
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
          (fun _ : Fin 1 => β)) with hp_yβ
  have hri_xα : p_xα ∈ riEpigraph f := by
    have hxri' :
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real) ∈
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
      simpa using hx
    have hxmem :
        (appendAffineEquiv n 1)
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real),
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => α)) ∈ riEpigraph f := by
      exact (riEpigraph_mem_iff (n := n) (f := f) hconv (x : Fin n → Real) α).2
        ⟨hxri', hfxα, hαtop⟩
    simpa [hp_xα] using hxmem
  have hyC' : p_yβ ∈ closure C := by
    simpa [hp_yβ, h, g] using hyC
  have hineq :
      ∀ t, 0 ≤ t → t < (1 : Real) →
        f ((1 - t) • x + t • y) < (((1 - t) * α + t * β : Real) : EReal) := by
    intro t ht0 ht1
    have hri_xα' : p_xα ∈ euclideanRelativeInterior (n + 1) C := by
      simpa [riEpigraph, hC, hp_xα] using hri_xα
    have hri_comb :
        (1 - t) • p_xα + t • p_yβ ∈ euclideanRelativeInterior (n + 1) C :=
      euclideanRelativeInterior_convex_combination_mem (n := n + 1) C hconv_C p_xα p_yβ
        hri_xα' hyC' t ht0 ht1
    have hri_comb' : (1 - t) • p_xα + t • p_yβ ∈ riEpigraph f := by
      simpa [riEpigraph, hC] using hri_comb
    have hcomb_repr :
        (appendAffineEquiv n 1)
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
                ((1 - t) • (x : Fin n → Real) + t • (y : Fin n → Real)),
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => (1 - t) * α + t * β)) =
          (1 - t) • p_xα + t • p_yβ := by
      have hline :=
        (AffineEquiv.apply_lineMap (appendAffineEquiv n 1)
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real),
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => α))
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (y : Fin n → Real),
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => β)) t)
      simpa [hp_xα, hp_yβ, AffineMap.lineMap_apply_module, map_add, map_smul] using hline
    have hri_repr :
        (appendAffineEquiv n 1)
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
                ((1 - t) • (x : Fin n → Real) + t • (y : Fin n → Real)),
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => (1 - t) * α + t * β)) ∈ riEpigraph f := by
      rw [hcomb_repr]
      exact hri_comb'
    have hineq' :
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
              ((1 - t) • (x : Fin n → Real) + t • (y : Fin n → Real)) ∈
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → Real)) f) ∧
          f ((1 - t) • (x : Fin n → Real) + t • (y : Fin n → Real)) <
            (((1 - t) * α + t * β : Real) : EReal) ∧
          (((1 - t) * α + t * β : Real) : EReal) < ⊤ :=
      (riEpigraph_mem_iff (n := n) (f := f) hconv
          ((1 - t) • (x : Fin n → Real) + t • (y : Fin n → Real))
          ((1 - t) * α + t * β)).1 hri_repr
    exact hineq'.2.1
  have hpos' : ∀ᶠ t in 𝓝 (1 : Real), 0 < t := by
    simpa using (Ioi_mem_nhds (a := (0 : Real)) (b := (1 : Real)) (by linarith))
  have hpos : ∀ᶠ t in nhdsWithin (1 : Real) (Set.Iio (1 : Real)), 0 ≤ t := by
    exact (eventually_nhdsWithin_of_eventually_nhds hpos').mono (fun _ ht => le_of_lt ht)
  have hlt : ∀ᶠ t in nhdsWithin (1 : Real) (Set.Iio (1 : Real)), t < (1 : Real) := by
    exact eventually_nhdsWithin_of_forall (s := Set.Iio (1 : Real)) (a := (1 : Real))
      (fun t ht => ht)
  have h_eventually :
      ∀ᶠ t in nhdsWithin (1 : Real) (Set.Iio (1 : Real)),
        f ((1 - t) • x + t • y) ≤ (((1 - t) * α + t * β : Real) : EReal) := by
    refine (hpos.and hlt).mono ?_
    intro t ht
    exact le_of_lt (hineq t ht.1 ht.2)
  have hlimsup_le :
      Filter.limsup (fun t : Real => f ((1 - t) • x + t • y))
          (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) ≤
        Filter.limsup (fun t : Real =>
            (((1 - t) * α + t * β : Real) : EReal))
          (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) :=
    Filter.limsup_le_limsup h_eventually
  have h_tendsto_real :
      Filter.Tendsto (fun t : Real => (1 - t) * α + t * β)
        (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) (𝓝 β) := by
    have hcont : Continuous (fun t : Real => (1 - t) * α + t * β) := by
      have h1 : Continuous (fun t : Real => (1 - t) * α) :=
        (continuous_const.sub continuous_id).mul continuous_const
      have h2 : Continuous (fun t : Real => t * β) :=
        continuous_id.mul continuous_const
      simpa using h1.add h2
    have hcont_at : ContinuousAt (fun t : Real => (1 - t) * α + t * β) (1 : Real) :=
      hcont.continuousAt
    have h_tendsto :
        Filter.Tendsto (fun t : Real => (1 - t) * α + t * β) (𝓝 (1 : Real))
          (𝓝 ((1 - (1 : Real)) * α + (1 : Real) * β)) := hcont_at.tendsto
    have h_tendsto' :
        Filter.Tendsto (fun t : Real => (1 - t) * α + t * β) (𝓝 (1 : Real)) (𝓝 β) := by
      simpa using h_tendsto
    exact tendsto_nhdsWithin_of_tendsto_nhds h_tendsto'
  have h_tendsto_ereal :
      Filter.Tendsto (fun t : Real =>
          (((1 - t) * α + t * β : Real) : EReal))
        (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) (𝓝 (β : EReal)) := by
    exact (EReal.tendsto_coe.2 h_tendsto_real)
  have hlimsup_eq :
      Filter.limsup (fun t : Real =>
            (((1 - t) * α + t * β : Real) : EReal))
        (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) = (β : EReal) :=
    Filter.Tendsto.limsup_eq h_tendsto_ereal
  calc
    Filter.limsup (fun t : Real => f ((1 - t) • x + t • y))
        (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) ≤
      Filter.limsup (fun t : Real =>
          (((1 - t) * α + t * β : Real) : EReal))
        (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) := hlimsup_le
    _ = (β : EReal) := hlimsup_eq

/-- Theorem 7.5. Let `f` be a proper convex function, and let `x ∈ ri (dom f)`. Then
`(cl f)(y) = lim_{λ ↑ 1} f((1 - λ)x + λ y)` for every `y`. (The formula is also valid
when `f` is improper and `y ∈ cl (dom f)`.) -/
theorem convexFunctionClosure_eq_limit_along_segment {n : Nat}
    {f : (Fin n → Real) → EReal} {x : EuclideanSpace Real (Fin n)}
    (hx :
      x ∈ euclideanRelativeInterior n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    (ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f →
        ∀ y : EuclideanSpace Real (Fin n),
          Filter.Tendsto
            (fun t : Real => f ((1 - t) • x + t • y))
            (nhdsWithin (1 : Real) (Set.Iio (1 : Real)))
            (𝓝 (convexFunctionClosure f y))) ∧
    (ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f →
        ∀ y : EuclideanSpace Real (Fin n),
          y ∈ closure
              ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → Real)) f) →
            Filter.Tendsto
              (fun t : Real => f ((1 - t) • x + t • y))
              (nhdsWithin (1 : Real) (Set.Iio (1 : Real)))
              (𝓝 (convexFunctionClosure f y))) := by
  constructor
  · intro hf y
    have hliminf :
        convexFunctionClosure f y ≤
          Filter.liminf (fun t : Real => f ((1 - t) • x + t • y))
            (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) :=
      liminf_along_segment_ge_closure (f := f) (x := x) (y := y) hf
    have hproper_cl :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (convexFunctionClosure f) :=
      (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri (f := f) hf).1.2
    have hbot_ne : convexFunctionClosure f y ≠ (⊥ : EReal) :=
      hproper_cl.2.2 y (by simp)
    cases hcy : convexFunctionClosure f y using EReal.rec with
    | bot =>
        exact (hbot_ne hcy).elim
    | top =>
        have hlimsup :
            Filter.limsup (fun t : Real => f ((1 - t) • x + t • y))
                (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) ≤ (⊤ : EReal) :=
          le_top
        have hliminf' :
            (⊤ : EReal) ≤
              Filter.liminf (fun t : Real => f ((1 - t) • x + t • y))
                (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) := by
          simpa [hcy] using hliminf
        simpa [hcy] using
          (tendsto_of_le_liminf_of_limsup_le hliminf' hlimsup)
    | coe r =>
        have hlimsup :
            Filter.limsup (fun t : Real => f ((1 - t) • x + t • y))
                (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) ≤ (r : EReal) := by
          have hβ : convexFunctionClosure f y ≤ (r : EReal) := by
            simp [hcy]
          exact limsup_along_segment_le_beta (f := f) (x := x) (y := y) hx hf hβ
        have hliminf' :
            (r : EReal) ≤
              Filter.liminf (fun t : Real => f ((1 - t) • x + t • y))
                (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) := by
          simpa [hcy] using hliminf
        simpa [hcy] using
          (tendsto_of_le_liminf_of_limsup_le hliminf' hlimsup)
  · intro hf y hy
    have hbot_x :
        f x = (⊥ : EReal) :=
      improperConvexFunctionOn_eq_bot_on_ri_effectiveDomain (f := f) hf x hx
    have hcl :
        convexFunctionClosure f = (fun _ => (⊥ : EReal)) :=
      convexFunctionClosure_eq_bot_of_exists_bot (f := f) ⟨x, hbot_x⟩
    have hconv_dom :
        Convex ℝ (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
      effectiveDomain_convex (S := Set.univ) (f := f) hf.1
    let A : EuclideanSpace Real (Fin n) →ₗ[Real] (Fin n → Real) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).toLinearMap
    have hconv_pre :
        Convex ℝ
          (A ⁻¹' effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
      hconv_dom.linear_preimage A
    have h_eventually :
        ∀ᶠ t in nhdsWithin (1 : Real) (Set.Iio (1 : Real)),
          f ((1 - t) • x + t • y) = (⊥ : EReal) := by
      have hpos' : ∀ᶠ t in 𝓝 (1 : Real), 0 < t := by
        simpa using (Ioi_mem_nhds (a := (0 : Real)) (b := (1 : Real)) (by linarith))
      have hpos :
          ∀ᶠ t in nhdsWithin (1 : Real) (Set.Iio (1 : Real)), 0 ≤ t := by
        exact (eventually_nhdsWithin_of_eventually_nhds hpos').mono (fun _ ht => le_of_lt ht)
      have hlt :
          ∀ᶠ t in nhdsWithin (1 : Real) (Set.Iio (1 : Real)), t < (1 : Real) := by
        exact eventually_nhdsWithin_of_forall (s := Set.Iio (1 : Real)) (a := (1 : Real))
          (fun t ht => ht)
      refine (hpos.and hlt).mono ?_
      intro t ht
      have hxri' :
          (1 - t) • x + t • y ∈
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
        have hxri :
            x ∈
              euclideanRelativeInterior n
                (A ⁻¹' effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
          simpa [A, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using hx
        have hycl :
            y ∈ closure
                (A ⁻¹' effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
          simpa [A, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using hy
        have hxri' :
            (1 - t) • x + t • y ∈
              euclideanRelativeInterior n
                (A ⁻¹' effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
          euclideanRelativeInterior_convex_combination_mem n
            (A ⁻¹' effectiveDomain (Set.univ : Set (Fin n → Real)) f) hconv_pre x y hxri hycl
              t ht.1 ht.2
        simpa [A, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using hxri'
      simpa using
        improperConvexFunctionOn_eq_bot_on_ri_effectiveDomain (f := f) hf _ hxri'
    have hconst :
        Filter.Tendsto (fun _ : Real => (⊥ : EReal))
          (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) (𝓝 (⊥ : EReal)) :=
      tendsto_const_nhds
    have h_tendsto :
        Filter.Tendsto (fun t : Real => f ((1 - t) • x + t • y))
          (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) (𝓝 (⊥ : EReal)) :=
      hconst.congr' (by
        have h_eventually' :
            (fun t : Real => f ((1 - t) • x + t • y)) =ᶠ[nhdsWithin (1 : Real) (Set.Iio (1 : Real))]
              fun _ => (⊥ : EReal) := by
          simpa using h_eventually
        simpa using h_eventually'.symm)
    simpa [hcl] using h_tendsto

/-- Corollary 7.5.1. For a closed proper convex function `f`, one has
`f y = lim_{λ ↑ 1} f((1 - λ) x + λ y)` for every `x ∈ dom f` and every `y`. -/
theorem closedProperConvexFunction_eq_limit_along_segment {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hfclosed : ClosedConvexFunction f)
    (hfproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {x : EuclideanSpace Real (Fin n)}
    (hx :
      x ∈
        (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f) :
    ∀ y : EuclideanSpace Real (Fin n),
      Filter.Tendsto
        (fun t : Real => f ((1 - t) • x + t • y))
        (nhdsWithin (1 : Real) (Set.Iio (1 : Real)))
        (𝓝 (f y)) := by
  intro y
  have hliminf_y :
      f y ≤ Filter.liminf (fun z : Fin n → Real => f z) (𝓝 (y : Fin n → Real)) :=
    lowerSemicontinuous_le_liminf_of_le (f := f) (g := f) hfclosed.2 le_rfl y
  have h_tendsto :
      Filter.Tendsto (fun t : Real => (1 - t) • x + t • y) (𝓝 (1 : Real)) (𝓝 y) :=
    tendsto_segment_to_y x y
  have h_tendsto_within :
      Filter.Tendsto (fun t : Real => (1 - t) • x + t • y)
        (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) (𝓝 y) :=
    tendsto_nhdsWithin_of_tendsto_nhds h_tendsto
  have h_tendsto_within' :
      Filter.Tendsto (fun t : Real => (1 - t) • x.ofLp + t • y.ofLp)
        (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) (𝓝 y.ofLp) := by
    have hcoe :
        Filter.Tendsto (fun z : EuclideanSpace Real (Fin n) => (z : Fin n → Real)) (𝓝 y)
          (𝓝 y.ofLp) := by
      simpa using (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).continuous.tendsto y
    simpa using (hcoe.comp h_tendsto_within)
  have hnebot_within :
      (nhdsWithin (1 : Real) (Set.Iio (1 : Real))).NeBot := by
    have hclosure : (1 : Real) ∈ closure (Set.Iio (1 : Real)) := by
      simp [closure_Iio]
    exact (mem_closure_iff_nhdsWithin_neBot).1 hclosure
  have hnebot_map :
      (Filter.map (fun t : Real => (1 - t) • x + t • y)
          (nhdsWithin (1 : Real) (Set.Iio (1 : Real)))).NeBot :=
    Filter.NeBot.map hnebot_within _
  have hbound :
      (𝓝 (y : Fin n → Real)).IsBoundedUnder (· ≥ ·) (fun z : Fin n → Real => f z) := by
    refine Filter.isBoundedUnder_of ?_
    refine ⟨(⊥ : EReal), ?_⟩
    intro z
    exact bot_le
  have hbound_map :
      (Filter.map (fun t : Real => (1 - t) • x.ofLp + t • y.ofLp)
          (nhdsWithin (1 : Real) (Set.Iio (1 : Real)))).IsCoboundedUnder (· ≥ ·)
        (fun z : Fin n → Real => f z) := by
    haveI := hnebot_map
    refine Filter.isCoboundedUnder_ge_of_le
      (l := Filter.map (fun t : Real => (1 - t) • x.ofLp + t • y.ofLp)
        (nhdsWithin (1 : Real) (Set.Iio (1 : Real))))
      (f := fun z : Fin n → Real => f z) (x := (⊤ : EReal)) ?_
    intro z
    exact le_top
  have hliminf_map :
      Filter.liminf (fun z : Fin n → Real => f z) (𝓝 (y : Fin n → Real)) ≤
        Filter.liminf (fun z : Fin n → Real => f z)
          (Filter.map (fun t : Real => (1 - t) • x.ofLp + t • y.ofLp)
            (nhdsWithin (1 : Real) (Set.Iio (1 : Real)))) :=
    Filter.liminf_le_liminf_of_le h_tendsto_within' (hf := hbound) (hg := hbound_map)
  have hliminf :
      f y ≤
        Filter.liminf (fun t : Real => f ((1 - t) • x + t • y))
          (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) := by
    have h := le_trans hliminf_y hliminf_map
    simpa [Function.comp] using h
  cases hfy : f y using EReal.rec with
  | bot =>
      have hybot : f y ≠ (⊥ : EReal) := hfproper.2.2 y (by simp)
      exact (hybot hfy).elim
  | top =>
      have hlimsup :
          Filter.limsup (fun t : Real => f ((1 - t) • x + t • y))
              (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) ≤ (⊤ : EReal) :=
        le_top
      have hliminf' :
          (⊤ : EReal) ≤
            Filter.liminf (fun t : Real => f ((1 - t) • x + t • y))
              (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) := by
        simpa [hfy] using hliminf
      simpa [hfy] using
        (tendsto_of_le_liminf_of_limsup_le hliminf' hlimsup)
  | coe r =>
      have hfx_ne_bot : f x ≠ (⊥ : EReal) := hfproper.2.2 x (by simp)
      have hx_dom :
          (x : Fin n → Real) ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
        simpa using hx
      have hfx_lt_top : f x < (⊤ : EReal) := by
        have hx' :
            (x : Fin n → Real) ∈ {x | x ∈ (Set.univ : Set (Fin n → Real)) ∧ f x < (⊤ : EReal)} := by
          simpa [effectiveDomain_eq (S := Set.univ) (f := f)] using hx_dom
        exact hx'.2
      have hfx_ne_top : f x ≠ (⊤ : EReal) := (lt_top_iff_ne_top).1 hfx_lt_top
      set α : Real := (f x).toReal
      have hα' : f x = (α : EReal) := by
        simpa [α] using (EReal.coe_toReal hfx_ne_top hfx_ne_bot).symm
      have hnotbot : ∀ z ∈ (Set.univ : Set (Fin n → Real)), f z ≠ ⊥ := by
        simpa using hfproper.2.2
      have hseg_ineq :
          ∀ t : Real, 0 < t → t < 1 →
            f ((1 - t) • x + t • y) ≤
              ((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y := by
        have hconv_seg :=
          (convexFunctionOn_iff_segment_inequality (C := Set.univ) (f := f)
            (hC := convex_univ) hnotbot).1 hfproper.1
        intro t ht0 ht1
        simpa using hconv_seg x (by simp) y (by simp) t ht0 ht1
      have hpos' : ∀ᶠ t in 𝓝 (1 : Real), 0 < t := by
        simpa using (Ioi_mem_nhds (a := (0 : Real)) (b := (1 : Real)) (by linarith))
      have hpos : ∀ᶠ t in nhdsWithin (1 : Real) (Set.Iio (1 : Real)), 0 < t := by
        exact eventually_nhdsWithin_of_eventually_nhds hpos'
      have hlt : ∀ᶠ t in nhdsWithin (1 : Real) (Set.Iio (1 : Real)), t < (1 : Real) := by
        exact eventually_nhdsWithin_of_forall (s := Set.Iio (1 : Real)) (a := (1 : Real))
          (fun t ht => ht)
      have h_eventually :
          ∀ᶠ t in nhdsWithin (1 : Real) (Set.Iio (1 : Real)),
            f ((1 - t) • x + t • y) ≤
              ((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y := by
        refine (hpos.and hlt).mono ?_
        intro t ht
        exact hseg_ineq t ht.1 ht.2
      have hlimsup_le :
          Filter.limsup (fun t : Real => f ((1 - t) • x + t • y))
              (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) ≤
            Filter.limsup (fun t : Real =>
                ((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y)
              (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) :=
        Filter.limsup_le_limsup h_eventually
      have h_tendsto_real :
          Filter.Tendsto (fun t : Real => (1 - t) * α + t * r)
            (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) (𝓝 r) := by
        have hcont : Continuous (fun t : Real => (1 - t) * α + t * r) := by
          have h1 : Continuous (fun t : Real => (1 - t) * α) :=
            (continuous_const.sub continuous_id).mul continuous_const
          have h2 : Continuous (fun t : Real => t * r) :=
            continuous_id.mul continuous_const
          simpa using h1.add h2
        have hcont_at : ContinuousAt (fun t : Real => (1 - t) * α + t * r) (1 : Real) :=
          hcont.continuousAt
        have h_tendsto :
            Filter.Tendsto (fun t : Real => (1 - t) * α + t * r) (𝓝 (1 : Real))
              (𝓝 ((1 - (1 : Real)) * α + (1 : Real) * r)) := hcont_at.tendsto
        have h_tendsto' :
            Filter.Tendsto (fun t : Real => (1 - t) * α + t * r) (𝓝 (1 : Real)) (𝓝 r) := by
          simpa using h_tendsto
        exact tendsto_nhdsWithin_of_tendsto_nhds h_tendsto'
      have h_tendsto_ereal :
          Filter.Tendsto (fun t : Real =>
              (((1 - t) * α + t * r : Real) : EReal))
            (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) (𝓝 (r : EReal)) := by
        exact (EReal.tendsto_coe.2 h_tendsto_real)
      have hlimsup_eq :
          Filter.limsup (fun t : Real =>
                (((1 - t) * α + t * r : Real) : EReal))
            (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) = (r : EReal) :=
        Filter.Tendsto.limsup_eq h_tendsto_ereal
      have hlimsup' :
          Filter.limsup (fun t : Real => f ((1 - t) • x + t • y))
              (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) ≤ (r : EReal) := by
        calc
          Filter.limsup (fun t : Real => f ((1 - t) • x + t • y))
              (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) ≤
            Filter.limsup (fun t : Real =>
                ((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y)
              (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) := hlimsup_le
          _ = (r : EReal) := by
            simpa [hα', hfy, EReal.coe_add, EReal.coe_mul, hlimsup_eq]
      have hliminf' :
          (r : EReal) ≤
            Filter.liminf (fun t : Real => f ((1 - t) • x + t • y))
              (nhdsWithin (1 : Real) (Set.Iio (1 : Real))) := by
        simpa [hfy] using hliminf
      simpa [hfy] using
        (tendsto_of_le_liminf_of_limsup_le hliminf' hlimsup')

end Section07
end Chap02
