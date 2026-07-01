/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

import Mathlib

open scoped Topology

section Chap04
section Section04

/-- Lemma 4.4.1: If `I, J ⊆ ℝ` are intervals and `f : ℝ → ℝ` is strictly
monotone on `I`, maps `I` onto `J`, is differentiable at `x₀ ∈ I`, and
`f' x₀ ≠ 0`, then the inverse satisfies
`(f ⁻¹)' (f x₀) = 1 / f' x₀`. If moreover `f` is continuously differentiable
with derivative never zero on `I`, then the inverse is continuously
differentiable on `J`. -/
lemma inverse_derivative_at {I J : Set ℝ} {f : ℝ → ℝ} {x0 f'x0 : ℝ}
    (hI : Set.OrdConnected I) (hJ : Set.OrdConnected J)
    (hmono : StrictMonoOn f I) (hmap : Set.MapsTo f I J) (hsurj : Set.SurjOn f I J)
    (hx0 : x0 ∈ I)
    (hdiff : HasDerivWithinAt f f'x0 I x0) (hzero : f'x0 ≠ 0) :
    HasDerivWithinAt (fun y => Function.invFunOn f I y) (f'x0)⁻¹ J (f x0) := by
  classical
  -- use the inverse restricted to `I`
  set g : ℝ → ℝ := fun y => Function.invFunOn f I y
  have hinj : Set.InjOn f I := hmono.injOn
  have hbij : Set.BijOn f I J := ⟨hmap, hinj, hsurj⟩
  have hInvOn : Set.InvOn g f I J := hbij.invOn_invFunOn
  have hleft : Set.LeftInvOn g f I := hInvOn.left
  have hright : Set.RightInvOn g f J := hInvOn.right
  have hx0' : g (f x0) = x0 := hleft hx0
  have hg_maps : Set.MapsTo g J I := hsurj.mapsTo_invFunOn
  have hx0J : f x0 ∈ J := hmap hx0
  have hfg : ∀ᶠ y in 𝓝[J] (f x0), f (g y) = y := by
    refine (eventually_mem_nhdsWithin).mono ?_
    intro y hy
    exact hright hy
  -- continuity of `g` on intervals (the inverse is continuous on the image interval)
  have hg_cont : ContinuousWithinAt g J (f x0) := by
    have himage : f '' I = J := by
      refine Set.Subset.antisymm ?_ ?_
      · exact hmap.image_subset
      · intro y hyJ
        rcases hsurj hyJ with ⟨x, hxI, rfl⟩
        exact ⟨x, hxI, rfl⟩
    have hx0J : f x0 ∈ J := hmap hx0
    -- build the order isomorphism induced by `f`
    let e₀ : I ≃o f '' I := hmono.orderIso f I
    let e : I ≃o J := e₀.trans (OrderIso.setCongr _ _ himage)
    have hval : ∀ x : I, (e x : ℝ) = f x := by
      intro x
      rfl
    have hgeq : ∀ y : J, g y = (e.symm y : ℝ) := by
      intro y
      have hyJ : (y : ℝ) ∈ J := y.property
      rcases hsurj hyJ with ⟨x, hxI, hxy⟩
      have hyJ' : f x ∈ J := hmap hxI
      have hgxI : g (f x) ∈ I := hg_maps hyJ'
      have hright' : f (g (f x)) = f x := hright hyJ'
      have hginv : g (f x) = x := hinj hgxI hxI hright'
      have heinv : (e.symm ⟨f x, hyJ'⟩ : I) = ⟨x, hxI⟩ := by
        have htemp := e.left_inv ⟨x, hxI⟩
        -- the value of `e` is given by `f`, so `e ⟨x, hxI⟩ = ⟨f x, hyJ'⟩`
        -- hence its inverse sends `⟨f x, hyJ'⟩` back to `⟨x, hxI⟩`
        have : e ⟨x, hxI⟩ = ⟨f x, hyJ'⟩ := by
          -- `hval` identifies the value of `e`
          apply Subtype.ext
          simp [hval]
        simpa [this] using htemp
      have hheq : (e.symm ⟨f x, hyJ'⟩ : ℝ) = x := by
        simpa using congrArg Subtype.val heinv
      -- replace `y` by `f x` using the surjectivity witness
      have : y = ⟨f x, hyJ'⟩ := by
        apply Subtype.ext
        simpa [Subtype.coe_mk] using hxy.symm
      subst this
      simpa [hheq] using hginv
    -- use the restriction to the subtype `J`
    have hRestr' : Set.restrict J g = fun y => (e.symm y : ℝ) := by
      ext y
      simp [Set.restrict, hgeq y]
    have hcont_sub :
        ContinuousAt (fun y : J => (e.symm y : ℝ)) ⟨f x0, hx0J⟩ := by
      have hcont :=
        (continuous_subtype_val : Continuous fun x : I => (x : ℝ)).comp
          (e.symm.continuous)
      simpa using hcont.continuousAt
    have hcont_restrict :
        ContinuousAt (Set.restrict J g) ⟨f x0, hx0J⟩ := by
      simpa [hRestr'] using hcont_sub
    exact (continuousWithinAt_iff_continuousAt_restrict g hx0J).2 hcont_restrict
  -- turn the derivative of `f` into an invertible linear map and apply the inverse function lemma
  have hderiv_g : HasDerivWithinAt g (f'x0)⁻¹ J (f x0) := by
    -- apply `HasFDerivWithinAt.of_local_left_inverse` once the derivative of `f` is upgraded
    let f'equiv : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 f'x0 hzero)
    have hderivCL : HasFDerivWithinAt f (f'equiv : ℝ →L[ℝ] ℝ) I (g (f x0)) := by
      have h := hdiff.hasFDerivWithinAt
      have hlin :
          (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) f'x0) =
            (f'equiv : ℝ →L[ℝ] ℝ) := by
        ext
        simp [f'equiv, ContinuousLinearEquiv.unitsEquivAut, mul_comm,
          ContinuousLinearMap.smulRight_apply]
      -- transport the base point using `hx0'`
      simpa [hlin, hx0'] using h
    have hF :=
      (HasFDerivWithinAt.of_local_left_inverse (hg_cont.tendsto_nhdsWithin hg_maps)
        hderivCL hx0J hfg)
    have hF_deriv := hF.hasDerivWithinAt
    simpa [f'equiv, ContinuousLinearEquiv.unitsEquivAut] using hF_deriv
  -- rewrite to the usual derivative statement
  simpa [g] using hderiv_g

/-- Lemma 4.4.1 (smoothness of the inverse): If `f : ℝ → ℝ` is continuously
`C¹`, strictly monotone on an interval `I`, maps `I` onto another interval `J`,
and `derivWithin f I x ≠ 0` for every `x ∈ I`, then the inverse function is
continuously differentiable on `J`. -/
lemma inverse_contDiff_on {I J : Set ℝ} {f : ℝ → ℝ} (hI : Set.OrdConnected I)
    (hJ : Set.OrdConnected J) (hmono : StrictMonoOn f I) (hmap : Set.MapsTo f I J)
    (hsurj : Set.SurjOn f I J) (hcont : ContDiffOn ℝ 1 f I)
    (hzero : ∀ x ∈ I, derivWithin f I x ≠ 0) :
    ContDiffOn ℝ 1 (fun y => Function.invFunOn f I y) J := by
  classical
  set g : ℝ → ℝ := fun y => Function.invFunOn f I y
  have hinj : Set.InjOn f I := hmono.injOn
  have hbij : Set.BijOn f I J := ⟨hmap, hinj, hsurj⟩
  have hInvOn : Set.InvOn g f I J := hbij.invOn_invFunOn
  have hright : Set.RightInvOn g f J := hInvOn.right
  have hg_maps : Set.MapsTo g J I := hsurj.mapsTo_invFunOn
  -- derivative of the inverse on `J`
  have hderiv_g :
      ∀ y ∈ J, HasDerivWithinAt g (derivWithin f I (g y))⁻¹ J y := by
    intro y hy
    have hyI : g y ∈ I := hg_maps hy
    have hdiff_f : DifferentiableWithinAt ℝ f I (g y) :=
      (hcont.differentiableOn (by decide) _ hyI)
    have hderivf : HasDerivWithinAt f (derivWithin f I (g y)) I (g y) :=
      hdiff_f.hasDerivWithinAt
    have hzero' : derivWithin f I (g y) ≠ 0 := hzero _ hyI
    have hmain := inverse_derivative_at hI hJ hmono hmap hsurj hyI hderivf hzero'
    have hfg : f (g y) = y := hright hy
    simpa [g, hfg] using hmain
  have hg_cont : ContinuousOn g J := by
    intro y hy
    exact (hderiv_g y hy).continuousWithinAt
  have hJ_eq : J = f '' I := by
    refine Set.Subset.antisymm ?_ hmap.image_subset
    intro y hyJ
    rcases hsurj hyJ with ⟨x, hxI, rfl⟩
    exact ⟨x, hxI, rfl⟩
  have hI_convex : Convex ℝ I := hI.convex
  have hJ_convex : Convex ℝ J := hJ.convex
  by_cases hI_sub : I.Subsingleton
  · -- if `I` is a singleton, the inverse is constant on `J`
    have hJ_sub : J.Subsingleton := by
      have hIm := hI_sub.image f
      simpa [hJ_eq] using hIm
    by_cases hJ_empty : J = ∅
    · simp [hJ_empty]
    · obtain ⟨y0, hy0⟩ : ∃ y0, y0 ∈ J := Set.nonempty_iff_ne_empty.mpr hJ_empty
      have hconst : Set.EqOn g (fun _ => g y0) J := by
        intro y hy
        have hyI : g y ∈ I := hg_maps hy
        have hy0I : g y0 ∈ I := hg_maps hy0
        exact hI_sub hyI hy0I
      have hconst_diff : ContDiffOn ℝ 1 (fun _ => g y0) J := contDiffOn_const
      exact hconst_diff.congr hconst
  · -- otherwise `I` and `J` have nonempty interior, so unique differentiability holds
    have hIint : (interior I).Nonempty := by
      classical
      rcases (by classical simpa [Set.Subsingleton] using hI_sub :
          ∃ x ∈ I, ∃ y ∈ I, x ≠ y) with ⟨x, hx, y, hy, hxy⟩
      have hlt : x < y ∨ y < x := lt_or_gt_of_ne hxy
      cases hlt with
      | inl hlt =>
          have hIoo : Set.Ioo x y ⊆ I := by
            intro z hz
            exact hI.out hx hy ⟨hz.1.le, hz.2.le⟩
          have hmid : (x + y) / 2 ∈ Set.Ioo x y := by
            constructor <;> linarith
          have hmid_int : (x + y) / 2 ∈ interior (Set.Ioo x y) := by
            simpa using hmid
          exact ⟨(x + y) / 2, (interior_mono hIoo) hmid_int⟩
      | inr hlt =>
          have hIoo : Set.Ioo y x ⊆ I := by
            intro z hz
            exact hI.out hy hx ⟨hz.1.le, hz.2.le⟩
          have hmid : (y + x) / 2 ∈ Set.Ioo y x := by
            constructor <;> linarith
          have hmid_int : (y + x) / 2 ∈ interior (Set.Ioo y x) := by
            simpa using hmid
          have : (interior I).Nonempty := ⟨(y + x) / 2, (interior_mono hIoo) hmid_int⟩
          simpa [add_comm] using this
    have hJ_not_sub : ¬ J.Subsingleton := by
      intro hJ_sub
      have hI_sub' : I.Subsingleton := by
        intro x hx y hy
        have hxJ : f x ∈ J := hmap hx
        have hyJ : f y ∈ J := hmap hy
        have hxy := hJ_sub hxJ hyJ
        exact hinj hx hy hxy
      exact hI_sub hI_sub'
    have hJint : (interior J).Nonempty := by
      classical
      rcases (by classical simpa [Set.Subsingleton] using hJ_not_sub :
          ∃ x ∈ J, ∃ y ∈ J, x ≠ y) with ⟨x, hx, y, hy, hxy⟩
      have hlt : x < y ∨ y < x := lt_or_gt_of_ne hxy
      cases hlt with
      | inl hlt =>
          have hJoo : Set.Ioo x y ⊆ J := by
            intro z hz
            exact hJ.out hx hy ⟨hz.1.le, hz.2.le⟩
          have hmid : (x + y) / 2 ∈ Set.Ioo x y := by
            constructor <;> linarith
          have hmid_int : (x + y) / 2 ∈ interior (Set.Ioo x y) := by
            simpa using hmid
          exact ⟨(x + y) / 2, (interior_mono hJoo) hmid_int⟩
      | inr hlt =>
          have hJoo : Set.Ioo y x ⊆ J := by
            intro z hz
            exact hJ.out hy hx ⟨hz.1.le, hz.2.le⟩
          have hmid : (y + x) / 2 ∈ Set.Ioo y x := by
            constructor <;> linarith
          have hmid_int : (y + x) / 2 ∈ interior (Set.Ioo y x) := by
            simpa using hmid
          have : (interior J).Nonempty := ⟨(y + x) / 2, (interior_mono hJoo) hmid_int⟩
          simpa [add_comm] using this
    have hI_ud : UniqueDiffOn ℝ I := uniqueDiffOn_convex hI_convex hIint
    have hcont_deriv :
        ContinuousOn (fun x => derivWithin f I x) I := by
      have h := (contDiffOn_succ_iff_derivWithin (n := 0) hI_ud).1 hcont
      have hcont0 : ContDiffOn ℝ 0 (fun x => derivWithin f I x) I := h.2.2
      simpa using hcont0
    have hcont_comp :
        ContinuousOn (fun y => derivWithin f I (g y)) J :=
      hcont_deriv.comp hg_cont hg_maps
    have hnonzero : ∀ y ∈ J, derivWithin f I (g y) ≠ 0 := by
      intro y hy
      exact hzero _ (hg_maps hy)
    have hcont_inv :
        ContinuousOn (fun y => (derivWithin f I (g y))⁻¹) J :=
      hcont_comp.inv₀ hnonzero
    have hJ_ud : UniqueDiffOn ℝ J := uniqueDiffOn_convex hJ_convex hJint
    have hderiv_eq :
        Set.EqOn (fun y => derivWithin g J y) (fun y => (derivWithin f I (g y))⁻¹) J := by
      intro y hy
      have huniq : UniqueDiffWithinAt ℝ J y := hJ_ud y hy
      simpa using (hderiv_g y hy).derivWithin huniq
    have hcont_deriv_g :
        ContinuousOn (fun y => derivWithin g J y) J :=
      hcont_inv.congr hderiv_eq
    -- use the characterization of `ContDiffOn` via continuity of the derivative
    have hdiff_g : DifferentiableOn ℝ g J := by
      intro y hy
      exact (hderiv_g y hy).differentiableWithinAt
    have hcont_deriv_g' :
        ContDiffOn ℝ 0 (fun y => derivWithin g J y) J := by
      simpa using hcont_deriv_g
    refine (contDiffOn_succ_iff_derivWithin (n := 0) hJ_ud).2 ?_
    refine ⟨hdiff_g, ?_, hcont_deriv_g'⟩
    intro h
    cases h

/-- If `x₀ ∈ (a, b)` then there is a small open interval around `x₀` contained in `(a, b)`. -/
lemma exists_Ioo_subset_of_mem {a b x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo a b) :
    ∃ δ > 0, Set.Ioo (x₀ - δ) (x₀ + δ) ⊆ Set.Ioo a b := by
  classical
  obtain ⟨hx₀_left, hx₀_right⟩ := hx₀
  set δ := min (x₀ - a) (b - x₀)
  have hδ_pos : 0 < δ := by
    have hleft : 0 < x₀ - a := sub_pos.mpr hx₀_left
    have hright : 0 < b - x₀ := sub_pos.mpr hx₀_right
    simpa [δ] using lt_min hleft hright
  refine ⟨δ, hδ_pos, ?_⟩
  intro y hy
  have hy_left : x₀ - δ < y := hy.1
  have hy_right : y < x₀ + δ := hy.2
  have hδ_le_left : δ ≤ x₀ - a := min_le_left _ _
  have hδ_le_right : δ ≤ b - x₀ := min_le_right _ _
  have hxδ_left : a ≤ x₀ - δ := by
    have h' : δ + a ≤ x₀ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        add_le_add_right hδ_le_left a
    have h'' : a + δ ≤ x₀ := by simpa [add_comm] using h'
    exact (le_sub_iff_add_le).2 h''
  have hxδ_right : x₀ + δ ≤ b := by
    have h' : x₀ + δ ≤ x₀ + (b - x₀) := by
      simpa [add_comm, add_left_comm] using add_le_add_right hδ_le_right x₀
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h'
  have hya : a < y := lt_of_le_of_lt hxδ_left hy_left
  have hyb : y < b := lt_of_lt_of_le hy_right hxδ_right
  exact ⟨hya, hyb⟩

/-- Theorem 4.4.2 (inverse function theorem). Given a continuously
`C¹` function `f : ℝ → ℝ` on `(a, b)` with `derivWithin f (Set.Ioo a b) x₀ ≠ 0`
at some `x₀ ∈ (a, b)`, there exists an open interval `I ⊆ (a, b)` containing
`x₀` such that `f` restricts to an injective map on `I` with a continuously
differentiable inverse `g : J → I` on `J = f '' I`, and for every `y ∈ J` we have
`derivWithin g J y = (derivWithin f (Set.Ioo a b) (g y))⁻¹`. -/
theorem inverse_function_open_interval {a b x0 : ℝ} (f : ℝ → ℝ)
    (hx0 : x0 ∈ Set.Ioo a b) (hcont : ContDiffOn ℝ 1 f (Set.Ioo a b))
    (hderiv : derivWithin f (Set.Ioo a b) x0 ≠ 0) :
    ∃ I J : Set ℝ, IsOpen I ∧ x0 ∈ I ∧ I ⊆ Set.Ioo a b ∧ J = f '' I ∧
      Set.InjOn f I ∧ Set.SurjOn f I J ∧
        ∃ g : ℝ → ℝ, Set.MapsTo g J I ∧ Set.SurjOn g J I ∧
          (∀ x ∈ I, g (f x) = x) ∧ (∀ y ∈ J, f (g y) = y) ∧
          ContDiffOn ℝ 1 g J ∧ ∀ y ∈ J, derivWithin g J y =
            (derivWithin f (Set.Ioo a b) (g y))⁻¹ := by
  classical
  have hx0_nhds : Set.Ioo a b ∈ 𝓝 x0 := isOpen_Ioo.mem_nhds hx0
  have hcontAt : ContDiffAt ℝ 1 f x0 := hcont.contDiffAt hx0_nhds
  have hstrict : HasStrictDerivAt f (deriv f x0) x0 :=
    hcontAt.hasStrictDerivAt (by decide)
  have hderiv_eq : derivWithin f (Set.Ioo a b) x0 = deriv f x0 :=
    derivWithin_of_isOpen isOpen_Ioo hx0
  have hderiv' : deriv f x0 ≠ 0 := by simpa [hderiv_eq] using hderiv
  have hIoo_ud : UniqueDiffOn ℝ (Set.Ioo a b) := isOpen_Ioo.uniqueDiffOn
  have hderiv_cont :
      ContinuousOn (fun x => derivWithin f (Set.Ioo a b) x) (Set.Ioo a b) := by
    have h := (contDiffOn_succ_iff_derivWithin (n := 0) hIoo_ud).1 hcont
    simpa using h.2.2
  have hnonzero_open :
      IsOpen (Set.Ioo a b ∩ {x | derivWithin f (Set.Ioo a b) x ≠ 0}) := by
    refine isOpen_iff_mem_nhds.mpr ?_
    intro x hx
    rcases hx with ⟨hxioo, hxne⟩
    have hx_nhds : Set.Ioo a b ∈ 𝓝 x := isOpen_Ioo.mem_nhds hxioo
    have hcont : ContinuousAt (fun x => derivWithin f (Set.Ioo a b) x) x := by
      have hcont_within := hderiv_cont x hxioo
      exact hcont_within.continuousAt hx_nhds
    have hne_nhds : {y | y ≠ 0} ∈ 𝓝 (derivWithin f (Set.Ioo a b) x) :=
      isOpen_ne.mem_nhds hxne
    have hpre :
        {x | derivWithin f (Set.Ioo a b) x ≠ 0} ∈ 𝓝 x := hcont.tendsto hne_nhds
    exact Filter.inter_mem hx_nhds hpre
  set φ :=
      (hstrict.hasStrictFDerivAt_equiv hderiv').toOpenPartialHomeomorph f
  have hx0φ : x0 ∈ φ.source :=
    (hstrict.hasStrictFDerivAt_equiv hderiv').mem_toOpenPartialHomeomorph_source
  have hx0fφ : f x0 ∈ φ.target :=
    (hstrict.hasStrictFDerivAt_equiv hderiv').image_mem_toOpenPartialHomeomorph_target
  have hφ_coe : (φ : ℝ → ℝ) = f :=
    (hstrict.hasStrictFDerivAt_equiv hderiv').toOpenPartialHomeomorph_coe (f := f)
  set I := φ.source ∩ (Set.Ioo a b ∩ {x | derivWithin f (Set.Ioo a b) x ≠ 0})
  set J := f '' I
  have hI_open : IsOpen I := φ.open_source.inter hnonzero_open
  have hx0I : x0 ∈ I := by
    refine ⟨hx0φ, ?_⟩
    refine ⟨hx0, ?_⟩
    simpa [hderiv_eq] using hderiv
  have hIsubset : I ⊆ Set.Ioo a b := by
    intro x hx
    exact hx.2.1
  have hsurj : Set.SurjOn f I J := by
    simpa [J] using Set.surjOn_image (s := I) (f := f)
  refine ⟨I, J, ?_⟩
  refine ⟨hI_open, ?_⟩
  refine ⟨hx0I, ?_⟩
  refine ⟨hIsubset, ?_⟩
  refine ⟨rfl, ?_⟩
  refine ⟨?_, ?_⟩
  · -- injectivity of `f` on `I`
    refine (φ.injOn.mono ?_)
    intro x hx
    exact hx.1
  · refine ⟨hsurj, ?_⟩
    -- construct the inverse map and its properties
    have hJ_sub : J ⊆ φ.target := by
      intro y hy
      rcases hy with ⟨x, hxI, rfl⟩
      exact φ.map_source hxI.1
    refine ⟨φ.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro y hy
      rcases hy with ⟨x, hxI, rfl⟩
      have hxsource : x ∈ φ.source := hxI.1
      have hxioo : x ∈ Set.Ioo a b := hxI.2.1
      have htarget : f x ∈ φ.target := by
        have := φ.map_source hxsource
        simpa [hφ_coe] using this
      have hg_source : φ.symm (f x) ∈ φ.source := φ.map_target htarget
      have hleft : φ.symm (f x) = x := by
        have := φ.left_inv hxsource
        simpa [hφ_coe] using this
      have hg_ioo : φ.symm (f x) ∈ Set.Ioo a b := by simpa [hleft] using hxioo
      have hg_deriv :
          derivWithin f (Set.Ioo a b) (φ.symm (f x)) ≠ 0 := by
        have hx_nonzero : derivWithin f (Set.Ioo a b) x ≠ 0 := hxI.2.2
        simpa [hleft] using hx_nonzero
      exact ⟨hg_source, ⟨hg_ioo, hg_deriv⟩⟩
    · intro x hxI
      refine ⟨f x, ?_, ?_⟩
      · exact ⟨x, hxI, rfl⟩
      · have hxsource : x ∈ φ.source := hxI.1
        have hleft := φ.left_inv hxsource
        simpa [hφ_coe] using hleft
    · intro x hxI
      have hxsource : x ∈ φ.source := hxI.1
      have hleft := φ.left_inv hxsource
      simpa [hφ_coe] using hleft
    · intro y hy
      rcases hy with ⟨x, hxI, rfl⟩
      have hxsource : x ∈ φ.source := hxI.1
      have hright := φ.right_inv (φ.map_source hxsource)
      simpa [hφ_coe] using hright
    · -- smoothness of the inverse on `J`
      have hJ_eq : φ.target ∩ φ.symm ⁻¹' I = J := by
        ext y
        constructor
        · intro hy
          set x := φ.symm y
          have hxI : x ∈ I := hy.2
          have hy' : f x = y := by
            have hy_target : y ∈ φ.target := hy.1
            have := φ.right_inv hy_target
            simpa [hφ_coe, x] using this
          exact ⟨x, hxI, hy'⟩
        · intro hy
          rcases hy with ⟨x, hxI, rfl⟩
          have hxsource : x ∈ φ.source := hxI.1
          have hxtarget : f x ∈ φ.target := by
            have := φ.map_source hxsource
            simpa [hφ_coe] using this
          have hleft : φ.symm (f x) = x := by
            have := φ.left_inv hxsource
            simpa [hφ_coe] using this
          have hg_source : φ.symm (f x) ∈ φ.source := φ.map_target hxtarget
          have hg_ioo : φ.symm (f x) ∈ Set.Ioo a b := by simpa [hleft] using hxI.2.1
          have hg_nonzero : derivWithin f (Set.Ioo a b) (φ.symm (f x)) ≠ 0 := by
            have hx_nonzero : derivWithin f (Set.Ioo a b) x ≠ 0 := hxI.2.2
            simpa [hleft] using hx_nonzero
          have hx_pre : φ.symm (f x) ∈ I := by
            exact ⟨hg_source, ⟨hg_ioo, hg_nonzero⟩⟩
          exact ⟨hxtarget, by simpa [hφ_coe] using hx_pre⟩
      have hpre : IsOpen (φ.target ∩ φ.symm ⁻¹' I) :=
        (φ.continuousOn_symm.isOpen_inter_preimage φ.open_target hI_open)
      have hJ_open : IsOpen J := by
        simpa [hJ_eq, Set.inter_comm] using hpre
      have hJ_ud : UniqueDiffOn ℝ J := hJ_open.uniqueDiffOn
      have hcont_symm_on : ContDiffOn ℝ 1 φ.symm J := by
        apply (hJ_open.contDiffOn_iff).2
        intro y hy
        rcases hy with ⟨x, hxI, rfl⟩
        have hxsource : x ∈ φ.source := hxI.1
        have hxioo : x ∈ Set.Ioo a b := hxI.2.1
        have hx_nonzero : derivWithin f (Set.Ioo a b) x ≠ 0 := hxI.2.2
        have hdiff_on : DifferentiableOn ℝ f (Set.Ioo a b) :=
          hcont.differentiableOn (by decide)
        have hdiff_within : DifferentiableWithinAt ℝ f (Set.Ioo a b) x :=
          hdiff_on x hxioo
        have hdiff_at : DifferentiableAt ℝ f x :=
          hdiff_within.differentiableAt (isOpen_Ioo.mem_nhds hxioo)
        have hderiv_target : HasDerivAt f (deriv f x) x := hdiff_at.hasDerivAt
        have hcont_at : ContDiffAt ℝ 1 f x :=
          (hcont.contDiffAt (isOpen_Ioo.mem_nhds hxioo))
        have hcont_at' : ContDiffAt ℝ 1 φ x := by simpa [hφ_coe] using hcont_at
        have htarget : f x ∈ φ.target := by
          have := φ.map_source hxsource
          simpa [hφ_coe] using this
        have hderiv_eq' :
            deriv f x = deriv φ x := by
          simp [hφ_coe]
        have hderiv_ne : deriv φ x ≠ 0 := by
          have hderiv_within_eq : derivWithin f (Set.Ioo a b) x = deriv f x :=
            derivWithin_of_isOpen isOpen_Ioo hxioo
          simpa [hderiv_eq', hderiv_within_eq] using hx_nonzero
        have hleft : φ.symm (f x) = x := by
          have := φ.left_inv hxsource
          simpa [hφ_coe] using this
        have hderiv_at_symm :
            HasDerivAt φ (deriv φ x) (φ.symm (f x)) := by
          have hderiv_target' : HasDerivAt φ (deriv φ x) x := by
            simpa [hφ_coe] using hderiv_target
          simpa [hleft] using hderiv_target'
        have hcont_at_symm : ContDiffAt ℝ 1 φ (φ.symm (f x)) := by
          simpa [hleft] using hcont_at'
        have hcont_symm :
            ContDiffAt ℝ 1 φ.symm (f x) :=
          φ.contDiffAt_symm_deriv hderiv_ne htarget hderiv_at_symm hcont_at_symm
        simpa [hφ_coe, derivWithin_of_isOpen isOpen_Ioo hxioo] using hcont_symm
      exact hcont_symm_on
    · intro y hy
      rcases hy with ⟨x, hxI, rfl⟩
      have hxsource : x ∈ φ.source := hxI.1
      have hxioo : x ∈ Set.Ioo a b := hxI.2.1
      have hleft : φ.symm (f x) = x := by
        have := φ.left_inv hxsource
        simpa [hφ_coe] using this
      have hderiv_fx : HasDerivAt φ (deriv φ x) x := by
        have hdiff_on : DifferentiableOn ℝ f (Set.Ioo a b) :=
          hcont.differentiableOn (by decide)
        have hdiff_within : DifferentiableWithinAt ℝ f (Set.Ioo a b) x :=
          hdiff_on x hxioo
        have hdiff_at : DifferentiableAt ℝ f x :=
          hdiff_within.differentiableAt (isOpen_Ioo.mem_nhds hxioo)
        have hderiv_f : HasDerivAt f (deriv f x) x := hdiff_at.hasDerivAt
        simpa [hφ_coe] using hderiv_f
      have hderiv_ne : deriv φ x ≠ 0 := by
        have hx_nonzero : derivWithin f (Set.Ioo a b) x ≠ 0 := hxI.2.2
        have hderiv_within_eq : derivWithin f (Set.Ioo a b) x = deriv f x :=
          derivWithin_of_isOpen isOpen_Ioo hxioo
        simpa [hφ_coe, hderiv_within_eq] using hx_nonzero
      have hy_target : f x ∈ φ.target := by
        have := φ.map_source hxsource
        simpa [hφ_coe] using this
      have hJ_eq' : φ.target ∩ φ.symm ⁻¹' I = J := by
        ext y
        constructor
        · intro hy
          set z := φ.symm y
          have hzI : z ∈ I := hy.2
          have hy' : f z = y := by
            have hy_target : y ∈ φ.target := hy.1
            have := φ.right_inv hy_target
            simpa [hφ_coe, z] using this
          exact ⟨z, hzI, hy'⟩
        · intro hy
          rcases hy with ⟨z, hzI, rfl⟩
          have hzsource : z ∈ φ.source := hzI.1
          have hztarget : f z ∈ φ.target := by
            have := φ.map_source hzsource
            simpa [hφ_coe] using this
          have hzleft : φ.symm (f z) = z := by
            have := φ.left_inv hzsource
            simpa [hφ_coe] using this
          have hz_nonzero : derivWithin f (Set.Ioo a b) (φ.symm (f z)) ≠ 0 := by
            have hz_nonzero' : derivWithin f (Set.Ioo a b) z ≠ 0 := hzI.2.2
            simpa [hzleft] using hz_nonzero'
          have hz_ioo : φ.symm (f z) ∈ Set.Ioo a b := by
            have hz_ioo' : z ∈ Set.Ioo a b := hzI.2.1
            simpa [hzleft] using hz_ioo'
          have hz_source : φ.symm (f z) ∈ φ.source := φ.map_target hztarget
          have hzI' : φ.symm (f z) ∈ I := ⟨hz_source, ⟨hz_ioo, hz_nonzero⟩⟩
          exact ⟨hztarget, by simpa [hφ_coe] using hzI'⟩
      have hpre' : IsOpen (φ.target ∩ φ.symm ⁻¹' I) :=
        (φ.continuousOn_symm.isOpen_inter_preimage φ.open_target hI_open)
      have hJ_open : IsOpen J := by
        simpa [hJ_eq', Set.inter_comm] using hpre'
      have hyJ : f x ∈ J := ⟨x, hxI, rfl⟩
      have hderiv_fx_symm :
          HasDerivAt φ (deriv φ x) (φ.symm (f x)) := by
        have hleft : φ.symm (f x) = x := by
          have := φ.left_inv hxsource
          simpa [hφ_coe] using this
        simpa [hleft] using hderiv_fx
      have hderiv_target :
          HasDerivAt φ.symm (deriv φ x)⁻¹ (f x) :=
        φ.hasDerivAt_symm (a := f x) (f' := deriv φ x) hy_target hderiv_ne hderiv_fx_symm
      have hderiv_J :
          HasDerivWithinAt φ.symm (deriv φ x)⁻¹ J (f x) :=
        hderiv_target.hasDerivWithinAt
      have hderiv_at_J :
          HasDerivAt φ.symm (deriv φ x)⁻¹ (f x) :=
        hderiv_J.hasDerivAt (hJ_open.mem_nhds hyJ)
      have hderiv_within_eq' :
          derivWithin φ.symm J (f x) = deriv φ.symm (f x) :=
        derivWithin_of_isOpen hJ_open hyJ
      have hderiv_at_eq :
          deriv φ.symm (f x) = (deriv φ x)⁻¹ := hderiv_at_J.deriv
      have hderiv_eq :
          derivWithin φ.symm J (f x) = (deriv φ x)⁻¹ :=
        by simpa [hderiv_within_eq'] using hderiv_at_eq
      have hderiv_within_eq :
          derivWithin f (Set.Ioo a b) x = deriv f x :=
        derivWithin_of_isOpen isOpen_Ioo hxioo
      calc
        derivWithin φ.symm J (f x) = (deriv φ x)⁻¹ := hderiv_eq
        _ = (deriv f x)⁻¹ := by simp [hφ_coe]
        _ = (derivWithin f (Set.Ioo a b) x)⁻¹ := by
              simp [hderiv_within_eq]
        _ = (derivWithin f (Set.Ioo a b) (φ.symm (f x)))⁻¹ := by
              simp [hleft]

/-- Corollary 4.4.3: For `n ∈ ℕ` and `x ≥ 0` there is a unique `y ≥ 0`
with `y ^ n = x`. The function `g x = x^{1/n}` on `(0, ∞)` is continuously
differentiable with derivative `g' x = (1 / n) * x ^ ((1 - n) / n)`,
where fractional powers use the convention `x ^ (m / n) = (x ^ (1 / n)) ^ m`. -/
theorem nth_root_exists_unique_and_deriv (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx : 0 ≤ x) :
    (∃! y : ℝ, 0 ≤ y ∧ y ^ n = x) ∧
      ∃ g : ℝ → ℝ, g = (fun t => t ^ (1 / (n : ℝ))) ∧
        ContDiffOn ℝ 1 g (Set.Ioi 0) ∧
        ∀ t ∈ Set.Ioi (0 : ℝ),
          derivWithin g (Set.Ioi 0) t =
            (1 / (n : ℝ)) * t ^ (((1 : ℝ) - (n : ℝ)) / (n : ℝ)) := by
  classical
  have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  have hn_real : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn_ne
  set g : ℝ → ℝ := fun t : ℝ => t ^ (1 / (n : ℝ))
  have hxroot : 0 ≤ g x ∧ (g x) ^ n = x := by
    constructor
    · simpa [g] using Real.rpow_nonneg hx (1 / (n : ℝ))
    · simpa [g, one_div] using Real.rpow_inv_natCast_pow hx hn_ne
  have huniq : ∀ y : ℝ, 0 ≤ y ∧ y ^ n = x → y = g x := by
    intro y hy
    have hy_pow : (y ^ n : ℝ) ^ (1 / (n : ℝ)) = y := by
      simpa [one_div] using Real.pow_rpow_inv_natCast (x := y) hy.1 hn_ne
    have : g x = y := by simpa [g, hy.2, one_div] using hy_pow
    exact this.symm
  have hcontId : ContDiffOn ℝ 1 (fun t : ℝ => t) (Set.Ioi 0) :=
    (contDiff_id : ContDiff ℝ 1 fun t : ℝ => t).contDiffOn
  have hcont_g : ContDiffOn ℝ 1 g (Set.Ioi 0) := by
    have hnonzero : ∀ t ∈ Set.Ioi (0 : ℝ), (t : ℝ) ≠ 0 := fun t ht => ne_of_gt ht
    simpa [g] using hcontId.rpow_const_of_ne (p := 1 / (n : ℝ)) hnonzero
  have hcoef : (n : ℝ)⁻¹ - 1 = ((1 : ℝ) - (n : ℝ)) / (n : ℝ) := by
    have htemp :
        (1 / (n : ℝ)) - (n : ℝ) / (n : ℝ) = ((1 : ℝ) - (n : ℝ)) / (n : ℝ) := by
      simpa [sub_eq_add_neg] using (div_sub_div_same (1 : ℝ) (n : ℝ) (n : ℝ))
    have hdiv : (n : ℝ) / (n : ℝ) = 1 := by simp [hn_real]
    simpa [one_div, hdiv] using htemp
  have hderiv_formula :
      ∀ t ∈ Set.Ioi (0 : ℝ),
        derivWithin g (Set.Ioi 0) t =
          (1 / (n : ℝ)) * t ^ (((1 : ℝ) - (n : ℝ)) / (n : ℝ)) := by
    intro t ht
    have huniqDiff : UniqueDiffWithinAt ℝ (Set.Ioi 0) t :=
      IsOpen.uniqueDiffWithinAt isOpen_Ioi ht
    have hdiff : DifferentiableWithinAt ℝ (fun u : ℝ => u) (Set.Ioi 0) t := by
      simpa using
        (differentiableWithinAt_id :
          DifferentiableWithinAt ℝ id (Set.Ioi 0) t)
    have hmain :=
      derivWithin_rpow_const (p := 1 / (n : ℝ)) (hf := hdiff)
        (hx := Or.inl (ne_of_gt ht)) (hxs := huniqDiff)
    have hId : derivWithin (fun u : ℝ => u) (Set.Ioi 0) t = (1 : ℝ) :=
      derivWithin_id' (𝕜 := ℝ) (s := Set.Ioi 0) (x := t) huniqDiff
    simpa [g, hcoef, hId, mul_comm, mul_left_comm, mul_assoc] using hmain
  refine ⟨?_, ?_⟩
  · refine ⟨g x, ?_, ?_⟩
    · exact hxroot
    · intro y hy
      exact huniq y hy
  · refine ⟨g, rfl, hcont_g, hderiv_formula⟩

/-- Example 4.4.4: For `f x = x^2`, the derivative at `x₀ ≠ 0` is nonzero.
At a positive point `x₀`, the inverse function theorem applies on the maximal
open interval `(0, ∞)` where `f` is injective; any open set on which `f` is
injective and contains `x₀` must lie in `(0, ∞)`. -/
theorem inverse_function_example_square {x0 : ℝ} (hx0 : 0 < x0) :
    derivWithin (fun x : ℝ => x ^ 2) (Set.Ioi 0) x0 ≠ 0 ∧
      Set.InjOn (fun x : ℝ => x ^ 2) (Set.Ioi 0) ∧
        (∀ I : Set ℝ, IsOpen I → Set.OrdConnected I → x0 ∈ I →
          Set.InjOn (fun x : ℝ => x ^ 2) I → I ⊆ Set.Ioi 0) := by
  classical
  have hx0_mem : x0 ∈ Set.Ioi (0 : ℝ) := hx0
  have hderiv_eq :
      derivWithin (fun x : ℝ => x ^ 2) (Set.Ioi 0) x0 =
        deriv (fun x : ℝ => x ^ 2) x0 :=
    derivWithin_of_isOpen isOpen_Ioi hx0_mem
  have hderiv_formula : deriv (fun x : ℝ => x ^ 2) x0 = 2 * x0 := by
    have hmul :
        HasDerivAt (fun x : ℝ => x * x) (1 * x0 + x0 * 1) x0 :=
      (hasDerivAt_id x0).mul (hasDerivAt_id x0)
    have hpow : HasDerivAt (fun x : ℝ => x ^ 2) (1 * x0 + x0 * 1) x0 := by
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hmul
    have h := hpow.deriv
    calc
      deriv (fun x : ℝ => x ^ 2) x0 = 1 * x0 + x0 * 1 := h
      _ = 2 * x0 := by simp [two_mul]
  have hderiv_ne :
      derivWithin (fun x : ℝ => x ^ 2) (Set.Ioi 0) x0 ≠ 0 := by
    have hneq : (2 : ℝ) * x0 ≠ 0 :=
      mul_ne_zero two_ne_zero (ne_of_gt hx0)
    simpa [hderiv_eq, hderiv_formula] using hneq
  have hinjIoi : Set.InjOn (fun x : ℝ => x ^ 2) (Set.Ioi 0) := by
    intro x hx y hy hxy
    have hxpos : 0 < x := hx
    have hypos : 0 < y := hy
    obtain h | h := sq_eq_sq_iff_eq_or_eq_neg.mp hxy
    · exact h
    · have hyneg : y = -x := by
        simpa using (congrArg Neg.neg h).symm
      have : 0 < -x := by simpa [hyneg] using hypos
      have hxneg : x < 0 := (neg_pos).mp this
      exact False.elim (lt_asymm hxpos hxneg)
  refine ⟨hderiv_ne, hinjIoi, ?_⟩
  intro I hIopen hIord hx0I hIinj x hx
  have hxpos : 0 < x := by
    by_contra hxnonpos
    have hxle : x ≤ 0 := le_of_not_gt hxnonpos
    have hzero_mem : (0 : ℝ) ∈ I := by
      have hmem : (0 : ℝ) ∈ Set.Icc x x0 := ⟨hxle, le_of_lt hx0⟩
      exact hIord.out hx hx0I hmem
    have hnhds : I ∈ 𝓝 (0 : ℝ) := hIopen.mem_nhds hzero_mem
    obtain ⟨ε, hεpos, hball⟩ := Metric.mem_nhds_iff.mp hnhds
    set y : ℝ := ε / 2 with hydef
    have hypos : 0 < y := by simpa [hydef] using half_pos hεpos
    have hyabs : |y| = y := abs_of_nonneg hypos.le
    have hylt : y < ε := by simpa [hydef] using half_lt_self hεpos
    have hyabs_lt : |y| < ε := by simpa [hyabs] using hylt
    have hyneg_abs_lt : |-y| < ε := by simpa [abs_neg] using hyabs_lt
    have hy_dist : dist y 0 < ε := by
      simpa [Real.dist_eq, sub_eq_add_neg] using hyabs_lt
    have hyneg_dist : dist (-y) 0 < ε := by
      simpa [Real.dist_eq, sub_eq_add_neg] using hyneg_abs_lt
    have hy_mem_ball : y ∈ Metric.ball (0 : ℝ) ε := by
      simpa [Metric.mem_ball] using hy_dist
    have hyneg_mem_ball : -y ∈ Metric.ball (0 : ℝ) ε := by
      simpa [Metric.mem_ball] using hyneg_dist
    have hy_mem : y ∈ I := hball hy_mem_ball
    have hyneg_mem : -y ∈ I := hball hyneg_mem_ball
    have hy_eq : y = -y := hIinj hy_mem hyneg_mem (by simp [pow_two, hydef])
    have hy' : y + y = 0 := by simpa using congrArg (fun t => t + y) hy_eq
    have hy'' : (2 : ℝ) * y = 0 := by simpa [two_mul] using hy'
    have hyzero : y = 0 := (mul_eq_zero.mp hy'').resolve_left two_ne_zero
    have hycontr' : (0 : ℝ) < 0 := hyzero ▸ hypos
    exact (lt_irrefl (0 : ℝ)) hycontr'
  simpa using hxpos

/-- Example 4.4.5: The cubic `f x = x^3 : ℝ → ℝ` is bijective with a
continuous derivative, so it has a set-theoretic inverse `g y = y^{1/3}` on
all of `ℝ`. Nevertheless the inverse fails to be differentiable at `0`
because `f' 0 = 0`, and the graph of the cube root has a vertical tangent at
the origin. -/
theorem cube_inverse_not_differentiable_at_zero :
    ContDiff ℝ 1 (fun x : ℝ => x ^ 3) ∧
      StrictMono (fun x : ℝ => x ^ 3) ∧ Function.Surjective (fun x : ℝ => x ^ 3) ∧
        deriv (fun x : ℝ => x ^ 3) 0 = 0 ∧
          ∃ g : ℝ → ℝ, Function.LeftInverse g (fun x : ℝ => x ^ 3) ∧
            Function.RightInverse g (fun x : ℝ => x ^ 3) ∧
              ¬ DifferentiableAt ℝ g 0 := by
  classical
  set f : ℝ → ℝ := fun x => x ^ 3
  have hcontDiff : ContDiff ℝ 1 f := by
    simpa [f] using (contDiff_id : ContDiff ℝ 1 fun x : ℝ => x).pow 3
  have hstrict : StrictMono f := by
    have hodd : Odd (3 : ℕ) := by decide
    simpa [f] using
      (Odd.strictMono_pow (R := ℝ) (n := 3) hodd :
        StrictMono fun x : ℝ => x ^ 3)
  have hsurj : Function.Surjective f := by
    intro y
    let R := |y| + 1
    have hRpos : 0 < R := add_pos_of_nonneg_of_pos (abs_nonneg _) zero_lt_one
    have hRnonneg : 0 ≤ R := le_of_lt hRpos
    have hab : -R ≤ R := neg_le_self hRnonneg
    have hcont_on : ContinuousOn f (Set.Icc (-R) R) :=
      (hcontDiff.continuous.continuousOn)
    have hy_le_R : |y| ≤ R := by
      unfold R
      exact le_add_of_nonneg_right (show 0 ≤ (1 : ℝ) by exact zero_le_one)
    have hRge_one : 1 ≤ R := by
      unfold R
      have hx : 0 ≤ |y| := abs_nonneg _
      have hx' : 1 + 0 ≤ 1 + |y| := add_le_add_right hx 1
      have hx'' : 1 ≤ |y| + 1 := by
        convert hx' using 1 <;> simp [add_comm]
      exact hx''
    have hR_le_Rsq : R ≤ R ^ 2 := by
      have := mul_le_mul_of_nonneg_left hRge_one hRnonneg
      simpa [pow_two] using this
    have hRsq_le_Rcube : R ^ 2 ≤ R ^ 3 := by
      have : 0 ≤ R ^ 2 := sq_nonneg R
      have := mul_le_mul_of_nonneg_left hRge_one this
      simpa [pow_succ] using this
    have hR_le_Rcube : R ≤ R ^ 3 := hR_le_Rsq.trans hRsq_le_Rcube
    have hy_abs_le : |y| ≤ R ^ 3 := hy_le_R.trans hR_le_Rcube
    have hfa : f (-R) = -R ^ 3 := by
      simp [f, pow_three]
    have hfb : f R = R ^ 3 := by
      simp [f, pow_three]
    have hy_mem : y ∈ Set.Icc (f (-R)) (f R) := by
      have hy_bounds : -R ^ 3 ≤ y ∧ y ≤ R ^ 3 := (abs_le).1 hy_abs_le
      simpa [Set.mem_Icc, hfa, hfb] using hy_bounds
    have hy_img : y ∈ f '' Set.Icc (-R) R :=
      (intermediate_value_Icc hab hcont_on) hy_mem
    rcases hy_img with ⟨x, hx, rfl⟩
    exact ⟨x, rfl⟩
  have hderiv_at_zero : HasDerivAt f 0 0 := by
    simpa [f, pow_two, pow_three] using (hasDerivAt_pow (n := 3) (0 : ℝ))
  have hderiv0 : deriv f 0 = 0 := hderiv_at_zero.deriv
  have hbij : Function.Bijective f := ⟨hstrict.injective, hsurj⟩
  classical
  let e := Equiv.ofBijective f hbij
  have hleft : Function.LeftInverse e.symm f := e.left_inv
  have hright : Function.RightInverse e.symm f := e.right_inv
  have hnotDiff : ¬ DifferentiableAt ℝ e.symm 0 := by
    intro hg
    have hcomp_fun : (fun x => e.symm (f x)) = fun x : ℝ => x := funext hleft
    have hf0 : f 0 = 0 := by simp [f]
    have hchain : HasDerivAt (fun x => e.symm (f x)) 0 0 := by
      have hg' : HasDerivAt e.symm (deriv e.symm 0) (f 0) := by
        simpa [hf0] using hg.hasDerivAt
      have := hg'.comp 0 hderiv_at_zero
      simpa [hf0, f] using this
    have hid : HasDerivAt (fun x : ℝ => e.symm (f x)) 1 0 := by
      simpa [hcomp_fun] using (hasDerivAt_id' (0 : ℝ))
    have : (0 : ℝ) = 1 := hchain.unique hid
    exact zero_ne_one this
  refine ⟨hcontDiff, hstrict, hsurj, hderiv0, ?_⟩
  refine ⟨e.symm, hleft, hright, hnotDiff⟩

end Section04
end Chap04
