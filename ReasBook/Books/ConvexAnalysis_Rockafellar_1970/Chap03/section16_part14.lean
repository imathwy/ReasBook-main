/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Weiran Shi, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section16_part13

section Chap03
section Section16

open scoped BigOperators
open scoped Pointwise
open scoped Topology
open Filter
open Set

/-! ### Bridging `EuclideanSpace` sublevel-closure to `Fin n → ℝ` -/

/-- Closure of a `≤ 1` sublevel set matches the `≤ 1` sublevel of the convex-function closure
when the domain is `Fin n → ℝ`. -/
lemma section16_closure_sublevel_eq_sublevel_convexFunctionClosure_one_fin {n : Nat}
    {h : (Fin n → ℝ) → EReal}
    (hh : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (hInf : iInf (fun x => h x) < (1 : EReal)) :
    closure {xStar : Fin n → ℝ | h xStar ≤ (1 : EReal)} =
      {xStar : Fin n → ℝ | convexFunctionClosure h xStar ≤ (1 : EReal)} := by
  classical
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let A : Set (EuclideanSpace ℝ (Fin n)) :=
    {x : EuclideanSpace ℝ (Fin n) | h (x : Fin n → ℝ) ≤ (1 : EReal)}
  let B : Set (EuclideanSpace ℝ (Fin n)) :=
    {x : EuclideanSpace ℝ (Fin n) | convexFunctionClosure h (x : Fin n → ℝ) ≤ (1 : EReal)}
  have hEq :
      closure A = B :=
    section16_closure_sublevel_eq_sublevel_convexFunctionClosure_one (n := n) (h := h) hh hInf
  have hEq' : closure (e '' A) = e '' B := by
    have hEq'' : (e.toHomeomorph) '' closure A = (e.toHomeomorph) '' B := by
      simpa using congrArg (fun S => (e.toHomeomorph) '' S) hEq
    have hcl :
        (e.toHomeomorph) '' closure A = closure ((e.toHomeomorph) '' A) := by
      simpa using (Homeomorph.image_closure (h := e.toHomeomorph) (s := A))
    have hEq''' : closure ((e.toHomeomorph) '' A) = (e.toHomeomorph) '' B := by
      calc
        closure ((e.toHomeomorph) '' A) = (e.toHomeomorph) '' closure A := by
            simpa using hcl.symm
        _ = (e.toHomeomorph) '' B := hEq''
    simpa using hEq'''
  have hA : e '' A = {xStar : Fin n → ℝ | h xStar ≤ (1 : EReal)} := by
    ext xStar
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [A] using hx
    · intro hx
      refine ⟨e.symm xStar, ?_, by simp [e]⟩
      simpa [A, e] using hx
  have hB : e '' B = {xStar : Fin n → ℝ | convexFunctionClosure h xStar ≤ (1 : EReal)} := by
    ext xStar
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [B] using hx
    · intro hx
      refine ⟨e.symm xStar, ?_, by simp [e]⟩
      simpa [B, e] using hx
  simpa [hA, hB] using hEq'

/-- The support function of a nonempty convex set agrees with that of its closure. -/
lemma section16_supportFunctionEReal_eq_supportFunctionEReal_closure {n : ℕ}
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCne : C.Nonempty) :
    supportFunctionEReal C = supportFunctionEReal (closure C) := by
  calc
    supportFunctionEReal C =
        fenchelConjugate n (indicatorFunction C) := by
          symm
          exact section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal (C := C)
    _ = fenchelConjugate n (convexFunctionClosure (indicatorFunction C)) := by
          symm
          exact
            (fenchelConjugate_eq_of_convexFunctionClosure (n := n)
              (f := indicatorFunction C))
    _ = fenchelConjugate n (indicatorFunction (closure C)) := by
          simp [section16_convexFunctionClosure_indicatorFunction_eq_indicatorFunction_closure,
            hC, hCne]
    _ = supportFunctionEReal (closure C) := by
          exact
            section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal
              (C := closure C)

/-- The support function is nonnegative when `0` lies in the closure. -/
lemma section16_supportFunctionEReal_nonneg_of_zero_mem_closure {n : ℕ}
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCne : C.Nonempty)
    (h0 : (0 : Fin n → ℝ) ∈ closure C) (xStar : Fin n → ℝ) :
    (0 : EReal) ≤ supportFunctionEReal C xStar := by
  have hmem :
      (0 : EReal) ∈
        {z : EReal | ∃ x ∈ closure C, z = ((dotProduct x xStar : ℝ) : EReal)} := by
    refine ⟨0, h0, ?_⟩
    simp
  have hnonneg_closure : (0 : EReal) ≤ supportFunctionEReal (closure C) xStar := by
    unfold supportFunctionEReal
    exact le_sSup hmem
  have hEq := section16_supportFunctionEReal_eq_supportFunctionEReal_closure (C := C) hC hCne
  simpa [hEq] using hnonneg_closure

/-- Points in the `≤ 1` sublevel of the hull lie in the closure of the convex hull
of the `≤ 1` sublevels. -/
lemma section16_mem_closure_convexHull_iUnion_sublevels_of_hle_one {n : ℕ} {ι : Sort _}
    [Nonempty ι] (C : ι → Set (Fin n → ℝ)) (hC : ∀ i, Convex ℝ (C i))
    (hCne : ∀ i, (C i).Nonempty) (h0 : ∀ i, (0 : Fin n → ℝ) ∈ closure (C i))
    {xStar : Fin n → ℝ}
    (hle : convexHullFunctionFamily (fun i => supportFunctionEReal (C i)) xStar ≤ (1 : EReal)) :
    xStar ∈
      closure
        (convexHull ℝ
          (⋃ i, {xStar : Fin n → ℝ | supportFunctionEReal (C i) xStar ≤ (1 : EReal)})) := by
  classical
  let g : ι → (Fin n → ℝ) → EReal := fun i => supportFunctionEReal (C i)
  let K : Set (Fin n → ℝ) :=
    convexHull ℝ (⋃ i, {xStar : Fin n → ℝ | g i xStar ≤ (1 : EReal)})
  have hpos : ∀ i, PositivelyHomogeneous (g i) := by
    intro i
    exact
      (section13_supportFunctionEReal_closedProperConvex_posHom (n := n) (C := C i) (hCne i)
            (hC i)).2.2
  have hnonneg : ∀ i x, (0 : EReal) ≤ g i x := by
    intro i x
    have hnonneg' :=
      section16_supportFunctionEReal_nonneg_of_zero_mem_closure
        (C := C i) (hC i) (hCne i) (h0 i) x
    simpa [g] using hnonneg'
  have hmemK : ∀ ε : ℝ, ε > 0 → ((1 + ε)⁻¹) • xStar ∈ closure K := by
    intro ε hε
    obtain ⟨μ, hμlt, hmem⟩ :=
      section16_exists_mem_convexHull_union_epigraph_lt_one_add_eps_of_hle_one (g := g)
        (xStar := xStar) (ε := ε) hε (by simpa [g] using hle)
    have hmem' :
        (xStar, 1 + ε) ∈
          convexHull ℝ (⋃ i, epigraph (S := (Set.univ : Set (Fin n → ℝ))) (g i)) := by
      refine
        section16_convexHull_union_epigraph_mono_snd (g := g) (x := xStar) (μ := μ)
          (μ' := 1 + ε) hmem ?_
      linarith
    have hnorm :
        ((1 + ε)⁻¹) • xStar ∈
          closure
            (convexHull ℝ (⋃ i, {xStar : Fin n → ℝ | g i xStar ≤ (1 : EReal)})) := by
      exact
        section16_mem_convexHull_iUnion_sublevels_one_of_mem_convexHull_union_epigraph_one_add_eps
          (g := g) hpos hnonneg hε hmem'
    simpa [K] using hnorm
  have hlim :
      Tendsto (fun ε : ℝ => ((1 + ε)⁻¹) • xStar) (𝓝[>] (0 : ℝ)) (𝓝 xStar) := by
    have hcont_add : ContinuousAt (fun ε : ℝ => (1 + ε)) 0 := by
      simpa using (continuousAt_const.add continuousAt_id)
    have hcont_inv' : ContinuousAt (fun t : ℝ => t⁻¹) ((1 : ℝ) + 0) := by
      have hne : ((1 : ℝ) + 0) ≠ 0 := by simp
      exact continuousAt_inv₀ hne
    have hcont_inv : ContinuousAt (fun ε : ℝ => (1 + ε)⁻¹) 0 :=
      hcont_inv'.comp hcont_add
    have hcont :
        ContinuousAt (fun ε : ℝ => ((1 + ε)⁻¹) • xStar) 0 :=
      hcont_inv.smul continuousAt_const
    have hlim0 :
        Tendsto (fun ε : ℝ => ((1 + ε)⁻¹) • xStar) (𝓝 (0 : ℝ)) (𝓝 xStar) := by
      simpa using hcont.tendsto
    exact hlim0.mono_left nhdsWithin_le_nhds
  have hmem_event :
      ∀ᶠ ε in (𝓝[>] (0 : ℝ)),
        ((1 + ε)⁻¹) • xStar ∈ closure K := by
    have hpos_event : ∀ᶠ ε in (𝓝[>] (0 : ℝ)), ε ∈ Ioi (0 : ℝ) := self_mem_nhdsWithin
    refine hpos_event.mono ?_
    intro ε hε
    have hε' : 0 < ε := by simpa using hε
    exact hmemK ε hε'
  have hxStar : xStar ∈ closure (closure K) := mem_closure_of_tendsto hlim hmem_event
  have hxStar' : xStar ∈ closure K := by simpa [closure_closure] using hxStar
  simpa [K, g] using hxStar'

/-- The `≤ 1` sublevel of the convex-hull support family has the same closure as the convex hull
of the `≤ 1` sublevels of the family. -/
lemma section16_closure_sublevel_convexHullFunctionFamily_supportFamily_one_eq_closure_convexHull_iUnion_sublevels
    {n : ℕ} {ι : Sort _} [Nonempty ι] (C : ι → Set (Fin n → ℝ))
    (hC : ∀ i, Convex ℝ (C i)) (hCne : ∀ i, (C i).Nonempty)
    (h0 : ∀ i, (0 : Fin n → ℝ) ∈ closure (C i)) :
    let g : ι → (Fin n → ℝ) → EReal := fun i => supportFunctionEReal (C i)
    let h := convexHullFunctionFamily g
    closure {xStar : Fin n → ℝ | h xStar ≤ (1 : EReal)} =
      closure (convexHull ℝ (⋃ i, {xStar : Fin n → ℝ | g i xStar ≤ (1 : EReal)})) := by
  classical
  let g : ι → (Fin n → ℝ) → EReal := fun i => supportFunctionEReal (C i)
  let h := convexHullFunctionFamily g
  have hgoal :
      closure {xStar : Fin n → ℝ | h xStar ≤ (1 : EReal)} =
        closure (convexHull ℝ (⋃ i, {xStar : Fin n → ℝ | g i xStar ≤ (1 : EReal)})) := by
    have hminor :
        ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h ∧
          (∀ i, h ≤ g i) ∧
          ∀ h' : (Fin n → ℝ) → EReal,
            ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h' →
            (∀ i, h' ≤ g i) → h' ≤ h := by
      simpa [h] using (convexHullFunctionFamily_greatest_convex_minorant (f := g))
    have hconvfun : ConvexFunction h := by
      simpa [ConvexFunction] using hminor.1
    have hconvset : Convex ℝ {xStar : Fin n → ℝ | h xStar ≤ (1 : EReal)} := by
      have hlevel := (convexFunction_level_sets_convex (f := h) hconvfun (1 : EReal))
      exact hlevel.2
    have hsubset :
        (⋃ i, {xStar : Fin n → ℝ | g i xStar ≤ (1 : EReal)}) ⊆
          {xStar : Fin n → ℝ | h xStar ≤ (1 : EReal)} := by
      intro x hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hi⟩
      have hle : h x ≤ g i x := (hminor.2.1 i) x
      exact le_trans hle (by simpa using hi)
    have hsubset_conv :
        convexHull ℝ (⋃ i, {xStar : Fin n → ℝ | g i xStar ≤ (1 : EReal)}) ⊆
          {xStar : Fin n → ℝ | h xStar ≤ (1 : EReal)} := by
      exact convexHull_min hsubset hconvset
    have hclosure :
        closure (convexHull ℝ (⋃ i, {xStar : Fin n → ℝ | g i xStar ≤ (1 : EReal)})) ⊆
          closure {xStar : Fin n → ℝ | h xStar ≤ (1 : EReal)} := by
      exact closure_mono hsubset_conv
    refine le_antisymm ?_ ?_
    ·
      have hsubset' :
          {xStar : Fin n → ℝ | h xStar ≤ (1 : EReal)} ⊆
            closure
              (convexHull ℝ (⋃ i, {xStar : Fin n → ℝ | g i xStar ≤ (1 : EReal)})) := by
        intro xStar hx
        have hx' :
            xStar ∈
              closure
                (convexHull ℝ
                  (⋃ i,
                    {xStar : Fin n → ℝ | supportFunctionEReal (C i) xStar ≤ (1 : EReal)})) := by
          simpa [g, h] using
            (section16_mem_closure_convexHull_iUnion_sublevels_of_hle_one (C := C) hC hCne h0
              (xStar := xStar) (by simpa [h] using hx))
        simpa [g] using hx'
      have hclosure' :
          closure {xStar : Fin n → ℝ | h xStar ≤ (1 : EReal)} ⊆
            closure
              (closure
                (convexHull ℝ (⋃ i, {xStar : Fin n → ℝ | g i xStar ≤ (1 : EReal)}))) :=
        closure_mono hsubset'
      simpa [closure_closure] using hclosure'
    · exact hclosure
  simpa [g, h] using hgoal

/-- Corollary 16.5.2.2: Let `C i` be a convex set in `ℝ^n` for each `i` in a nonempty index set,
assume the intersection of the closures is nonempty, and that this intersection contains `0`.
Then

`(⋂ i, closure (C i))^∘ = closure (convexHull ℝ (⋃ i, (C i)^∘))`.

In this development, the polar of a set `S` is represented by
`{xStar | ∀ x ∈ S, (dotProduct x xStar : ℝ) ≤ 1}`. -/
theorem section16_polar_iInter_closure_eq_closure_convexHull_iUnion_polars {n : ℕ} {ι : Sort _}
    [Nonempty ι] (C : ι → Set (Fin n → ℝ)) (hC : ∀ i, Convex ℝ (C i))
    (h0 : (0 : Fin n → ℝ) ∈ ⋂ i, closure (C i)) (hInter : (⋂ i, closure (C i)).Nonempty) :
    {xStar : Fin n → ℝ | ∀ x ∈ (⋂ i, closure (C i)), (dotProduct x xStar : ℝ) ≤ 1} =
      closure
        (convexHull ℝ (⋃ i, {xStar : Fin n → ℝ | ∀ x ∈ C i, (dotProduct x xStar : ℝ) ≤ 1})) := by
  classical
  have hCne : ∀ i, (C i).Nonempty := by
    intro i
    rcases hInter with ⟨x0, hx0⟩
    have hx0i : x0 ∈ closure (C i) := (Set.mem_iInter.1 hx0 i)
    by_contra hne
    have hCi : C i = ∅ := Set.not_nonempty_iff_eq_empty.1 hne
    simp [hCi] at hx0i
  have h0i : ∀ i, (0 : Fin n → ℝ) ∈ closure (C i) := by
    intro i
    exact (Set.mem_iInter.1 h0 i)
  let g : ι → (Fin n → ℝ) → EReal := fun i => supportFunctionEReal (C i)
  let h := convexHullFunctionFamily g
  have hpolar :
      {xStar : Fin n → ℝ | ∀ x ∈ (⋂ i, closure (C i)), (dotProduct x xStar : ℝ) ≤ 1} =
        {xStar : Fin n → ℝ |
          supportFunctionEReal (⋂ i, closure (C i)) xStar ≤ (1 : EReal)} := by
    simpa using (section16_polar_eq_sublevel_deltaStar (C := ⋂ i, closure (C i)))
  have hsupport :
      supportFunctionEReal (⋂ i, closure (C i)) = convexFunctionClosure h := by
    simpa [h] using
      (section16_supportFunctionEReal_iInter_closure_eq_convexFunctionClosure_convexHullFunctionFamily
        (C := C) hC hCne)
  have hproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h ∧
        iInf (fun xStar => h xStar) < (1 : EReal) := by
    simpa [g, h] using
      (section16_properConvexFunctionOn_convexHullFunctionFamily_supportFamily_of_exists_common_point
        (C := C) hC hInter)
  have hsub :
      {xStar : Fin n → ℝ | convexFunctionClosure h xStar ≤ (1 : EReal)} =
        closure {xStar : Fin n → ℝ | h xStar ≤ (1 : EReal)} := by
    simpa using
      (section16_closure_sublevel_eq_sublevel_convexFunctionClosure_one_fin (h := h) hproper.1
        hproper.2).symm
  have hsublevels :
      (⋃ i, {xStar : Fin n → ℝ | g i xStar ≤ (1 : EReal)}) =
        (⋃ i, {xStar : Fin n → ℝ | ∀ x ∈ C i, (dotProduct x xStar : ℝ) ≤ 1}) := by
    ext xStar
    constructor
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
      have hx' :
          xStar ∈ {xStar : Fin n → ℝ | supportFunctionEReal (C i) xStar ≤ (1 : EReal)} := by
        simpa [g] using hx
      have hx'' :
          xStar ∈ {xStar : Fin n → ℝ | ∀ x ∈ C i, (dotProduct x xStar : ℝ) ≤ 1} := by
        simpa [(section16_polar_eq_sublevel_deltaStar (C := C i)).symm] using hx'
      exact Set.mem_iUnion.2 ⟨i, hx''⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨i, hx⟩
      have hx' :
          xStar ∈ {xStar : Fin n → ℝ | supportFunctionEReal (C i) xStar ≤ (1 : EReal)} := by
        simpa [section16_polar_eq_sublevel_deltaStar (C := C i)] using hx
      have hx'' :
          xStar ∈ {xStar : Fin n → ℝ | g i xStar ≤ (1 : EReal)} := by
        simpa [g] using hx'
      exact Set.mem_iUnion.2 ⟨i, hx''⟩
  calc
    {xStar : Fin n → ℝ | ∀ x ∈ (⋂ i, closure (C i)), (dotProduct x xStar : ℝ) ≤ 1} =
        {xStar : Fin n → ℝ |
          supportFunctionEReal (⋂ i, closure (C i)) xStar ≤ (1 : EReal)} := hpolar
    _ = {xStar : Fin n → ℝ | convexFunctionClosure h xStar ≤ (1 : EReal)} := by
          simp [hsupport]
    _ = closure {xStar : Fin n → ℝ | h xStar ≤ (1 : EReal)} := hsub
    _ = closure (convexHull ℝ (⋃ i, {xStar : Fin n → ℝ | g i xStar ≤ (1 : EReal)})) := by
          simpa [g, h] using
            (section16_closure_sublevel_convexHullFunctionFamily_supportFamily_one_eq_closure_convexHull_iUnion_sublevels
              (C := C) hC hCne h0i)
    _ = closure
        (convexHull ℝ (⋃ i, {xStar : Fin n → ℝ | ∀ x ∈ C i, (dotProduct x xStar : ℝ) ≤ 1})) := by
          simp [hsublevels]

/-- A common relative-interior point yields finite `iSup` for a finite family. -/
lemma section16_exists_common_ri_point_finite_iSup_ne_top_of_common_closure_effectiveDomain
    {n : ℕ} {ι : Type _} [Fintype ι] [Nonempty ι]
    (f : ι → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) (C : Set (Fin n → ℝ))
    (hC : ∀ i, closure (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) = C) :
    ∃ x0 : EuclideanSpace ℝ (Fin n),
      (∀ i,
          x0 ∈
            euclideanRelativeInterior n
              (Set.image (EuclideanSpace.equiv (Fin n) ℝ).symm
                (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))) ∧
        (iSup (fun i => f i ((EuclideanSpace.equiv (Fin n) ℝ) x0))) ≠ (⊤ : EReal) := by
  classical
  obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
  let e := (EuclideanSpace.equiv (Fin n) ℝ)
  let domE : ι → Set (EuclideanSpace ℝ (Fin n)) :=
    fun i =>
      Set.image e.symm (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))
  let CE : Set (EuclideanSpace ℝ (Fin n)) := Set.image e.symm C
  have hconv_dom :
      ∀ i, Convex ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) := by
    intro i
    exact
      effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ))) (f := f i) (hf i).1
  have hconv_domE : ∀ i, Convex ℝ (domE i) := by
    intro i
    exact (hconv_dom i).linear_image e.symm.toLinearMap
  have hne_dom :
      ∀ i, (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)).Nonempty := by
    intro i
    exact section13_effectiveDomain_nonempty_of_proper (n := n) (f := f i) (hf i)
  have hconv_C : Convex ℝ C := by
    have hconv0 :
        Convex ℝ (closure (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i0))) :=
      (hconv_dom i0).closure
    simpa [hC i0] using hconv0
  have hconv_CE : Convex ℝ CE := by
    exact hconv_C.linear_image e.symm.toLinearMap
  have hCne : C.Nonempty := by
    have hne0 :
        (closure (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i0))).Nonempty :=
      (hne_dom i0).closure
    simpa [hC i0] using hne0
  have hCEne : CE.Nonempty := by
    rcases hCne with ⟨x, hx⟩
    exact ⟨e.symm x, ⟨x, hx, rfl⟩⟩
  have hcl_domE : ∀ i, closure (domE i) = CE := by
    intro i
    have hcl :=
      (e.symm.toHomeomorph.image_closure
        (s := effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))).symm
    simpa [domE, CE, hC i] using hcl
  have hCE_closed : IsClosed CE := by
    have hcl0 : closure (domE i0) = CE := hcl_domE i0
    simpa [hcl0] using (isClosed_closure : IsClosed (closure (domE i0)))
  obtain ⟨x0, hx0C⟩ :
      (euclideanRelativeInterior n CE).Nonempty :=
    (euclideanRelativeInterior_closure_convex_affineSpan n CE hconv_CE).2.2.2.2 hCEne
  have hri_eq :
      ∀ i, euclideanRelativeInterior n (domE i) = euclideanRelativeInterior n CE := by
    intro i
    have hcl' : closure (domE i) = closure CE := by
      calc
        closure (domE i) = CE := hcl_domE i
        _ = closure CE := by simp
    exact euclideanRelativeInterior_eq_of_closure_eq n (domE i) CE (hconv_domE i) hconv_CE hcl'
  have hx0ri : ∀ i, x0 ∈ euclideanRelativeInterior n (domE i) := by
    intro i
    simpa [hri_eq i] using hx0C
  have hx0_dom :
      ∀ i, (e x0) ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := by
    intro i
    have hx0_mem : x0 ∈ domE i := (euclideanRelativeInterior_subset_closure n (domE i)).1 (hx0ri i)
    rcases hx0_mem with ⟨x', hx', hx0_eq⟩
    have hx_eq : x' = e x0 := by
      simpa using congrArg e hx0_eq
    simpa [hx_eq] using hx'
  have hlt_top : iSup (fun i => f i (e x0)) < (⊤ : EReal) := by
    let eFin : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
    have hm : 0 < Fintype.card ι := by
      simpa using (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι))
    have hlt' :
        iSup (fun k : Fin (Fintype.card ι) => f (eFin.symm k) (e x0)) < (⊤ : EReal) := by
      refine iSup_lt_of_forall_lt_fin (m := Fintype.card ι) (r := (⊤ : EReal)) hm ?_
      intro k
      have hx0_lt :
          f (eFin.symm k) (e x0) < (⊤ : EReal) := by
        have hx0' :
            (e x0) ∈ (Set.univ : Set (Fin n → ℝ)) ∧
              f (eFin.symm k) (e x0) < (⊤ : EReal) := by
          simpa [effectiveDomain_eq] using (hx0_dom (eFin.symm k))
        exact hx0'.2
      exact hx0_lt
    have hcongr :
        iSup (fun i : ι => f i (e x0)) =
          iSup (fun k : Fin (Fintype.card ι) => f (eFin.symm k) (e x0)) := by
      refine (Equiv.iSup_congr eFin ?_)
      intro i
      simp
    simpa [hcongr] using hlt'
  exact ⟨x0, hx0ri, ne_of_lt hlt_top⟩

/-- Closure commutes with a finite `iSup` under a common domain closure. -/
lemma section16_convexFunctionClosure_iSup_eq_iSup_convexFunctionClosure_of_fintype_of_common_closure_effectiveDomain
    {n : ℕ} {ι : Type _} [Fintype ι] [Nonempty ι]
    (f : ι → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) (C : Set (Fin n → ℝ))
    (hC : ∀ i, closure (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) = C) :
    convexFunctionClosure (fun x => iSup (fun i => f i x)) =
      fun x => iSup (fun i => convexFunctionClosure (f i) x) := by
  classical
  let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
  let fSup : (Fin n → Real) → EReal := fun x => iSup (fun i => f i x)
  let f0_plus : ι → (Fin n → Real) → EReal := fun _ _ => (0 : EReal)
  obtain ⟨x0, hx0ri, hx0_top⟩ :=
    section16_exists_common_ri_point_finite_iSup_ne_top_of_common_closure_effectiveDomain
      (f := f) hf C hC
  have hx0_bot : fSup x0 ≠ (⊥ : EReal) := by
    obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
    have hle : f i0 x0 ≤ fSup x0 := le_iSup (fun i => f i x0) i0
    intro hbot
    have hle' : f i0 x0 ≤ (⊥ : EReal) := by
      simpa [fSup, hbot] using hle
    have hbot_i0 : f i0 x0 = (⊥ : EReal) := le_antisymm hle' bot_le
    exact (hf i0).2.2 x0 (by simp) hbot_i0
  have hx0_top' : fSup (e.symm x0) ≠ (⊤ : EReal) := by
    have hx :
        (e x0) = x0.ofLp := by
      simpa using (section16_euclideanSpace_equiv_toLp (n := n) (x := x0.ofLp))
    have hx' : e.symm x0.ofLp = x0 := by
      simp [e]
    simpa [fSup, hx, hx'] using hx0_top
  have hx0_bot' : fSup (e.symm x0) ≠ (⊥ : EReal) := by
    have hx :
        (e x0) = x0.ofLp := by
      simpa using (section16_euclideanSpace_equiv_toLp (n := n) (x := x0.ofLp))
    have hx' : e.symm x0.ofLp = x0 := by
      simp [e]
    simpa [fSup, hx, hx'] using hx0_bot
  have hkey :=
    (iSup_closed_proper_convex_recession_and_closure (n := n) (I := ι)
        (f := f) (f0_plus := f0_plus) hf)
  simpa [fSup] using (hkey.2 ⟨x0, hx0ri, hx0_top', hx0_bot'⟩)

/-- Conjugates share a common recession function under a common domain closure. -/
lemma section16_common_recession_fenchelConjugate_of_common_closure_effectiveDomain
    {n : ℕ} {ι : Type _} [Fintype ι] [Nonempty ι]
    (f : ι → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) (C : Set (Fin n → ℝ))
    (hC : ∀ i, closure (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) = C) :
    ∀ i, recessionFunction (fenchelConjugate n (f i)) = supportFunctionEReal C := by
  intro i
  have hdom_ne :
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)).Nonempty :=
    section13_effectiveDomain_nonempty_of_proper (n := n) (f := f i) (hf i)
  have hconv_dom :
      Convex ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) :=
    effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ))) (f := f i) (hf i).1
  have hsupport :
      supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) =
        recessionFunction (fenchelConjugate n (f i)) := by
    simpa using
      (supportFunctionEReal_effectiveDomain_eq_recession_fenchelConjugate (n := n) (f := f i)
        (hf := hf i) (fStar0_plus := recessionFunction (fenchelConjugate n (f i)))
        (hfStar0_plus := by intro y; rfl))
  calc
    recessionFunction (fenchelConjugate n (f i)) =
        supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) := by
          exact hsupport.symm
    _ = supportFunctionEReal (closure (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) := by
          exact
            section16_supportFunctionEReal_eq_supportFunctionEReal_closure hconv_dom hdom_ne
    _ = supportFunctionEReal C := by
          simp [hC i]

/-- Closedness and attainment for the convex hull of conjugates under common domain closure. -/
lemma section16_convexHullFunctionFamily_fenchelConjugate_closed_and_attained_of_common_closure_effectiveDomain
    {n : ℕ} {ι : Type _} [Fintype ι] [Nonempty ι]
    (f : ι → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) (C : Set (Fin n → ℝ))
    (hC : ∀ i, closure (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) = C) :
    let g : ι → (Fin n → ℝ) → EReal := fun i => fenchelConjugate n (f i)
    (convexFunctionClosure (convexHullFunctionFamily g) = convexHullFunctionFamily g) ∧
      (∀ xStar : Fin n → ℝ,
        ∃ (lam : ι → ℝ) (xStar_i : ι → Fin n → ℝ),
          (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1 ∧
            (∑ i, lam i • xStar_i i) = xStar ∧
              convexHullFunctionFamily g xStar =
                ∑ i, ((lam i : ℝ) : EReal) * g i (xStar_i i)) := by
  classical
  intro g
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let g' : Fin (Fintype.card ι) → (Fin n → ℝ) → EReal := fun k => g (e.symm k)
  have hclosed' : ∀ k, ClosedConvexFunction (g' k) := by
    intro k
    have h := fenchelConjugate_closedConvex (n := n) (f := f (e.symm k))
    exact ⟨h.2, h.1⟩
  have hproper' :
      ∀ k, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (g' k) := by
    intro k
    simpa [g', g] using
      (proper_fenchelConjugate_of_proper (n := n) (f := f (e.symm k)) (hf (e.symm k)))
  have hk :
      ∀ (k : Fin (Fintype.card ι)) (y : Fin n → ℝ),
        supportFunctionEReal C y =
          sSup { r : EReal | ∃ x : Fin n → ℝ, r = g' k (x + y) - g' k x } := by
    intro k y
    have hrec :
        recessionFunction (g' k) = supportFunctionEReal C := by
      simpa [g', g] using
        (section16_common_recession_fenchelConjugate_of_common_closure_effectiveDomain
          (f := f) hf C hC (e.symm k))
    have hrec_y :
        recessionFunction (g' k) y =
          sSup { r : EReal | ∃ x : Fin n → ℝ, r = g' k (x + y) - g' k x } := by
      simpa using (section16_recessionFunction_eq_sSup_unrestricted (f := g' k) y)
    simpa [hrec] using hrec_y
  have hm : 0 < Fintype.card ι := by
    simpa using (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι))
  have hcor :=
    convexHullFunctionFamily_closed_proper_recession_and_attained
      (f := g') (k := supportFunctionEReal C) hclosed' hproper' hk hm
  have hconv_eq :
      convexHullFunctionFamily g' = convexHullFunctionFamily g := by
    funext x
    have hunion :
        (⋃ k, epigraph (Set.univ : Set (Fin n → ℝ)) (g' k)) =
          ⋃ i, epigraph (Set.univ : Set (Fin n → ℝ)) (g i) := by
      ext p
      constructor
      · intro hp
        rcases Set.mem_iUnion.mp hp with ⟨k, hk⟩
        refine Set.mem_iUnion.mpr ?_
        refine ⟨e.symm k, ?_⟩
        simpa [g'] using hk
      · intro hp
        rcases Set.mem_iUnion.mp hp with ⟨i, hi⟩
        refine Set.mem_iUnion.mpr ?_
        refine ⟨e i, ?_⟩
        simpa [g'] using hi
    simp [convexHullFunctionFamily, hunion]
  have hclosed_g : ClosedConvexFunction (convexHullFunctionFamily g) := by
    have hclosed_g' : ClosedConvexFunction (convexHullFunctionFamily g') := hcor.1
    simpa [hconv_eq] using hclosed_g'
  have hproper_g :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (convexHullFunctionFamily g) := by
    have hproper_g' :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (convexHullFunctionFamily g') :=
      hcor.2.1
    simpa [hconv_eq] using hproper_g'
  have hbot_g : ∀ x, convexHullFunctionFamily g x ≠ (⊥ : EReal) := by
    intro x
    exact hproper_g.2.2 x (by simp)
  have hclosure :
      convexFunctionClosure (convexHullFunctionFamily g) = convexHullFunctionFamily g := by
    exact convexFunctionClosure_eq_of_closedConvexFunction (f := convexHullFunctionFamily g)
      hclosed_g hbot_g
  refine ⟨hclosure, ?_⟩
  intro xStar
  have hreach := hcor.2.2.2 xStar
  rcases hreach with ⟨lam, x', hlam, hsum, hsumx, hval⟩
  refine ⟨(fun i => lam (e i)), (fun i => x' (e i)), ?_, ?_, ?_, ?_⟩
  · intro i
    exact hlam (e i)
  · have hsum' :
        (∑ i : ι, lam (e i)) = ∑ k : Fin (Fintype.card ι), lam k := by
      refine Fintype.sum_equiv (e := e) (f := fun i => lam (e i)) (g := fun k => lam k) ?_
      intro i
      rfl
    simpa [hsum'] using hsum
  · have hsumx' :
        (∑ i : ι, lam (e i) • x' (e i)) =
          ∑ k : Fin (Fintype.card ι), lam k • x' k := by
      refine Fintype.sum_equiv (e := e)
        (f := fun i => lam (e i) • x' (e i)) (g := fun k => lam k • x' k) ?_
      intro i
      rfl
    simpa [hsumx'] using hsumx
  · have hsumr' :
        ∑ k : Fin (Fintype.card ι), ((lam k : ℝ) : EReal) * g' k (x' k) =
          ∑ i : ι, ((lam (e i) : ℝ) : EReal) * g i (x' (e i)) := by
      refine Fintype.sum_equiv (e := e.symm)
        (f := fun k => ((lam k : ℝ) : EReal) * g' k (x' k))
        (g := fun i => ((lam (e i) : ℝ) : EReal) * g i (x' (e i))) ?_
      intro k
      simp [g', g]
    have hconvx :
        convexHullFunctionFamily g xStar = convexHullFunctionFamily g' xStar := by
      simp [hconv_eq]
    simpa [hconv_eq, hsumr'] using hval

/-- Reindexing a function family by an equivalence does not change its convex hull. -/
lemma section16_convexHullFunctionFamily_congr_equiv {n : ℕ} {ι κ : Sort _}
    (e : ι ≃ κ) (g : ι → (Fin n → ℝ) → EReal) :
    convexHullFunctionFamily (fun k => g (e.symm k)) = convexHullFunctionFamily g := by
  classical
  funext x
  have hunion :
      (⋃ k, epigraph (Set.univ : Set (Fin n → ℝ)) (g (e.symm k))) =
        ⋃ i, epigraph (Set.univ : Set (Fin n → ℝ)) (g i) := by
    ext p
    constructor
    · intro hp
      rcases Set.mem_iUnion.mp hp with ⟨k, hk⟩
      refine Set.mem_iUnion.mpr ?_
      refine ⟨e.symm k, ?_⟩
      simpa using hk
    · intro hp
      rcases Set.mem_iUnion.mp hp with ⟨i, hi⟩
      refine Set.mem_iUnion.mpr ?_
      refine ⟨e i, ?_⟩
      simpa using hi
  simp [convexHullFunctionFamily, hunion]

/-- Convex-combination formula with full-index sums on a finite index type. -/
lemma section16_convexHullFunctionFamily_eq_sInf_convexCombination_univ_fintype
    {n : ℕ} {ι : Type _} [Fintype ι] [Nonempty ι]
    (f : ι → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) :
    ∀ x : Fin n → ℝ,
      convexHullFunctionFamily f x =
        sInf { r : EReal |
          ∃ (lam : ι → ℝ) (x' : ι → Fin n → ℝ),
            (∀ i, 0 ≤ lam i) ∧
            (∑ i, lam i) = 1 ∧
            (∑ i, lam i • x' i) = x ∧
            r = ∑ i, ((lam i : ℝ) : EReal) * f i (x' i) } := by
  classical
  intro x
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let g : Fin (Fintype.card ι) → (Fin n → ℝ) → EReal := fun k => f (e.symm k)
  have hproper :
      ∀ k, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (g k) := by
    intro k
    simpa [g] using (hf (e.symm k))
  let Sg : Set EReal :=
    { r : EReal |
      ∃ (lam : Fin (Fintype.card ι) → ℝ) (x' : Fin (Fintype.card ι) → Fin n → ℝ),
        (∀ i, 0 ≤ lam i) ∧
        (∑ i, lam i) = 1 ∧
        (∑ i, lam i • x' i) = x ∧
        r = ∑ i, ((lam i : ℝ) : EReal) * g i (x' i) }
  let Sf : Set EReal :=
    { r : EReal |
      ∃ (lam : ι → ℝ) (x' : ι → Fin n → ℝ),
        (∀ i, 0 ≤ lam i) ∧
        (∑ i, lam i) = 1 ∧
        (∑ i, lam i • x' i) = x ∧
        r = ∑ i, ((lam i : ℝ) : EReal) * f i (x' i) }
  have hformula :
      convexHullFunctionFamily g x = sInf Sg := by
    simpa [Sg] using
      (convexHullFunctionFamily_eq_sInf_convexCombination_univ (f := g) hproper x)
  have hconv : convexHullFunctionFamily g = convexHullFunctionFamily f := by
    simpa [g] using (section16_convexHullFunctionFamily_congr_equiv (e := e) (g := f))
  have hS : Sg = Sf := by
    ext r
    constructor
    · intro hr
      rcases hr with ⟨lam, x', hlam, hsum, hsumx, rfl⟩
      refine ⟨(fun i => lam (e i)), (fun i => x' (e i)), ?_, ?_, ?_, ?_⟩
      · intro i
        exact hlam (e i)
      · have hsum' :
            (∑ i : ι, lam (e i)) = ∑ k : Fin (Fintype.card ι), lam k := by
          refine Fintype.sum_equiv (e := e) (f := fun i => lam (e i))
            (g := fun k => lam k) ?_
          intro i
          rfl
        simpa [hsum'] using hsum
      · have hsumx' :
            (∑ i : ι, lam (e i) • x' (e i)) =
              ∑ k : Fin (Fintype.card ι), lam k • x' k := by
          refine Fintype.sum_equiv (e := e) (f := fun i => lam (e i) • x' (e i))
            (g := fun k => lam k • x' k) ?_
          intro i
          rfl
        simpa [hsumx'] using hsumx
      · have hsumr' :
            ∑ k : Fin (Fintype.card ι), ((lam k : ℝ) : EReal) * g k (x' k) =
              ∑ i : ι, ((lam (e i) : ℝ) : EReal) * f i (x' (e i)) := by
          refine Fintype.sum_equiv (e := e.symm)
            (f := fun k => ((lam k : ℝ) : EReal) * g k (x' k))
            (g := fun i => ((lam (e i) : ℝ) : EReal) * f i (x' (e i))) ?_
          intro k
          simp [g]
        simp [hsumr']
    · intro hr
      rcases hr with ⟨lam, x', hlam, hsum, hsumx, rfl⟩
      refine ⟨(fun k => lam (e.symm k)), (fun k => x' (e.symm k)), ?_, ?_, ?_, ?_⟩
      · intro k
        exact hlam (e.symm k)
      · have hsum' :
            (∑ k : Fin (Fintype.card ι), lam (e.symm k)) = ∑ i : ι, lam i := by
          refine Fintype.sum_equiv (e := e.symm) (f := fun k => lam (e.symm k))
            (g := fun i => lam i) ?_
          intro k
          rfl
        simpa [hsum'] using hsum
      · have hsumx' :
            (∑ k : Fin (Fintype.card ι), lam (e.symm k) • x' (e.symm k)) =
              ∑ i : ι, lam i • x' i := by
          refine Fintype.sum_equiv (e := e.symm)
            (f := fun k => lam (e.symm k) • x' (e.symm k))
            (g := fun i => lam i • x' i) ?_
          intro k
          rfl
        simpa [hsumx'] using hsumx
      · have hsumr' :
            ∑ i : ι, ((lam i : ℝ) : EReal) * f i (x' i) =
              ∑ k : Fin (Fintype.card ι), ((lam (e.symm k) : ℝ) : EReal) * g k (x' (e.symm k)) := by
          refine Fintype.sum_equiv (e := e)
            (f := fun i => ((lam i : ℝ) : EReal) * f i (x' i))
            (g := fun k => ((lam (e.symm k) : ℝ) : EReal) * g k (x' (e.symm k))) ?_
          intro i
          simp [g]
        simp [hsumr']
  have hconvx : convexHullFunctionFamily f x = convexHullFunctionFamily g x := by
    simpa using congrArg (fun h => h x) hconv.symm
  have hformula' : convexHullFunctionFamily f x = sInf Sg := by
    simpa [hconvx] using hformula
  simpa [Sf, hS] using hformula'

/-- Theorem 16.5.3: Let `f i` be a proper convex function on `ℝ^n` for each `i` in a finite index
set. If the sets `cl (dom f i)` are all the same set `C`, then

`(supᵢ f i)^* = conv { (f i)^* | i }`.

Moreover, for each `xStar`, `(supᵢ f i)^*(xStar)` can be expressed as the infimum of
`∑ i, λ i * (f i)^*(xStarᵢ)` over all representations of `xStar` as a convex combination
`xStar = ∑ i, λ i • xStarᵢ`, and this infimum is attained. Here `dom f i` is modeled by
`effectiveDomain univ (f i)` and `cl` denotes topological closure of sets. -/
theorem section16_fenchelConjugate_sSup_eq_convexHullFunctionFamily_of_finite_of_closure_effectiveDomain_eq
    {n : ℕ} {ι : Type _} [Fintype ι] [Nonempty ι] (f : ι → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i)) (C : Set (Fin n → ℝ))
    (hC : ∀ i, closure (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) = C) :
    (fenchelConjugate n (fun x => sSup (Set.range fun i => f i x)) =
        convexHullFunctionFamily fun i => fenchelConjugate n (f i)) ∧
      (∀ xStar : Fin n → ℝ,
        let S : Set EReal :=
          {r |
            ∃ (lam : ι → ℝ) (xStar_i : ι → Fin n → ℝ),
              (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1 ∧ (∑ i, (lam i) • (xStar_i i)) = xStar ∧
                r = ∑ i, ((lam i : ℝ) : EReal) * fenchelConjugate n (f i) (xStar_i i)}
        fenchelConjugate n (fun x => sSup (Set.range fun i => f i x)) xStar = sInf S ∧
          ∃ r, r ∈ S ∧ sInf S = r) := by
  classical
  let g : ι → (Fin n → ℝ) → EReal := fun i => fenchelConjugate n (f i)
  have hclSup :
      convexFunctionClosure (fun x => iSup (fun i => f i x)) =
        fun x => iSup (fun i => convexFunctionClosure (f i) x) :=
    section16_convexFunctionClosure_iSup_eq_iSup_convexFunctionClosure_of_fintype_of_common_closure_effectiveDomain
      (f := f) hf C hC
  have hfench :
      fenchelConjugate n (fun x => iSup (fun i => f i x)) =
        fenchelConjugate n (fun x => iSup (fun i => convexFunctionClosure (f i) x)) := by
    have h :=
      (fenchelConjugate_eq_of_convexFunctionClosure (n := n)
        (f := fun x => iSup (fun i => f i x)))
    simpa [hclSup] using h.symm
  have h16 :
      fenchelConjugate n (fun x => iSup (fun i => convexFunctionClosure (f i) x)) =
        convexFunctionClosure (convexHullFunctionFamily g) := by
    simpa [g, sSup_range] using
      (section16_fenchelConjugate_sSup_convexFunctionClosure_eq_convexFunctionClosure_convexHullFunctionFamily
        (f := f) hf)
  have hclosed_attained :=
    section16_convexHullFunctionFamily_fenchelConjugate_closed_and_attained_of_common_closure_effectiveDomain
      (f := f) hf C hC
  have hclosure_g :
      convexFunctionClosure (convexHullFunctionFamily g) = convexHullFunctionFamily g := by
    simpa [g] using hclosed_attained.1
  have hmain :
      fenchelConjugate n (fun x => sSup (Set.range fun i => f i x)) =
        convexHullFunctionFamily g := by
    calc
      fenchelConjugate n (fun x => sSup (Set.range fun i => f i x)) =
          fenchelConjugate n (fun x => iSup (fun i => f i x)) := by
            simp [sSup_range]
      _ = fenchelConjugate n (fun x => iSup (fun i => convexFunctionClosure (f i) x)) := hfench
      _ = convexFunctionClosure (convexHullFunctionFamily g) := h16
      _ = convexHullFunctionFamily g := hclosure_g
  refine ⟨?_, ?_⟩
  · simpa [g] using hmain
  · intro xStar
    let S : Set EReal :=
      {r |
        ∃ (lam : ι → ℝ) (xStar_i : ι → Fin n → ℝ),
          (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1 ∧
            (∑ i, (lam i) • (xStar_i i)) = xStar ∧
              r = ∑ i, ((lam i : ℝ) : EReal) * g i (xStar_i i)}
    have hproper_g :
        ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (g i) := by
      intro i
      simpa [g] using
        (proper_fenchelConjugate_of_proper (n := n) (f := f i) (hf i))
    have hxS :
        fenchelConjugate n (fun x => sSup (Set.range fun i => f i x)) xStar = sInf S := by
      calc
        fenchelConjugate n (fun x => sSup (Set.range fun i => f i x)) xStar =
            convexHullFunctionFamily g xStar := by
              simpa [g] using congrArg (fun h => h xStar) hmain
        _ = sInf S := by
              simpa [S] using
                (section16_convexHullFunctionFamily_eq_sInf_convexCombination_univ_fintype
                  (f := g) hproper_g xStar)
    have hatt : ∃ (lam : ι → ℝ) (xStar_i : ι → Fin n → ℝ),
        (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1 ∧
          (∑ i, lam i • xStar_i i) = xStar ∧
            convexHullFunctionFamily g xStar =
              ∑ i, ((lam i : ℝ) : EReal) * g i (xStar_i i) := by
      simpa [g] using hclosed_attained.2 xStar
    rcases hatt with ⟨lam, xStar_i, hlam, hsum, hsumx, hval⟩
    have hrS : (∑ i, ((lam i : ℝ) : EReal) * g i (xStar_i i)) ∈ S := by
      refine ⟨lam, xStar_i, hlam, hsum, hsumx, rfl⟩
    have hsInf : sInf S = ∑ i, ((lam i : ℝ) : EReal) * g i (xStar_i i) := by
      calc
        sInf S =
            fenchelConjugate n (fun x => sSup (Set.range fun i => f i x)) xStar := by
              symm
              exact hxS
        _ = convexHullFunctionFamily g xStar := by
              simpa [g] using congrArg (fun h => h xStar) hmain
        _ = ∑ i, ((lam i : ℝ) : EReal) * g i (xStar_i i) := by
              simpa using hval
    exact ⟨hxS, ⟨_, hrS, hsInf⟩⟩
end Section16
end Chap03
