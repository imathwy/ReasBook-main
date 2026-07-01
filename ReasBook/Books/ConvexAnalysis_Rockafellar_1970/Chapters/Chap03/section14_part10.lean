/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yuhao Jiang, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section14_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part3
section Chap03
section Section14

open scoped Pointwise
open scoped Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

noncomputable local instance section14_instTopologicalSpace_dualWeak_part10 :
    TopologicalSpace (Module.Dual ℝ E) :=
  WeakBilin.instTopologicalSpace
    (B := (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)).flip)

/-- Polar sets are intersections of half-spaces `{φ | φ x ≤ 1}`. -/
lemma section14_polar_eq_iInter_halfspaces (C : Set E) :
    polar (E := E) C = ⋂ x : E, ⋂ (_ : x ∈ C), {φ : Module.Dual ℝ E | φ x ≤ 1} := by
  classical
  ext φ
  constructor
  · intro hφ
    refine Set.mem_iInter.2 (fun x => Set.mem_iInter.2 (fun hx => ?_))
    exact (mem_polar_iff (E := E) (C := C) (φ := φ)).1 hφ x hx
  · intro hφ
    refine (mem_polar_iff (E := E) (C := C) (φ := φ)).2 ?_
    intro x hx
    exact (Set.mem_iInter.1 (Set.mem_iInter.1 hφ x) hx)

/-- Under the weak topology on the algebraic dual induced by evaluation, polar sets are closed. -/
lemma section14_isClosed_polar (C : Set E) : IsClosed (polar (E := E) C) := by
  classical
  have hclosed_half : ∀ x : E, IsClosed {φ : Module.Dual ℝ E | φ x ≤ 1} := by
    intro x
    have hcont : Continuous fun φ : Module.Dual ℝ E => φ x :=
      section14_continuous_dual_apply (E := E) x
    simpa [Set.preimage, Set.mem_Iic] using (isClosed_Iic.preimage hcont)
  -- Rewrite as an intersection of closed sets.
  simpa [section14_polar_eq_iInter_halfspaces (E := E) (C := C)] using
    (isClosed_iInter (fun x : E => isClosed_iInter (fun _ : x ∈ C => hclosed_half x)))

/-- Convexity and `0`-membership of a polar set (topology-free). -/
lemma section14_convex_and_zeroMem_polar (C : Set E) :
    Convex ℝ (polar (E := E) C) ∧ (0 : Module.Dual ℝ E) ∈ polar (E := E) C := by
  classical
  refine ⟨?_, ?_⟩
  · intro φ₁ hφ₁ φ₂ hφ₂ a b ha hb hab
    refine (mem_polar_iff (E := E) (C := C)).2 ?_
    intro x hx
    have h₁x : φ₁ x ≤ 1 := (mem_polar_iff (E := E) (C := C) (φ := φ₁)).1 hφ₁ x hx
    have h₂x : φ₂ x ≤ 1 := (mem_polar_iff (E := E) (C := C) (φ := φ₂)).1 hφ₂ x hx
    calc
      (a • φ₁ + b • φ₂) x = a * φ₁ x + b * φ₂ x := by simp [smul_eq_mul]
      _ ≤ a * (1 : ℝ) + b * (1 : ℝ) := by
          exact add_le_add (mul_le_mul_of_nonneg_left h₁x ha) (mul_le_mul_of_nonneg_left h₂x hb)
      _ = 1 := by linarith
  ·
    refine (mem_polar_iff (E := E) (C := C) (φ := (0 : Module.Dual ℝ E))).2 ?_
    intro x hx
    simp

/-- The bipolar identity for closed convex sets containing the origin. -/
lemma section14_bipolar_eq_of_closed_convex
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    {C : Set E} (hCclosed : IsClosed C) (hCconv : Convex ℝ C) (hC0 : (0 : E) ∈ C) :
    {x : E | ∀ φ ∈ polar (E := E) C, φ x ≤ 1} = C := by
  classical
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    by_contra hxC
    obtain ⟨f, u, hfu, hux⟩ :=
      geometric_hahn_banach_closed_point (E := E) (s := C) (x := x) hCconv hCclosed hxC
    have hu_pos : 0 < u := by
      simpa using (hfu 0 hC0)
    have hu_ne : u ≠ 0 := ne_of_gt hu_pos
    let φ : Module.Dual ℝ E := (1 / u) • (f : Module.Dual ℝ E)
    have hφ : φ ∈ polar (E := E) C := by
      refine (mem_polar_iff (E := E) (C := C) (φ := φ)).2 ?_
      intro a ha
      have hau : f a < u := hfu a ha
      have hmul : (1 / u) * f a < 1 := by
        have : (1 / u) * f a < (1 / u) * u :=
          mul_lt_mul_of_pos_left hau (one_div_pos.2 hu_pos)
        simpa [one_div, hu_ne] using this
      have : φ a < 1 := by simpa [φ, smul_eq_mul] using hmul
      exact le_of_lt this
    have hφxle : φ x ≤ 1 := hx φ hφ
    have hφxgt : 1 < φ x := by
      have : (1 / u) * u < (1 / u) * f x :=
        mul_lt_mul_of_pos_left hux (one_div_pos.2 hu_pos)
      have : 1 < (1 / u) * f x := by
        simpa [one_div, hu_ne] using this
      simpa [φ, smul_eq_mul] using this
    exact (not_lt_of_ge hφxle) hφxgt
  · intro x hx φ hφ
    exact (mem_polar_iff (E := E) (C := C) (φ := φ)).1 hφ x hx

/-- An `EReal`-valued gauge: `sInf {r | 0 < r ∧ x ∈ r • C}` (with `⊤` for points not in any
positive scaling of `C`). This is the textbook gauge, unlike mathlib's real-valued `gauge`. -/
noncomputable def section14_egauge (C : Set E) (x : E) : EReal :=
  sInf ((fun r : ℝ => (r : EReal)) '' {r : ℝ | 0 < r ∧ x ∈ r • C})

/-- For `r ≠ 0`, membership in `r • C` is equivalent to membership of `(1 / r) • x` in `C`. -/
lemma section14_mem_smul_set_iff (C : Set E) {r : ℝ} (hr : r ≠ 0) {x : E} :
    x ∈ r • C ↔ (1 / r) • x ∈ C := by
  constructor
  · rintro ⟨y, hyC, rfl⟩
    simpa [smul_smul, div_eq_mul_inv, hr] using hyC
  · intro hx
    refine ⟨(1 / r) • x, hx, ?_⟩
    simp [smul_smul, div_eq_mul_inv, hr]

/-- If `C` satisfies the bipolar identity, then `x ∈ r • C` is equivalent to `φ x ≤ r` for all
`φ ∈ polar C` (for `r > 0`). -/
lemma section14_mem_smul_set_iff_forall_polar_le
    {C : Set E} (hCpolar : {x : E | ∀ φ ∈ polar (E := E) C, φ x ≤ 1} = C) {r : ℝ} (hr : 0 < r)
    {x : E} :
    x ∈ r • C ↔ ∀ φ ∈ polar (E := E) C, φ x ≤ r := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  -- Move membership to `(1/r) • x ∈ C`.
  have hxC : x ∈ r • C ↔ (1 / r) • x ∈ C :=
    section14_mem_smul_set_iff (E := E) (C := C) (r := r) hr0 (x := x)
  -- Unfold the bipolar set equality at `(1/r) • x`.
  have hbip :
      (1 / r) • x ∈ C ↔ ∀ φ ∈ polar (E := E) C, φ ((1 / r) • x) ≤ 1 := by
    constructor
    · intro hxC
      have : (1 / r) • x ∈ {x : E | ∀ φ ∈ polar (E := E) C, φ x ≤ 1} := by
        simpa [hCpolar] using hxC
      simpa [Set.mem_setOf_eq] using this
    · intro hxP
      have : (1 / r) • x ∈ {x : E | ∀ φ ∈ polar (E := E) C, φ x ≤ 1} := by
        simpa [Set.mem_setOf_eq] using hxP
      simpa [hCpolar] using this
  -- Convert `φ ((1/r) • x) ≤ 1` to `φ x ≤ r`.
  constructor
  · intro hx
    have hx' : (1 / r) • x ∈ C := (hxC.1 hx)
    have hall : ∀ φ ∈ polar (E := E) C, φ ((1 / r) • x) ≤ 1 := (hbip.1 hx')
    intro φ hφ
    have hdiv : (φ x) / r ≤ 1 := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, smul_eq_mul] using
        (hall φ hφ)
    have : φ x ≤ 1 * r := (_root_.div_le_iff₀ hr).1 hdiv
    simpa [one_mul] using this
  · intro hall
    have hall' : ∀ φ ∈ polar (E := E) C, φ ((1 / r) • x) ≤ 1 := by
      intro φ hφ
      have hdiv : (φ x) / r ≤ 1 := by
        have : φ x ≤ (1 : ℝ) * r := by simpa [one_mul] using hall φ hφ
        have : (φ x) / r ≤ (1 : ℝ) := (_root_.div_le_iff₀ hr).2 this
        simpa using this
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, smul_eq_mul] using hdiv
    have hx' : (1 / r) • x ∈ C := (hbip.2 hall')
    exact (hxC.2 hx')

/-- `fenchelConjugateBilin` of an `erealIndicator` is a support function: for the flipped evaluation
pairing, it is `sSup {φ x | φ ∈ polar C}`. -/
lemma section14_fenchelConjugate_flip_erealIndicator_polar_eq_sSup (C : Set E) (x : E) :
    let p := LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)
    fenchelConjugateBilin p.flip
        (erealIndicator (E := Module.Dual ℝ E) (polar (E := E) C)) x =
      sSup ((fun φ : Module.Dual ℝ E => (φ x : EReal)) '' polar (E := E) C) := by
  classical
  intro p
  apply le_antisymm
  · -- `≤`: use the `≤` characterization of the Fenchel conjugate.
    have hle :
        fenchelConjugateBilin p.flip
            (erealIndicator (E := Module.Dual ℝ E) (polar (E := E) C)) x ≤
          sSup ((fun φ : Module.Dual ℝ E => (φ x : EReal)) '' polar (E := E) C) :=
      (section14_fenchelConjugate_le_iff_forall (E := Module.Dual ℝ E) (F := E) (p := p.flip)
          (f := erealIndicator (E := Module.Dual ℝ E) (polar (E := E) C)) (xStar := x)
          (μStar := sSup ((fun φ : Module.Dual ℝ E => (φ x : EReal)) '' polar (E := E) C))).2
        (by
          intro φ
          by_cases hφ : φ ∈ polar (E := E) C
          ·
            have hmem :
                (φ x : EReal) ∈
                  (fun φ : Module.Dual ℝ E => (φ x : EReal)) '' polar (E := E) C :=
              ⟨φ, hφ, rfl⟩
            simpa [erealIndicator, hφ] using (le_sSup hmem)
          ·
            -- Outside `polar C` the indicator is `⊤`, hence the term is `⊥`.
            simp [erealIndicator, hφ])
    simpa using hle
  · -- `≥`: every `φ ∈ polar C` contributes the value `φ x`.
    refine sSup_le ?_
    rintro _ ⟨φ, hφ, rfl⟩
    unfold fenchelConjugateBilin
    have : (p.flip φ x : EReal) -
          erealIndicator (E := Module.Dual ℝ E) (polar (E := E) C) φ ≤
        sSup (Set.range fun ψ : Module.Dual ℝ E =>
          (p.flip ψ x : EReal) -
            erealIndicator (E := Module.Dual ℝ E) (polar (E := E) C) ψ) := by
      exact le_sSup ⟨φ, rfl⟩
    simpa [p, erealIndicator, hφ, LinearMap.applyₗ] using this

/-- `fenchelConjugateBilin` of an `erealIndicator` is a support function: for the evaluation pairing,
it is `sSup {φ x | x ∈ C}`. -/
lemma section14_fenchelConjugate_erealIndicator_eq_sSup (C : Set E) (φ : Module.Dual ℝ E) :
    let p := LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)
    fenchelConjugateBilin p (erealIndicator (E := E) C) φ =
      sSup ((fun x : E => (φ x : EReal)) '' C) := by
  classical
  intro p
  apply le_antisymm
  ·
    have hle :
        fenchelConjugateBilin p (erealIndicator (E := E) C) φ ≤
          sSup ((fun x : E => (φ x : EReal)) '' C) :=
      (section14_fenchelConjugate_le_iff_forall (E := E) (F := Module.Dual ℝ E) (p := p)
          (f := erealIndicator (E := E) C) (xStar := φ)
          (μStar := sSup ((fun x : E => (φ x : EReal)) '' C))).2
        (by
          intro x
          by_cases hx : x ∈ C
          ·
            have hmem : (φ x : EReal) ∈ (fun x : E => (φ x : EReal)) '' C :=
              ⟨x, hx, rfl⟩
            simpa [erealIndicator, hx] using (le_sSup hmem)
          · simp [erealIndicator, hx])
    simpa using hle
  ·
    refine sSup_le ?_
    rintro _ ⟨x, hx, rfl⟩
    unfold fenchelConjugateBilin
    have : (p x φ : EReal) - erealIndicator (E := E) C x ≤
        sSup (Set.range fun y : E => (p y φ : EReal) - erealIndicator (E := E) C y) := by
      exact le_sSup ⟨x, rfl⟩
    simpa [p, erealIndicator, hx, LinearMap.applyₗ] using this

/-- The `EReal`-valued gauge of a closed convex set containing `0` agrees with the support function
of its polar set. -/
lemma section14_egauge_eq_fenchelConjugate_indicator_polar
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    {C : Set E} (hCclosed : IsClosed C) (hCconv : Convex ℝ C) (hC0 : (0 : E) ∈ C) :
    let p := LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)
    (fun x : E => section14_egauge (E := E) C x) =
      fenchelConjugateBilin p.flip
        (erealIndicator (E := Module.Dual ℝ E) (polar (E := E) C)) := by
  classical
  intro p
  funext x
  -- Reduce both sides to `sSup {φ x | φ ∈ polar C}`.
  have hbip : {x : E | ∀ φ ∈ polar (E := E) C, φ x ≤ 1} = C :=
    section14_bipolar_eq_of_closed_convex (E := E) hCclosed hCconv hC0
  have hEgauge :
      section14_egauge (E := E) C x =
        sSup ((fun φ : Module.Dual ℝ E => (φ x : EReal)) '' polar (E := E) C) := by
    -- Set `μ := sSup {φ x | φ ∈ polar C}` and show `μ = egauge C x` by a `≤`-sandwich.
    set μ : EReal :=
      sSup ((fun φ : Module.Dual ℝ E => (φ x : EReal)) '' polar (E := E) C) with hμ
    have hμle : μ ≤ section14_egauge (E := E) C x := by
      -- Any admissible scaling `r` bounds all `φ x`, hence also `μ`.
      refine le_sInf ?_
      rintro _ ⟨r, ⟨hrpos, hxmem⟩, rfl⟩
      have hall : ∀ b ∈ (fun φ : Module.Dual ℝ E => (φ x : EReal)) '' polar (E := E) C,
          b ≤ (r : EReal) := by
        rintro _ ⟨φ, hφ, rfl⟩
        rcases hxmem with ⟨y, hyC, rfl⟩
        have hφy : φ y ≤ 1 :=
          (mem_polar_iff (E := E) (C := C) (φ := φ)).1 hφ y hyC
        have hmul : r * φ y ≤ r * (1 : ℝ) :=
          mul_le_mul_of_nonneg_left hφy (le_of_lt hrpos)
        have : φ (r • y) ≤ r := by
          simpa [smul_eq_mul, mul_assoc, mul_one] using hmul
        exact EReal.coe_le_coe this
      have : μ ≤ (r : EReal) := sSup_le hall
      simpa [hμ] using this
    have hleμ : section14_egauge (E := E) C x ≤ μ := by
      -- For any real `z > μ`, we have `x ∈ z • C`, hence `egauge C x ≤ z`. Conclude by
      -- `EReal.le_of_forall_lt_iff_le`.
      have h0polar : (0 : Module.Dual ℝ E) ∈ polar (E := E) C :=
        (section14_convex_and_zeroMem_polar (E := E) (C := C)).2
      have h0mem :
          (0 : EReal) ∈ (fun φ : Module.Dual ℝ E => (φ x : EReal)) '' polar (E := E) C := by
        refine ⟨0, h0polar, ?_⟩
        simp
      have h0leμ : (0 : EReal) ≤ μ := by simpa [hμ] using (le_sSup h0mem)
      -- Use the real upper-approximation lemma for `EReal`.
      have hz : ∀ z : ℝ, μ < z → section14_egauge (E := E) C x ≤ (z : EReal) := by
        intro z hz
        have hz0E : (0 : EReal) < (z : EReal) := lt_of_le_of_lt h0leμ hz
        have hz0 : (0 : ℝ) < z := by
          simpa using (EReal.coe_lt_coe_iff).1 (by simpa using hz0E)
        have hforall : ∀ φ ∈ polar (E := E) C, φ x ≤ z := by
          intro φ hφ
          have hmem :
              (φ x : EReal) ∈ (fun φ : Module.Dual ℝ E => (φ x : EReal)) '' polar (E := E) C :=
            ⟨φ, hφ, rfl⟩
          -- `φ x ≤ μ < z`, hence `φ x ≤ z`.
          have : (φ x : EReal) ≤ (z : EReal) := (le_trans (le_sSup hmem) hz.le)
          exact (EReal.coe_le_coe_iff).1 (by simpa using this)
        have hxz : x ∈ z • C :=
          (section14_mem_smul_set_iff_forall_polar_le (E := E) (C := C) hbip (r := z) hz0
              (x := x)).2 hforall
        have hzmem : (z : EReal) ∈
            (fun r : ℝ => (r : EReal)) '' {r : ℝ | 0 < r ∧ x ∈ r • C} := by
          refine ⟨z, ⟨hz0, hxz⟩, rfl⟩
        simpa [section14_egauge] using (sInf_le hzmem)
      -- Turn the `∀ z, μ < z → ...` into `egauge ≤ μ`.
      exact
        (EReal.le_of_forall_lt_iff_le (x := μ) (y := section14_egauge (E := E) C x)).1 hz
    exact (hleμ.antisymm hμle)
  simp [hEgauge, section14_fenchelConjugate_flip_erealIndicator_polar_eq_sSup (E := E) (C := C)
    (x := x), p]

/-- Membership in `r • polar C` is equivalent to a uniform bound `φ x ≤ r` on `C` (for `r > 0`). -/
lemma section14_mem_smul_polar_iff_forall_le (C : Set E) {r : ℝ} (hr : 0 < r)
    {φ : Module.Dual ℝ E} :
    φ ∈ r • polar (E := E) C ↔ ∀ x ∈ C, φ x ≤ r := by
  constructor
  · rintro ⟨ψ, hψ, rfl⟩ x hx
    have hψx : ψ x ≤ 1 := (mem_polar_iff (E := E) (C := C) (φ := ψ)).1 hψ x hx
    have hmul : r * ψ x ≤ r * (1 : ℝ) :=
      mul_le_mul_of_nonneg_left hψx (le_of_lt hr)
    simpa [smul_eq_mul, mul_assoc, mul_one] using hmul
  · intro h
    have hr0 : r ≠ 0 := ne_of_gt hr
    have hpol : (1 / r) • φ ∈ polar (E := E) C := by
      refine (mem_polar_iff (E := E) (C := C) (φ := (1 / r) • φ)).2 ?_
      intro x hx
      have hx' : φ x ≤ r := h x hx
      have : (φ x) / r ≤ 1 := by
        have : φ x ≤ (1 : ℝ) * r := by simpa [one_mul] using hx'
        have : (φ x) / r ≤ (1 : ℝ) := (_root_.div_le_iff₀ hr).2 this
        simpa using this
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, smul_eq_mul] using this
    refine ⟨(1 / r) • φ, hpol, ?_⟩
    simp [smul_smul, div_eq_mul_inv, hr0]

/-- The `EReal`-valued gauge of the polar set agrees with the support function of `C`. -/
lemma section14_egauge_polar_eq_fenchelConjugate_indicator
    {C : Set E} (hC0 : (0 : E) ∈ C) :
    let p := LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)
    (fun φ : Module.Dual ℝ E => section14_egauge (E := Module.Dual ℝ E) (polar (E := E) C) φ) =
      fenchelConjugateBilin p (erealIndicator (E := E) C) := by
  classical
  intro p
  funext φ
  -- Reduce both sides to `sSup {φ x | x ∈ C}`.
  have hEgauge :
      section14_egauge (E := Module.Dual ℝ E) (polar (E := E) C) φ =
        sSup ((fun x : E => (φ x : EReal)) '' C) := by
    set μ : EReal := sSup ((fun x : E => (φ x : EReal)) '' C) with hμ
    have hμle : μ ≤ section14_egauge (E := Module.Dual ℝ E) (polar (E := E) C) φ := by
      refine le_sInf ?_
      rintro _ ⟨r, ⟨hrpos, hφmem⟩, rfl⟩
      have hall : ∀ x ∈ C, (φ x : EReal) ≤ (r : EReal) := by
        intro x hx
        have hxle : φ x ≤ r :=
          (section14_mem_smul_polar_iff_forall_le (E := E) (C := C) (r := r) hrpos (φ := φ)).1
            hφmem x hx
        exact EReal.coe_le_coe hxle
      have : μ ≤ (r : EReal) := by
        refine sSup_le ?_
        rintro _ ⟨x, hx, rfl⟩
        exact hall x hx
      simpa [hμ] using this
    have hleμ : section14_egauge (E := Module.Dual ℝ E) (polar (E := E) C) φ ≤ μ := by
      -- Approximate `μ` from above by reals `z > μ`, as in the primal case.
      have h0mem : (0 : EReal) ∈ (fun x : E => (φ x : EReal)) '' C := by
        refine ⟨0, hC0, ?_⟩
        simp
      have h0leμ : (0 : EReal) ≤ μ := by simpa [hμ] using (le_sSup h0mem)
      have hz :
          ∀ z : ℝ, μ < z → section14_egauge (E := Module.Dual ℝ E) (polar (E := E) C) φ ≤
            (z : EReal) := by
        intro z hz
        have hz0E : (0 : EReal) < (z : EReal) := lt_of_le_of_lt h0leμ hz
        have hz0 : (0 : ℝ) < z := by
          simpa using (EReal.coe_lt_coe_iff).1 (by simpa using hz0E)
        have hall : ∀ x ∈ C, φ x ≤ z := by
          intro x hx
          have hmem : (φ x : EReal) ∈ (fun x : E => (φ x : EReal)) '' C := ⟨x, hx, rfl⟩
          have : (φ x : EReal) ≤ (z : EReal) := (le_trans (le_sSup hmem) hz.le)
          exact (EReal.coe_le_coe_iff).1 (by simpa using this)
        have hφz : φ ∈ z • polar (E := E) C :=
          (section14_mem_smul_polar_iff_forall_le (E := E) (C := C) (r := z) hz0 (φ := φ)).2 hall
        have hzmem :
            (z : EReal) ∈
              (fun r : ℝ => (r : EReal)) '' {r : ℝ | 0 < r ∧ φ ∈ r • polar (E := E) C} := by
          refine ⟨z, ⟨hz0, hφz⟩, rfl⟩
        simpa [section14_egauge] using (sInf_le hzmem)
      exact
        (EReal.le_of_forall_lt_iff_le (x := μ)
              (y := section14_egauge (E := Module.Dual ℝ E) (polar (E := E) C) φ)).1
          hz
    exact (hleμ.antisymm hμle)
  simp [hEgauge, section14_fenchelConjugate_erealIndicator_eq_sSup (E := E) (C := C) (φ := φ),
    p]

/-- Theorem 14.5: Let `C` be a closed convex set containing the origin. Then the polar `C^∘` is
another closed convex set containing the origin, and the bipolar identity `C^{∘∘} = C` holds.
The gauge function of `C` is the support function of `C^∘`. Dually, the gauge function of `C^∘`
is the support function of `C`. -/
theorem polar_closed_convex_bipolar_eq_and_gauge_eq_support
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    {C : Set E} :
    IsClosed C → Convex ℝ C → (0 : E) ∈ C →
      (IsClosed (polar (E := E) C) ∧ Convex ℝ (polar (E := E) C) ∧
          (0 : Module.Dual ℝ E) ∈ polar (E := E) C) ∧
        {x : E | ∀ φ ∈ polar (E := E) C, φ x ≤ 1} = C ∧
          (let p := LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)
          (fun x : E => section14_egauge (E := E) C x) =
              fenchelConjugateBilin p.flip
                (erealIndicator (E := Module.Dual ℝ E) (polar (E := E) C)) ∧
            (fun φ : Module.Dual ℝ E =>
                section14_egauge (E := Module.Dual ℝ E) (polar (E := E) C) φ) =
              fenchelConjugateBilin p (erealIndicator (E := E) C)) := by
  intro hCclosed hCconv hC0
  refine ⟨?_, ?_⟩
  ·
    have hconv0 := section14_convex_and_zeroMem_polar (E := E) (C := C)
    refine ⟨section14_isClosed_polar (E := E) C, hconv0.1, hconv0.2⟩
  · refine ⟨section14_bipolar_eq_of_closed_convex (E := E) hCclosed hCconv hC0, ?_⟩
    classical
    dsimp
    refine ⟨?_, ?_⟩
    ·
      simpa using
        (section14_egauge_eq_fenchelConjugate_indicator_polar (E := E) (C := C) hCclosed hCconv hC0)
    · simpa using (section14_egauge_polar_eq_fenchelConjugate_indicator (E := E) (C := C) hC0)

/-- In a finite-dimensional Hausdorff real topological vector space, a convex set contains the
origin in its interior iff every vector can be scaled into it. -/
lemma section14_zero_mem_interior_iff_forall_exists_pos_smul_mem
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [FiniteDimensional ℝ E] [T2Space E]
    {C : Set E} (hCconv : Convex ℝ C) :
    (0 : E) ∈ interior C ↔ ∀ y : E, ∃ ε : ℝ, 0 < ε ∧ ε • y ∈ C := by
  classical
  let n : Nat := Module.finrank ℝ E
  let e : E ≃L[ℝ] EuclideanSpace Real (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (𝕜 := ℝ) (E := E) (F := EuclideanSpace Real (Fin n))
      (by
        simp [n])
  have h0 :
      (0 : E) ∈ interior C ↔ (0 : EuclideanSpace Real (Fin n)) ∈ interior (e '' C) := by
    have hpre :
        e.toHomeomorph ⁻¹' interior (e '' C) = interior C := by
      simpa [Set.preimage_image_eq C e.injective] using
        (e.toHomeomorph.preimage_interior (s := e '' C))
    constructor
    · intro h
      have : (0 : E) ∈ e.toHomeomorph ⁻¹' interior (e '' C) := by
        rw [hpre]
        exact h
      simpa [Set.mem_preimage, e.map_zero] using this
    · intro h
      have : (0 : E) ∈ e.toHomeomorph ⁻¹' interior (e '' C) := by
        simpa [Set.mem_preimage, e.map_zero] using h
      rw [← hpre]
      exact this
  have hconv_im : Convex ℝ (e '' C) := by
    simpa [Set.image_image] using hCconv.linear_image (e : E →ₗ[ℝ] EuclideanSpace Real (Fin n))
  -- Apply Corollary 6.4.1 in `EuclideanSpace Real (Fin n)` and transport back along `e`.
  have hEuclid :
      (0 : EuclideanSpace Real (Fin n)) ∈ interior (e '' C) ↔
        ∀ y : EuclideanSpace Real (Fin n), ∃ ε > (0 : Real),
          (0 : EuclideanSpace Real (Fin n)) + ε • y ∈ e '' C :=
    euclidean_interior_iff_forall_exists_add_smul_mem n (e '' C) hconv_im 0
  have hEuclid' :
      (0 : EuclideanSpace Real (Fin n)) ∈ interior (e '' C) ↔
        ∀ y : EuclideanSpace Real (Fin n), ∃ ε > (0 : Real), ε • y ∈ e '' C := by
    simpa using hEuclid
  have hscale :
      (∀ y : EuclideanSpace Real (Fin n), ∃ ε > (0 : Real), ε • y ∈ e '' C) ↔
        (∀ y : E, ∃ ε > (0 : Real), ε • y ∈ C) := by
    constructor
    · intro h y
      rcases h (e y) with ⟨ε, hε, hmem⟩
      rcases hmem with ⟨x, hxC, hxEq⟩
      have : x = ε • y := by
        apply e.injective
        simpa [e.map_smul] using hxEq
      subst this
      exact ⟨ε, hε, hxC⟩
    · intro h y
      rcases h (e.symm y) with ⟨ε, hε, hyC⟩
      refine ⟨ε, hε, ?_⟩
      refine ⟨ε • e.symm y, hyC, ?_⟩
      simp [e.map_smul]
  constructor
  · intro h0E
    have h0F : (0 : EuclideanSpace Real (Fin n)) ∈ interior (e '' C) := (h0.1 h0E)
    have hF : ∀ y : EuclideanSpace Real (Fin n), ∃ ε > (0 : Real), ε • y ∈ e '' C :=
      (hEuclid'.1 h0F)
    simpa using (hscale.1 hF)
  · intro hE
    have hF : ∀ y : EuclideanSpace Real (Fin n), ∃ ε > (0 : Real), ε • y ∈ e '' C :=
      (hscale.2 (by simpa using hE))
    have h0F : (0 : EuclideanSpace Real (Fin n)) ∈ interior (e '' C) := hEuclid'.2 hF
    exact h0.2 h0F

/-- Corollary 14.5.1. Let `C` be a closed convex set containing the origin. Then the polar `C^∘`
is bounded if and only if `0 ∈ int C`. Dually, `C` is bounded if and only if `0 ∈ int C^∘`. -/
theorem polar_bounded_iff_zero_mem_interior_and_dual
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    [FiniteDimensional ℝ E] [T2Space E] {C : Set E}
    (hCclosed : IsClosed C) (hCconv : Convex ℝ C) (hC0 : (0 : E) ∈ C) :
    (@Bornology.IsBounded (Module.Dual ℝ E)
          (Bornology.induced (fun φ : Module.Dual ℝ E => fun x : E => φ x))
          (polar (E := E) C) ↔ (0 : E) ∈ interior C) ∧
      (@Bornology.IsBounded E
          (Bornology.induced (fun x : E => fun φ : Module.Dual ℝ E => φ x)) C ↔
        (0 : Module.Dual ℝ E) ∈ interior (polar (E := E) C)) := by
  classical
  -- Bipolar identity for `C`, used to move between bounds on `polar C` and membership in scalings of `C`.
  have hbip : {x : E | ∀ φ ∈ polar (E := E) C, φ x ≤ 1} = C :=
    section14_bipolar_eq_of_closed_convex (E := E) hCclosed hCconv hC0

  -- Translate `0 ∈ interior C` into the absorbency-style scaling property.
  have hC0int_iff :
      (0 : E) ∈ interior C ↔ ∀ y : E, ∃ ε : ℝ, 0 < ε ∧ ε • y ∈ C :=
    section14_zero_mem_interior_iff_forall_exists_pos_smul_mem (E := E) (C := C) hCconv

  -- Boundedness of a set of functionals in the induced bornology is exactly pointwise boundedness.
  have hpolar_bdd :
      @Bornology.IsBounded (Module.Dual ℝ E)
          (Bornology.induced (fun φ : Module.Dual ℝ E => fun x : E => φ x))
          (polar (E := E) C) ↔
        ∀ x : E, Bornology.IsBounded ((fun φ : Module.Dual ℝ E => φ x) '' polar (E := E) C) := by
    -- Unfold induced bornology and use boundedness in `Π x, ℝ`.
    have :
        Bornology.IsBounded ((fun φ : Module.Dual ℝ E => fun x : E => φ x) '' polar (E := E) C) ↔
          ∀ x : E,
            Bornology.IsBounded
              (Function.eval x ''
                ((fun φ : Module.Dual ℝ E => fun x : E => φ x) '' polar (E := E) C)) := by
      simpa using
        (Bornology.forall_isBounded_image_eval_iff
          (s := (fun φ : Module.Dual ℝ E => fun x : E => φ x) '' polar (E := E) C)).symm
    -- Simplify the evaluation images.
    have :
        Bornology.IsBounded ((fun φ : Module.Dual ℝ E => fun x : E => φ x) '' polar (E := E) C) ↔
          ∀ x : E, Bornology.IsBounded ((fun φ : Module.Dual ℝ E => φ x) '' polar (E := E) C) := by
      simpa [Set.image_image] using this
    -- Move from the induced bornology on `Module.Dual` to the image set in `E → ℝ`.
    simpa using (Bornology.isBounded_induced (f := fun φ : Module.Dual ℝ E => fun x : E => φ x)
      (s := polar (E := E) C)).trans this

  -- Boundedness of `C` in the induced bornology is exactly boundedness of all linear images `φ '' C`.
  have hC_bdd :
      @Bornology.IsBounded E
          (Bornology.induced (fun x : E => fun φ : Module.Dual ℝ E => φ x)) C ↔
        ∀ φ : Module.Dual ℝ E, Bornology.IsBounded (φ '' C) := by
    have :
        Bornology.IsBounded ((fun x : E => fun φ : Module.Dual ℝ E => φ x) '' C) ↔
          ∀ φ : Module.Dual ℝ E,
            Bornology.IsBounded
              (Function.eval φ '' ((fun x : E => fun φ : Module.Dual ℝ E => φ x) '' C)) := by
      simpa using
        (Bornology.forall_isBounded_image_eval_iff
          (s := (fun x : E => fun φ : Module.Dual ℝ E => φ x) '' C)).symm
    have :
        Bornology.IsBounded ((fun x : E => fun φ : Module.Dual ℝ E => φ x) '' C) ↔
          ∀ φ : Module.Dual ℝ E, Bornology.IsBounded (φ '' C) := by
      simpa [Set.image_image] using this
    simpa using
      (Bornology.isBounded_induced (f := fun x : E => fun φ : Module.Dual ℝ E => φ x) (s := C)).trans
        this

  refine ⟨?_, ?_⟩
  · -- `polar C` bounded ↔ `0 ∈ interior C`.
    constructor
    · intro hbd
      -- From pointwise boundedness of `polar C`, show every `y` can be scaled into `C`.
      have hscale : ∀ y : E, ∃ ε : ℝ, 0 < ε ∧ ε • y ∈ C := by
        intro y
        have hybd : Bornology.IsBounded ((fun φ : Module.Dual ℝ E => φ y) '' polar (E := E) C) :=
          (hpolar_bdd.1 hbd) y
        rcases hybd.exists_pos_norm_le with ⟨R, hRpos, hR⟩
        set r : ℝ := max 1 R
        have hrpos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
        have hall : ∀ φ ∈ polar (E := E) C, φ y ≤ r := by
          intro φ hφ
          have hnorm : ‖φ y‖ ≤ R := hR (φ y) ⟨φ, hφ, rfl⟩
          have hleR : φ y ≤ R := by
            have : |φ y| ≤ R := by simpa [Real.norm_eq_abs] using hnorm
            exact le_trans (le_abs_self (φ y)) this
          exact le_trans hleR (le_trans (le_max_right 1 R) (le_rfl))
        have hy_mem : y ∈ r • C :=
          (section14_mem_smul_set_iff_forall_polar_le (E := E) (C := C) hbip (r := r) hrpos
              (x := y)).2
            hall
        have hr0 : r ≠ 0 := ne_of_gt hrpos
        have hyC : (1 / r) • y ∈ C :=
          (section14_mem_smul_set_iff (E := E) (C := C) (r := r) hr0 (x := y)).1 hy_mem
        refine ⟨1 / r, one_div_pos.2 hrpos, ?_⟩
        simpa using hyC
      exact (hC0int_iff.2 hscale)
    · intro h0int
      -- From `0 ∈ interior C`, get scaling witnesses and deduce pointwise boundedness of `polar C`.
      have hscale : ∀ y : E, ∃ ε : ℝ, 0 < ε ∧ ε • y ∈ C := (hC0int_iff.1 h0int)
      have hpointwise :
          ∀ x : E, Bornology.IsBounded ((fun φ : Module.Dual ℝ E => φ x) '' polar (E := E) C) := by
        intro x
        rcases hscale x with ⟨ε₁, hε₁, hε₁x⟩
        rcases hscale (-x) with ⟨ε₂, hε₂, hε₂x⟩
        set r₁ : ℝ := 1 / ε₁
        set r₂ : ℝ := 1 / ε₂
        have hr₁ : 0 < r₁ := by simpa [r₁] using one_div_pos.2 hε₁
        have hr₂ : 0 < r₂ := by simpa [r₂] using one_div_pos.2 hε₂
        have hx_mem : x ∈ r₁ • C := by
          have hr₁0 : r₁ ≠ 0 := ne_of_gt hr₁
          have : (1 / r₁) • x ∈ C := by
            simpa [r₁] using hε₁x
          exact (section14_mem_smul_set_iff (E := E) (C := C) (r := r₁) hr₁0 (x := x)).2 this
        have hnx_mem : (-x) ∈ r₂ • C := by
          have hr₂0 : r₂ ≠ 0 := ne_of_gt hr₂
          have : (1 / r₂) • (-x) ∈ C := by
            simpa [r₂] using hε₂x
          exact (section14_mem_smul_set_iff (E := E) (C := C) (r := r₂) hr₂0 (x := -x)).2 this
        have hupper : ∀ φ ∈ polar (E := E) C, φ x ≤ r₁ :=
          (section14_mem_smul_set_iff_forall_polar_le (E := E) (C := C) hbip (r := r₁) hr₁
                (x := x)).1
            hx_mem
        have hlower : ∀ φ ∈ polar (E := E) C, -(φ x) ≤ r₂ := by
          intro φ hφ
          have : φ (-x) ≤ r₂ :=
            (section14_mem_smul_set_iff_forall_polar_le (E := E) (C := C) hbip (r := r₂) hr₂
                  (x := -x)).1
              hnx_mem φ hφ
          simpa using (by simpa using this : -(φ x) ≤ r₂)
        refine (isBounded_iff_forall_norm_le (s := (fun φ : Module.Dual ℝ E => φ x) '' polar (E := E) C)).2 ?_
        refine ⟨max r₁ r₂, ?_⟩
        rintro _ ⟨φ, hφ, rfl⟩
        have hle : φ x ≤ max r₁ r₂ := le_trans (hupper φ hφ) (le_max_left _ _)
        have hge : -max r₁ r₂ ≤ φ x := by
          have : -(φ x) ≤ max r₁ r₂ := le_trans (hlower φ hφ) (le_max_right _ _)
          -- Rewrite `-(φ x) ≤ ...` as `-... ≤ φ x`.
          have : -max r₁ r₂ ≤ φ x := by
            have := neg_le_neg this
            simpa [neg_neg] using this
          exact this
        have habs : |φ x| ≤ max r₁ r₂ := (abs_le).2 ⟨hge, hle⟩
        simpa [Real.norm_eq_abs] using habs
      exact hpolar_bdd.2 hpointwise
  · -- `C` bounded ↔ `0 ∈ interior (polar C)`.
    -- Establish the required T2 instance for the weak topology on the dual.
    haveI : T2Space (Module.Dual ℝ E) := by
      let f : Module.Dual ℝ E → (E → ℝ) := fun φ x => φ x
      have hf : Topology.IsEmbedding f := by
        refine
          (WeakBilin.isEmbedding (B := (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)).flip) ?_)
        intro φ ψ h
        ext x
        simpa using congrArg (fun g => g x) h
      exact hf.t2Space
    haveI : IsTopologicalAddGroup (Module.Dual ℝ E) := by
      let B : (Module.Dual ℝ E) →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
        (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)).flip
      change IsTopologicalAddGroup (WeakBilin B)
      infer_instance
    haveI : ContinuousSMul ℝ (Module.Dual ℝ E) := by
      let B : (Module.Dual ℝ E) →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
        (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)).flip
      change ContinuousSMul ℝ (WeakBilin B)
      infer_instance
    have h0int_polar_iff :
        (0 : Module.Dual ℝ E) ∈ interior (polar (E := E) C) ↔
          ∀ ψ : Module.Dual ℝ E, ∃ ε : ℝ, 0 < ε ∧ ε • ψ ∈ polar (E := E) C := by
      have hconv_polar : Convex ℝ (polar (E := E) C) :=
        (section14_convex_and_zeroMem_polar (E := E) (C := C)).1
      -- `Module.Dual` is finite-dimensional when `E` is.
      haveI : FiniteDimensional ℝ (Module.Dual ℝ E) := by infer_instance
      simpa using
        (section14_zero_mem_interior_iff_forall_exists_pos_smul_mem
          (E := Module.Dual ℝ E) (C := polar (E := E) C) hconv_polar)
    constructor
    · intro hbd
      have hpointwise : ∀ ψ : Module.Dual ℝ E, Bornology.IsBounded (ψ '' C) := (hC_bdd.1 hbd)
      refine (h0int_polar_iff.2 ?_)
      intro ψ
      rcases (hpointwise ψ).exists_pos_norm_le with ⟨R, hRpos, hR⟩
      set r : ℝ := max 1 R
      have hrpos : 0 < r := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
      have hall : ∀ x ∈ C, ψ x ≤ r := by
        intro x hx
        have hnorm : ‖ψ x‖ ≤ R := hR (ψ x) ⟨x, hx, rfl⟩
        have hleR : ψ x ≤ R := by
          have : |ψ x| ≤ R := by simpa [Real.norm_eq_abs] using hnorm
          exact le_trans (le_abs_self (ψ x)) this
        exact le_trans hleR (le_trans (le_max_right 1 R) (le_rfl))
      -- `ψ ∈ r • polar C`, hence `(1/r) • ψ ∈ polar C`.
      have hmem : ψ ∈ r • polar (E := E) C :=
        (section14_mem_smul_polar_iff_forall_le (E := E) (C := C) (r := r) hrpos (φ := ψ)).2 hall
      rcases hmem with ⟨ψ', hψ', rfl⟩
      have hr0 : r ≠ 0 := ne_of_gt hrpos
      refine ⟨1 / r, one_div_pos.2 hrpos, ?_⟩
      simpa [smul_smul, div_eq_mul_inv, hr0]
    · intro h0int
      have hscale :
          ∀ ψ : Module.Dual ℝ E, ∃ ε : ℝ, 0 < ε ∧ ε • ψ ∈ polar (E := E) C :=
        (h0int_polar_iff.1 h0int)
      have hpointwise : ∀ ψ : Module.Dual ℝ E, Bornology.IsBounded (ψ '' C) := by
        intro ψ
        rcases hscale ψ with ⟨ε₁, hε₁, hε₁mem⟩
        rcases hscale (-ψ) with ⟨ε₂, hε₂, hε₂mem⟩
        set r₁ : ℝ := 1 / ε₁
        set r₂ : ℝ := 1 / ε₂
        have hr₁ : 0 < r₁ := by simpa [r₁] using one_div_pos.2 hε₁
        have hr₂ : 0 < r₂ := by simpa [r₂] using one_div_pos.2 hε₂
        have hupper : ∀ x ∈ C, ψ x ≤ r₁ := by
          -- `ε₁ • ψ ∈ polar C` implies `ψ ∈ (1/ε₁) • polar C`.
          have hr₁mem : ψ ∈ r₁ • polar (E := E) C := by
            refine ⟨ε₁ • ψ, hε₁mem, ?_⟩
            have hε₁0 : ε₁ ≠ 0 := ne_of_gt hε₁
            -- `ψ = (1/ε₁) • (ε₁ • ψ)`.
            simp [r₁, smul_smul, div_eq_mul_inv, hε₁0]
          exact
            (section14_mem_smul_polar_iff_forall_le (E := E) (C := C) (r := r₁) hr₁ (φ := ψ)).1
              hr₁mem
        have hlower : ∀ x ∈ C, -(ψ x) ≤ r₂ := by
          have hr₂mem : (-ψ) ∈ r₂ • polar (E := E) C := by
            refine ⟨ε₂ • (-ψ), hε₂mem, ?_⟩
            have hε₂0 : ε₂ ≠ 0 := ne_of_gt hε₂
            simp [r₂, smul_smul, div_eq_mul_inv, hε₂0]
          have h' :
              ∀ x ∈ C, (-ψ) x ≤ r₂ :=
            (section14_mem_smul_polar_iff_forall_le (E := E) (C := C) (r := r₂) hr₂ (φ := -ψ)).1
              hr₂mem
          intro x hx
          simpa using (h' x hx)
        refine (isBounded_iff_forall_norm_le (s := ψ '' C)).2 ?_
        refine ⟨max r₁ r₂, ?_⟩
        rintro _ ⟨x, hx, rfl⟩
        have hle : ψ x ≤ max r₁ r₂ := le_trans (hupper x hx) (le_max_left _ _)
        have hge : -max r₁ r₂ ≤ ψ x := by
          have : -(ψ x) ≤ max r₁ r₂ := le_trans (hlower x hx) (le_max_right _ _)
          have : -max r₁ r₂ ≤ ψ x := by
            have := neg_le_neg this
            simpa [neg_neg] using this
          exact this
        have habs : |ψ x| ≤ max r₁ r₂ := (abs_le).2 ⟨hge, hle⟩
        simpa [Real.norm_eq_abs] using habs
      exact hC_bdd.2 hpointwise

/-- If `C` is given as `{x | ∀ φ ∈ Cpolar, φ x ≤ 1}`, then its recession cone is exactly the set of
directions on which every `φ ∈ Cpolar` is nonpositive. -/
lemma section14_recessionCone_eq_forall_polar_le_zero_of_bipolar
    {C : Set E} {Cpolar : Set (Module.Dual ℝ E)}
    (hbipolar : {x : E | ∀ φ ∈ Cpolar, φ x ≤ 1} = C) (hC0 : (0 : E) ∈ C) :
    Set.recessionCone C = {y : E | ∀ φ ∈ Cpolar, φ y ≤ 0} := by
  classical
  ext y
  constructor
  · intro hy φ hφ
    have hmul_le : ∀ n : ℕ, (n : ℝ) * (φ y) ≤ (1 : ℝ) := by
      intro n
      have hn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      have hmem0 : (0 : E) + (n : ℝ) • y ∈ C := hy (x := 0) hC0 (t := (n : ℝ)) hn
      have hmem : (n : ℝ) • y ∈ C := by simpa [zero_add] using hmem0
      have hmem' : (n : ℝ) • y ∈ {x : E | ∀ φ ∈ Cpolar, φ x ≤ 1} := by
        simpa [hbipolar] using hmem
      have : φ ((n : ℝ) • y) ≤ (1 : ℝ) := hmem' φ hφ
      simpa [map_smul, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using this
    exact section14_real_nonpos_of_nat_mul_le (r := φ y) (C := (1 : ℝ)) hmul_le
  · intro hy x hx t ht
    have hx' : x ∈ {x : E | ∀ φ ∈ Cpolar, φ x ≤ 1} := by
      simpa [hbipolar] using hx
    have hxt :
        x + t • y ∈ {x : E | ∀ φ ∈ Cpolar, φ x ≤ 1} := by
      -- Check the defining inequalities.
      show ∀ φ : Module.Dual ℝ E, φ ∈ Cpolar → φ (x + t • y) ≤ 1
      intro φ hφ
      have hxφ : φ x ≤ 1 := hx' φ hφ
      have hyφ : φ y ≤ 0 := hy φ hφ
      have hty : t * (φ y) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hyφ
      calc
        φ (x + t • y) = φ x + t * (φ y) := by
          simp [map_add, map_smul, smul_eq_mul]
        _ ≤ 1 + 0 := add_le_add hxφ hty
        _ = 1 := by ring
    simpa [hbipolar] using hxt

/-- Under the same bipolar hypothesis, the set of "two-sided" recession directions is exactly the
set of vectors annihilated by all `φ ∈ Cpolar`. -/
lemma section14_neg_rec_inter_rec_eq_forall_polar_eq_zero_of_bipolar
    {C : Set E} {Cpolar : Set (Module.Dual ℝ E)}
    (hbipolar : {x : E | ∀ φ ∈ Cpolar, φ x ≤ 1} = C) (hC0 : (0 : E) ∈ C) :
    (-Set.recessionCone C) ∩ Set.recessionCone C = {y : E | ∀ φ ∈ Cpolar, φ y = 0} := by
  classical
  have hrec :
      Set.recessionCone C = {y : E | ∀ φ ∈ Cpolar, φ y ≤ 0} :=
    section14_recessionCone_eq_forall_polar_le_zero_of_bipolar (E := E) (C := C) (Cpolar := Cpolar)
      hbipolar hC0
  ext y
  constructor
  · rintro ⟨hyneg, hypos⟩
    have hypos' : ∀ φ ∈ Cpolar, φ y ≤ 0 := by
      have : y ∈ {y : E | ∀ φ ∈ Cpolar, φ y ≤ 0} := by simpa [hrec] using hypos
      simpa [Set.mem_setOf_eq] using this
    have hyneg' : ∀ φ ∈ Cpolar, φ (-y) ≤ 0 := by
      have hyneg' : (-y) ∈ Set.recessionCone C := by simpa using hyneg
      have : (-y) ∈ {y : E | ∀ φ ∈ Cpolar, φ y ≤ 0} := by simpa [hrec] using hyneg'
      simpa [Set.mem_setOf_eq] using this
    -- Combine `φ y ≤ 0` and `φ (-y) ≤ 0` to get `φ y = 0`.
    show ∀ φ ∈ Cpolar, φ y = 0
    intro φ hφ
    have hle : φ y ≤ 0 := hypos' φ hφ
    have hge : 0 ≤ φ y := by
      have : φ (-y) ≤ 0 := hyneg' φ hφ
      have : -(φ y) ≤ 0 := by simpa [map_neg] using this
      exact (neg_nonpos).1 this
    exact le_antisymm hle hge
  · intro hy0
    have hypos' : ∀ φ ∈ Cpolar, φ y ≤ 0 := by
      intro φ hφ
      exact le_of_eq (hy0 φ hφ)
    have hyneg' : ∀ φ ∈ Cpolar, φ (-y) ≤ 0 := by
      intro φ hφ
      have : φ y = 0 := hy0 φ hφ
      simp [map_neg, this]
    have hypos : y ∈ Set.recessionCone C := by
      have : y ∈ {y : E | ∀ φ ∈ Cpolar, φ y ≤ 0} := by
        simpa [Set.mem_setOf_eq] using hypos'
      simpa [hrec] using this
    have hyneg : (-y) ∈ Set.recessionCone C := by
      have : (-y) ∈ {y : E | ∀ φ ∈ Cpolar, φ y ≤ 0} := by
        simpa [Set.mem_setOf_eq] using hyneg'
      simpa [hrec] using this
    exact ⟨by simpa using hyneg, hypos⟩

/-- Under the bipolar hypothesis, the lineality subspace of `C` (spanned by `(-rec C) ∩ rec C`)
is the dual coannihilator of the span of `Cpolar`. -/
lemma section14_dualCoannihilator_span_polar_eq_span_negRec_inter_rec_of_bipolar
    {C : Set E} {Cpolar : Set (Module.Dual ℝ E)}
    (hbipolar : {x : E | ∀ φ ∈ Cpolar, φ x ≤ 1} = C) (hC0 : (0 : E) ∈ C) :
    (Submodule.span ℝ Cpolar).dualCoannihilator =
        Submodule.span ℝ ((-Set.recessionCone C) ∩ Set.recessionCone C) := by
  classical
  have hlin :
      (-Set.recessionCone C) ∩ Set.recessionCone C = {y : E | ∀ φ ∈ Cpolar, φ y = 0} :=
    section14_neg_rec_inter_rec_eq_forall_polar_eq_zero_of_bipolar (E := E) (C := C)
      (Cpolar := Cpolar) hbipolar hC0
  ext x
  constructor
  · intro hx
    have hx0 : ∀ φ ∈ Cpolar, φ x = 0 := by
      have hx' : x ∈ ((Submodule.span ℝ Cpolar).dualCoannihilator : Set E) := hx
      simpa [Submodule.coe_dualCoannihilator_span] using hx'
    have hxlin : x ∈ (-Set.recessionCone C) ∩ Set.recessionCone C := by
      have : x ∈ {y : E | ∀ φ ∈ Cpolar, φ y = 0} := by
        simpa [Set.mem_setOf_eq] using hx0
      simpa [hlin] using this
    exact Submodule.subset_span hxlin
  · intro hx
    -- It suffices to check the defining equations on the generators.
    have hsub :
        (-Set.recessionCone C) ∩ Set.recessionCone C ⊆
          ((Submodule.span ℝ Cpolar).dualCoannihilator : Set E) := by
      intro z hz
      have hz0 : ∀ φ ∈ Cpolar, φ z = 0 := by
        have : z ∈ {y : E | ∀ φ ∈ Cpolar, φ y = 0} := by simpa [hlin] using hz
        simpa [Set.mem_setOf_eq] using this
      -- Turn `∀ φ ∈ Cpolar, φ z = 0` into membership in the coannihilator.
      simpa [Submodule.coe_dualCoannihilator_span] using hz0
    exact (Submodule.span_le.2 hsub) hx

/-- If `Cpolar = polar C` and `0 ∈ Cpolar`, then recession directions in `Cpolar` are exactly the
functionals nonpositive on `C`. -/
lemma section14_recessionCone_Cpolar_eq_forall_primal_le_zero_of_hpolar
    {C : Set E} {Cpolar : Set (Module.Dual ℝ E)}
    (hpolar : Cpolar = polar (E := E) C) (hCpolar0 : (0 : Module.Dual ℝ E) ∈ Cpolar) :
    Set.recessionCone Cpolar = {ψ : Module.Dual ℝ E | ∀ x ∈ C, ψ x ≤ 0} := by
  classical
  ext ψ
  constructor
  · intro hψ
    refine Set.mem_setOf.2 ?_
    intro x hxC
    have hmul_le : ∀ n : ℕ, (n : ℝ) * (ψ x) ≤ (1 : ℝ) := by
      intro n
      have hn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      have hmem : (0 : Module.Dual ℝ E) + (n : ℝ) • ψ ∈ Cpolar :=
        hψ (x := (0 : Module.Dual ℝ E)) hCpolar0 (t := (n : ℝ)) hn
      have hmem' : (0 : Module.Dual ℝ E) + (n : ℝ) • ψ ∈ polar (E := E) C := by
        simpa [hpolar] using hmem
      have hxle : ((0 : Module.Dual ℝ E) + (n : ℝ) • ψ) x ≤ 1 :=
        (mem_polar_iff (E := E) (C := C)
              (φ := (0 : Module.Dual ℝ E) + (n : ℝ) • ψ)).1 hmem' x hxC
      simpa [smul_eq_mul] using hxle
    exact section14_real_nonpos_of_nat_mul_le (r := ψ x) (C := (1 : ℝ)) hmul_le
  · intro hψ φ hφ t ht
    have hφ' : φ ∈ polar (E := E) C := by simpa [hpolar] using hφ
    have hsum : φ + t • ψ ∈ polar (E := E) C := by
      refine (mem_polar_iff (E := E) (C := C) (φ := φ + t • ψ)).2 ?_
      intro x hxC
      have hφx : φ x ≤ 1 := (mem_polar_iff (E := E) (C := C) (φ := φ)).1 hφ' x hxC
      have hψx : ψ x ≤ 0 := hψ x hxC
      have htψx : (t • ψ) x ≤ 0 := by
        simpa [smul_eq_mul] using (mul_nonpos_of_nonneg_of_nonpos ht hψx)
      calc
        (φ + t • ψ) x = φ x + (t • ψ) x := by simp
        _ ≤ 1 + 0 := add_le_add hφx htψx
        _ = 1 := by ring
    simpa [hpolar] using hsum

/-- If `Cpolar = polar C` and `0 ∈ Cpolar`, then the two-sided recession directions in `Cpolar`
are exactly the functionals vanishing on `C`. -/
lemma section14_lineality_Cpolar_eq_forall_primal_eq_zero_of_hpolar
    {C : Set E} {Cpolar : Set (Module.Dual ℝ E)}
    (hpolar : Cpolar = polar (E := E) C) (hCpolar0 : (0 : Module.Dual ℝ E) ∈ Cpolar) :
    (-Set.recessionCone Cpolar) ∩ Set.recessionCone Cpolar =
        {ψ : Module.Dual ℝ E | ∀ x ∈ C, ψ x = 0} := by
  classical
  have hrec :
      Set.recessionCone Cpolar = {ψ : Module.Dual ℝ E | ∀ x ∈ C, ψ x ≤ 0} :=
    section14_recessionCone_Cpolar_eq_forall_primal_le_zero_of_hpolar (E := E) (C := C)
      (Cpolar := Cpolar) hpolar hCpolar0
  ext ψ
  constructor
  · rintro ⟨hneg, hpos⟩
    have hpos' : ∀ x ∈ C, ψ x ≤ 0 := by
      have : ψ ∈ {ψ : Module.Dual ℝ E | ∀ x ∈ C, ψ x ≤ 0} := by simpa [hrec] using hpos
      simpa [Set.mem_setOf_eq] using this
    have hneg' : ∀ x ∈ C, (-ψ) x ≤ 0 := by
      have hneg_mem : (-ψ) ∈ Set.recessionCone Cpolar := by simpa using hneg
      have : (-ψ) ∈ {ψ : Module.Dual ℝ E | ∀ x ∈ C, ψ x ≤ 0} := by simpa [hrec] using hneg_mem
      simpa [Set.mem_setOf_eq] using this
    refine Set.mem_setOf.2 ?_
    intro x hxC
    have hle : ψ x ≤ 0 := hpos' x hxC
    have hge : 0 ≤ ψ x := by
      have : (-ψ) x ≤ 0 := hneg' x hxC
      have : -(ψ x) ≤ 0 := by simpa using this
      exact (neg_nonpos).1 this
    exact le_antisymm hle hge
  · intro hψ0
    have hpos' : ∀ x ∈ C, ψ x ≤ 0 := by
      intro x hxC
      exact le_of_eq (hψ0 x hxC)
    have hneg' : ∀ x ∈ C, (-ψ) x ≤ 0 := by
      intro x hxC
      have : ψ x = 0 := hψ0 x hxC
      simp [this]
    have hpos : ψ ∈ Set.recessionCone Cpolar := by
      have : ψ ∈ {ψ : Module.Dual ℝ E | ∀ x ∈ C, ψ x ≤ 0} := by
        simpa [Set.mem_setOf_eq] using hpos'
      simpa [hrec] using this
    have hneg_mem : (-ψ) ∈ Set.recessionCone Cpolar := by
      have : (-ψ) ∈ {ψ : Module.Dual ℝ E | ∀ x ∈ C, ψ x ≤ 0} := by
        simpa [Set.mem_setOf_eq] using hneg'
      simpa [hrec] using this
    exact ⟨by simpa using hneg_mem, hpos⟩

end Section14
end Chap03
