/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yuhao Jiang, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section14_part3

section Chap03
section Section14

open scoped Pointwise
open scoped Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Points in the polar (w.r.t. flipped evaluation) of the barrier cone of a closed convex set are
recession directions. -/
lemma section14_polar_barrierCone_subset_recessionCone [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] {C : Set E} (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C) :
    (PointedCone.dual (R := ℝ)
            ((-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))).flip (Set.barrierCone (E := E) C) :
          Set E) ⊆
      Set.recessionCone C := by
  classical
  intro y hy
  have hy_le :
      ∀ φ : Module.Dual ℝ E, φ ∈ Set.barrierCone (E := E) C → φ y ≤ 0 := by
    exact
      (section14_mem_dual_flip_eval_iff_forall_le_zero (E := E) (S := Set.barrierCone (E := E) C)
            (x := y)).1 hy
  intro x hx t ht
  by_contra hxt
  have ht0 : t ≠ 0 := by
    intro ht0
    subst ht0
    exact hxt (by simpa using hx)
  have hznot : x + t • y ∉ C := by simpa using hxt
  set z : E := x + t • y
  obtain ⟨f, u, hf, huz⟩ :=
    geometric_hahn_banach_closed_point (E := E) (s := C) (x := z) hCconv hCclosed (by
      simpa [z] using hznot)
  have hf_mem : (f : Module.Dual ℝ E) ∈ Set.barrierCone (E := E) C := by
    refine ⟨u, ?_⟩
    intro a ha
    exact le_of_lt (hf a ha)
  have hfy_le : (f : Module.Dual ℝ E) y ≤ 0 := hy_le (f : Module.Dual ℝ E) hf_mem

  have hxltu : f x < u := hf x hx
  have hxltz : f x < f z := lt_trans hxltu huz
  have hzcalc : f z = f x + t • f y := by
    simp [z, map_add, map_smul]
  have hmulpos : 0 < t * f y := by
    have : f x < f x + t * f y := by
      simpa [hzcalc, smul_eq_mul] using hxltz
    linarith
  have hfypos : 0 < f y := by
    have hmulpos' : 0 < f y * t := by simpa [mul_comm] using hmulpos
    exact pos_of_mul_pos_left hmulpos' ht
  exact (not_le_of_gt hfypos) (by simpa using hfy_le)

/-- Corollary 14.2.1. The polar of the barrier cone of a non-empty closed convex set `C` is the
recession cone of `C`. -/
theorem polar_barrierCone_eq_recessionCone_part4 [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] {C : Set E} (hCne : C.Nonempty)
    (hCclosed : IsClosed C) (hCconv : Convex ℝ C) :
    (PointedCone.dual (R := ℝ)
            ((-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))).flip (Set.barrierCone (E := E) C) :
          Set E) =
      Set.recessionCone C := by
  refine subset_antisymm ?_ ?_
  ·
    exact
      section14_polar_barrierCone_subset_recessionCone (E := E) (C := C) hCclosed hCconv
  ·
    exact section14_recessionCone_subset_polar_barrierCone (E := E) (C := C) hCne

/-- The zero vector always lies in the recession cone of an `EReal` function. -/
lemma section14_recessionConeEReal_zero_mem {F : Type*} [AddCommGroup F] (f : F → EReal) :
    (0 : F) ∈ recessionConeEReal (F := F) f := by
  refine (section14_mem_recessionConeEReal_iff (F := F) (g := f) (y := 0)).2 ?_
  intro x hx
  have hle : f (x + (0 : F)) ≤ f x := by simp
  exact (EReal.sub_nonpos).2 hle

/-- If a set is contained in `{0}`, then its polar cone is all of the dual space. -/
lemma section14_polarCone_eq_univ_of_subset_singleton_zero (S : Set E) (hS : S ⊆ ({0} : Set E)) :
    polarCone (E := E) S = (Set.univ : Set (Module.Dual ℝ E)) := by
  ext φ
  constructor
  · intro _
    trivial
  · intro _
    refine (mem_polarCone_iff (E := E) (K := S) (φ := φ)).2 ?_
    intro x hx
    have hx0 : x = 0 := by
      have : x ∈ ({0} : Set E) := hS hx
      simpa using this
    subst hx0
    simp

/-- A polar cone is all of the dual space iff the original set is contained in `{0}`. -/
lemma section14_polarCone_eq_univ_iff_subset_singleton_zero (S : Set E) :
    polarCone (E := E) S = (Set.univ : Set (Module.Dual ℝ E)) ↔ S ⊆ ({0} : Set E) := by
  constructor
  · intro hpol x hx
    have hx0 : (∀ φ : Module.Dual ℝ E, φ x = 0) := by
      intro φ
      have hφmem : φ ∈ polarCone (E := E) S := by
        simp [hpol]
      have hle : φ x ≤ 0 :=
        (mem_polarCone_iff (E := E) (K := S) (φ := φ)).1 hφmem x hx
      have hlem : (-φ) x ≤ 0 := by
        have hφmem' : (-φ) ∈ polarCone (E := E) S := by
          simp [hpol]
        exact (mem_polarCone_iff (E := E) (K := S) (φ := -φ)).1 hφmem' x hx
      have hnonneg : 0 ≤ φ x := by
        have : -(φ x) ≤ 0 := by simpa using hlem
        exact (neg_nonpos).1 this
      exact le_antisymm hle hnonneg
    have : x = 0 :=
      (Module.forall_dual_apply_eq_zero_iff (K := ℝ) (V := E) x).1 hx0
    simp [Set.mem_singleton_iff, this]
  · intro hS
    exact
      section14_polarCone_eq_univ_of_subset_singleton_zero (E := E) (S := S) hS

/-- A set equals `{0}` iff its polar cone is `univ`, provided it contains `0`. -/
lemma section14_eq_singleton_zero_iff_polarCone_eq_univ {S : Set E} (h0 : (0 : E) ∈ S) :
    S = ({0} : Set E) ↔ polarCone (E := E) S = (Set.univ : Set (Module.Dual ℝ E)) := by
  constructor
  · intro hS
    refine
      section14_polarCone_eq_univ_of_subset_singleton_zero (E := E) (S := S) (by
        intro x hx
        simpa [hS] using hx)
  · intro hpol
    have hsub : S ⊆ ({0} : Set E) :=
      (section14_polarCone_eq_univ_iff_subset_singleton_zero (E := E) (S := S)).1 hpol
    apply subset_antisymm hsub
    intro x hx
    have hx0 : x = 0 := by simpa [Set.mem_singleton_iff] using hx
    subst hx0
    simpa using h0

/-- If `C` is closed under translation by `y`, then all natural translates stay in `C`. -/
lemma section14_add_mem_of_add_mem_nat_smul {C : Set E} {y : E} (hadd : ∀ x ∈ C, x + y ∈ C) :
    ∀ {x} (_hx : x ∈ C) (m : ℕ), x + (m : ℝ) • y ∈ C := by
  intro x hx m
  induction m generalizing x with
  | zero =>
      simpa using hx
  | succ m ih =>
      have hx' : x + (m : ℝ) • y ∈ C := ih hx
      have : x + (m : ℝ) • y + y ∈ C := hadd (x := x + (m : ℝ) • y) hx'
      simpa [Nat.cast_add, add_smul, one_smul, add_assoc] using this

/-- If `C` is convex and `C + y ⊆ C`, then `y` lies in the recession cone. -/
lemma section14_mem_recessionCone_of_add_mem {C : Set E} (hconv : Convex ℝ C) {y : E}
    (hadd : ∀ x ∈ C, x + y ∈ C) : y ∈ Set.recessionCone C := by
  intro x hx t ht
  by_cases hzero : t = 0
  · simpa [hzero] using hx
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
  obtain ⟨m : ℕ, hm⟩ := exists_nat_ge t
  have hxmy : x + (m : ℝ) • y ∈ C :=
    section14_add_mem_of_add_mem_nat_smul (E := E) (C := C) (y := y) hadd hx m
  have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le htpos hm
  have hdivnonneg : 0 ≤ t / (m : ℝ) := div_nonneg ht (le_of_lt hmpos)
  have hdivle : t / (m : ℝ) ≤ (1 : ℝ) :=
    (div_le_one (a := t) (b := (m : ℝ)) hmpos).2 hm
  have hxmem : x + (t / (m : ℝ)) • ((m : ℝ) • y) ∈ C :=
    hconv.add_smul_mem hx hxmy ⟨hdivnonneg, hdivle⟩
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hmul : (t / (m : ℝ)) * (m : ℝ) = t := by
    field_simp [hm0]
  simpa [smul_smul, hmul] using hxmem

/-- Sublevel sets of a Jensen-convex `EReal` function are convex. -/
lemma section14_convex_sublevel {f : E → EReal} (hfconv : ConvexERealFunction (F := E) f)
    (α : ℝ) : Convex ℝ {x : E | f x ≤ (α : EReal)} := by
  intro x hx y hy a b ha hb hab
  have hconv := hfconv (x := x) (y := y) (a := a) (b := b) ha hb hab
  have ha' : (0 : EReal) ≤ (a : EReal) := by simpa [EReal.coe_nonneg] using ha
  have hb' : (0 : EReal) ≤ (b : EReal) := by simpa [EReal.coe_nonneg] using hb
  have hmulx : (a : EReal) * f x ≤ (a : EReal) * (α : EReal) :=
    mul_le_mul_of_nonneg_left hx ha'
  have hmuly : (b : EReal) * f y ≤ (b : EReal) * (α : EReal) :=
    mul_le_mul_of_nonneg_left hy hb'
  have hsum :
      (a : EReal) * f x + (b : EReal) * f y ≤
        (a : EReal) * (α : EReal) + (b : EReal) * (α : EReal) :=
    add_le_add hmulx hmuly
  have hab' : (a : EReal) + (b : EReal) = (1 : EReal) := by
    simpa [EReal.coe_add] using congrArg (fun r : ℝ => (r : EReal)) hab
  have hα :
      (a : EReal) * (α : EReal) + (b : EReal) * (α : EReal) = (α : EReal) := by
    have haα : (a : EReal) * (α : EReal) = ((a * α : ℝ) : EReal) := by
      simp
    have hbα : (b : EReal) * (α : EReal) = ((b * α : ℝ) : EReal) := by
      simp
    have hreal : (a * α + b * α : ℝ) = α := by
      calc
        a * α + b * α = (a + b) * α := by ring
        _ = 1 * α := by simp [hab]
        _ = α := by ring
    calc
      (a : EReal) * (α : EReal) + (b : EReal) * (α : EReal)
          = ((a * α : ℝ) : EReal) + ((b * α : ℝ) : EReal) := by
              rw [haα, hbα]
      _ = ((a * α + b * α : ℝ) : EReal) := by
          simp
      _ = (α : EReal) := by simp [hreal]
  exact (hconv.trans hsum).trans_eq hα

/-- A recession direction of `f` is a recession direction of every real sublevel set of `f`. -/
lemma section14_recessionConeEReal_subset_recessionCone_sublevel {f : E → EReal}
    (hfconv : ConvexERealFunction (F := E) f) {α : ℝ} :
    recessionConeEReal (F := E) f ⊆ Set.recessionCone {x : E | f x ≤ (α : EReal)} := by
  intro y hy
  have hconv : Convex ℝ {x : E | f x ≤ (α : EReal)} :=
    section14_convex_sublevel (E := E) (f := f) hfconv α
  have hadd : ∀ x ∈ {x : E | f x ≤ (α : EReal)}, x + y ∈ {x : E | f x ≤ (α : EReal)} := by
    intro x hx
    have hxdom : x ∈ erealDom f :=
      lt_of_le_of_lt hx (EReal.coe_lt_top α)
    have hstep : f (x + y) ≤ f x ∧ x + y ∈ erealDom f :=
      section14_step_le_of_mem_recessionCone (g := f) (x := x) (y := y) hy hxdom
    exact hstep.1.trans hx
  exact section14_mem_recessionCone_of_add_mem (E := E) (C := {x : E | f x ≤ (α : EReal)})
    hconv hadd

/-- If `f` is proper, convex, and lower semicontinuous, then any recession direction of a nonempty
real sublevel set is a recession direction of `f`. -/
lemma section14_recessionCone_sublevel_subset_recessionConeEReal {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → EReal} (hf : ProperConvexERealFunction (F := E) f)
    (hf_closed : LowerSemicontinuous f) {α : ℝ}
    (hne : ({x : E | f x ≤ (α : EReal)}).Nonempty) :
    Set.recessionCone {x : E | f x ≤ (α : EReal)} ⊆ recessionConeEReal (F := E) f := by
  classical
  have hfconv : ConvexERealFunction (F := E) f := hf.2
  intro y hy
  rcases hne with ⟨x0, hx0⟩
  refine (section14_mem_recessionConeEReal_iff (g := f) (y := y)).2 ?_
  intro x hxdom
  -- Write `f x` as a real number.
  rcases section14_eq_coe_of_lt_top (z := f x) hxdom (hf.1.1 x) with ⟨β, hβ⟩
  -- Define the interpolation coefficients and points.
  let b : ℕ → ℝ := fun n => (1 : ℝ) / ((n : ℝ) + 1)
  let a : ℕ → ℝ := fun n => (n : ℝ) / ((n : ℝ) + 1)
  let u : ℕ → E := fun n => (a n) • x + (b n) • (x0 + ((n : ℝ) + 1) • y)

  have hb_tendsto : Filter.Tendsto b Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa [b] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

  have hu_eq : ∀ n, u n = x + y + (b n) • (x0 - x) := by
    intro n
    have hden : (n : ℝ) + 1 ≠ 0 := by
      have : (0 : ℝ) < (n : ℝ) + 1 := by
        have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
        linarith
      exact ne_of_gt this
    have hab : a n = 1 - b n := by
      -- `n/(n+1) = 1 - 1/(n+1)`
      unfold a b
      field_simp [hden]
      ring
    have hbt : (b n) * ((n : ℝ) + 1) = (1 : ℝ) := by
      unfold b
      field_simp [hden]
    -- Expand `u n` and simplify.
    calc
      u n
          = (a n) • x + (b n) • x0 + ((b n) * ((n : ℝ) + 1)) • y := by
              simp [u, smul_add, add_assoc, smul_smul]
      _ = (a n) • x + (b n) • x0 + y := by
              simp [hbt]
      _ = x + y + (b n) • (x0 - x) := by
              -- Rewrite the first two terms using `a n = 1 - b n`.
              simp [hab, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_add,
                add_smul, one_smul]

  have hu_tendsto : Filter.Tendsto u Filter.atTop (𝓝 (x + y)) := by
    have hsmul :
        Filter.Tendsto (fun n => (b n) • (x0 - x)) Filter.atTop (𝓝 (0 : E)) := by
      simpa using hb_tendsto.smul_const (x0 - x)
    have : Filter.Tendsto (fun n => x + y + (b n) • (x0 - x)) Filter.atTop (𝓝 ((x + y) + 0)) :=
      (tendsto_const_nhds (x := x + y)).add hsmul
    have huv : (fun n => x + y + (b n) • (x0 - x)) = u := by
      funext n
      exact (hu_eq n).symm
    simpa [huv, add_zero] using this

  have hsublevel_step :
      ∀ n : ℕ, f (x0 + ((n : ℝ) + 1) • y) ≤ (α : EReal) := by
    intro n
    have ht : (0 : ℝ) ≤ (n : ℝ) + 1 := by
      have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      linarith
    -- `y` is a recession direction of the sublevel set.
    have : x0 + ((n : ℝ) + 1) • y ∈ {z : E | f z ≤ (α : EReal)} :=
      hy (x := x0) hx0 (t := (n : ℝ) + 1) ht
    simpa using this

  have hconv_u :
      ∀ n : ℕ,
        f (u n) ≤ (a n : EReal) * f x + (b n : EReal) * (α : EReal) := by
    intro n
    have ha : 0 ≤ a n := by
      have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      have hden : 0 < (n : ℝ) + 1 := by linarith
      exact div_nonneg hn (le_of_lt hden)
    have hb : 0 ≤ b n := by
      have hden : 0 < (n : ℝ) + 1 := by
        have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
        linarith
      exact div_nonneg (show (0 : ℝ) ≤ 1 by norm_num) (le_of_lt hden)
    have hab : a n + b n = 1 := by
      have hden : (n : ℝ) + 1 ≠ 0 := by
        have : (0 : ℝ) < (n : ℝ) + 1 := by
          have hn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
          linarith
        exact ne_of_gt this
      unfold a b
      field_simp [hden]
    have hmain :=
      hfconv (x := x) (y := x0 + ((n : ℝ) + 1) • y) (a := a n) (b := b n) ha hb hab
    have hsub : (b n : EReal) * f (x0 + ((n : ℝ) + 1) • y) ≤ (b n : EReal) * (α : EReal) := by
      have hb' : (0 : EReal) ≤ (b n : EReal) := by
        simpa [EReal.coe_nonneg] using hb
      exact mul_le_mul_of_nonneg_left (hsublevel_step n) hb'
    have : (a n : EReal) * f x + (b n : EReal) * f (x0 + ((n : ℝ) + 1) • y)
        ≤ (a n : EReal) * f x + (b n : EReal) * (α : EReal) := by
      have h' :
          (b n : EReal) * f (x0 + ((n : ℝ) + 1) • y) + (a n : EReal) * f x ≤
            (b n : EReal) * (α : EReal) + (a n : EReal) * f x :=
        add_le_add_left hsub ((a n : EReal) * f x)
      simpa [add_assoc, add_left_comm, add_comm] using h'
    exact hmain.trans this

  -- For any `ε > 0`, eventually `u n` lies in the closed sublevel `{z | f z ≤ β + ε}`.
  have hmem_closedSublevel :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in Filter.atTop, u n ∈ {z : E | f z ≤ ((β + ε : ℝ) : EReal)} := by
    intro ε hε
    have hmul_tendsto :
        Filter.Tendsto (fun n => (b n) * |α - β|) Filter.atTop (𝓝 (0 : ℝ)) := by
      simpa [b, mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (|α - β|)
    have hlt : ∀ᶠ n : ℕ in Filter.atTop, (b n) * |α - β| < ε :=
      (tendsto_order.1 hmul_tendsto).2 ε hε
    filter_upwards [hlt] with n hn
    have hn_le : |(b n) * (α - β)| ≤ ε := by
      have hb_nonneg : 0 ≤ b n := by
        have hden : 0 < (n : ℝ) + 1 := by
          have hn' : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
          linarith
        exact div_nonneg (show (0 : ℝ) ≤ 1 by norm_num) (le_of_lt hden)
      have habs : |(b n) * (α - β)| = (b n) * |α - β| := by
        simp [abs_mul, abs_of_nonneg hb_nonneg]
      exact le_of_lt (by simpa [habs] using hn)
    have hn_le' : (b n) * (α - β) ≤ ε := le_trans (le_abs_self _) hn_le

    have hcoe : ((β + (b n) * (α - β) : ℝ) : EReal) ≤ ((β + ε : ℝ) : EReal) := by
      have h' : (b n) * (α - β) + β ≤ ε + β := add_le_add_left hn_le' β
      have h'' : β + (b n) * (α - β) ≤ β + ε := by
        simpa [add_assoc, add_left_comm, add_comm] using h'
      exact (EReal.coe_le_coe_iff).2 h''

    have hbound :
        f (u n) ≤ ((β + (b n) * (α - β) : ℝ) : EReal) := by
      have h1 := hconv_u n
      -- Rewrite the RHS into real arithmetic.
      have hR :
          (a n : EReal) * f x + (b n : EReal) * (α : EReal) =
            ((β + (b n) * (α - β) : ℝ) : EReal) := by
        -- Use `f x = β` and compute the convex combination.
        have hden : (n : ℝ) + 1 ≠ 0 := by
          have : (0 : ℝ) < (n : ℝ) + 1 := by
            have hn' : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
            linarith
          exact ne_of_gt this
        -- `a n = 1 - b n`.
        have hab' : a n = 1 - b n := by
          unfold a b
          field_simp [hden]
          ring
        -- Put everything back in `ℝ`.
        have hxR : (a n : EReal) * f x = ((a n * β : ℝ) : EReal) := by
          simp [hβ]
        have hyR : (b n : EReal) * (α : EReal) = ((b n * α : ℝ) : EReal) := by
          simp
        have hsum :
            ((a n * β : ℝ) : EReal) + ((b n * α : ℝ) : EReal) =
              ((a n * β + b n * α : ℝ) : EReal) := by
          simp
        have hreal : a n * β + b n * α = β + b n * (α - β) := by
          calc
            a n * β + b n * α = (1 - b n) * β + b n * α := by simp [hab']
            _ = β + b n * (α - β) := by ring
        calc
          (a n : EReal) * f x + (b n : EReal) * (α : EReal)
              = ((a n * β : ℝ) : EReal) + ((b n * α : ℝ) : EReal) := by
                  rw [hxR, hyR]
          _ = ((a n * β + b n * α : ℝ) : EReal) := hsum
          _ = ((β + b n * (α - β) : ℝ) : EReal) := by simp [hreal]
      exact h1.trans_eq hR
    exact le_trans hbound hcoe

  have hforall_eps :
      ∀ ε : ℝ, 0 < ε → f (x + y) ≤ ((β + ε : ℝ) : EReal) := by
    intro ε hε
    have hclosed : IsClosed {z : E | f z ≤ ((β + ε : ℝ) : EReal)} := by
      simpa [Set.preimage, Set.Iic] using hf_closed.isClosed_preimage ((β + ε : ℝ) : EReal)
    have hmem : ∀ᶠ n : ℕ in Filter.atTop, u n ∈ {z : E | f z ≤ ((β + ε : ℝ) : EReal)} :=
      hmem_closedSublevel ε hε
    exact (hclosed.mem_of_tendsto hu_tendsto hmem)

  -- Turn the `ε`-bounds into the desired inequality `f (x+y) ≤ f x`.
  have hxylttop : f (x + y) < ⊤ := by
    have := hforall_eps 1 (by norm_num : (0 : ℝ) < 1)
    exact lt_of_le_of_lt this (EReal.coe_lt_top _)
  rcases section14_eq_coe_of_lt_top (z := f (x + y)) hxylttop (hf.1.1 (x + y)) with ⟨γ, hγ⟩
  have hγle : γ ≤ β := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hleE : (γ : EReal) ≤ ((β + ε : ℝ) : EReal) := by
      simpa [hγ] using hforall_eps ε hε
    exact (EReal.coe_le_coe_iff).1 hleE
  have hle : f (x + y) ≤ f x := by
    simpa [hγ, hβ] using (EReal.coe_le_coe_iff.2 hγle : (γ : EReal) ≤ (β : EReal))
  exact (EReal.sub_nonpos).2 hle

/-- Corollary 14.2.2. Let `f` be a closed proper convex function. In order that the sublevel set
`{x | f x ≤ α}` be bounded for every `α ∈ ℝ`, it is necessary and sufficient that
`0 ∈ int (dom f*)`. Here `f*` is the Fenchel–Legendre conjugate and `dom` denotes the effective
domain (the set where the value is finite).

In this formalization we record a topology-free equivalent criterion:
the polar cone of the recession cone of `f` is all of the dual space. -/
theorem sublevelSets_bounded_iff_zero_mem_interior_dom_fenchelConjugate {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EReal}
    (hf : ProperConvexERealFunction (F := EuclideanSpace ℝ (Fin n)) f)
    (hf_closed : LowerSemicontinuous f) :
    (∀ α : ℝ, Bornology.IsBounded {x : EuclideanSpace ℝ (Fin n) | f x ≤ (α : EReal)}) ↔
      polarCone (E := EuclideanSpace ℝ (Fin n))
          (recessionConeEReal (F := EuclideanSpace ℝ (Fin n)) f) =
        (Set.univ : Set (Module.Dual ℝ (EuclideanSpace ℝ (Fin n)))) := by
  classical
  -- Work with `E = ℝ^n`.
  let E := EuclideanSpace ℝ (Fin n)

  have hbdd :
      (∀ α : ℝ, Bornology.IsBounded {x : E | f x ≤ (α : EReal)}) ↔
        recessionConeEReal (F := E) f = ({0} : Set E) := by
    -- TODO: this is the Theorem 8.7/8.4 ingredient from the textbook: bounded sublevel sets
    -- iff the recession cone is `{0}`.
    constructor
    · intro hαbdd
      -- Pick a nonempty bounded sublevel set using properness.
      rcases hf.1.2 with ⟨x0, hx0neTop⟩
      have hx0lt : f x0 < ⊤ := lt_top_iff_ne_top.2 hx0neTop
      rcases section14_eq_coe_of_lt_top (z := f x0) hx0lt (hf.1.1 x0) with ⟨r0, hr0⟩
      set C : Set E := {x : E | f x ≤ (r0 : EReal)}
      have hCne : C.Nonempty := by
        refine ⟨x0, ?_⟩
        simp [C, hr0]
      have hCclosed : IsClosed C := by
        -- sublevel sets of a lsc function are closed
        simpa [C, Set.preimage, Set.Iic] using hf_closed.isClosed_preimage (r0 : EReal)
      have hCconv : Convex ℝ C := section14_convex_sublevel (E := E) (f := f) hf.2 r0
      have hCbdd : Bornology.IsBounded C := by
        simpa [C] using hαbdd r0
      have hrcC : Set.recessionCone C = {0} :=
        (bounded_iff_recessionCone_eq_singleton_zero (n := n) (C := C) hCne hCclosed hCconv).1 hCbdd
      have hsub : recessionConeEReal (F := E) f ⊆ ({0} : Set E) := by
        intro y hy
        have hy' : y ∈ Set.recessionCone C := by
          have : y ∈ Set.recessionCone {x : E | f x ≤ (r0 : EReal)} :=
            section14_recessionConeEReal_subset_recessionCone_sublevel (E := E) (f := f) hf.2
              (α := r0) hy
          simpa [C] using this
        have : y ∈ ({0} : Set E) := by simpa [hrcC] using hy'
        simpa using this
      apply subset_antisymm
      · simpa using hsub
      · intro y hy0
        have : y = 0 := by simpa using hy0
        subst this
        simpa using section14_recessionConeEReal_zero_mem (F := E) f
    · intro hrc α
      -- If the sublevel set is empty, it is bounded.
      by_cases hne : ({x : E | f x ≤ (α : EReal)}).Nonempty
      ·
        have hCclosed : IsClosed {x : E | f x ≤ (α : EReal)} := by
          simpa [Set.preimage, Set.Iic] using hf_closed.isClosed_preimage (α : EReal)
        have hCconv : Convex ℝ {x : E | f x ≤ (α : EReal)} :=
          section14_convex_sublevel (E := E) (f := f) hf.2 α
        have hsub : Set.recessionCone {x : E | f x ≤ (α : EReal)} ⊆ ({0} : Set E) := by
          intro y hy
          have hyf : y ∈ recessionConeEReal (F := E) f :=
            (section14_recessionCone_sublevel_subset_recessionConeEReal (E := E) (f := f) hf
              hf_closed (α := α) hne) hy
          have : y ∈ ({0} : Set E) := by simpa [hrc] using hyf
          simpa using this
        have h0mem : (0 : E) ∈ Set.recessionCone {x : E | f x ≤ (α : EReal)} := by
          intro x hx t ht
          simpa using hx
        have hrcC : Set.recessionCone {x : E | f x ≤ (α : EReal)} = {0} := by
          apply subset_antisymm hsub
          intro y hy0
          have : y = 0 := by simpa using hy0
          subst this
          exact h0mem
        exact
          (bounded_iff_recessionCone_eq_singleton_zero (n := n)
                (C := {x : E | f x ≤ (α : EReal)}) hne hCclosed hCconv).2 hrcC
      ·
        have hempty : ({x : E | f x ≤ (α : EReal)}) = ∅ := by
          simpa using (Set.not_nonempty_iff_eq_empty.1 hne)
        simp [hempty]

  have h0mem : (0 : E) ∈ recessionConeEReal (F := E) f := by
    simpa using section14_recessionConeEReal_zero_mem (F := E) f
  have hpolar_univ :
      recessionConeEReal (F := E) f = ({0} : Set E) ↔
        polarCone (E := E) (recessionConeEReal (F := E) f) =
          (Set.univ : Set (Module.Dual ℝ E)) := by
    simpa using
      (section14_eq_singleton_zero_iff_polarCone_eq_univ (E := E)
          (S := recessionConeEReal (F := E) f) h0mem)

  simpa [E] using hbdd.trans hpolar_univ

end Section14
end Chap03
