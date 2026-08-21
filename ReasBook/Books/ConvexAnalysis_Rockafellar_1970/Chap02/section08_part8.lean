/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Shu Miao, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section08_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section07_part3

noncomputable section
open scoped Pointwise

section Chap02
section Section09

/-- Definition 8.9.0. The lineality space of `f0_plus` on `ℝ^n`. -/
def Function.linealitySpace' {n : Nat} (f0_plus : (Fin n → Real) → EReal) :
    Set (Fin n → Real) :=
  { y | f0_plus (-y) = -(f0_plus y) }

/-- Definition 8.9.1. The directions of the vectors in the lineality space of `f` are called
directions in which `f` is affine. -/
def Function.IsAffineDirection {n : Nat} (f0_plus : (Fin n → Real) → EReal)
    (y : Fin n → Real) : Prop :=
  y ∈ Function.linealitySpace' f0_plus

/-- Definition 8.9.2. The dimension of the lineality space of `f` is the lineality of `f`. -/
def Function.lineality {n : Nat} (f0_plus : (Fin n → Real) → EReal) : Nat :=
  Module.finrank Real (Submodule.span Real (Function.linealitySpace' f0_plus))

/-- Definition 8.9.2. The rank of `f` is defined to be the dimension of `f` minus the
lineality of `f`. -/
def Function.rank {n : Nat} (f0_plus : (Fin n → Real) → EReal)
    (dim_f : Nat) : Nat :=
  dim_f - Function.lineality f0_plus

/-- Rank zero forces `dim_f` to be at most the lineality. -/
lemma rank_eq_zero_le_lineality {n : Nat}
    {f0_plus : (Fin n → Real) → EReal} {dim_f : Nat}
    (h : Function.rank f0_plus dim_f = 0) :
    dim_f ≤ Function.lineality f0_plus := by
  exact (Nat.sub_eq_zero_iff_le).1 (by simpa [Function.rank] using h)

/-- Proper convexity implies the effective domain is nonempty. -/
lemma properConvexFunctionOn_effectiveDomain_nonempty {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
  have hne_epi :
      Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) f) := hf.2.1
  exact
    (nonempty_epigraph_iff_nonempty_effectiveDomain (S := (Set.univ : Set (Fin n → Real)))
        (f := f)).1 hne_epi

/-- Points outside the affine span of the effective domain are not in the effective domain. -/
lemma not_mem_effectiveDomain_of_not_mem_affineSpan {n : Nat}
    {f : (Fin n → Real) → EReal} {x : Fin n → Real}
    (hx :
      x ∉ affineSpan Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    x ∉ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
  intro hxmem
  apply hx
  exact
    (subset_affineSpan (k := Real)
      (s := effectiveDomain (Set.univ : Set (Fin n → Real)) f)) hxmem

/-- Values of the recession function are finite on its lineality space. -/
lemma linealitySpace_value_real {n : Nat}
    {f0_plus : (Fin n → Real) → EReal}
    (hf0_plus : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f0_plus)
    {y : Fin n → Real} (hy : y ∈ Function.linealitySpace' f0_plus) :
    ∃ v : ℝ, f0_plus y = (v : EReal) := by
  have hbot : f0_plus y ≠ (⊥ : EReal) := by
    simpa using (hf0_plus.2.2 y (by simp))
  have hbot_neg : f0_plus (-y) ≠ (⊥ : EReal) := by
    simpa using (hf0_plus.2.2 (-y) (by simp))
  have htop : f0_plus y ≠ (⊤ : EReal) := by
    intro htop
    have hneg : f0_plus (-y) = (⊥ : EReal) := by
      simpa [Function.linealitySpace', htop] using hy
    exact (hbot_neg hneg).elim
  rcases (EReal.exists (p := fun r => r = f0_plus y)).1 ⟨f0_plus y, rfl⟩ with
    hy_bot | hy_top | hy_real
  · exact (hbot hy_bot.symm).elim
  · exact (htop hy_top.symm).elim
  · rcases hy_real with ⟨v, hv⟩
    exact ⟨v, hv.symm⟩

/-- Rank zero identifies the affine-span direction with the span of the lineality space,
provided the inclusion is available. -/
lemma lineality_span_eq_affineSpan_direction_of_rank_zero {n : Nat}
    {f : (Fin n → Real) → EReal} {f0_plus : (Fin n → Real) → EReal}
    {dim_f : Nat}
    (hdim :
      dim_f =
        Module.finrank Real
          (affineSpan Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).direction)
    (hrank : Function.rank f0_plus dim_f = 0)
    (hspan :
      Submodule.span Real (Function.linealitySpace' f0_plus) ≤
        (affineSpan Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).direction) :
    Submodule.span Real (Function.linealitySpace' f0_plus) =
      (affineSpan Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).direction := by
  have hle : dim_f ≤ Function.lineality f0_plus :=
    rank_eq_zero_le_lineality (f0_plus := f0_plus) (dim_f := dim_f) hrank
  refine Submodule.eq_of_le_of_finrank_le hspan ?_
  have hle' :
      Module.finrank Real
          (affineSpan Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).direction ≤
        Module.finrank Real (Submodule.span Real (Function.linealitySpace' f0_plus)) := by
    simpa [Function.lineality, hdim] using hle
  exact hle'

/-- If `x0` and `x0 + y` are in the effective domain, then `y` is a direction of its affine span. -/
lemma mem_direction_affineSpan_of_mem_effectiveDomain_add {n : Nat}
    {f : (Fin n → Real) → EReal} {x0 y : Fin n → Real}
    (hx0 : x0 ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (hx0y : x0 + y ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f) :
    y ∈
      (affineSpan Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).direction := by
  have hx0' :
      x0 ∈ affineSpan Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
    subset_affineSpan (k := Real)
      (s := effectiveDomain (Set.univ : Set (Fin n → Real)) f) hx0
  have hx0y' :
      x0 + y ∈ affineSpan Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
    subset_affineSpan (k := Real)
      (s := effectiveDomain (Set.univ : Set (Fin n → Real)) f) hx0y
  have hdir :
      (x0 + y) -ᵥ x0 ∈
        (affineSpan Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).direction :=
    AffineSubspace.vsub_mem_direction
      (s := affineSpan Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) hx0y' hx0'
  simpa [vsub_eq_sub, add_sub_cancel_left] using hdir

/-- Additive majorants keep lineality directions inside the effective domain. -/
lemma lineality_mem_effectiveDomain_of_additive_majorant {n : Nat}
    {f : (Fin n → Real) → EReal} {f0_plus : (Fin n → Real) → EReal}
    (hf0_plus : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f0_plus)
    (hmaj : ∀ x y : Fin n → Real, f (x + y) ≤ f x + f0_plus y)
    {x0 : Fin n → Real}
    (hx0 : x0 ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f) :
    ∀ y ∈ Function.linealitySpace' f0_plus,
      x0 + y ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
  intro y hy
  obtain ⟨v, hv⟩ := linealitySpace_value_real (f0_plus := f0_plus) hf0_plus hy
  have hx0_top : f x0 ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := f) hx0
  have hy_top : f0_plus y ≠ (⊤ : EReal) := by
    simp [hv]
  have hsum_top : (f x0 : EReal) + f0_plus y ≠ (⊤ : EReal) :=
    EReal.add_ne_top hx0_top hy_top
  have hxy_top : f (x0 + y) ≠ (⊤ : EReal) := by
    intro htop
    have htop_le : (⊤ : EReal) ≤ (f x0 : EReal) + f0_plus y := by
      simpa [htop] using (hmaj x0 y)
    exact hsum_top (top_le_iff.mp htop_le)
  have hlt : f (x0 + y) < (⊤ : EReal) := (lt_top_iff_ne_top).2 hxy_top
  have hmem :
      x0 + y ∈
        {x | x ∈ (Set.univ : Set (Fin n → Real)) ∧ f x < (⊤ : EReal)} := by
    exact ⟨by simp, hlt⟩
  simpa [effectiveDomain_eq] using hmem

/-- If lineality directions preserve the effective domain, then their span lies in the
direction of the affine span of the effective domain. -/
lemma lineality_span_le_direction_affineSpan {n : Nat}
    {f : (Fin n → Real) → EReal} {f0_plus : (Fin n → Real) → EReal}
    {x0 : Fin n → Real}
    (hx0 : x0 ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    (hmem :
      ∀ y ∈ Function.linealitySpace' f0_plus,
        x0 + y ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f) :
    Submodule.span Real (Function.linealitySpace' f0_plus) ≤
      (affineSpan Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).direction := by
  refine Submodule.span_le.2 ?_
  intro y hy
  exact
    mem_direction_affineSpan_of_mem_effectiveDomain_add (f := f) (x0 := x0) (y := y)
      hx0 (hmem y hy)

/-- Membership in the affine span is equivalent to membership in the translated direction. -/
lemma mem_affineSpan_iff_vsub_mem_direction {n : Nat}
    {s : Set (Fin n → Real)} {x0 x : Fin n → Real}
    (hx0 : x0 ∈ affineSpan Real s) :
    x ∈ affineSpan Real s ↔ x -ᵥ x0 ∈ (affineSpan Real s).direction := by
  have hmk :
      AffineSubspace.mk' x0 (affineSpan Real s).direction =
        affineSpan Real s := by
    simpa using (AffineSubspace.mk'_eq (s := affineSpan Real s) (p := x0) hx0)
  have hmem :
      x ∈ AffineSubspace.mk' x0 (affineSpan Real s).direction ↔
        x -ᵥ x0 ∈ (affineSpan Real s).direction := by
    simp [AffineSubspace.mem_mk']
  simpa [hmk] using hmem

/-- Lineality is symmetric under negation. -/
lemma lineality_neg {n : Nat} {f0_plus : (Fin n → Real) → EReal}
    {y : Fin n → Real}
    (hy : y ∈ Function.linealitySpace' f0_plus) :
    (-y) ∈ Function.linealitySpace' f0_plus := by
  dsimp [Function.linealitySpace'] at hy ⊢
  simp [neg_neg, hy]

/-- Lineality directions give additivity of `f0_plus`. -/
lemma lineality_add {n : Nat} {f0_plus : (Fin n → Real) → EReal}
    (hf0_plus : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f0_plus)
    (hpos : PositivelyHomogeneous f0_plus)
    {y1 y2 : Fin n → Real}
    (hy1 : y1 ∈ Function.linealitySpace' f0_plus) :
    f0_plus (y1 + y2) = f0_plus y1 + f0_plus y2 := by
  have hconv : ConvexFunction f0_plus := by
    simpa [ConvexFunction] using hf0_plus.1
  have hnotbot : ∀ x, f0_plus x ≠ (⊥ : EReal) := by
    intro x
    exact hf0_plus.2.2 x (by simp)
  have hsub :
      ∀ x y : Fin n → Real, f0_plus (x + y) ≤ f0_plus x + f0_plus y :=
    subadditive_of_convex_posHom (hpos := hpos) hconv hnotbot
  have hle : f0_plus (y1 + y2) ≤ f0_plus y1 + f0_plus y2 := hsub y1 y2
  have hle' :
      f0_plus y2 ≤ f0_plus (y1 + y2) + f0_plus (-y1) := by
    have h := hsub (y1 + y2) (-y1)
    simpa [add_assoc, add_left_comm, add_comm] using h
  rcases linealitySpace_value_real (f0_plus := f0_plus) hf0_plus hy1 with ⟨v1, hv1⟩
  have hy1_neg : f0_plus (-y1) = (-v1 : EReal) := by
    simpa [Function.linealitySpace', hv1] using hy1
  have hcancel : f0_plus y1 + f0_plus (-y1) = (0 : EReal) := by
    calc
      f0_plus y1 + f0_plus (-y1) = (v1 : EReal) + (-v1 : EReal) := by
        simp [hv1, hy1_neg]
      _ = ((v1 + -v1 : Real) : EReal) := by
        simpa using (EReal.coe_add v1 (-v1)).symm
      _ = 0 := by simp
  have hle'' :
      f0_plus y1 + f0_plus y2 ≤ f0_plus (y1 + y2) := by
    have hle'' :=
      add_le_add_right hle' (f0_plus y1)
    have hle''' :
        f0_plus y1 + f0_plus y2 ≤
          f0_plus y1 + (f0_plus (y1 + y2) + f0_plus (-y1)) := by
      simpa [add_comm] using hle''
    calc
      f0_plus y1 + f0_plus y2
          ≤ f0_plus y1 + (f0_plus (y1 + y2) + f0_plus (-y1)) := hle'''
      _ = f0_plus (y1 + y2) + (f0_plus y1 + f0_plus (-y1)) := by
            simp [add_left_comm]
      _ = f0_plus (y1 + y2) := by simp [hcancel]
  exact le_antisymm hle hle''

/-- If the lineality space is nonempty, then `f0_plus 0 = 0`. -/
lemma lineality_zero_of_nonempty {n : Nat} {f0_plus : (Fin n → Real) → EReal}
    (hf0_plus : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f0_plus)
    (hpos : PositivelyHomogeneous f0_plus)
    (hne : Set.Nonempty (Function.linealitySpace' f0_plus)) :
    f0_plus (0 : Fin n → Real) = 0 := by
  rcases hne with ⟨y, hy⟩
  have hadd := lineality_add (f0_plus := f0_plus) hf0_plus hpos (y2 := -y) hy
  rcases linealitySpace_value_real (f0_plus := f0_plus) hf0_plus hy with ⟨v, hv⟩
  have hyneg_val : f0_plus (-y) = (-v : EReal) := by
    simpa [Function.linealitySpace', hv] using hy
  have hsum : f0_plus y + f0_plus (-y) = (0 : EReal) := by
    calc
      f0_plus y + f0_plus (-y) = (v : EReal) + (-v : EReal) := by
        simp [hv, hyneg_val]
      _ = ((v + -v : Real) : EReal) := by
        simpa using (EReal.coe_add v (-v)).symm
      _ = 0 := by simp
  calc
    f0_plus (0 : Fin n → Real) = f0_plus (y + -y) := by simp
    _ = f0_plus y + f0_plus (-y) := by
          simpa [add_comm] using hadd
    _ = 0 := hsum

/-- The lineality relation extends to the linear span of the lineality space. -/
lemma lineality_span_neg_eq {n : Nat} {f0_plus : (Fin n → Real) → EReal}
    (hf0_plus : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f0_plus)
    (hpos : PositivelyHomogeneous f0_plus)
    (hne : Set.Nonempty (Function.linealitySpace' f0_plus)) :
    ∀ y ∈ Submodule.span Real (Function.linealitySpace' f0_plus),
      f0_plus (-y) = - f0_plus y := by
  classical
  have hzero : f0_plus (0 : Fin n → Real) = 0 :=
    lineality_zero_of_nonempty (f0_plus := f0_plus) hf0_plus hpos hne
  have hnotbot : ∀ z : Fin n → Real, f0_plus z ≠ (⊥ : EReal) := by
    intro z
    exact hf0_plus.2.2 z (by simp)
  intro y hy
  refine Submodule.span_induction (s := Function.linealitySpace' f0_plus)
      (p := fun y _ => f0_plus (-y) = - f0_plus y) ?_ ?_ ?_ ?_ hy
  · intro y hy
    dsimp [Function.linealitySpace'] at hy ⊢
    exact hy
  · simp [hzero]
  · intro x y hx hy hx' hy'
    have hx_line : x ∈ Function.linealitySpace' f0_plus := by
      simpa [Function.linealitySpace'] using hx'
    have hy_line : y ∈ Function.linealitySpace' f0_plus := by
      simpa [Function.linealitySpace'] using hy'
    have hx_neg : (-x) ∈ Function.linealitySpace' f0_plus :=
      lineality_neg (f0_plus := f0_plus) hx_line
    have hy_neg : (-y) ∈ Function.linealitySpace' f0_plus :=
      lineality_neg (f0_plus := f0_plus) hy_line
    have hadd :
        f0_plus (x + y) = f0_plus x + f0_plus y :=
      lineality_add (f0_plus := f0_plus) hf0_plus hpos hx_line
    have hadd_neg :
        f0_plus (-x + -y) = f0_plus (-x) + f0_plus (-y) :=
      lineality_add (f0_plus := f0_plus) hf0_plus hpos hx_neg
    calc
      f0_plus (-(x + y)) = f0_plus (-x + -y) := by
        exact congrArg f0_plus (neg_add x y)
      _ = f0_plus (-x) + f0_plus (-y) := hadd_neg
      _ = -f0_plus x + -f0_plus y := by simp [hx', hy']
      _ = - (f0_plus x + f0_plus y) := by
            have h1 : f0_plus x ≠ ⊥ ∨ f0_plus y ≠ ⊤ := Or.inl (hnotbot x)
            have h2 : f0_plus x ≠ ⊤ ∨ f0_plus y ≠ ⊥ := Or.inr (hnotbot y)
            simpa using (EReal.neg_add (x := f0_plus x) (y := f0_plus y) h1 h2).symm
      _ = - f0_plus (x + y) := by simp [hadd]
  · intro a x hx hxlin
    by_cases ha : a = 0
    · subst ha
      simp [hzero]
    · have ha' : 0 < a ∨ a < 0 := lt_or_gt_of_ne (Ne.symm ha)
      cases ha' with
      | inl ha_pos =>
          have hleft :
              f0_plus (-(a • x)) = (a : EReal) * f0_plus (-x) := by
            simpa [smul_neg] using (hpos (-x) a ha_pos)
          calc
            f0_plus (-(a • x)) = (a : EReal) * f0_plus (-x) := hleft
            _ = - ((a : EReal) * f0_plus x) := by
                  simp [hxlin, mul_neg]
            _ = - f0_plus (a • x) := by
                  simp [hpos x a ha_pos]
      | inr ha_neg =>
          have hs : 0 < -a := by linarith
          have hleft :
              f0_plus (-(a • x)) = (-a : EReal) * f0_plus x := by
            simpa [neg_smul] using (hpos x (-a) hs)
          have hright :
              f0_plus (a • x) = (-a : EReal) * f0_plus (-x) := by
            have hsmul_eq : a • x = (-a) • (-x) := by
              simp [smul_neg, neg_smul]
            have hpos' := hpos (-x) (-a) hs
            -- rewrite the left side to `a • x` using `hsmul_eq`
            have hpos'' := hpos'
            rw [← hsmul_eq] at hpos''
            exact hpos''
          calc
            f0_plus (-(a • x)) = (-a : EReal) * f0_plus x := hleft
            _ = - ((-a : EReal) * f0_plus (-x)) := by
                  simp [hxlin, mul_neg]
            _ = - f0_plus (a • x) := by
                  simp [hright]

/-- On the span of its lineality space, `f0_plus` agrees with a linear functional. -/
lemma linealitySpace_linear_on_span {n : Nat} {f0_plus : (Fin n → Real) → EReal}
    (hf0_plus : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f0_plus)
    (hpos : PositivelyHomogeneous f0_plus)
    (hne : Set.Nonempty (Function.linealitySpace' f0_plus)) :
    ∃ aL :
      (Submodule.span Real (Function.linealitySpace' f0_plus)) →ₗ[Real] Real,
      ∀ y : Submodule.span Real (Function.linealitySpace' f0_plus),
        f0_plus (y : Fin n → Real) = (aL y : EReal) := by
  classical
  let L : Submodule Real (Fin n → Real) :=
    Submodule.span Real (Function.linealitySpace' f0_plus)
  have hneg :
      ∀ y ∈ L, f0_plus (-y) = - f0_plus y :=
    lineality_span_neg_eq (f0_plus := f0_plus) hf0_plus hpos hne
  have hnotbot : ∀ y : Fin n → Real, f0_plus y ≠ (⊥ : EReal) := by
    intro y
    exact hf0_plus.2.2 y (by simp)
  have hnot_top : ∀ y ∈ L, f0_plus y ≠ (⊤ : EReal) := by
    intro y hy htop
    have hyneg : f0_plus (-y) = - f0_plus y := hneg y hy
    have hbot : f0_plus (-y) = (⊥ : EReal) := by
      simpa [htop] using hyneg
    exact (hnotbot (-y)) hbot
  have hadd :
      ∀ y1 y2 : Fin n → Real, y1 ∈ L → y2 ∈ L →
        f0_plus (y1 + y2) = f0_plus y1 + f0_plus y2 := by
    intro y1 y2 hy1 hy2
    have hy1' : y1 ∈ Function.linealitySpace' f0_plus := by
      simpa [Function.linealitySpace'] using hneg y1 hy1
    exact lineality_add (f0_plus := f0_plus) hf0_plus hpos hy1'
  have hsmul :
      ∀ (t : Real) (y : Fin n → Real), y ∈ L →
        f0_plus (t • y) = (t : EReal) * f0_plus y := by
    intro t y hy
    by_cases ht : t = 0
    · subst ht
      simp [lineality_zero_of_nonempty (f0_plus := f0_plus) hf0_plus hpos hne]
    · have ht' : 0 < t ∨ t < 0 := lt_or_gt_of_ne (Ne.symm ht)
      cases ht' with
      | inl ht_pos =>
          exact hpos y t ht_pos
      | inr ht_neg =>
          have hs : 0 < -t := by linarith
          have hpos' := hpos (-y) (-t) hs
          have ht' : t • y = (-t) • (-y) := by
            simp [smul_neg, neg_smul]
          have hpos'' : f0_plus (t • y) = (-t : EReal) * f0_plus (-y) := by
            have hpos'' := hpos'
            rw [← ht'] at hpos''
            exact hpos''
          calc
            f0_plus (t • y) = (-t : EReal) * f0_plus (-y) := hpos''
            _ = (-t : EReal) * (-f0_plus y) := by
                  simp [hneg y hy]
            _ = (t : EReal) * f0_plus y := by
                  simp [mul_neg, neg_mul, neg_neg]
  let aL : L →ₗ[Real] Real :=
    { toFun := fun y => (f0_plus (y : Fin n → Real)).toReal
      map_add' := by
        intro y1 y2
        have hy1 : (y1 : Fin n → Real) ∈ L := y1.property
        have hy2 : (y2 : Fin n → Real) ∈ L := y2.property
        have hsum := hadd (y1 : Fin n → Real) (y2 : Fin n → Real) hy1 hy2
        have htop1 : f0_plus (y1 : Fin n → Real) ≠ (⊤ : EReal) := hnot_top _ hy1
        have htop2 : f0_plus (y2 : Fin n → Real) ≠ (⊤ : EReal) := hnot_top _ hy2
        have hbot1 : f0_plus (y1 : Fin n → Real) ≠ (⊥ : EReal) := hnotbot _
        have hbot2 : f0_plus (y2 : Fin n → Real) ≠ (⊥ : EReal) := hnotbot _
        have hsum' :
            (f0_plus ((y1 : Fin n → Real) + (y2 : Fin n → Real))).toReal =
              (f0_plus (y1 : Fin n → Real) + f0_plus (y2 : Fin n → Real)).toReal := by
          simpa using congrArg EReal.toReal hsum
        calc
          (f0_plus ((y1 : Fin n → Real) + (y2 : Fin n → Real))).toReal
              = (f0_plus (y1 : Fin n → Real) + f0_plus (y2 : Fin n → Real)).toReal := hsum'
          _ = (f0_plus (y1 : Fin n → Real)).toReal +
              (f0_plus (y2 : Fin n → Real)).toReal := by
                exact EReal.toReal_add htop1 hbot1 htop2 hbot2
      map_smul' := by
        intro t y
        have hy : (y : Fin n → Real) ∈ L := y.property
        have hsmul' := hsmul t (y : Fin n → Real) hy
        have hsmul'' :
            (f0_plus (t • (y : Fin n → Real))).toReal =
              EReal.toReal ((t : EReal) * f0_plus (y : Fin n → Real)) := by
          simpa using congrArg EReal.toReal hsmul'
        calc
          (f0_plus (t • (y : Fin n → Real))).toReal
              = EReal.toReal ((t : EReal) * f0_plus (y : Fin n → Real)) := hsmul''
          _ = EReal.toReal (t : EReal) * EReal.toReal (f0_plus (y : Fin n → Real)) := by
                simpa using (EReal.toReal_mul (x := (t : EReal)) (y := f0_plus (y : Fin n → Real)))
          _ = t * (f0_plus (y : Fin n → Real)).toReal := by
                simp [EReal.toReal_coe] }
  refine ⟨aL, ?_⟩
  intro y
  have hy : (y : Fin n → Real) ∈ L := y.property
  have htop : f0_plus (y : Fin n → Real) ≠ (⊤ : EReal) := hnot_top _ hy
  have hbot : f0_plus (y : Fin n → Real) ≠ (⊥ : EReal) := hnotbot _
  simpa [aL] using (EReal.coe_toReal htop hbot).symm

/-- Rank zero should force affine behavior on the affine span of the effective domain. -/
lemma properConvexFunction_rank_zero_affine_on_affineSpan {n : Nat}
    {f : (Fin n → Real) → EReal} {f0_plus : (Fin n → Real) → EReal}
    {dim_f : Nat}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hf0_plus : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f0_plus)
    (hpos : PositivelyHomogeneous f0_plus)
    (hmaj : ∀ x y : Fin n → Real, f (x + y) ≤ f x + f0_plus y)
    (hdim :
      dim_f =
        Module.finrank Real
          (affineSpan Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).direction)
    (hrank : Function.rank f0_plus dim_f = 0) :
    ∃ g : (Fin n → Real) →ᵃ[Real] Real,
      ∀ x ∈
        (affineSpan Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :
          Set (Fin n → Real)),
        f x = (g x : EReal) := by
  classical
  have hne_dom :=
    properConvexFunctionOn_effectiveDomain_nonempty (f := f) hf
  rcases hne_dom with ⟨x0, hx0⟩
  have hspan_le :
      Submodule.span Real (Function.linealitySpace' f0_plus) ≤
        (affineSpan Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).direction := by
    have hmem :
        ∀ y ∈ Function.linealitySpace' f0_plus,
          x0 + y ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
      exact
        lineality_mem_effectiveDomain_of_additive_majorant (f := f) (f0_plus := f0_plus)
          hf0_plus hmaj hx0
    exact lineality_span_le_direction_affineSpan (f := f) (f0_plus := f0_plus) (x0 := x0)
      hx0 hmem
  have hspan_eq :
      Submodule.span Real (Function.linealitySpace' f0_plus) =
        (affineSpan Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).direction :=
    lineality_span_eq_affineSpan_direction_of_rank_zero (f := f) (f0_plus := f0_plus)
      (dim_f := dim_f) hdim hrank hspan_le
  let L : Submodule Real (Fin n → Real) :=
    Submodule.span Real (Function.linealitySpace' f0_plus)
  have hspan_eq' :
      L =
        (affineSpan Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).direction := by
    simpa [L] using hspan_eq
  by_cases hne : Set.Nonempty (Function.linealitySpace' f0_plus)
  · rcases linealitySpace_linear_on_span (f0_plus := f0_plus) hf0_plus hpos hne with ⟨aL, haL⟩
    obtain ⟨a, ha⟩ := LinearMap.exists_extend (p := L) aL
    have hx0_top : f x0 ≠ (⊤ : EReal) :=
      mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := f) hx0
    have hx0_bot : f x0 ≠ (⊥ : EReal) := hf.2.2 x0 (by simp)
    let c : Real := (f x0).toReal - a x0
    let g : (Fin n → Real) →ᵃ[Real] Real :=
      { toFun := fun x => a x + c
        linear := a
        map_vadd' := by
          intro p v
          simp [vadd_eq_add, add_assoc, add_left_comm, add_comm] }
    refine ⟨g, ?_⟩
    intro x hx
    have hx0_aff :
        x0 ∈ affineSpan Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
      subset_affineSpan (k := Real)
        (s := effectiveDomain (Set.univ : Set (Fin n → Real)) f) hx0
    have hx_dir :
        x -ᵥ x0 ∈
          (affineSpan Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).direction :=
      (mem_affineSpan_iff_vsub_mem_direction (x0 := x0) hx0_aff).1 hx
    have hx_L : x -ᵥ x0 ∈ L := by
      simpa [hspan_eq'] using hx_dir
    let yL : L := ⟨x -ᵥ x0, hx_L⟩
    have hy_real : f0_plus (x -ᵥ x0) = (aL yL : EReal) := by
      simpa using haL yL
    have hneg :
        f0_plus (-(x -ᵥ x0)) = - f0_plus (x -ᵥ x0) := by
      have hneg' := lineality_span_neg_eq (f0_plus := f0_plus) hf0_plus hpos hne
      exact hneg' (x -ᵥ x0) (by simpa [L] using hx_L)
    have hle :
        f (x0 + (x -ᵥ x0)) ≤ f x0 + f0_plus (x -ᵥ x0) :=
      hmaj x0 (x -ᵥ x0)
    have hge :
        f x0 ≤ f (x0 + (x -ᵥ x0)) + f0_plus (-(x -ᵥ x0)) := by
      have h := hmaj (x0 + (x -ᵥ x0)) (-(x -ᵥ x0))
      have hsum :
          (x0 + (x -ᵥ x0)) + (-(x -ᵥ x0)) = x0 := by
        calc
          (x0 + (x -ᵥ x0)) + (-(x -ᵥ x0))
              = x0 + ((x -ᵥ x0) + (-(x -ᵥ x0))) := by
                    simp
          _ = x0 + 0 := by simp
          _ = x0 := by simp
      simpa [hsum] using h
    have hge' :
        f x0 ≤ f (x0 + (x -ᵥ x0)) - f0_plus (x -ᵥ x0) := by
      rw [sub_eq_add_neg, ← hneg]
      exact hge
    have hge'' :
        f x0 + f0_plus (x -ᵥ x0) ≤ f (x0 + (x -ᵥ x0)) := by
      have h := add_le_add_left hge' (f0_plus (x -ᵥ x0))
      have hcancel : (-f0_plus (x -ᵥ x0)) + f0_plus (x -ᵥ x0) = (0 : EReal) := by
        calc
          (-f0_plus (x -ᵥ x0)) + f0_plus (x -ᵥ x0)
              = (-(aL yL : EReal)) + (aL yL : EReal) := by
                    rw [hy_real]
          _ = ((-aL yL + aL yL : Real) : EReal) := by
                simpa using (EReal.coe_add (-aL yL) (aL yL)).symm
          _ = 0 := by simp
      rw [sub_eq_add_neg] at h
      rw [add_assoc] at h
      rw [hcancel] at h
      rw [add_zero] at h
      exact h
    have hEq :
        f (x0 + (x -ᵥ x0)) = f x0 + f0_plus (x -ᵥ x0) :=
      le_antisymm hle hge''
    have hx_repr : x0 + (x -ᵥ x0) = x := by
      simp
    have ha_apply : a (yL : Fin n → Real) = aL yL := by
      simpa using congrArg (fun f => f yL) ha
    have hgx : g x = aL yL + (f x0).toReal := by
      have hx_repr' : x = x0 + (x -ᵥ x0) := hx_repr.symm
      calc
        g x = a x + c := rfl
        _ = a (x0 + (x -ᵥ x0)) + c := by
              exact congrArg (fun z => a z + c) hx_repr'
        _ = (a x0 + a (x -ᵥ x0)) + c := by
              simp
        _ = a (x -ᵥ x0) + (f x0).toReal := by
              simp [c, sub_eq_add_neg, add_left_comm, add_comm]
        _ = a (yL : Fin n → Real) + (f x0).toReal := by
              rfl
        _ = aL yL + (f x0).toReal := by
              rw [ha_apply]
    have hx0_coe : ((f x0).toReal : EReal) = f x0 :=
      EReal.coe_toReal hx0_top hx0_bot
    have hfx : f x = f x0 + f0_plus (x -ᵥ x0) := by
      simpa [hx_repr] using hEq
    calc
      f x = f x0 + f0_plus (x -ᵥ x0) := hfx
      _ = f x0 + (aL yL : EReal) := by
            rw [hy_real]
      _ = ((f x0).toReal : EReal) + (aL yL : EReal) := by
            simp [hx0_coe]
      _ = ((aL yL + (f x0).toReal : Real) : EReal) := by
            simp [add_comm]
      _ = (g x : EReal) := by
            simp [hgx]
  · have hspan_bot : L = ⊥ := by
      have hzero : ∀ y ∈ Function.linealitySpace' f0_plus, (y : Fin n → Real) = 0 := by
        intro y hy
        exfalso
        exact hne ⟨y, hy⟩
      simpa [L] using
        (Submodule.span_eq_bot (R := Real) (M := Fin n → Real)
            (s := Function.linealitySpace' f0_plus)).2 hzero
    have hdir_bot :
        (affineSpan Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).direction = ⊥ := by
      simpa [hspan_eq'] using hspan_bot
    have hx0_top : f x0 ≠ (⊤ : EReal) :=
      mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := f) hx0
    have hx0_bot : f x0 ≠ (⊥ : EReal) := hf.2.2 x0 (by simp)
    let g : (Fin n → Real) →ᵃ[Real] Real :=
      AffineMap.const Real (Fin n → Real) (f x0).toReal
    refine ⟨g, ?_⟩
    intro x hx
    have hx0_aff :
        x0 ∈ affineSpan Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
      subset_affineSpan (k := Real)
        (s := effectiveDomain (Set.univ : Set (Fin n → Real)) f) hx0
    have hx_dir :
        x -ᵥ x0 ∈
          (affineSpan Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).direction :=
      (mem_affineSpan_iff_vsub_mem_direction (x0 := x0) hx0_aff).1 hx
    have hx0' : x -ᵥ x0 = 0 := by
      have hx_dir' : x -ᵥ x0 ∈ (⊥ : Submodule Real (Fin n → Real)) := by
        simpa [hdir_bot] using hx_dir
      simpa using hx_dir'
    have hx_eq : x = x0 := by
      exact (vsub_eq_zero_iff_eq.mp hx0')
    have hx0_coe : ((f x0).toReal : EReal) = f x0 :=
      EReal.coe_toReal hx0_top hx0_bot
    simp [g, hx_eq, hx0_coe]

/-- Theorem 8.9.3. The proper convex functions of rank `0` are the partial affine functions,
i.e. the functions which agree with an affine function along a certain affine set and are
`⊤` elsewhere. -/
theorem properConvexFunction_rank_zero_partialAffine {n : Nat}
    {f : (Fin n → Real) → EReal} {f0_plus : (Fin n → Real) → EReal}
    {dim_f : Nat}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hf0_plus : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f0_plus)
    (hpos : PositivelyHomogeneous f0_plus)
    (hmaj : ∀ x y : Fin n → Real, f (x + y) ≤ f x + f0_plus y)
    (hdim :
      dim_f =
        Module.finrank Real
          (affineSpan Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).direction)
    (hrank : Function.rank f0_plus dim_f = 0) :
    ∃ (S : AffineSubspace Real (Fin n → Real)) (g : (Fin n → Real) →ᵃ[Real] Real),
      (∀ x ∈ (S : Set (Fin n → Real)), f x = (g x : EReal)) ∧
      (∀ x ∉ (S : Set (Fin n → Real)), f x = (⊤ : EReal)) := by
  classical
  let S : AffineSubspace Real (Fin n → Real) :=
    affineSpan Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f)
  have hAffine :
      ∃ g : (Fin n → Real) →ᵃ[Real] Real,
        ∀ x ∈ (S : Set (Fin n → Real)), f x = (g x : EReal) := by
    simpa [S] using
      (properConvexFunction_rank_zero_affine_on_affineSpan (f := f) (f0_plus := f0_plus)
        (dim_f := dim_f) hf hf0_plus hpos hmaj hdim hrank)
  rcases hAffine with ⟨g, hg⟩
  refine ⟨S, g, ?_, ?_⟩
  · exact hg
  · intro x hx
    have hx' :
        x ∉ effectiveDomain (Set.univ : Set (Fin n → Real)) f :=
      not_mem_effectiveDomain_of_not_mem_affineSpan (f := f) (x := x) (by simpa [S] using hx)
    exact not_mem_effectiveDomain_univ_imp_eq_top (f := f) hx'

/-- Rank equals dimension iff the lineality is zero, provided the lineality is bounded. -/
lemma rank_eq_dim_iff_lineality_eq_zero {n : Nat}
    {f0_plus : (Fin n → Real) → EReal} {dim_f : Nat}
    (hle : Function.lineality f0_plus ≤ dim_f) :
    Function.rank f0_plus dim_f = dim_f ↔ Function.lineality f0_plus = 0 := by
  constructor
  · intro h
    have hsub : dim_f - Function.lineality f0_plus = dim_f := by
      simpa [Function.rank] using h
    have h' :
        dim_f =
          dim_f + Function.lineality f0_plus :=
      (Nat.sub_eq_iff_eq_add (a := dim_f) (b := Function.lineality f0_plus) (c := dim_f)
          hle).1 hsub
    have h'' :
        dim_f + 0 =
          dim_f + Function.lineality f0_plus := by
      simpa using h'
    have hline : 0 = Function.lineality f0_plus :=
      Nat.add_left_cancel h''
    simpa using hline.symm
  · intro hline
    simp [Function.rank, hline]

/-- Lineality zero iff there is no nonzero affine direction. -/
lemma lineality_eq_zero_iff_no_nonzero_affineDirection {n : Nat}
    {f0_plus : (Fin n → Real) → EReal} :
    Function.lineality f0_plus = 0 ↔
      ¬ ∃ y : Fin n → Real, y ≠ 0 ∧ Function.IsAffineDirection f0_plus y := by
  constructor
  · intro hfin
    have hspan_eq :
        Submodule.span Real (Function.linealitySpace' f0_plus) = ⊥ :=
      (Submodule.finrank_eq_zero
          (S := Submodule.span Real (Function.linealitySpace' f0_plus))).1
        (by simpa [Function.lineality] using hfin)
    intro hy
    rcases hy with ⟨y, hyne, hy⟩
    have hyspan :
        y ∈ Submodule.span Real (Function.linealitySpace' f0_plus) :=
      Submodule.subset_span hy
    have hy0 : y = 0 := by
      have : y ∈ (⊥ : Submodule Real (Fin n → Real)) := by
        simpa [hspan_eq] using hyspan
      simpa using this
    exact hyne hy0
  · intro hno
    have hsubset :
        Function.linealitySpace' f0_plus ⊆ ({0} : Set (Fin n → Real)) := by
      intro y hy
      by_contra hyne
      have hyne' : y ≠ 0 := by
        simpa using hyne
      exact hno ⟨y, hyne', hy⟩
    have hspan_eq :
        Submodule.span Real (Function.linealitySpace' f0_plus) = ⊥ :=
      (Submodule.span_eq_bot).2 hsubset
    have hfin :
        Module.finrank Real
            (Submodule.span Real (Function.linealitySpace' f0_plus)) = 0 :=
      (Submodule.finrank_eq_zero
          (S := Submodule.span Real (Function.linealitySpace' f0_plus))).2 hspan_eq
    simpa [Function.lineality] using hfin

/-- Theorem 8.9.4. A closed proper convex function `f` has `rank f = dim f` if and only if
it is not affine along any line in `dom f`. -/
theorem closedProperConvexFunction_rank_eq_dim_iff_not_affineLine {n : Nat}
    {f : (Fin n → Real) → EReal} {f0_plus : (Fin n → Real) → EReal}
    {dim_f : Nat}
    (_hfclosed :
      ClosedConvexFunction
        (fun x => f ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x)))
    (_hfproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hle : Function.lineality f0_plus ≤ dim_f) :
    Function.rank f0_plus dim_f = dim_f ↔
      ¬ ∃ y : Fin n → Real, y ≠ 0 ∧ Function.IsAffineDirection f0_plus y := by
  have hrank :
      Function.rank f0_plus dim_f = dim_f ↔ Function.lineality f0_plus = 0 :=
    rank_eq_dim_iff_lineality_eq_zero (f0_plus := f0_plus) (dim_f := dim_f) hle
  have hline :
      Function.lineality f0_plus = 0 ↔
        ¬ ∃ y : Fin n → Real, y ≠ 0 ∧ Function.IsAffineDirection f0_plus y :=
    lineality_eq_zero_iff_no_nonzero_affineDirection (f0_plus := f0_plus)
  exact hrank.trans hline

/-- The lineality space of an indicator function consists of points in the set and its negation. -/
lemma indicatorFunction_linealitySpace'_iff {n : Nat} {S : Set (Fin n → Real)}
    {y : Fin n → Real} :
    y ∈ Function.linealitySpace' (indicatorFunction S) ↔ y ∈ S ∧ -y ∈ S := by
  classical
  constructor
  · intro hy
    have hyS : y ∈ S := by
      by_contra hyS
      have hy' : indicatorFunction S (-y) = (⊥ : EReal) := by
        simpa [Function.linealitySpace', indicatorFunction, hyS] using hy
      have hne : indicatorFunction S (-y) ≠ (⊥ : EReal) := by
        by_cases hneg : -y ∈ S
        · simp [indicatorFunction, hneg]
        · simp [indicatorFunction, hneg]
      exact (hne hy').elim
    have hneg : -y ∈ S := by
      have hy' : indicatorFunction S (-y) = (0 : EReal) := by
        simpa [Function.linealitySpace', indicatorFunction, hyS] using hy
      by_contra hneg
      have hne : indicatorFunction S (-y) ≠ (0 : EReal) := by
        simp [indicatorFunction, hneg]
      exact (hne hy').elim
    exact ⟨hyS, hneg⟩
  · intro hy
    rcases hy with ⟨hy, hneg⟩
    simp [Function.linealitySpace', indicatorFunction, hy, hneg]

/-- If the recession cone equals the set, then the lineality space is `C ∩ -C`. -/
lemma Set.linealitySpace_eq_inter_of_recessionCone_eq {n : Nat}
    {C : Set (EuclideanSpace Real (Fin n))} (hcone : Set.recessionCone C = C) :
    Set.linealitySpace C = C ∩ -C := by
  simp [Set.linealitySpace, hcone, Set.inter_comm]

/-- The lineality space of the indicator function of the image of `C` is the image of `C ∩ -C`. -/
lemma linealitySpace_indicatorFunction_image_eq {n : Nat}
    {C : Set (EuclideanSpace Real (Fin n))} :
    Function.linealitySpace'
        (indicatorFunction (Set.image (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) C)) =
      Set.image (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) (C ∩ -C) := by
  classical
  let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
  have h :
      Function.linealitySpace' (indicatorFunction (Set.image e C)) =
        Set.image e (C ∩ -C) := by
    ext y
    constructor
    · intro hy
      have hy' : y ∈ Set.image e C ∧ -y ∈ Set.image e C := by
        simpa using
          (indicatorFunction_linealitySpace'_iff (S := Set.image e C) (y := y)).1 hy
      rcases hy' with ⟨hyC, hynegC⟩
      rcases hyC with ⟨x, hx, rfl⟩
      rcases hynegC with ⟨x', hx', hx'eq⟩
      have hxneg : -x ∈ C := by
        have hx'' : x' = -x := by
          apply e.injective
          calc
            e x' = -e x := hx'eq
            _ = e (-x) := by
              simp
        simpa [hx''] using hx'
      refine ⟨x, ?_, rfl⟩
      exact ⟨hx, by simpa using hxneg⟩
    · intro hy
      rcases hy with ⟨x, hx, rfl⟩
      rcases hx with ⟨hxC, hxneg⟩
      have hxneg' : -x ∈ C := by
        simpa using hxneg
      have hyC : e x ∈ Set.image e C := ⟨x, hxC, rfl⟩
      have hynegC : -e x ∈ Set.image e C := by
        refine ⟨-x, hxneg', ?_⟩
        simp
      exact
        (indicatorFunction_linealitySpace'_iff (S := Set.image e C) (y := e x)).2
          ⟨hyC, by simpa using hynegC⟩
  simpa [e] using h

/-- Finrank of the span is preserved under a linear equivalence. -/
lemma finrank_span_image_linearEquiv {V W : Type*}
    [AddCommGroup V] [Module Real V] [AddCommGroup W] [Module Real W]
    [FiniteDimensional Real V] [FiniteDimensional Real W]
    (e : V ≃ₗ[Real] W) (S : Set V) :
    Module.finrank Real (Submodule.span Real (Set.image e S)) =
      Module.finrank Real (Submodule.span Real S) := by
  have hmap :
      (Submodule.span Real S).map (e : V →ₗ[Real] W) =
        Submodule.span Real (Set.image e S) := by
    simpa using (LinearMap.map_span (f := (e : V →ₗ[Real] W)) (s := S))
  calc
    Module.finrank Real (Submodule.span Real (Set.image e S)) =
        Module.finrank Real ((Submodule.span Real S).map (e : V →ₗ[Real] W)) := by
          rw [← hmap]
    _ = Module.finrank Real (Submodule.span Real S) := by
      simpa using (LinearEquiv.finrank_map_eq (f := e) (p := Submodule.span Real S))

/-- Theorem 8.9.5. The rank of a convex set `C` equals the rank of its indicator function. -/
theorem convexSet_rank_eq_indicatorFunction_rank {n : Nat}
    {C : Set (EuclideanSpace Real (Fin n))} (_hC : Convex Real C)
    (hcone : Set.recessionCone C = C) :
    Set.rank C =
      Function.rank
        (fun x =>
          indicatorFunction
              (C := Set.image (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) C)
              x)
        (Module.finrank Real (affineSpan Real C).direction) := by
  classical
  let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
  have hline_set :
      (-Set.recessionCone C) ∩ Set.recessionCone C = C ∩ -C := by
    simpa [Set.linealitySpace] using
      (Set.linealitySpace_eq_inter_of_recessionCone_eq (C := C) hcone)
  have hline_fun :
      Function.linealitySpace' (indicatorFunction (Set.image e C)) =
        Set.image e (C ∩ -C) := by
    simpa using (linealitySpace_indicatorFunction_image_eq (C := C))
  have hlineality :
      Function.lineality (indicatorFunction (Set.image e C)) =
        Module.finrank Real
          (Submodule.span Real ((-Set.recessionCone C) ∩ Set.recessionCone C)) := by
    calc
      Function.lineality (indicatorFunction (Set.image e C)) =
          Module.finrank Real
            (Submodule.span Real
              (Function.linealitySpace' (indicatorFunction (Set.image e C)))) := by
        rfl
      _ = Module.finrank Real (Submodule.span Real (Set.image e (C ∩ -C))) := by
        exact
          congrArg (fun s => Module.finrank Real (Submodule.span Real s)) hline_fun
      _ = Module.finrank Real (Submodule.span Real (C ∩ -C)) := by
        simpa using
          (finrank_span_image_linearEquiv
            (V := EuclideanSpace Real (Fin n)) (W := Fin n → Real)
            (e := e) (S := C ∩ -C))
      _ =
          Module.finrank Real
            (Submodule.span Real ((-Set.recessionCone C) ∩ Set.recessionCone C)) := by
        rw [hline_set]
  have hlineality' :
      Function.lineality
          (fun x =>
            indicatorFunction
                (C := Set.image (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) C)
                x) =
        Module.finrank Real
          (Submodule.span Real ((-Set.recessionCone C) ∩ Set.recessionCone C)) := by
    simpa [e] using hlineality
  simp [Set.rank, Function.rank, hlineality']

end Section09
end Chap02
