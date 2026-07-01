/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Siyuan Shao, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section13_part7

open scoped Pointwise

section Chap03
section Section13

/-- Support-function characterization of `(0 : ℝ^n) ∈ ri C` for convex nonempty `C`. -/
lemma section13_zero_mem_intrinsicInterior_iff_supportFunctionEReal {n : Nat}
    (C : Set (Fin n → Real)) (hCconv : Convex ℝ C) (hCne : C.Nonempty) :
    (0 : Fin n → Real) ∈ intrinsicInterior ℝ C ↔
      ∀ y : Fin n → Real,
        (¬ (-(supportFunctionEReal C (-y)) = supportFunctionEReal C y ∧ supportFunctionEReal C y = 0)) →
          supportFunctionEReal C y > (0 : EReal) := by
  classical
  -- Helper: if `0 ∈ C`, then `0 ≤ supportFunctionEReal C y`.
  have nonneg_of_mem (h0C : (0 : Fin n → Real) ∈ C) (y : Fin n → Real) :
      (0 : EReal) ≤ supportFunctionEReal C y := by
    unfold supportFunctionEReal
    refine le_sSup ?_
    exact ⟨0, h0C, by simp [dotProduct]⟩
  constructor
  · intro h0ri y hy
    have h0C : (0 : Fin n → Real) ∈ C := (intrinsicInterior_subset (𝕜 := ℝ) (s := C)) h0ri
    have hnonneg : (0 : EReal) ≤ supportFunctionEReal C y := nonneg_of_mem h0C y
    -- If `supportFunctionEReal C y = 0`, then `supportFunctionEReal C (-y) = 0`; otherwise we get a
    -- nontrivial supporting hyperplane through `0`, contradicting `0 ∈ ri C`.
    have hy_ne0 : supportFunctionEReal C y ≠ 0 := by
      intro hy0
      have hyneg0 : supportFunctionEReal C (-y) = 0 := by
        by_contra hyneg_ne0
        have hyneg_pos : (0 : EReal) < supportFunctionEReal C (-y) :=
          lt_of_le_of_ne (nonneg_of_mem h0C (-y)) (Ne.symm hyneg_ne0)
        have hy_vec_ne0 : y ≠ 0 := by
          intro hyz
          subst hyz
          have : supportFunctionEReal C 0 = (0 : EReal) := by
            unfold supportFunctionEReal
            refine le_antisymm ?_ ?_
            · refine sSup_le ?_
              rintro _ ⟨x, _hxC, rfl⟩
              simp [dotProduct]
            · rcases hCne with ⟨x0, hx0C⟩
              refine le_sSup ?_
              exact ⟨x0, hx0C, by simp [dotProduct]⟩
          have hyneg_pos' := hyneg_pos
          simp [this] at hyneg_pos'
        -- Obtain `x0 ∈ C` with `0 < ⟪x0, -y⟫`, hence `⟪x0, y⟫ < 0`.
        have hx0 : ∃ x0, x0 ∈ C ∧ (0 : Real) < dotProduct x0 (-y) := by
          classical
          by_contra h
          push_neg at h
          have : supportFunctionEReal C (-y) ≤ (0 : EReal) :=
            (section13_supportFunctionEReal_le_coe_iff (n := n) (C := C) (y := -y) (μ := 0)).2 h
          exact (not_lt_of_ge this) hyneg_pos
        rcases hx0 with ⟨x0, hx0C, hx0pos⟩
        have hx0lt : dotProduct x0 y < 0 := by
          have : dotProduct x0 (-y) = -dotProduct x0 y := by simp [dotProduct_neg]
          have : 0 < -dotProduct x0 y := by simpa [this] using hx0pos
          exact neg_pos.1 this
        -- Build a nontrivial supporting hyperplane through `0` with normal `y`.
        let H : Set (Fin n → Real) := {x : Fin n → Real | dotProduct x y = (0 : Real)}
        have hC_le : ∀ x, x ∈ C → dotProduct x y ≤ (0 : Real) := by
          have hsupp_le : supportFunctionEReal C y ≤ (0 : EReal) := by simp [hy0]
          exact
            (section13_supportFunctionEReal_le_coe_iff (n := n) (C := C) (y := y) (μ := 0)).1 hsupp_le
        have hHsupport : IsSupportingHyperplane n C H := by
          refine ⟨y, 0, hy_vec_ne0, rfl, hC_le, ?_⟩
          refine ⟨0, h0C, by simp [dotProduct]⟩
        have hCnot : ¬ C ⊆ H := by
          intro hsub
          have : x0 ∈ H := hsub hx0C
          have : dotProduct x0 y = 0 := by simpa using this
          exact (ne_of_lt hx0lt) this
        have hnontriv : IsNontrivialSupportingHyperplane n C H := ⟨hHsupport, hCnot⟩
        -- Apply Theorem 11.6 with `D = {0}`.
        have hsubset : ({0} : Set (Fin n → Real)) ⊆ C := by
          intro x hx
          have : x = 0 := by simpa [Set.mem_singleton_iff] using hx
          simpa [this] using h0C
        have hiff :=
          exists_nontrivialSupportingHyperplane_containing_iff_disjoint_intrinsicInterior (n := n)
            (C := C) (D := ({0} : Set (Fin n → Real))) hCconv (Set.singleton_nonempty 0)
            (convex_singleton 0) hsubset
        have hdisj : Disjoint ({0} : Set (Fin n → Real)) (intrinsicInterior ℝ C) :=
          hiff.1
            ⟨H, hnontriv, by
              intro x hx
              have hx0 : x = 0 := by simpa [Set.mem_singleton_iff] using hx
              subst hx0
              simp [H, dotProduct]⟩
        have : (0 : Fin n → Real) ∉ intrinsicInterior ℝ C := by
          exact (Set.disjoint_singleton_left).1 hdisj
        exact (this h0ri).elim
      have : (-(supportFunctionEReal C (-y)) = supportFunctionEReal C y ∧ supportFunctionEReal C y = 0) := by
        simp [hy0, hyneg0]
      exact (hy this).elim
    exact lt_of_le_of_ne hnonneg hy_ne0.symm
  · intro hcond
    -- Contrapositive: if `0 ∉ ri C`, then the RHS fails for an explicit normal.
    by_contra h0ri
    by_cases h0C : (0 : Fin n → Real) ∈ C
    · -- Use Theorem 11.6 to obtain a nontrivial supporting hyperplane through `0`.
      have h0not : (0 : Fin n → Real) ∉ intrinsicInterior ℝ C := h0ri
      have hdisj :
          Disjoint ({0} : Set (Fin n → Real)) (intrinsicInterior ℝ C) := by
        exact Set.disjoint_singleton_left.2 h0not
      have hsubset : ({0} : Set (Fin n → Real)) ⊆ C := by
        intro x hx
        have : x = 0 := by simpa [Set.mem_singleton_iff] using hx
        simpa [this] using h0C
      have hiff :=
        exists_nontrivialSupportingHyperplane_containing_iff_disjoint_intrinsicInterior (n := n) (C := C)
          (D := ({0} : Set (Fin n → Real))) hCconv (Set.singleton_nonempty 0) (convex_singleton 0) hsubset
      rcases (hiff.2 hdisj) with ⟨H, hHnontriv, hDH⟩
      rcases hHnontriv with ⟨hHsupport, hCnotH⟩
      rcases hHsupport with ⟨b, β, hb0, hHdef, hC_le, _hx_touch⟩
      have h0H : (0 : Fin n → Real) ∈ H := hDH (by simp)
      have hβ : β = 0 := by
        have : dotProduct (0 : Fin n → Real) b = β := by simpa [hHdef] using h0H
        simpa [dotProduct] using this.symm
      have hsupp_le : supportFunctionEReal C b ≤ (0 : EReal) := by
        refine (section13_supportFunctionEReal_le_coe_iff (n := n) (C := C) (y := b) (μ := 0)).2 ?_
        intro x hxC
        have : dotProduct x b ≤ β := hC_le x hxC
        simpa [hβ] using this
      have hsupp_ge : (0 : EReal) ≤ supportFunctionEReal C b := nonneg_of_mem h0C b
      have hsupp0 : supportFunctionEReal C b = 0 := le_antisymm hsupp_le hsupp_ge
      -- Since `C` is not contained in `H`, pick `x0 ∈ C` with `⟪x0, b⟫ < 0`, hence `σ(-b) > 0`.
      rcases Set.not_subset.1 hCnotH with ⟨x0, hx0C, hx0notH⟩
      have hx0lt : dotProduct x0 b < 0 := by
        have hx0le : dotProduct x0 b ≤ β := hC_le x0 hx0C
        have hx0ne : dotProduct x0 b ≠ β := by
          intro hEq
          have : x0 ∈ H := by simp [hHdef, hEq]
          exact hx0notH this
        have : dotProduct x0 b < β := lt_of_le_of_ne hx0le hx0ne
        simpa [hβ] using this
      have hsupp_neg_pos : supportFunctionEReal C (-b) > (0 : EReal) := by
        have hx0pos : (0 : Real) < dotProduct x0 (-b) := by
          simpa [dotProduct_neg] using (neg_pos.2 hx0lt)
        have hle : ((dotProduct x0 (-b) : Real) : EReal) ≤ supportFunctionEReal C (-b) := by
          unfold supportFunctionEReal
          refine le_sSup ?_
          exact ⟨x0, hx0C, rfl⟩
        have : (0 : EReal) < ((dotProduct x0 (-b) : Real) : EReal) :=
          EReal.coe_lt_coe_iff.2 hx0pos
        exact lt_of_lt_of_le this hle
      have hfail :
          ¬ (-(supportFunctionEReal C (-b)) = supportFunctionEReal C b ∧ supportFunctionEReal C b = 0) := by
        intro hconj
        have : supportFunctionEReal C (-b) = 0 := by
          have : -(supportFunctionEReal C (-b)) = 0 := by simpa [hsupp0] using hconj.1
          have : supportFunctionEReal C (-b) = -(0 : EReal) := (neg_eq_iff_eq_neg).1 this
          simpa using this
        exact (not_lt_of_ge (le_of_eq this)) hsupp_neg_pos
      have : supportFunctionEReal C b > (0 : EReal) := hcond b hfail
      have this' := this
      simp [hsupp0] at this'
    · -- If `0 ∉ C`, separate `{0}` from `C` and contradict the RHS.
      rcases
          cor11_5_2_exists_hyperplaneSeparatesProperly_point (n := n) (C := C)
            (a := (0 : Fin n → Real)) hCne hCconv h0C with
        ⟨H, hsep⟩
      rcases hyperplaneSeparatesProperly_oriented n H ({0} : Set (Fin n → Real)) C hsep with
        ⟨b, β, hb0, hHdef, h0_ge, hC_le, hnot⟩
      have hβle : β ≤ 0 := by
        have := h0_ge (0 : Fin n → Real) (by simp)
        simpa [dotProduct] using this
      have hsupp_le0 : supportFunctionEReal C b ≤ (0 : EReal) := by
        have : supportFunctionEReal C b ≤ (β : EReal) := by
          refine (section13_supportFunctionEReal_le_coe_iff (n := n) (C := C) (y := b) (μ := β)).2 ?_
          intro x hxC
          exact hC_le x hxC
        exact this.trans (by simpa using (EReal.coe_le_coe_iff.2 hβle))
      have hfail : ¬ (-(supportFunctionEReal C (-b)) = supportFunctionEReal C b ∧ supportFunctionEReal C b = 0) := by
        -- If `β < 0`, then `supportFunctionEReal C b < 0`, so the conjunction fails.
        by_cases hβ0 : β = 0
        · -- If `β = 0`, then `{0} ⊆ H`, hence `C ⊄ H`; pick `x0 ∈ C` with `⟪x0,b⟫ < 0`, so `σ(-b) > 0`.
          subst hβ0
          have h0sub : ({0} : Set (Fin n → Real)) ⊆ H := by
            intro x hx
            have hx0 : x = 0 := by simpa [Set.mem_singleton_iff] using hx
            subst hx0
            simp [hHdef, dotProduct]
          have hCnotH : ¬ C ⊆ H := by
            intro hCH
            exact hnot ⟨h0sub, hCH⟩
          rcases Set.not_subset.1 hCnotH with ⟨x0, hx0C, hx0notH⟩
          have hx0lt : dotProduct x0 b < 0 := by
            have hx0le : dotProduct x0 b ≤ (0 : Real) := by simpa using (hC_le x0 hx0C)
            have hx0ne : dotProduct x0 b ≠ (0 : Real) := by
              intro hEq
              have : x0 ∈ H := by simp [hHdef, hEq]
              exact hx0notH this
            exact lt_of_le_of_ne hx0le hx0ne
          have hsupp_neg_pos : supportFunctionEReal C (-b) > (0 : EReal) := by
            have hx0pos : (0 : Real) < dotProduct x0 (-b) := by
              simpa [dotProduct_neg] using (neg_pos.2 hx0lt)
            have hle : ((dotProduct x0 (-b) : Real) : EReal) ≤ supportFunctionEReal C (-b) := by
              unfold supportFunctionEReal
              refine le_sSup ?_
              exact ⟨x0, hx0C, rfl⟩
            have : (0 : EReal) < ((dotProduct x0 (-b) : Real) : EReal) :=
              EReal.coe_lt_coe_iff.2 hx0pos
            exact lt_of_lt_of_le this hle
          intro hconj
          have hneg0 : supportFunctionEReal C (-b) = 0 := by
            have : -(supportFunctionEReal C (-b)) = 0 := by simpa [hconj.2] using hconj.1
            have : supportFunctionEReal C (-b) = -(0 : EReal) := (neg_eq_iff_eq_neg).1 this
            simpa using this
          exact (not_lt_of_ge (le_of_eq hneg0)) hsupp_neg_pos
        · -- If `β ≠ 0`, then `β < 0`, hence `supportFunctionEReal C b < 0`, contradicting `supportFunctionEReal C b = 0`.
          have hβneg : β < 0 := lt_of_le_of_ne hβle hβ0
          have hsupp_leβ : supportFunctionEReal C b ≤ (β : EReal) := by
            refine (section13_supportFunctionEReal_le_coe_iff (n := n) (C := C) (y := b) (μ := β)).2 ?_
            intro x hxC
            exact hC_le x hxC
          have hsupp_lt0 : supportFunctionEReal C b < (0 : EReal) :=
            lt_of_le_of_lt hsupp_leβ (EReal.coe_lt_coe_iff.2 hβneg)
          intro hconj
          exact (ne_of_lt hsupp_lt0) hconj.2
      have : supportFunctionEReal C b > (0 : EReal) := hcond b hfail
      exact (not_lt_of_ge hsupp_le0) this

/-- Support-function characterization of `0 ∈ affineSpan C`. -/
lemma section13_zero_mem_affineSpan_iff_supportFunctionEReal {n : Nat}
    (C : Set (Fin n → Real)) (hCne : C.Nonempty) :
    (0 : Fin n → Real) ∈ (affineSpan ℝ C : Set (Fin n → Real)) ↔
      ∀ y : Fin n → Real,
        (-(supportFunctionEReal C (-y)) = supportFunctionEReal C y) →
          supportFunctionEReal C y = 0 := by
  classical
  constructor
  · intro h0span y hsymm
    have hy_ne_top : supportFunctionEReal C y ≠ ⊤ := by
      intro htop
      have : -supportFunctionEReal C (-y) = (⊤ : EReal) := by simpa [htop] using hsymm
      have hbot : supportFunctionEReal C (-y) = (⊥ : EReal) := by
        have h' := congrArg (fun z : EReal => -z) this
        simpa using h'
      exact
        section13_supportFunctionEReal_ne_bot_of_nonempty (n := n) (C := C) hCne (-y) hbot
    have hy_ne_bot : supportFunctionEReal C y ≠ ⊥ :=
      section13_supportFunctionEReal_ne_bot_of_nonempty (n := n) (C := C) hCne y
    set μ : Real := (supportFunctionEReal C y).toReal
    have hμ : (μ : EReal) = supportFunctionEReal C y := by
      simpa [μ] using (EReal.coe_toReal (x := supportFunctionEReal C y) hy_ne_top hy_ne_bot)
    have hsupp_le : ∀ x ∈ C, dotProduct x y ≤ μ := by
      have hsupp_leμ : supportFunctionEReal C y ≤ (μ : EReal) := by
        simp [hμ]
      exact
        (section13_supportFunctionEReal_le_coe_iff (n := n) (C := C) (y := y) (μ := μ)).1 hsupp_leμ
    have hsupp_ge : ∀ x ∈ C, μ ≤ dotProduct x y := by
      have hneg :
          supportFunctionEReal C (-y) = ((-μ : Real) : EReal) := by
        have : supportFunctionEReal C (-y) = -supportFunctionEReal C y := by
          have := congrArg (fun z : EReal => -z) hsymm
          simpa [neg_neg] using this
        simp [this, hμ]
      intro x hx
      have hsupp_neg_le : dotProduct x (-y) ≤ -μ := by
        have hsupp_le_neg : supportFunctionEReal C (-y) ≤ ((-μ : Real) : EReal) := by
          simp [hneg]
        have :=
          (section13_supportFunctionEReal_le_coe_iff (n := n) (C := C) (y := -y) (μ := -μ)).1
            hsupp_le_neg x hx
        simpa using this
      have : -dotProduct x y ≤ -μ := by simpa [dotProduct_neg] using hsupp_neg_le
      exact (neg_le_neg_iff).1 this
    have hdot_eq : ∀ x ∈ C, dotProduct x y = μ := by
      intro x hx
      exact le_antisymm (hsupp_le x hx) (hsupp_ge x hx)
    -- The level set `{x | ⟪x,y⟫ = μ}` is an affine subspace containing `C`, hence contains `affineSpan C`.
    let Hμ : AffineSubspace ℝ (Fin n → Real) :=
      { carrier := {x : Fin n → Real | dotProduct x y = μ}
        smul_vsub_vadd_mem := by
          intro c p1 p2 p3 hp1 hp2 hp3
          have hp1' : dotProduct p1 y = μ := by simpa using hp1
          have hp2' : dotProduct p2 y = μ := by simpa using hp2
          have hp3' : dotProduct p3 y = μ := by simpa using hp3
          have hp12 : dotProduct (p1 - p2) y = 0 := by
            have : dotProduct (p1 - p2) y = dotProduct p1 y - dotProduct p2 y := by
              simp
            simp [this, hp1', hp2']
          have : dotProduct (c • (p1 - p2) + p3) y = μ := by
            simp [add_dotProduct, smul_dotProduct, hp12, hp3']
          simpa [vsub_eq_sub, vadd_eq_add] using this }
    have hC_Hμ : C ⊆ (Hμ : Set (Fin n → Real)) := by
      intro x hx
      exact hdot_eq x hx
    have hspan_le : affineSpan ℝ C ≤ Hμ :=
      (affineSpan_le (k := ℝ) (s := C) (Q := Hμ)).2 hC_Hμ
    have hμ0 : dotProduct (0 : Fin n → Real) y = μ := hspan_le h0span
    have hμ0' : μ = 0 := by simpa [dotProduct] using hμ0.symm
    simpa [hμ0'] using hμ.symm
  · intro hsymm0
    by_contra h0not
    rcases hCne with ⟨x0, hx0C⟩
    set A : AffineSubspace ℝ (Fin n → Real) := affineSpan ℝ C
    have hx0A : x0 ∈ (A : Set (Fin n → Real)) := subset_affineSpan (k := ℝ) (s := C) hx0C
    have hx0_not_dir : x0 ∉ A.direction := by
      intro hx0dir
      have h0A : (0 : Fin n → Real) ∈ (A : Set (Fin n → Real)) := by
        have hx0dir' : (-x0 : Fin n → Real) ∈ A.direction := A.direction.neg_mem hx0dir
        have : (-x0) +ᵥ x0 ∈ A := AffineSubspace.vadd_mem_of_mem_direction (s := A) hx0dir' hx0A
        simpa [vadd_eq_add] using this
      exact h0not h0A
    obtain ⟨f, hfx0, hdir⟩ := Submodule.exists_le_ker_of_notMem (p := A.direction) hx0_not_dir
    have hf0 : (f : Module.Dual ℝ (Fin n → Real)) ≠ 0 := by
      intro hf
      have : f x0 = 0 := by simp [hf]
      exact hfx0 this
    rcases dual_eq_dotProductLinear n (f := f) hf0 with ⟨b, hb0, hfb⟩
    have hAconst :
        (A : Set (Fin n → Real)) ⊆ {x : Fin n → Real | f x = f x0} :=
      affineSubspace_subset_setOf_apply_eq_of_le_ker_direction (A := A) hx0A (f := f) hdir
    have hconst : ∀ x ∈ C, dotProduct x b = dotProduct x0 b := by
      intro x hxC
      have hxA : x ∈ (A : Set (Fin n → Real)) := subset_affineSpan (k := ℝ) (s := C) hxC
      have hxEq : f x = f x0 := by
        have : x ∈ {x : Fin n → Real | f x = f x0} := hAconst hxA
        simpa using this
      -- Rewrite `f` as `dotProductLinear n b`.
      have hfx : f x = dotProduct x b := by
        have : f x = (dotProductLinear n b) x := by simp [hfb]
        simpa [dotProductLinear] using this
      have hfx0' : f x0 = dotProduct x0 b := by
        have : f x0 = (dotProductLinear n b) x0 := by simp [hfb]
        simpa [dotProductLinear] using this
      simpa [hfx, hfx0'] using congrArg (fun t => t) hxEq
    set β : Real := dotProduct x0 b
    have hβne : β ≠ 0 := by
      -- `f x0 = β` and `f x0 ≠ 0`.
      have : f x0 = β := by
        have : f x0 = (dotProductLinear n b) x0 := by simp [hfb]
        simpa [β, dotProductLinear] using this
      exact fun hβ0 => hfx0 (by simp [this, hβ0])
    have hsupp_b : supportFunctionEReal C b = ((β : Real) : EReal) := by
      unfold supportFunctionEReal
      refine le_antisymm ?_ ?_
      · refine sSup_le ?_
        rintro _ ⟨x, hxC, rfl⟩
        have : dotProduct x b = β := by simpa [β] using hconst x hxC
        simp [this]
      · refine le_sSup ?_
        exact ⟨x0, hx0C, by simp [β]⟩
    have hsupp_neg : supportFunctionEReal C (-b) = ((-β : Real) : EReal) := by
      unfold supportFunctionEReal
      refine le_antisymm ?_ ?_
      · refine sSup_le ?_
        rintro _ ⟨x, hxC, rfl⟩
        have : dotProduct x b = β := by simpa [β] using hconst x hxC
        simp [dotProduct_neg, this]
      · refine le_sSup ?_
        exact ⟨x0, hx0C, by simp [β, dotProduct_neg]⟩
    have hsymm : -(supportFunctionEReal C (-b)) = supportFunctionEReal C b := by
      simp [hsupp_b, hsupp_neg]
    have : supportFunctionEReal C b = 0 := hsymm0 b hsymm
    have : (β : Real) = 0 := by
      have : ((β : Real) : EReal) = 0 := by simpa [hsupp_b] using this
      exact EReal.coe_eq_zero.1 this
    exact hβne this
  /-
  constructor
  · intro h0span y hsymm
    have hy_ne_top : supportFunctionEReal C y ≠ ⊤ := by
      intro htop
      have : -supportFunctionEReal C (-y) = (⊤ : EReal) := by simpa [htop] using hsymm
      have : supportFunctionEReal C (-y) = (⊥ : EReal) := by
        simpa using (neg_eq_top.1 this)
      exact section13_supportFunctionEReal_ne_bot_of_nonempty (n := n) (C := C) hCne (-y) this
    have hy_ne_bot : supportFunctionEReal C y ≠ ⊥ :=
      section13_supportFunctionEReal_ne_bot_of_nonempty (n := n) (C := C) hCne y
    set μ : Real := (supportFunctionEReal C y).toReal
    have hμ : (μ : EReal) = supportFunctionEReal C y := by
      simpa [μ] using (EReal.coe_toReal (x := supportFunctionEReal C y) hy_ne_top hy_ne_bot).symm
    have hsupp_le : ∀ x ∈ C, dotProduct x y ≤ μ := by
      have hsupp_leμ : supportFunctionEReal C y ≤ (μ : EReal) := by
        simpa [μ] using (EReal.le_coe_toReal (x := supportFunctionEReal C y) hy_ne_top)
      exact (section13_supportFunctionEReal_le_coe_iff (n := n) (C := C) (y := y) (μ := μ)).1 hsupp_leμ
    have hsupp_ge : ∀ x ∈ C, μ ≤ dotProduct x y := by
      have hneg :
          supportFunctionEReal C (-y) = ((-μ : Real) : EReal) := by
        have : supportFunctionEReal C (-y) = -supportFunctionEReal C y := by
          have := congrArg (fun z : EReal => -z) hsymm
          simpa [neg_neg] using this
        simp [this, hμ]
      intro x hx
      have hsupp_neg_le : dotProduct x (-y) ≤ -μ := by
        have hsupp_le_neg :
            supportFunctionEReal C (-y) ≤ ((-μ : Real) : EReal) := by simpa [hneg]
        have := (section13_supportFunctionEReal_le_coe_iff (n := n) (C := C) (y := -y) (μ := -μ)).1
            hsupp_le_neg x hx
        simpa using this
      have : -dotProduct x y ≤ -μ := by simpa [dotProduct_neg] using hsupp_neg_le
      exact (neg_le_neg_iff).1 this
    have hdot_eq : ∀ x ∈ C, dotProduct x y = μ := by
      intro x hx
      exact le_antisymm (hsupp_le x hx) (hsupp_ge x hx)
    -- The level set `{x | ⟪x,y⟫ = μ}` is an affine subspace containing `C`, hence contains `affineSpan C`.
    let Hμ : AffineSubspace ℝ (Fin n → Real) :=
      { carrier := {x : Fin n → Real | dotProduct x y = μ}
        smul_vsub_vadd_mem := by
          intro c p1 p2 p3 hp1 hp2 hp3
          have hp1' : dotProduct p1 y = μ := by simpa using hp1
          have hp2' : dotProduct p2 y = μ := by simpa using hp2
          have hp3' : dotProduct p3 y = μ := by simpa using hp3
          have hp12 : dotProduct (p1 - p2) y = 0 := by
            have : dotProduct (p1 - p2) y = dotProduct p1 y - dotProduct p2 y := by
              simp [dotProduct_sub]
            simp [this, hp1', hp2']
          have : dotProduct (c • (p1 - p2) + p3) y = μ := by
            simp [add_dotProduct, smul_dotProduct, hp12, hp3']
          simpa [vsub_eq_sub, vadd_eq_add] using this }
    have hC_Hμ : C ⊆ (Hμ : Set (Fin n → Real)) := by
      intro x hx
      exact hdot_eq x hx
    have hspan_le : affineSpan ℝ C ≤ Hμ := (affineSpan_le (k := ℝ) (s := C) (Q := Hμ)).2 hC_Hμ
    have hμ0 : dotProduct (0 : Fin n → Real) y = μ := hspan_le h0span
    have : μ = 0 := by simpa [dotProduct] using hμ0.symm
    simpa [hμ, this]
  · intro hsymm0
    by_contra h0not
    -- If `0 ∉ affineSpan C`, separate `0` from the direction to get a nonzero linear functional
    -- constant (and nonzero) on `C`, producing a contradiction.
    have hAne : (affineSpan ℝ C : AffineSubspace ℝ (Fin n → Real)).Nonempty :=
      (subset_affineSpan (k := ℝ) (s := C)).nonempty_iff.2 hCne
    rcases hCne with ⟨x0, hx0C⟩
    set A : AffineSubspace ℝ (Fin n → Real) := affineSpan ℝ C
    have hx0A : x0 ∈ (A : Set (Fin n → Real)) := subset_affineSpan (k := ℝ) (s := C) hx0C
    have hx0_not_dir : x0 ∉ A.direction := by
      intro hx0dir
      have h0A : (0 : Fin n → Real) ∈ (A : Set (Fin n → Real)) := by
        -- `0 = (-x0) +ᵥ x0` and `-x0 ∈ A.direction`.
        have : (-x0 : Fin n → Real) ∈ A.direction := A.direction.neg_mem hx0dir
        have : (-x0) +ᵥ x0 ∈ A := AffineSubspace.vadd_mem_of_mem_direction (s := A) this hx0A
        simpa [vadd_eq_add] using this
      exact h0not h0A
    obtain ⟨f, hf0, hdir⟩ := Submodule.exists_le_ker_of_not_mem (p := A.direction) hx0_not_dir
    -- Turn `f` into a strong dual and represent it as a dot product.
    let l : StrongDual ℝ (Fin n → Real) :=
      (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := (Fin n → Real)) (F' := ℝ) f)
    have hl : ∀ x : Fin n → Real,
        l x = dotProduct x (fun i => l (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ))) :=
      strongDual_apply_eq_dotProduct (n := n) l
    let b : Fin n → Real := fun i => l (Pi.single (M := fun _ : Fin n => ℝ) i (1 : ℝ))
    have hb0 : b ≠ 0 := by
      intro hb
      have hl0 : l = 0 := by
        ext x
        simpa [hl x, hb] using rfl
      have : f x0 = 0 := by
        -- `f x0 = l x0`.
        have : l x0 = 0 := by simpa [hl0] using rfl
        simpa [l, LinearMap.toContinuousLinearMap] using this
      exact hf0 this
    have hdir0 : ∀ v ∈ A.direction, dotProduct v b = 0 := by
      intro v hv
      have : f v = 0 := by
        have hvker : v ∈ LinearMap.ker f := hdir hv
        simpa using hvker
      -- Convert via the dot-product representation of `l`.
      have : l v = 0 := by
        -- `l v = f v` by construction.
        simpa [l, LinearMap.toContinuousLinearMap, this]
      simpa [hl v, b] using this
    have hconst : ∀ x ∈ (A : Set (Fin n → Real)), dotProduct x b = dotProduct x0 b := by
      intro x hxA
      have hxv : x - x0 ∈ A.direction := by
        simpa [vsub_eq_sub] using (AffineSubspace.vsub_mem_direction hxA hx0A)
      have : dotProduct (x - x0) b = 0 := hdir0 (x - x0) hxv
      have : dotProduct x b - dotProduct x0 b = 0 := by
        simpa [dotProduct_sub] using this
      linarith
    have hb_nonzero_val : dotProduct x0 b ≠ 0 := by
      have : f x0 ≠ 0 := hf0
      -- `f x0 = l x0 = dotProduct x0 b`.
      have : f x0 = dotProduct x0 b := by
        have : l x0 = dotProduct x0 b := by simpa [hl x0, b]
        simpa [l, LinearMap.toContinuousLinearMap] using this
      exact this ▸ hf0
    have hsupp_eq : supportFunctionEReal C b = ((dotProduct x0 b : Real) : EReal) := by
      unfold supportFunctionEReal
      refine le_antisymm ?_ ?_
      · refine sSup_le ?_
        intro z hz
        rcases hz with ⟨x, hxC, rfl⟩
        have hxA' : x ∈ (A : Set (Fin n → Real)) := subset_affineSpan (k := ℝ) (s := C) hxC
        simp [hconst x hxA']
      · refine le_sSup ?_
        exact ⟨x0, hx0C, rfl⟩
    have hsupp_symm : -supportFunctionEReal C (-b) = supportFunctionEReal C b := by
      -- Since `dotProduct · b` is constant on `C`, the support function is symmetric.
      have hsupp_neg : supportFunctionEReal C (-b) = ((dotProduct x0 (-b) : Real) : EReal) := by
        unfold supportFunctionEReal
        refine le_antisymm ?_ ?_
        · refine sSup_le ?_
          intro z hz
          rcases hz with ⟨x, hxC, rfl⟩
          have hxA' : x ∈ (A : Set (Fin n → Real)) := subset_affineSpan (k := ℝ) (s := C) hxC
          simp [hconst x hxA', dotProduct_neg]
        · refine le_sSup ?_
          exact ⟨x0, hx0C, rfl⟩
      simp [hsupp_eq, hsupp_neg, dotProduct_neg]
    have : supportFunctionEReal C b = 0 := hsymm0 b hsupp_symm
    have : dotProduct x0 b = 0 := by
      -- Compare the computed value of `supportFunctionEReal`.
      have : ((dotProduct x0 b : Real) : EReal) = 0 := by simpa [hsupp_eq] using this
      exact (EReal.coe_eq_zero.1 this)
    exact hb_nonzero_val this
  -/

/-- Corollary 13.3.4. Let `f` be a closed proper convex function. Let `xStar` be a fixed vector and
let `g x = f x - ⟪x, xStar⟫`. Then:

(a) `xStar ∈ cl (dom f^*)` if and only if `(g₀⁺) y ≥ 0` for every `y`;
(b) `xStar ∈ ri (dom f^*)` if and only if `(g₀⁺) y > 0` for all `y` except those satisfying
  `-(g₀⁺ (-y)) = (g₀⁺) y = 0`;
(c) `xStar ∈ int (dom f^*)` if and only if `(g₀⁺) y > 0` for every `y ≠ 0`;
(d) `xStar ∈ aff (dom f^*)` if and only if `(g₀⁺) y = 0` for every `y` such that
  `-(g₀⁺ (-y)) = (g₀⁺) y`.

Here `f^*` is `fenchelConjugate n f`, its domain is `effectiveDomain univ (fenchelConjugate n f)`,
and `g₀⁺` is `recessionFunction g`. -/
theorem mem_closure_ri_interior_affineSpan_effectiveDomain_fenchelConjugate_iff_recessionFunction
    {n : Nat} (f : (Fin n → Real) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) (xStar : Fin n → Real) :
    (let domFstar :
        Set (Fin n → Real) :=
        effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)
      let g : (Fin n → Real) → EReal := fun x => f x - ((dotProduct x xStar : Real) : EReal)
      (xStar ∈ closure domFstar ↔ ∀ y : Fin n → Real, 0 ≤ recessionFunction g y) ∧
        (xStar ∈ intrinsicInterior ℝ domFstar ↔
            ∀ y : Fin n → Real,
              (¬
                  (-(recessionFunction g (-y)) = recessionFunction g y ∧
                    recessionFunction g y = 0)) →
                recessionFunction g y > 0) ∧
          (xStar ∈ interior domFstar ↔
              ∀ y : Fin n → Real, y ≠ 0 → recessionFunction g y > 0) ∧
            (xStar ∈ (affineSpan ℝ domFstar : Set (Fin n → Real)) ↔
                ∀ y : Fin n → Real,
                  (-(recessionFunction g (-y)) = recessionFunction g y) →
                    recessionFunction g y = 0)) := by
  classical
  dsimp
  set domFstar : Set (Fin n → Real) :=
    effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)
  set g : (Fin n → Real) → EReal := fun x => f x - ((dotProduct x xStar : Real) : EReal)
  have hproperStar_f : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  haveI : Nonempty domFstar :=
    (section13_effectiveDomain_nonempty_of_proper (n := n) (f := fenchelConjugate n f) hproperStar_f).to_subtype
  -- Compute `dom g*` as a translate of `dom f*`.
  have hdom :
      effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n g) =
        domFstar - ({xStar} : Set (Fin n → Real)) := by
    simpa [domFstar, g] using
      (section13_effectiveDomain_fenchelConjugate_sub_dotProduct (n := n) (f := f) (xStar := xStar))
  -- `g` is proper closed convex.
  let lin : (Fin n → Real) → EReal := fun x => ((dotProduct x (-xStar) : Real) : EReal)
  have hlin_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) lin :=
    section13_properConvexFunctionOn_dotProduct (n := n) (-xStar)
  have hg_eq : g = fun x => f x + lin x := by
    funext x
    simp [g, lin, sub_eq_add_neg, dotProduct_neg]
  have hg_conv : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) g := by
    simpa [hg_eq] using
      (convexFunctionOn_add_of_proper (n := n) (f1 := f) (f2 := lin) hproper hlin_proper)
  have hg_epi : Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) g) := by
    have hdom_ne : Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
      (nonempty_epigraph_iff_nonempty_effectiveDomain (S := (Set.univ : Set (Fin n → Real))) (f := f)).1
        hproper.2.1
    rcases hdom_ne with ⟨x0, hx0⟩
    have hx0lt : f x0 < (⊤ : EReal) := by
      have : x0 ∈ {u : Fin n → Real | u ∈ (Set.univ : Set (Fin n → Real)) ∧ f u < (⊤ : EReal)} := by
        simpa [effectiveDomain_eq] using hx0
      exact this.2
    have hx0_ne_top : f x0 ≠ (⊤ : EReal) := ne_of_lt hx0lt
    have hlin_ne_top : lin x0 ≠ (⊤ : EReal) := EReal.coe_ne_top _
    have hx0g_lt : g x0 < (⊤ : EReal) := by
      have : f x0 + lin x0 < (⊤ : EReal) := EReal.add_lt_top hx0_ne_top hlin_ne_top
      simpa [hg_eq] using this
    have hx0g : x0 ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) g := by
      have : x0 ∈ {u : Fin n → Real | u ∈ (Set.univ : Set (Fin n → Real)) ∧ g u < (⊤ : EReal)} :=
        ⟨by simp, hx0g_lt⟩
      simpa [effectiveDomain_eq] using this
    have : Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → Real)) g) := ⟨x0, hx0g⟩
    exact
      (nonempty_epigraph_iff_nonempty_effectiveDomain (S := (Set.univ : Set (Fin n → Real))) (f := g)).2
        this
  have hg_notbot : ∀ x ∈ (Set.univ : Set (Fin n → Real)), g x ≠ (⊥ : EReal) := by
    intro x _hx
    have hxbot : f x ≠ (⊥ : EReal) := hproper.2.2 x (by simp)
    have hxlinbot : lin x ≠ (⊥ : EReal) := EReal.coe_ne_bot _
    have : f x + lin x ≠ (⊥ : EReal) := add_ne_bot_of_notbot hxbot hxlinbot
    simpa [hg_eq] using this
  have hg_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) g :=
    ⟨hg_conv, hg_epi, hg_notbot⟩
  have hg_closed : ClosedConvexFunction g := by
    have hcont_dot : Continuous fun x : Fin n → Real => (dotProduct x (-xStar) : Real) := by
      simpa using
        (continuous_id.dotProduct
          (continuous_const : Continuous fun _ : Fin n → Real => (-xStar)))
    have hcont_lin : Continuous fun x : Fin n → Real => lin x :=
      (_root_.continuous_coe_real_ereal.comp hcont_dot)
    have hlin_lsc : LowerSemicontinuous lin := hcont_lin.lowerSemicontinuous
    have hcont_add :
        ∀ x,
          ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (f x, lin x) := by
      intro x
      have hnotbot_f : f x ≠ (⊥ : EReal) := hproper.2.2 x (by simp)
      have hnotbot_lin : lin x ≠ (⊥ : EReal) := EReal.coe_ne_bot _
      exact EReal.continuousAt_add (h := Or.inr hnotbot_lin) (h' := Or.inl hnotbot_f)
    have hg_lsc : LowerSemicontinuous g := by
      have : LowerSemicontinuous (fun x => f x + lin x) :=
        LowerSemicontinuous.add' hclosed.2 hlin_lsc hcont_add
      simpa [hg_eq] using this
    refine ⟨?_, hg_lsc⟩
    simpa [ConvexFunction] using hg_proper.1
  -- Identify the support function of `dom g*` with `recessionFunction g`.
  have hsupp :
      supportFunctionEReal
          (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n g)) =
        recessionFunction g := by
    simpa using
      (section13_supportFunctionEReal_dom_fenchelConjugate_eq_recessionFunction (n := n) (f := g)
        hg_closed hg_proper)
  have hsupp_y :
      ∀ y : Fin n → Real,
        supportFunctionEReal
            (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n g)) y =
          recessionFunction g y := by
    intro y
    simpa using congrArg (fun h => h y) hsupp
  have htrans :=
    section13_translate_mem_closure_ri_interior_affineSpan_iff_zero (n := n) domFstar xStar
  -- Convexity and nonemptiness of `dom g*`.
  have hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fenchelConjugate n g) :=
    proper_fenchelConjugate_of_proper (n := n) (f := g) hg_proper
  set C : Set (Fin n → Real) :=
    effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n g)
  have hsuppC_y : ∀ y : Fin n → Real, supportFunctionEReal C y = recessionFunction g y := by
    intro y
    simpa [C] using hsupp_y y
  have hCne : C.Nonempty :=
    section13_effectiveDomain_nonempty_of_proper (n := n) (f := fenchelConjugate n g) hproperStar
  haveI : Nonempty C := hCne.to_subtype
  have hCconv : Convex ℝ C := by
    have hconvStar : ConvexFunction (fenchelConjugate n g) :=
      (fenchelConjugate_closedConvex (n := n) (f := g)).2
    simpa [C] using
      (effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real))) (f := fenchelConjugate n g)
        (hf := (by simpa [ConvexFunction] using hconvStar)))
  -- Origin characterizations.
  have hcl0 :
      ((0 : Fin n → Real) ∈ closure C ↔ ∀ y : Fin n → Real, (0 : EReal) ≤ supportFunctionEReal C y) := by
    simpa using
      (section13_zero_mem_closure_iff_forall_zero_le_supportFunctionEReal (n := n) (C := C) hCconv hCne)
  have hri0 :
      ((0 : Fin n → Real) ∈ intrinsicInterior ℝ C ↔
          ∀ y : Fin n → Real,
            (¬ (-(supportFunctionEReal C (-y)) = supportFunctionEReal C y ∧ supportFunctionEReal C y = 0)) →
              supportFunctionEReal C y > 0) := by
    simpa using
      (section13_zero_mem_intrinsicInterior_iff_supportFunctionEReal (n := n) (C := C) hCconv hCne)
  have hint0 :
      ((0 : Fin n → Real) ∈ interior C ↔ ∀ y : Fin n → Real, y ≠ 0 → supportFunctionEReal C y > 0) := by
    simpa using
      (section13_zero_mem_interior_iff_forall_supportFunctionEReal_pos (n := n) (C := C) hCconv hCne)
  have haff0 :
      ((0 : Fin n → Real) ∈ (affineSpan ℝ C : Set (Fin n → Real)) ↔
          ∀ y : Fin n → Real, (-(supportFunctionEReal C (-y)) = supportFunctionEReal C y) →
            supportFunctionEReal C y = 0) := by
    simpa using
      (section13_zero_mem_affineSpan_iff_supportFunctionEReal (n := n) (C := C) hCne)
  -- Translation step.
  have hCeq : C = domFstar - ({xStar} : Set (Fin n → Real)) := by
    simpa [C] using hdom
  have hcl : xStar ∈ closure domFstar ↔ (0 : Fin n → Real) ∈ closure C := by
    simpa [hCeq] using htrans.1
  have hri : xStar ∈ intrinsicInterior ℝ domFstar ↔ (0 : Fin n → Real) ∈ intrinsicInterior ℝ C := by
    simpa [hCeq] using htrans.2.1
  have hint : xStar ∈ interior domFstar ↔ (0 : Fin n → Real) ∈ interior C := by
    simpa [hCeq] using htrans.2.2.1
  have haff : xStar ∈ (affineSpan ℝ domFstar : Set (Fin n → Real)) ↔
      (0 : Fin n → Real) ∈ (affineSpan ℝ C : Set (Fin n → Real)) := by
    simpa [hCeq] using htrans.2.2.2
  -- Assemble the four conditions.
  refine ⟨?_, ?_⟩
  · -- (a)
    calc
      xStar ∈ closure domFstar ↔ (0 : Fin n → Real) ∈ closure C := hcl
      _ ↔ ∀ y : Fin n → Real, (0 : EReal) ≤ supportFunctionEReal C y := hcl0
      _ ↔ ∀ y : Fin n → Real, (0 : EReal) ≤ recessionFunction g y := by
            simp [hsuppC_y]
  · refine ⟨?_, ?_⟩
    · -- (b)
      calc
        xStar ∈ intrinsicInterior ℝ domFstar ↔ (0 : Fin n → Real) ∈ intrinsicInterior ℝ C := hri
        _ ↔
            ∀ y : Fin n → Real,
              (¬ (-(supportFunctionEReal C (-y)) = supportFunctionEReal C y ∧ supportFunctionEReal C y = 0)) →
                supportFunctionEReal C y > 0 := hri0
        _ ↔
            ∀ y : Fin n → Real,
              (¬ (-(recessionFunction g (-y)) = recessionFunction g y ∧ recessionFunction g y = 0)) →
                recessionFunction g y > 0 := by
              simp [hsuppC_y]
    · refine ⟨?_, ?_⟩
      · -- (c)
        calc
          xStar ∈ interior domFstar ↔ (0 : Fin n → Real) ∈ interior C := hint
          _ ↔ ∀ y : Fin n → Real, y ≠ 0 → supportFunctionEReal C y > 0 := hint0
          _ ↔ ∀ y : Fin n → Real, y ≠ 0 → recessionFunction g y > 0 := by
                simp [hsuppC_y]
      · -- (d)
        calc
          xStar ∈ (affineSpan ℝ domFstar : Set (Fin n → Real)) ↔
              (0 : Fin n → Real) ∈ (affineSpan ℝ C : Set (Fin n → Real)) := haff
          _ ↔
              ∀ y : Fin n → Real,
                (-(supportFunctionEReal C (-y)) = supportFunctionEReal C y) →
                  supportFunctionEReal C y = 0 := haff0
          _ ↔
              ∀ y : Fin n → Real,
                (-(recessionFunction g (-y)) = recessionFunction g y) →
                  recessionFunction g y = 0 := by
                simp [hsuppC_y]

/-- Rewrite `linearitySpace (f*)` using Theorem 13.3: it is a finiteness+symmetry condition on the
support function of `dom f`. -/
lemma section13_linearitySpace_fenchelConjugate_iff_supportFunctionEReal_effectiveDomain {n : Nat}
    (f : (Fin n → Real) → EReal) (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (y : Fin n → Real) :
    y ∈ linearitySpace (fenchelConjugate n f) ↔
      supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin n → Real)) f) y ≠ ⊤ ∧
        (-(supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin n → Real)) f) (-y)) =
          supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin n → Real)) f) y) := by
  classical
  have hsupp :
      supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin n → Real)) f) =
        recessionFunction (fenchelConjugate n f) := by
    simpa using
      (supportFunctionEReal_effectiveDomain_eq_recession_fenchelConjugate (n := n) (f := f) (hf := hf)
        (fStar0_plus := recessionFunction (fenchelConjugate n f)) (hfStar0_plus := by intro y; rfl))
  constructor
  · intro hy
    refine ⟨?_, ?_⟩
    · simpa [hsupp] using hy.1
    · simpa [hsupp] using hy.2
  · rintro ⟨hy_ne_top, hy_symm⟩
    refine ⟨?_, ?_⟩
    · simpa [hsupp] using hy_ne_top
    · simpa [hsupp] using hy_symm

/-- If a support function is finite and symmetric at `y`, then the dot-product functional
`x ↦ ⟪x,y⟫` is constant on the underlying set. -/
lemma section13_supportFunctionEReal_symm_finite_imp_dotProduct_const {n : Nat}
    {C : Set (Fin n → Real)} (hCne : C.Nonempty) {y : Fin n → Real}
    (hy : supportFunctionEReal C y ≠ ⊤)
    (hsymm : -(supportFunctionEReal C (-y)) = supportFunctionEReal C y) :
    ∃ μ : Real, ∀ x ∈ C, dotProduct x y = μ := by
  classical
  have hy_ne_bot : supportFunctionEReal C y ≠ ⊥ :=
    section13_supportFunctionEReal_ne_bot_of_nonempty (n := n) (C := C) hCne y
  set μ : Real := (supportFunctionEReal C y).toReal
  have hμ : ((μ : Real) : EReal) = supportFunctionEReal C y := by
    simpa [μ] using (EReal.coe_toReal (x := supportFunctionEReal C y) hy hy_ne_bot)
  have hle : ∀ x ∈ C, dotProduct x y ≤ μ := by
    have hsup_le : supportFunctionEReal C y ≤ (μ : EReal) := by
      exact le_of_eq hμ.symm
    exact (section13_supportFunctionEReal_le_coe_iff (n := n) (C := C) (y := y) (μ := μ)).1 hsup_le
  have hge : ∀ x ∈ C, μ ≤ dotProduct x y := by
    have hneg : supportFunctionEReal C (-y) = ((-μ : Real) : EReal) := by
      have h1 : supportFunctionEReal C (-y) = -supportFunctionEReal C y :=
        (neg_eq_iff_eq_neg).1 hsymm
      calc
        supportFunctionEReal C (-y) = -supportFunctionEReal C y := h1
        _ = -((μ : Real) : EReal) := by simp [hμ]
        _ = ((-μ : Real) : EReal) := by simp
    intro x hx
    have hx_neg : dotProduct x (-y) ≤ -μ := by
      have hsup_le : supportFunctionEReal C (-y) ≤ ((-μ : Real) : EReal) := le_of_eq hneg
      have :=
        (section13_supportFunctionEReal_le_coe_iff (n := n) (C := C) (y := -y) (μ := -μ)).1
          hsup_le x hx
      simpa using this
    have : -dotProduct x y ≤ -μ := by simpa [dotProduct_neg] using hx_neg
    exact (neg_le_neg_iff).1 this
  refine ⟨μ, ?_⟩
  intro x hx
  exact le_antisymm (hle x hx) (hge x hx)

/-- The dot-product functional `x ↦ ⟪x,y⟫` is constant on a nonempty set `C` iff `y` is orthogonal
to the direction of `affineSpan C`. -/
lemma section13_dotProduct_const_iff_mem_orthogonalComplement_direction_affineSpan {n : Nat}
    {C : Set (Fin n → Real)} (hCne : C.Nonempty) (y : Fin n → Real) :
    (∃ μ : Real, ∀ x ∈ C, dotProduct x y = μ) ↔
      y ∈ orthogonalComplement n ((affineSpan ℝ C).direction) := by
  classical
  -- Use `direction_affineSpan` to identify the direction with `vectorSpan`.
  have hdir : (affineSpan ℝ C).direction = vectorSpan ℝ C := direction_affineSpan (k := ℝ) (s := C)
  constructor
  · rintro ⟨μ, hμ⟩
    -- Show `y` is orthogonal to every element of `vectorSpan ℝ C = span (C -ᵥ C)`.
    intro v hv
    have hv' : v ∈ Submodule.span ℝ (C -ᵥ C) := by
      have : v ∈ vectorSpan ℝ C := by simpa [hdir] using hv
      simpa [vectorSpan_def] using this
    have hv0 : dotProduct v y = 0 := by
      refine Submodule.span_induction (p := fun v _ => dotProduct v y = (0 : Real)) ?_ ?_ ?_ ?_ hv'
      · intro w hw
        rcases hw with ⟨x1, hx1, x2, hx2, rfl⟩
        have hx1' : dotProduct x1 y = μ := hμ x1 hx1
        have hx2' : dotProduct x2 y = μ := hμ x2 hx2
        have : dotProduct (x1 - x2) y = 0 := by
          simp [hx1', hx2']
        simpa [vsub_eq_sub] using this
      · simp
      · intro u v _ _ hu hv
        simp [add_dotProduct, hu, hv]
      · intro a v _ hv
        simp [smul_dotProduct, hv]
    -- Convert `dotProduct v y = 0` to `y ⬝ᵥ v = 0`.
    simpa [dotProduct_comm] using hv0
  · intro hy
    rcases hCne with ⟨x0, hx0⟩
    refine ⟨dotProduct x0 y, ?_⟩
    intro x hx
    have hxv : x -ᵥ x0 ∈ vectorSpan ℝ C := vsub_mem_vectorSpan (k := ℝ) hx hx0
    have hxdir : x -ᵥ x0 ∈ (affineSpan ℝ C).direction := by simpa [hdir] using hxv
    have horth : y ⬝ᵥ (x -ᵥ x0) = 0 := hy (x -ᵥ x0) hxdir
    have : dotProduct (x - x0) y = 0 := by
      -- Convert to `dotProduct (x - x0) y` using symmetry.
      have : dotProduct y (x - x0) = 0 := by simpa [vsub_eq_sub] using horth
      simpa [dotProduct_comm] using this
    -- Expand `⟪x - x0, y⟫ = 0` to get constancy.
    have : dotProduct x y - dotProduct x0 y = 0 := by simpa [dotProduct_sub] using this
    linarith

/-- Finite-dimensional formula: `dim(Lᗮ) = n - dim(L)` for the book’s `orthogonalComplement`. -/
lemma section13_finrank_orthogonalComplement {n : Nat} (L : Submodule ℝ (Fin n → Real)) :
    Module.finrank ℝ (orthogonalComplement n L) = n - Module.finrank ℝ L := by
  classical
  -- Identify `orthogonalComplement` with the preimage of the dual annihilator under `piEquiv`.
  let e : (Fin n → Real) ≃ₗ[ℝ] Module.Dual ℝ (Fin n → Real) :=
    Module.piEquiv (Fin n) ℝ ℝ
  have hortho :
      orthogonalComplement n L =
        (L.dualAnnihilator).comap (e : (Fin n → Real) →ₗ[ℝ] Module.Dual ℝ (Fin n → Real)) := by
    ext x
    constructor
    · intro hx
      -- `e x` vanishes on `L` because `⟪x,·⟫` does.
      refine (Submodule.mem_dualAnnihilator (W := L) (φ := e x)).2 ?_
      intro y hy
      have : x ⬝ᵥ y = 0 := hx y hy
      simpa [e, Module.piEquiv_apply_apply, dotProduct_comm, dotProduct, smul_eq_mul, mul_comm,
        mul_left_comm, mul_assoc] using this
    · intro hx y hy
      -- Conversely, if `e x` vanishes on `L`, then `x` is orthogonal to `L`.
      have hx' : ∀ w ∈ L, (e x) w = 0 :=
        (Submodule.mem_dualAnnihilator (W := L) (φ := e x)).1 hx
      have : (e x) y = 0 := hx' y hy
      simpa [e, Module.piEquiv_apply_apply, dotProduct_comm, dotProduct, smul_eq_mul, mul_comm,
        mul_left_comm, mul_assoc] using this
  have hfinrank_comap :
      Module.finrank ℝ
          ((L.dualAnnihilator).comap
              (e : (Fin n → Real) →ₗ[ℝ] Module.Dual ℝ (Fin n → Real))) =
        Module.finrank ℝ (L.dualAnnihilator) := by
    simpa using (e.ofSubmodule' (L.dualAnnihilator)).finrank_eq
  have hsum :
      Module.finrank ℝ L + Module.finrank ℝ (L.dualAnnihilator) =
        Module.finrank ℝ (Fin n → Real) := by
    simpa using (Subspace.finrank_add_finrank_dualAnnihilator_eq (K := ℝ) (V := Fin n → Real) L)
  have hdual :
      Module.finrank ℝ (L.dualAnnihilator) =
        Module.finrank ℝ (Fin n → Real) - Module.finrank ℝ L := by
    -- Solve for `finrank (dualAnnihilator)` from `finrank L + finrank Lᵃⁿⁿ = finrank V`.
    calc
      Module.finrank ℝ (L.dualAnnihilator) =
          (Module.finrank ℝ L + Module.finrank ℝ (L.dualAnnihilator)) - Module.finrank ℝ L := by
            simp
      _ = Module.finrank ℝ (Fin n → Real) - Module.finrank ℝ L := by
            simp [hsum]
  calc
    Module.finrank ℝ (orthogonalComplement n L) =
        Module.finrank ℝ
          ((L.dualAnnihilator).comap
              (e : (Fin n → Real) →ₗ[ℝ] Module.Dual ℝ (Fin n → Real))) := by
          simpa using
            congrArg (fun S : Submodule ℝ (Fin n → Real) => Module.finrank ℝ S) hortho
    _ = Module.finrank ℝ (L.dualAnnihilator) := hfinrank_comap
    _ = Module.finrank ℝ (Fin n → Real) - Module.finrank ℝ L := hdual
    _ = n - Module.finrank ℝ L := by simp

end Section13
end Chap03
