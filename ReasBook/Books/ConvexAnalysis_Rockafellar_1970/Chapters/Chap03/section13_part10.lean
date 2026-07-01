/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Siyuan Shao, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section13_part9

open scoped Pointwise

section Chap03
section Section13

/-- For any `f : ℝ^n → (-∞, +∞]`, the direction of `affineSpan (dom f)` has finrank at most `n`. -/
lemma section13_finrank_direction_affineSpan_effectiveDomain_le {n : Nat} (f : (Fin n → Real) → EReal) :
    Module.finrank ℝ
        ((affineSpan ℝ (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).direction) ≤ n := by
  simpa [Module.finrank_fin_fun] using
    (Submodule.finrank_le (R := ℝ) (M := (Fin n → Real))
      ((affineSpan ℝ (effectiveDomain (Set.univ : Set (Fin n → Real)) f)).direction))

/-- The book-defined rank `dim(aff(dom f)) - lin(f)` is invariant under Fenchel conjugation. -/
lemma section13_rank_eq_rank_fenchelConjugate {n : Nat} {f : (Fin n → Real) → EReal}
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    (let rank (h : (Fin n → Real) → EReal) : Nat :=
        Module.finrank ℝ
            (affineSpan ℝ (effectiveDomain (Set.univ : Set (Fin n → Real)) h)).direction -
          Module.finrank ℝ (Submodule.span ℝ (linearitySpace h));
      rank (fenchelConjugate n f) = rank f) := by
  classical
  dsimp
  set domF : Set (Fin n → Real) := effectiveDomain (Set.univ : Set (Fin n → Real)) f
  set domFstar : Set (Fin n → Real) :=
    effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)
  set A : Nat := Module.finrank ℝ ((affineSpan ℝ domF).direction)
  set B : Nat := Module.finrank ℝ (Submodule.span ℝ (linearitySpace f))
  have hA_le : A ≤ n := by
    simpa [A, domF] using section13_finrank_direction_affineSpan_effectiveDomain_le (n := n) f
  have hmain :=
    (linearitySpace_fenchelConjugate_eq_orthogonal_direction_affineSpan_effectiveDomain_and_dual
        (n := n) (f := f) hf_proper)
  have hclosed_part :
      (affineSpan ℝ domFstar).direction =
          orthogonalComplement n (Submodule.span ℝ (linearitySpace f)) ∧
        (Module.finrank ℝ (Submodule.span ℝ (linearitySpace (fenchelConjugate n f))) =
            n - Module.finrank ℝ ((affineSpan ℝ domF).direction)) ∧
          (Module.finrank ℝ ((affineSpan ℝ domFstar).direction) =
            n - Module.finrank ℝ (Submodule.span ℝ (linearitySpace f))) := by
    simpa [domF, domFstar] using (by
      exact (hmain.2 hf_closed))
  have hfinrank_span_linearity_fstar :
      Module.finrank ℝ (Submodule.span ℝ (linearitySpace (fenchelConjugate n f))) = n - A := by
    simpa [A, domF] using hclosed_part.2.1
  have hfinrank_direction_domFstar :
      Module.finrank ℝ ((affineSpan ℝ domFstar).direction) = n - B := by
    simpa [B] using hclosed_part.2.2
  -- Plug the finrank identities into the definition of rank and simplify `(n - B) - (n - A)`.
  rw [hfinrank_direction_domFstar, hfinrank_span_linearity_fstar]
  simpa [A, B] using (tsub_tsub_tsub_cancel_left (a := n) (b := A) (c := B) hA_le)

/-- Corollary 13.4.1. Closed proper convex functions conjugate to each other have the same rank. -/
theorem rank_eq_of_conjugate {n : Nat} {f g : (Fin n → Real) → EReal}
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hg_closed : ClosedConvexFunction g)
    (hg_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) g)
    (hfg : fenchelConjugate n f = g) (hgf : fenchelConjugate n g = f) :
    (let rank (h : (Fin n → Real) → EReal) : Nat :=
        Module.finrank ℝ
            (affineSpan ℝ (effectiveDomain (Set.univ : Set (Fin n → Real)) h)).direction -
          Module.finrank ℝ (Submodule.span ℝ (linearitySpace h));
      rank f = rank g) := by
  -- Rewrite `g` as the Fenchel conjugate of `f` and use rank invariance under conjugation.
  cases hfg
  simpa using
    (section13_rank_eq_rank_fenchelConjugate (n := n) (f := f) hf_closed hf_proper).symm

/-- The affine hyperplane `{x | ⟪y, x⟫ = a}` as an `AffineSubspace`. -/
def section13_dotProductHyperplane {n : Nat} (y : Fin n → Real) (a : Real) :
    AffineSubspace ℝ (Fin n → Real) where
  carrier := {xStar | dotProduct y xStar = a}
  smul_vsub_vadd_mem := by
    intro c p₁ p₂ p₃ hp₁ hp₂ hp₃
    -- In the ambient affine space `P = V`, we have `p₁ -ᵥ p₂ = p₁ - p₂` and `v +ᵥ p₃ = v + p₃`.
    -- The defining equation is preserved under `c • (p₁ -ᵥ p₂) +ᵥ p₃` by bilinearity of `dotProduct`.
    -- Here `hp₁`, `hp₂`, `hp₃` are exactly the defining equations for membership.
    have hp₁' : y ⬝ᵥ p₁ = a := by simpa using hp₁
    have hp₂' : y ⬝ᵥ p₂ = a := by simpa using hp₂
    have hp₃' : y ⬝ᵥ p₃ = a := by simpa using hp₃
    simp [vsub_eq_sub, vadd_eq_add, hp₁', hp₂', hp₃', dotProduct_add, dotProduct_smul, smul_eq_mul,
      sub_eq_add_neg]

/-- If `f` is affine along a line, then its Fenchel conjugate is `⊤` off the corresponding
hyperplane in the dual variable. -/
lemma section13_fenchelConjugate_eq_top_of_affineLine {n : Nat} (f : (Fin n → Real) → EReal)
    {x y xStar : Fin n → Real} {a b : Real}
    (hline : ∀ t : ℝ, f (x + t • y) = ((a * t + b : ℝ) : EReal))
    (hcoeff : dotProduct y xStar ≠ a) :
    fenchelConjugate n f xStar = ⊤ := by
  classical
  -- Use `EReal.eq_top_iff_forall_lt` and exhibit arbitrarily large range terms along the line.
  refine (EReal.eq_top_iff_forall_lt _).2 ?_
  intro μ
  set k : ℝ := dotProduct y xStar - a
  set c0 : ℝ := dotProduct x xStar - b
  have hk : k ≠ 0 := by
    dsimp [k]
    exact sub_ne_zero.2 hcoeff
  -- A convenient rewriting of the range term along the line.
  have hterm (t : ℝ) :
      ((x + t • y) ⬝ᵥ xStar : ℝ) - (a * t + b) = c0 + t * k := by
    -- Expand dot products and collect coefficients of `t`.
    -- `⟪x + t y, xStar⟫ - (a t + b) = (⟪x,xStar⟫ - b) + t*(⟪y,xStar⟫ - a)`.
    simp [c0, k, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm, smul_eq_mul, mul_add]
  -- Choose `t` so that `c0 + t*k > μ`.
  have hk0 : (0 : ℝ) ≠ k := by simpa [eq_comm] using hk
  have hkpos_or_neg : 0 < k ∨ k < 0 := lt_or_gt_of_ne hk0
  rcases hkpos_or_neg with hkpos | hkneg
  ·
    let t0 : ℝ := (μ - c0) / k + 1
    have hμt : μ < c0 + t0 * k := by
      have hcalc : c0 + t0 * k = μ + k := by
        have : c0 + ((μ - c0) / k + 1) * k = μ + k := by
          field_simp [hk]
          ring
        simpa [t0, mul_add, add_mul, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm,
          mul_left_comm] using this
      have : μ < μ + k := by linarith
      simpa [hcalc] using this
    have hμt' : (μ : EReal) <
        (((x + t0 • y) ⬝ᵥ xStar : ℝ) : EReal) - f (x + t0 • y) := by
      have hEq :
          (((x + t0 • y) ⬝ᵥ xStar : ℝ) : EReal) - f (x + t0 • y) =
            ((c0 + t0 * k : ℝ) : EReal) := by
        have hEqE :
            (((x + t0 • y) ⬝ᵥ xStar : ℝ) - (a * t0 + b) : ℝ) = c0 + t0 * k := by
          simpa [t0, hterm] using (hterm t0)
        have hEqE' :
            (((x + t0 • y) ⬝ᵥ xStar : ℝ) : EReal) - ((a * t0 + b : ℝ) : EReal) =
              ((c0 + t0 * k : ℝ) : EReal) := by
          simpa [EReal.coe_sub] using congrArg (fun r : ℝ => (r : EReal)) hEqE
        simpa [hline t0] using hEqE'
      have hμcoe : (μ : EReal) < ((c0 + t0 * k : ℝ) : EReal) :=
        (EReal.coe_lt_coe_iff.2 hμt)
      exact lt_of_lt_of_eq hμcoe hEq.symm
    have hle :
        (((x + t0 • y) ⬝ᵥ xStar : ℝ) : EReal) - f (x + t0 • y) ≤ fenchelConjugate n f xStar := by
      unfold fenchelConjugate
      exact le_sSup ⟨x + t0 • y, rfl⟩
    exact lt_of_lt_of_le hμt' hle
  ·
    let t0 : ℝ := (μ - c0) / k - 1
    have hμt : μ < c0 + t0 * k := by
      have hcalc : c0 + t0 * k = μ - k := by
        have : c0 + ((μ - c0) / k - 1) * k = μ - k := by
          field_simp [hk]
          ring
        simpa [t0, sub_eq_add_neg, mul_add, add_mul, add_assoc, add_comm, add_left_comm,
          mul_assoc, mul_comm, mul_left_comm] using this
      have : μ < μ - k := by linarith
      simpa [hcalc] using this
    have hμt' : (μ : EReal) <
        (((x + t0 • y) ⬝ᵥ xStar : ℝ) : EReal) - f (x + t0 • y) := by
      have hEq :
          (((x + t0 • y) ⬝ᵥ xStar : ℝ) : EReal) - f (x + t0 • y) =
            ((c0 + t0 * k : ℝ) : EReal) := by
        have hEqE :
            (((x + t0 • y) ⬝ᵥ xStar : ℝ) - (a * t0 + b) : ℝ) = c0 + t0 * k := by
          simpa [t0, hterm] using (hterm t0)
        have hEqE' :
            (((x + t0 • y) ⬝ᵥ xStar : ℝ) : EReal) - ((a * t0 + b : ℝ) : EReal) =
              ((c0 + t0 * k : ℝ) : EReal) := by
          simpa [EReal.coe_sub] using congrArg (fun r : ℝ => (r : EReal)) hEqE
        simpa [hline t0] using hEqE'
      have hμcoe : (μ : EReal) < ((c0 + t0 * k : ℝ) : EReal) :=
        (EReal.coe_lt_coe_iff.2 hμt)
      exact lt_of_lt_of_eq hμcoe hEq.symm
    have hle :
        (((x + t0 • y) ⬝ᵥ xStar : ℝ) : EReal) - f (x + t0 • y) ≤ fenchelConjugate n f xStar := by
      unfold fenchelConjugate
      exact le_sSup ⟨x + t0 • y, rfl⟩
    exact lt_of_lt_of_le hμt' hle

/-- If `f` is affine along a line with direction `y ≠ 0`, then `dom (f*)` has empty interior. -/
lemma section13_not_nonempty_interior_dom_fenchelConjugate_of_exists_affineLine {n : Nat}
    (f : (Fin n → Real) → EReal)
    (hline :
      ∃ (x y : Fin n → Real),
        y ≠ 0 ∧ ∃ a b : ℝ, ∀ t : ℝ, f (x + t • y) = ((a * t + b : ℝ) : EReal)) :
    ¬ Set.Nonempty (interior (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f))) := by
  classical
  rcases hline with ⟨x, y, _hy0, a, b, hxy⟩
  set C : Set (Fin n → Real) :=
    effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)
  -- `C` is convex.
  have hconvStar : ConvexFunction (fenchelConjugate n f) :=
    (fenchelConjugate_closedConvex (n := n) (f := f)).2
  have hCconv : Convex ℝ C := by
    simpa [C] using
      (effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real))) (f := fenchelConjugate n f)
        (hf := (by simpa [ConvexFunction] using hconvStar)))
  -- `C` is contained in the hyperplane `⟪y, xStar⟫ = a`.
  let H : AffineSubspace ℝ (Fin n → Real) := section13_dotProductHyperplane (n := n) y a
  have hCsubset : C ⊆ (H : Set (Fin n → Real)) := by
    intro xStar hxStar
    have hxStar_ne_top : fenchelConjugate n f xStar ≠ (⊤ : EReal) :=
      mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := fenchelConjugate n f)
        (by simpa [C] using hxStar)
    by_contra hdot
    have htop : fenchelConjugate n f xStar = ⊤ :=
      section13_fenchelConjugate_eq_top_of_affineLine (n := n) (f := f) (x := x) (y := y)
        (xStar := xStar) (a := a) (b := b) hxy hdot
    exact hxStar_ne_top htop
  -- The hyperplane `H` is not `⊤` (its defining equation fails at some point).
  have hHne : (H : AffineSubspace ℝ (Fin n → Real)) ≠ ⊤ := by
    intro hHtop
    have : (0 : Fin n → Real) ∈ (H : Set (Fin n → Real)) := by simp [hHtop]
    -- But `0 ∈ H` forces `a = 0`, and then `y ∈ H` forces `y = 0`, contradicting `y ≠ 0`.
    have ha0 : a = 0 := by
      have h0 : dotProduct y (0 : Fin n → Real) = a := by
        have h0' := this
        dsimp [H, section13_dotProductHyperplane] at h0'
        change dotProduct y (0 : Fin n → Real) = a at h0'
        exact h0'
      have : (0 : ℝ) = a := by simpa using h0
      simpa using this.symm
    have : y ∈ (H : Set (Fin n → Real)) := by simp [hHtop]
    have hy_eq : dotProduct y y = a := by
      have hy' := this
      dsimp [H, section13_dotProductHyperplane] at hy'
      simpa using hy'
    have : dotProduct y y = 0 := by simpa [ha0] using hy_eq
    have : y = 0 := (dotProduct_self_eq_zero).1 this
    exact _hy0 this
  -- If `interior C` were nonempty, then `affineSpan C = ⊤`, hence `H = ⊤`, contradiction.
  intro hne
  have hspan : affineSpan ℝ C = ⊤ :=
    (Convex.interior_nonempty_iff_affineSpan_eq_top (V := (Fin n → Real)) hCconv).1
      (by simpa [C] using hne)
  have hspan_le : affineSpan ℝ C ≤ H := (affineSpan_le.2 hCsubset)
  have : (⊤ : AffineSubspace ℝ (Fin n → Real)) ≤ H := by simpa [hspan] using hspan_le
  exact hHne (top_le_iff.1 this)

/-- Addition by a real constant as an order isomorphism on `EReal`. -/
def section13_addRightOrderIso (c : ℝ) : EReal ≃o EReal where
  toEquiv :=
    { toFun := fun x => x + (c : EReal)
      invFun := fun x => x - (c : EReal)
      left_inv := by
        intro x
        simpa using (EReal.add_sub_cancel_right (a := x) (b := c))
      right_inv := by
        intro x
        simpa using (EReal.sub_add_cancel (a := x) (b := c)) }
  map_rel_iff' := by
    intro x y
    exact (EReal.addLECancellable_coe c).add_le_add_iff_right

/-- `sSup` commutes with addition by a real constant on `EReal`. -/
lemma section13_sSup_image_add_right (c : ℝ) (s : Set EReal) :
    sSup ((fun z : EReal => z + (c : EReal)) '' s) = sSup s + (c : EReal) := by
  classical
  have h1 :
      sSup s + (c : EReal) = ⨆ a ∈ s, a + (c : EReal) := by
    have h1' := (OrderIso.map_sSup (section13_addRightOrderIso c) s)
    dsimp [section13_addRightOrderIso] at h1'
    simpa using h1'
  have h2 :
      sSup ((fun z : EReal => z + (c : EReal)) '' s) = ⨆ a ∈ s, a + (c : EReal) := by
    simpa using (sSup_image (f := fun z : EReal => z + (c : EReal)) (s := s))
  calc
    sSup ((fun z : EReal => z + (c : EReal)) '' s) = ⨆ a ∈ s, a + (c : EReal) := h2
    _ = sSup s + (c : EReal) := by simpa using h1.symm

/-- If the dot product `xStar ↦ ⟪xStar, y⟫` is constant on `dom g`, then `fenchelConjugate n g`
is affine along the line `x + t • y`. -/
lemma section13_fenchelConjugate_translate_of_dotProduct_const {n : Nat}
    (g : (Fin n → Real) → EReal)
    (hg_bot : ∀ xStar : Fin n → Real, g xStar ≠ (⊥ : EReal))
    {y : Fin n → Real} {μ : Real}
    (hμ :
      ∀ xStar ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) g, dotProduct xStar y = μ)
    (x : Fin n → Real) (t : ℝ) :
    fenchelConjugate n g (x + t • y) = fenchelConjugate n g x + ((t * μ : ℝ) : EReal) := by
  classical
  set c : ℝ := t * μ
  -- The range terms at `x` and `x + t • y`.
  set h : (Fin n → Real) → EReal := fun xStar => ((xStar ⬝ᵥ x : Real) : EReal) - g xStar
  have hterm :
      (fun xStar : Fin n → Real =>
          ((xStar ⬝ᵥ (x + t • y) : Real) : EReal) - g xStar) =
        fun xStar : Fin n → Real => h xStar + (c : EReal) := by
    funext xStar
    by_cases hxStar : xStar ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) g
    · have hxStar_ne_top : g xStar ≠ (⊤ : EReal) :=
        mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := g) hxStar
      have hxStar_ne_bot : g xStar ≠ (⊥ : EReal) := hg_bot xStar
      -- Lift `g xStar` to a real so that `simp` can use `EReal.coe_add`, `EReal.coe_sub`, etc.
      lift g xStar to ℝ using ⟨hxStar_ne_top, hxStar_ne_bot⟩ with r hr
      have hdot : (xStar ⬝ᵥ y) = μ := by simpa using hμ xStar hxStar
      simp [h, c, hr, hdot, dotProduct_add, dotProduct_smul, smul_eq_mul, sub_eq_add_neg,
        add_left_comm, add_comm, mul_comm]
    · have hxStar_top : g xStar = ⊤ := by
        by_contra hxStar_ne_top
        have hxlt : g xStar < (⊤ : EReal) := (lt_top_iff_ne_top).2 hxStar_ne_top
        have : xStar ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) g := by
          have : xStar ∈ {z | z ∈ (Set.univ : Set (Fin n → Real)) ∧ g z < (⊤ : EReal)} :=
            ⟨by simp, hxlt⟩
          simpa [effectiveDomain_eq] using this
        exact hxStar this
      simp [h, c, hxStar_top]
  have hrange :
      Set.range (fun xStar : Fin n → Real =>
          ((xStar ⬝ᵥ (x + t • y) : Real) : EReal) - g xStar) =
        (fun z : EReal => z + (c : EReal)) '' Set.range h := by
    ext z
    constructor
    · rintro ⟨xStar, rfl⟩
      refine ⟨h xStar, ⟨xStar, rfl⟩, ?_⟩
      have hxStar_eq :
          h xStar + (c : EReal) =
            ((xStar ⬝ᵥ (x + t • y) : Real) : EReal) - g xStar := by
        simpa using (congrArg (fun F => F xStar) hterm).symm
      simp [hxStar_eq]
    · rintro ⟨w, ⟨xStar, rfl⟩, rfl⟩
      refine ⟨xStar, ?_⟩
      simpa using (congrArg (fun F => F xStar) hterm)
  -- Take `sSup` of both sides and use that `sSup` commutes with adding a real constant.
  unfold fenchelConjugate
  -- Replace the range using `hrange` and commute `sSup` with addition by `c`.
  have hsSup_range :
      sSup
          (Set.range fun xStar : Fin n → Real =>
            ((xStar ⬝ᵥ (x + t • y) : Real) : EReal) - g xStar) =
        sSup ((fun z : EReal => z + (c : EReal)) '' Set.range h) :=
    congrArg sSup hrange
  calc
    sSup
        (Set.range fun xStar : Fin n → Real =>
          ((xStar ⬝ᵥ (x + t • y) : Real) : EReal) - g xStar) =
        sSup ((fun z : EReal => z + (c : EReal)) '' Set.range h) := hsSup_range
    _ = sSup (Set.range h) + (c : EReal) := section13_sSup_image_add_right c (Set.range h)
    _ = sSup (Set.range h) + ((t * μ : ℝ) : EReal) := by
          simp [c]

/-- For the book’s `orthogonalComplement`, one has `Lᗮ = ⊤` iff `L = ⊥`. -/
lemma section13_orthogonalComplement_eq_top_iff {n : Nat} (L : Submodule ℝ (Fin n → Real)) :
    orthogonalComplement n L = ⊤ ↔ L = ⊥ := by
  constructor
  · intro htop
    apply le_antisymm
    · intro x hx
      have hx' : x ∈ (⊤ : Submodule ℝ (Fin n → Real)) := by simp
      have hxorth : x ∈ orthogonalComplement n L := by simp [htop]
      have : x ⬝ᵥ x = 0 := hxorth x hx
      have : x = 0 := (dotProduct_self_eq_zero).1 this
      simp [this]
    · exact bot_le
  · intro hbot
    ext x
    simp [orthogonalComplement, hbot]

/-- In finite dimension, the book orthogonal complement is involutive: `(Lᗮ)ᗮ = L`. -/
lemma section13_orthogonalComplement_orthogonalComplement_eq {n : Nat}
    (L : Submodule ℝ (Fin n → Real)) :
    orthogonalComplement n (orthogonalComplement n L) = L := by
  classical
  -- First, `L ≤ (Lᗮ)ᗮ`.
  have hle : L ≤ orthogonalComplement n (orthogonalComplement n L) := by
    intro x hx y hy
    have : y ⬝ᵥ x = 0 := hy x hx
    simpa [dotProduct_comm] using this
  -- Then compare dimensions using `dim(Lᗮ) = n - dim(L)`.
  have hL_le : Module.finrank ℝ L ≤ n := by
    simpa [Module.finrank_fin_fun] using
      (Submodule.finrank_le (R := ℝ) (M := (Fin n → Real)) L)
  have hfin :
      Module.finrank ℝ (orthogonalComplement n (orthogonalComplement n L)) =
        Module.finrank ℝ L := by
    calc
      Module.finrank ℝ (orthogonalComplement n (orthogonalComplement n L)) =
          n - Module.finrank ℝ (orthogonalComplement n L) := by
            simpa using (section13_finrank_orthogonalComplement (n := n) (L := orthogonalComplement n L))
      _ = n - (n - Module.finrank ℝ L) := by
            simp [section13_finrank_orthogonalComplement (n := n) (L := L)]
      _ = Module.finrank ℝ L := by
            simp [Nat.sub_sub_self hL_le]
  exact (Submodule.eq_of_le_of_finrank_eq hle hfin.symm).symm

/-- If `dom (f*)` has empty interior, then `linearitySpace f` contains a nonzero direction. -/
lemma section13_exists_nonzero_mem_linearitySpace_of_not_nonempty_interior_dom_fenchelConjugate
    {n : Nat} (f : (Fin n → Real) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hno : ¬ Set.Nonempty
        (interior (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)))) :
    ∃ y : Fin n → Real, y ≠ 0 ∧ y ∈ linearitySpace f := by
  classical
  set domFstar : Set (Fin n → Real) :=
    effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)
  have hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  have hdomFstar_ne : domFstar.Nonempty :=
    section13_effectiveDomain_nonempty_of_proper (n := n) (f := fenchelConjugate n f) hproperStar
  have hconvStar : ConvexFunction (fenchelConjugate n f) :=
    (fenchelConjugate_closedConvex (n := n) (f := f)).2
  have hdomFstar_conv : Convex ℝ domFstar := by
    simpa [domFstar] using
      (effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real))) (f := fenchelConjugate n f)
        (hf := (by simpa [ConvexFunction] using hconvStar)))
  have hspan_ne : affineSpan ℝ domFstar ≠ ⊤ := by
    intro htop
    have : (interior domFstar).Nonempty :=
      (Convex.interior_nonempty_iff_affineSpan_eq_top (V := (Fin n → Real)) hdomFstar_conv).2 htop
    exact hno (by simpa [domFstar] using this)
  have hdir_ne_top : (affineSpan ℝ domFstar).direction ≠ ⊤ := by
    have hne' : ((affineSpan ℝ domFstar : AffineSubspace ℝ (Fin n → Real)) : Set (Fin n → Real)).Nonempty :=
      (affineSpan_nonempty (k := ℝ) (s := domFstar)).2 hdomFstar_ne
    intro hdir
    have : (affineSpan ℝ domFstar : AffineSubspace ℝ (Fin n → Real)) = ⊤ :=
      (AffineSubspace.direction_eq_top_iff_of_nonempty (s := affineSpan ℝ domFstar) hne').1 hdir
    exact hspan_ne (by simpa using this)
  have hmain :=
    (linearitySpace_fenchelConjugate_eq_orthogonal_direction_affineSpan_effectiveDomain_and_dual
        (n := n) (f := f) hproper)
  have hdir :
      (affineSpan ℝ domFstar).direction =
        orthogonalComplement n (Submodule.span ℝ (linearitySpace f)) := by
    simpa [domFstar] using (hmain.2 hclosed).1
  have hspan_linearity_ne :
      Submodule.span ℝ (linearitySpace f) ≠ ⊥ := by
    intro hbot
    have : orthogonalComplement n (Submodule.span ℝ (linearitySpace f)) = ⊤ :=
      (section13_orthogonalComplement_eq_top_iff (n := n)
        (L := Submodule.span ℝ (linearitySpace f))).2 hbot
    exact hdir_ne_top (by simp [hdir, this])
  have hnot_subset : ¬ linearitySpace f ⊆ ({0} : Set (Fin n → Real)) := by
    intro hsub
    have : Submodule.span ℝ (linearitySpace f) = ⊥ := (Submodule.span_eq_bot).2 hsub
    exact hspan_linearity_ne this
  rcases (Set.not_subset.1 hnot_subset) with ⟨y, hy, hy0⟩
  refine ⟨y, ?_, hy⟩
  simpa using hy0

/-- A nonzero direction in `linearitySpace f` yields an affine line along which `f` is finite and
affine. -/
lemma section13_exists_affineLine_of_mem_linearitySpace {n : Nat} (f : (Fin n → Real) → EReal)
    (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {y : Fin n → Real} (hy0 : y ≠ 0) (hy : y ∈ linearitySpace f) :
    ∃ (x y : Fin n → Real),
      y ≠ 0 ∧ ∃ a b : ℝ, ∀ t : ℝ, f (x + t • y) = ((a * t + b : ℝ) : EReal) := by
  classical
  set domFstar : Set (Fin n → Real) :=
    effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)
  have hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  have hdomFstar_ne : domFstar.Nonempty :=
    section13_effectiveDomain_nonempty_of_proper (n := n) (f := fenchelConjugate n f) hproperStar
  have hmain :=
    (linearitySpace_fenchelConjugate_eq_orthogonal_direction_affineSpan_effectiveDomain_and_dual
        (n := n) (f := f) hproper)
  have hdir :
      (affineSpan ℝ domFstar).direction =
        orthogonalComplement n (Submodule.span ℝ (linearitySpace f)) := by
    simpa [domFstar] using (hmain.2 hclosed).1
  have hy_span : y ∈ Submodule.span ℝ (linearitySpace f) := Submodule.subset_span hy
  have hy_orth :
      y ∈ orthogonalComplement n ((affineSpan ℝ domFstar).direction) := by
    -- `y ∈ span(linearitySpace f) = (dir domFstar)ᗮ`.
    have : y ∈ orthogonalComplement n (orthogonalComplement n (Submodule.span ℝ (linearitySpace f))) := by
      simpa [section13_orthogonalComplement_orthogonalComplement_eq (n := n)
        (L := Submodule.span ℝ (linearitySpace f))] using hy_span
    simpa [hdir] using this
  -- Therefore `dotProduct y ·` is constant on `dom f*`.
  rcases
      (section13_dotProduct_const_iff_mem_orthogonalComplement_direction_affineSpan (n := n)
          (C := domFstar) hdomFstar_ne y).2 hy_orth with
    ⟨μ, hμ⟩
  -- Pick a base point `x0 ∈ dom f`.
  rcases (section13_effectiveDomain_nonempty_of_proper (n := n) (f := f) hproper) with ⟨x0, hx0⟩
  have hx0_ne_top : f x0 ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := f) hx0
  have hx0_ne_bot : f x0 ≠ (⊥ : EReal) := hproper.2.2 x0 (by simp)
  -- Use biconjugacy for closed proper convex functions.
  have hcl : clConv n f = f :=
    clConv_eq_of_closedProperConvex (n := n) (f := f) (hf_closed := hclosed.2) (hf_proper := hproper)
  have hbiconj : fenchelConjugate n (fenchelConjugate n f) = f := by
    have : fenchelConjugate n (fenchelConjugate n f) = clConv n f :=
      fenchelConjugate_biconjugate_eq_clConv (n := n) (f := f)
    simpa [hcl] using this
  -- Translate the biconjugate using constancy of `⟪xStar, y⟫` on `dom f*`.
  have htranslate :
      ∀ t : ℝ,
        fenchelConjugate n (fenchelConjugate n f) (x0 + t • y) =
          fenchelConjugate n (fenchelConjugate n f) x0 + ((t * μ : ℝ) : EReal) := by
    intro t
    have hμ' :
        ∀ xStar ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f),
          dotProduct xStar y = μ := by
      intro xStar hxStar
      exact hμ xStar (by simpa [domFstar] using hxStar)
    simpa using
      (section13_fenchelConjugate_translate_of_dotProduct_const (n := n)
        (g := fenchelConjugate n f)
        (hg_bot := fun xStar => hproperStar.2.2 xStar (by simp))
        (y := y) (μ := μ) hμ' x0 t)
  -- Package the affine line using `x0`, `y`, `a = μ`, `b = f x0`.
  refine ⟨x0, y, hy0, ⟨μ, (f x0).toReal, ?_⟩⟩
  intro t
  have hb : (f x0 : EReal) = ((f x0).toReal : EReal) := by
    symm
    simpa using (EReal.coe_toReal hx0_ne_top hx0_ne_bot)
  -- Rewrite `f` as its biconjugate and use `htranslate`.
  have hb_t : fenchelConjugate n (fenchelConjugate n f) (x0 + t • y) = f (x0 + t • y) :=
    by simpa using congrArg (fun g => g (x0 + t • y)) hbiconj
  have hb_0 : fenchelConjugate n (fenchelConjugate n f) x0 = f x0 :=
    by simpa using congrArg (fun g => g x0) hbiconj
  have haff : f (x0 + t • y) = f x0 + ((t * μ : ℝ) : EReal) := by
    simpa [hb_t, hb_0] using (htranslate t)
  have haff' : f (x0 + t • y) = ((f x0).toReal : EReal) + ((t * μ : ℝ) : EReal) := by
    have haff'' := haff
    -- Rewrite `f x0` as `((f x0).toReal : EReal)` without triggering simp loops.
    rw [hb] at haff''
    simpa [add_assoc, add_comm, add_left_comm] using haff''
  -- Convert to the requested affine form.
  calc
    f (x0 + t • y) = ((f x0).toReal : EReal) + ((t * μ : ℝ) : EReal) := haff'
    _ = ((μ * t + (f x0).toReal : ℝ) : EReal) := by
      have h1 :
          ((f x0).toReal : EReal) + ((t * μ : ℝ) : EReal) =
            ((t * μ + (f x0).toReal : ℝ) : EReal) := by
        calc
          ((f x0).toReal : EReal) + ((t * μ : ℝ) : EReal) =
              ((t * μ : ℝ) : EReal) + ((f x0).toReal : EReal) := by
                simp [add_comm]
          _ = ((t * μ + (f x0).toReal : ℝ) : EReal) := by
                simp [EReal.coe_add]
      simp [mul_comm, add_comm]

/-- Corollary 13.4.2. Let `f` be a closed proper convex function. Then `dom f^*` has a non-empty
interior if and only if there are no lines along which `f` is (finite and) affine.

Here `f^*` is the Fenchel conjugate `fenchelConjugate n f`, and `dom f^*` is its effective domain
`effectiveDomain univ (fenchelConjugate n f)`. The absence of a line along which `f` is finite and
affine is expressed by the nonexistence of `x` and a nonzero direction `y` such that
`t ↦ f (x + t • y)` agrees with an affine function of `t`. -/
theorem effectiveDomain_fenchelConjugate_interior_nonempty_iff_not_exists_affineLine {n : Nat}
    (f : (Fin n → Real) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    Set.Nonempty
        (interior (effectiveDomain (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f))) ↔
      ¬ ∃ (x y : Fin n → Real),
          y ≠ 0 ∧ ∃ a b : ℝ, ∀ t : ℝ, f (x + t • y) = ((a * t + b : ℝ) : EReal) := by
  constructor
  · intro hne hline
    exact
      (section13_not_nonempty_interior_dom_fenchelConjugate_of_exists_affineLine (n := n) (f := f)
          (by exact hline))
        hne
  · intro hno
    by_contra hne
    have hline' :
        ∃ y : Fin n → Real, y ≠ 0 ∧ y ∈ linearitySpace f :=
      section13_exists_nonzero_mem_linearitySpace_of_not_nonempty_interior_dom_fenchelConjugate
        (n := n) (f := f) hclosed hproper (by simpa using hne)
    rcases hline' with ⟨y, hy0, hy⟩
    have hline'' :
        ∃ (x y : Fin n → Real),
          y ≠ 0 ∧ ∃ a b : ℝ, ∀ t : ℝ, f (x + t • y) = ((a * t + b : ℝ) : EReal) :=
      section13_exists_affineLine_of_mem_linearitySpace (n := n) (f := f) hclosed hproper hy0 hy
    exact hno hline''

/-- Rewriting a dot-product level set as a `≤ 0` sublevel set by moving affine terms across the
inequality in `EReal`. -/
lemma section13_levelSet_eq_setOf_sub_dotProduct_sub_le_zero {n : Nat}
    (h : (Fin n → Real) → EReal) (bStar : Fin n → Real) (β : ℝ) :
    {x | h x ≤ ((β : ℝ) : EReal) + ((dotProduct x bStar : Real) : EReal)} =
      {x |
        h x - ((dotProduct x bStar : Real) : EReal) - ((β : ℝ) : EReal) ≤ (0 : EReal)} := by
  ext x
  constructor
  · intro hx
    have h1 :
        ((dotProduct x bStar : Real) : EReal) ≠ (⊥ : EReal) ∨
          ((β : ℝ) : EReal) ≠ (⊤ : EReal) := Or.inl (by simp)
    have h2 :
        ((dotProduct x bStar : Real) : EReal) ≠ (⊤ : EReal) ∨
          ((β : ℝ) : EReal) ≠ (⊥ : EReal) := Or.inl (by simp)
    have hx' :
        h x - ((dotProduct x bStar : Real) : EReal) ≤ ((β : ℝ) : EReal) :=
      (EReal.sub_le_iff_le_add h1 h2).2 hx
    have h3 :
        ((β : ℝ) : EReal) ≠ (⊥ : EReal) ∨ (0 : EReal) ≠ (⊤ : EReal) := Or.inl (by simp)
    have h4 :
        ((β : ℝ) : EReal) ≠ (⊤ : EReal) ∨ (0 : EReal) ≠ (⊥ : EReal) := Or.inl (by simp)
    have hx'' :
        (h x - ((dotProduct x bStar : Real) : EReal)) - ((β : ℝ) : EReal) ≤ (0 : EReal) :=
      (EReal.sub_le_iff_le_add h3 h4).2 (by simpa [zero_add] using hx')
    simpa [sub_eq_add_neg, add_assoc] using hx''
  · intro hx
    have h3 :
        ((β : ℝ) : EReal) ≠ (⊥ : EReal) ∨ (0 : EReal) ≠ (⊤ : EReal) := Or.inl (by simp)
    have h4 :
        ((β : ℝ) : EReal) ≠ (⊤ : EReal) ∨ (0 : EReal) ≠ (⊥ : EReal) := Or.inl (by simp)
    have hx'0 :
        h x - ((dotProduct x bStar : Real) : EReal) ≤ (0 : EReal) + ((β : ℝ) : EReal) :=
      (EReal.sub_le_iff_le_add h3 h4).1 hx
    have hx' :
        h x - ((dotProduct x bStar : Real) : EReal) ≤ ((β : ℝ) : EReal) := by
      simpa [zero_add] using hx'0
    have h1 :
        ((dotProduct x bStar : Real) : EReal) ≠ (⊥ : EReal) ∨
          ((β : ℝ) : EReal) ≠ (⊤ : EReal) := Or.inl (by simp)
    have h2 :
        ((dotProduct x bStar : Real) : EReal) ≠ (⊤ : EReal) ∨
          ((β : ℝ) : EReal) ≠ (⊥ : EReal) := Or.inl (by simp)
    exact (EReal.sub_le_iff_le_add h1 h2).1 hx'

/-- Subtracting a real constant from the primal function adds that constant to its Fenchel
conjugate. -/
lemma section13_fenchelConjugate_sub_const {n : Nat} (g : (Fin n → Real) → EReal) (β : ℝ) :
    fenchelConjugate n (fun x => g x - ((β : ℝ) : EReal)) =
      fun xStar => fenchelConjugate n g xStar + ((β : ℝ) : EReal) := by
  classical
  funext xStar
  unfold fenchelConjugate
  set h : (Fin n → Real) → EReal := fun x => ((x ⬝ᵥ xStar : Real) : EReal) - g x
  have hterm :
      (fun x : Fin n → Real =>
          ((x ⬝ᵥ xStar : Real) : EReal) - (g x - ((β : ℝ) : EReal))) =
        fun x : Fin n → Real => h x + ((β : ℝ) : EReal) := by
    funext x
    have hneg : -(g x - ((β : ℝ) : EReal)) = -g x + ((β : ℝ) : EReal) := by
      have h1 : g x ≠ (⊥ : EReal) ∨ ((β : ℝ) : EReal) ≠ (⊥ : EReal) := Or.inr (by simp)
      have h2 : g x ≠ (⊤ : EReal) ∨ ((β : ℝ) : EReal) ≠ (⊤ : EReal) := Or.inr (by simp)
      simpa using (EReal.neg_sub (x := g x) (y := ((β : ℝ) : EReal)) h1 h2)
    calc
      ((x ⬝ᵥ xStar : Real) : EReal) - (g x - ((β : ℝ) : EReal)) =
          ((x ⬝ᵥ xStar : Real) : EReal) + -(g x - ((β : ℝ) : EReal)) := by
            simp [sub_eq_add_neg]
      _ = ((x ⬝ᵥ xStar : Real) : EReal) + (-g x + ((β : ℝ) : EReal)) := by
            simp [hneg]
      _ = h x + ((β : ℝ) : EReal) := by
            simp [h, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hrange :
      Set.range (fun x : Fin n → Real =>
          ((x ⬝ᵥ xStar : Real) : EReal) - (g x - ((β : ℝ) : EReal))) =
        (fun z : EReal => z + ((β : ℝ) : EReal)) '' Set.range h := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨h x, ⟨x, rfl⟩, ?_⟩
      simpa using (congrArg (fun F => F x) hterm).symm
    · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
      refine ⟨x, ?_⟩
      simpa using (congrArg (fun F => F x) hterm)
  calc
    sSup
        (Set.range fun x : Fin n → Real =>
          ((x ⬝ᵥ xStar : Real) : EReal) - (g x - ((β : ℝ) : EReal))) =
        sSup ((fun z : EReal => z + ((β : ℝ) : EReal)) '' Set.range h) := by
          simp [hrange]
    _ = sSup (Set.range h) + ((β : ℝ) : EReal) :=
        section13_sSup_image_add_right (c := β) (s := Set.range h)
    _ =
        sSup
            (Set.range fun x : Fin n → Real =>
              ((x ⬝ᵥ xStar : Real) : EReal) - g x) +
          ((β : ℝ) : EReal) := by
        rfl

/-- Text 13.4.3: Let `h : ℝ^n → (-∞, +∞]` be a proper convex function, let `bStar ∈ ℝ^n`, and let
`β ∈ ℝ`. Define the level set `C := {x | h x ≤ β + ⟪x, bStar⟫}` and the shifted function
`f x := h x - ⟪x, bStar⟫ - β`. Then `C = {x | f x ≤ 0}`. Moreover, the Fenchel conjugate of `f`
satisfies `f^*(xStar) = h^*(xStar + bStar) + β` for all `xStar ∈ ℝ^n`. -/
theorem levelSet_le_add_dotProduct_eq_setOf_sub_dotProduct_sub_le_zero_and_fenchelConjugate
    {n : Nat} (h : (Fin n → Real) → EReal)
    (bStar : Fin n → Real) (β : ℝ) :
    (let C : Set (Fin n → Real) :=
        {x | h x ≤ ((β : ℝ) : EReal) + ((dotProduct x bStar : Real) : EReal)}
      let f : (Fin n → Real) → EReal :=
        fun x => h x - ((dotProduct x bStar : Real) : EReal) - ((β : ℝ) : EReal)
      C = {x | f x ≤ (0 : EReal)} ∧
        ∀ xStar : Fin n → Real,
          fenchelConjugate n f xStar =
            fenchelConjugate n h (xStar + bStar) + ((β : ℝ) : EReal)) := by
  classical
  dsimp
  refine ⟨?_, ?_⟩
  · simpa using
      (section13_levelSet_eq_setOf_sub_dotProduct_sub_le_zero (n := n) (h := h) (bStar := bStar)
        (β := β))
  · intro xStar
    -- Split off the constant `β` and use the dot-product translation formula for conjugates.
    set g : (Fin n → Real) → EReal :=
      fun x => h x - ((dotProduct x bStar : Real) : EReal)
    have hg :
        fenchelConjugate n g = fun yStar => fenchelConjugate n h (yStar + bStar) := by
      simpa [g] using
        (section13_fenchelConjugate_sub_dotProduct (n := n) (f := h) (xStar := bStar))
    have hβ :
        fenchelConjugate n (fun x => g x - ((β : ℝ) : EReal)) xStar =
          fenchelConjugate n g xStar + ((β : ℝ) : EReal) := by
      simpa using
        congrArg (fun F : (Fin n → Real) → EReal => F xStar)
          (section13_fenchelConjugate_sub_const (n := n) (g := g) (β := β))
    have hg' : fenchelConjugate n g xStar = fenchelConjugate n h (xStar + bStar) := by
      simpa using congrArg (fun F : (Fin n → Real) → EReal => F xStar) hg
    calc
      fenchelConjugate n
          (fun x => h x - ((dotProduct x bStar : Real) : EReal) - ((β : ℝ) : EReal)) xStar =
          fenchelConjugate n (fun x => g x - ((β : ℝ) : EReal)) xStar := by
            simp [g]
      _ = fenchelConjugate n g xStar + ((β : ℝ) : EReal) := hβ
      _ = fenchelConjugate n h (xStar + bStar) + ((β : ℝ) : EReal) := by
            simp [hg']

/-- The linear functional `x ↦ ⟪x, xStar⟫` is positively homogeneous when viewed as an
`EReal`-valued function. -/
lemma section13_posHom_dotProduct {n : Nat} (xStar : Fin n → Real) :
    PositivelyHomogeneous (fun x : Fin n → Real => ((dotProduct x xStar : Real) : EReal)) := by
  intro x t _ht
  simp [smul_eq_mul, EReal.coe_mul]

/-- The linear functional `x ↦ ⟪x, xStar⟫` is convex on `ℝ^n` (its epigraph is a half-space). -/
lemma section13_convexFunctionOn_dotProduct {n : Nat} (xStar : Fin n → Real) :
    ConvexFunctionOn (Set.univ : Set (Fin n → Real))
      (fun x : Fin n → Real => ((dotProduct x xStar : Real) : EReal)) := by
  -- Show the epigraph is convex by a direct calculation.
  unfold ConvexFunctionOn epigraph
  intro p hp q hq a b ha hb hab
  refine And.intro (by trivial) ?_
  have hp' : dotProduct p.1 xStar ≤ p.2 := by
    simpa [EReal.coe_le_coe_iff] using hp.2
  have hq' : dotProduct q.1 xStar ≤ q.2 := by
    simpa [EReal.coe_le_coe_iff] using hq.2
  have hp'' : a * dotProduct p.1 xStar ≤ a * p.2 :=
    mul_le_mul_of_nonneg_left hp' ha
  have hq'' : b * dotProduct q.1 xStar ≤ b * q.2 :=
    mul_le_mul_of_nonneg_left hq' hb
  have hadd :
      a * dotProduct p.1 xStar + b * dotProduct q.1 xStar ≤ a * p.2 + b * q.2 :=
    add_le_add hp'' hq''
  have hcomb : dotProduct ((a • p + b • q).1) xStar ≤ (a • p + b • q).2 := by
    simpa [dotProduct_add, dotProduct_smul, smul_eq_mul, add_assoc, add_comm, add_left_comm,
      mul_assoc, mul_comm, mul_left_comm] using hadd
  exact (EReal.coe_le_coe_iff.2 hcomb)

/-- Majorants of the positively homogeneous hull coincide with majorants of the original
convex function. -/
lemma section13_setOf_forall_dotProduct_le_posHomGenerated_eq {n : Nat}
    {f : (Fin n → Real) → EReal} (hf : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    let k := positivelyHomogeneousConvexFunctionGenerated f
    {xStar : Fin n → Real |
        ∀ x : Fin n → Real, ((dotProduct x xStar : Real) : EReal) ≤ k x} =
      {xStar : Fin n → Real |
        ∀ x : Fin n → Real, ((dotProduct x xStar : Real) : EReal) ≤ f x} := by
  classical
  intro k
  have hkmax :
      (∃ C : ConvexCone ℝ ((Fin n → Real) × Real),
        (C : Set ((Fin n → Real) × Real)) =
          epigraph (Set.univ : Set (Fin n → Real)) k ∧
        (0 : (Fin n → Real) × Real) ∈ epigraph (Set.univ : Set (Fin n → Real)) k) ∧
        (ConvexFunctionOn (Set.univ : Set (Fin n → Real)) k ∧ PositivelyHomogeneous k ∧
          k 0 ≤ 0 ∧ k ≤ f) ∧
          (∀ u : (Fin n → Real) → EReal,
            PositivelyHomogeneous u →
              ConvexFunctionOn (Set.univ : Set (Fin n → Real)) u →
                u 0 ≤ 0 → u ≤ f → u ≤ k) := by
    simpa [k] using (maximality_posHomogeneousHull (n := n) (h := f) hf)
  have hk_le : k ≤ f := hkmax.2.1.2.2.2
  have hk_greatest := hkmax.2.2
  ext xStar
  constructor
  · intro hx x
    exact le_trans (hx x) (hk_le x)
  · intro hx x
    let u : (Fin n → Real) → EReal := fun y => ((dotProduct y xStar : Real) : EReal)
    have hu_pos : PositivelyHomogeneous u :=
      section13_posHom_dotProduct (n := n) xStar
    have hu_conv : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) u :=
      section13_convexFunctionOn_dotProduct (n := n) xStar
    have hu0 : u 0 ≤ 0 := by simp [u]
    have hu_le : u ≤ f := by
      intro y
      simpa [u] using hx y
    have hu_le_k : u ≤ k := hk_greatest u hu_pos hu_conv hu0 hu_le
    simpa [u] using hu_le_k x

/-- The closed positively homogeneous hull of a closed proper convex function `f` is the support
function of the polar set `{xStar | f*(xStar) ≤ 0}`. -/
lemma section13_clConv_posHomGenerated_eq_supportFunctionEReal_setOf_fenchelConjugate_le_zero
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    clConv n (positivelyHomogeneousConvexFunctionGenerated f) =
      supportFunctionEReal {xStar : Fin n → Real | fenchelConjugate n f xStar ≤ (0 : EReal)} := by
  classical
  set k : (Fin n → Real) → EReal := positivelyHomogeneousConvexFunctionGenerated f
  have hfconv : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
    simpa [ConvexFunction] using hf_closed.1
  have hkmax :
      (∃ C : ConvexCone ℝ ((Fin n → Real) × Real),
        (C : Set ((Fin n → Real) × Real)) =
          epigraph (Set.univ : Set (Fin n → Real)) k ∧
        (0 : (Fin n → Real) × Real) ∈ epigraph (Set.univ : Set (Fin n → Real)) k) ∧
        (ConvexFunctionOn (Set.univ : Set (Fin n → Real)) k ∧ PositivelyHomogeneous k ∧
          k 0 ≤ 0 ∧ k ≤ f) ∧
          (∀ u : (Fin n → Real) → EReal,
            PositivelyHomogeneous u →
              ConvexFunctionOn (Set.univ : Set (Fin n → Real)) u →
                u 0 ≤ 0 → u ≤ f → u ≤ k) := by
    simpa [k] using (maximality_posHomogeneousHull (n := n) (h := f) hfconv)
  have hk_pos : PositivelyHomogeneous k := hkmax.2.1.2.1
  have hk_conv : ConvexFunction k := by
    simpa [ConvexFunction] using hkmax.2.1.1
  have hk_le : k ≤ f := hkmax.2.1.2.2.2
  have hnotTop : ¬ (∀ x : Fin n → Real, k x = ⊤) := by
    rcases hf_proper.2.1 with ⟨p, hp⟩
    have hp2 : f p.1 ≤ (p.2 : EReal) := hp.2
    have hf_ne_top : f p.1 ≠ (⊤ : EReal) := by
      intro htop
      have hp2' := hp2
      simp [htop] at hp2'
    have hk_ne_top : k p.1 ≠ (⊤ : EReal) := by
      intro hkt
      have : (⊤ : EReal) ≤ f p.1 := by
        simpa [hkt] using (hk_le p.1)
      exact hf_ne_top (top_le_iff.mp this)
    intro hall
    exact hk_ne_top (hall p.1)
  obtain ⟨C, _hCclosed, _hCconv, hcl, hCeq⟩ :=
    clConv_eq_supportFunctionEReal_setOf_forall_dotProduct_le (n := n) k hk_pos hk_conv hnotTop
  have hCeq' :
      C = {xStar : Fin n → Real | fenchelConjugate n f xStar ≤ (0 : EReal)} := by
    calc
      C =
          {xStar : Fin n → Real |
            ∀ x : Fin n → Real, ((dotProduct x xStar : Real) : EReal) ≤ k x} := hCeq
      _ =
          {xStar : Fin n → Real |
            ∀ x : Fin n → Real, ((dotProduct x xStar : Real) : EReal) ≤ f x} := by
          simpa [k] using
            (section13_setOf_forall_dotProduct_le_posHomGenerated_eq (n := n) (f := f) hfconv)
      _ = {xStar : Fin n → Real | fenchelConjugate n f xStar ≤ (0 : EReal)} := by
          simpa using
            (section13_setOf_forall_dotProduct_le_eq_setOf_fenchelConjugate_le_zero (n := n) f)
  simpa [hCeq', k] using hcl

/-- The support function of the `0`-sublevel set of `f` is the closed positively homogeneous hull
of `f*`. -/
lemma section13_supportFunctionEReal_setOf_le_zero_eq_clConv_posHomGenerated_fenchelConjugate
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    supportFunctionEReal {x : Fin n → Real | f x ≤ (0 : EReal)} =
      clConv n (positivelyHomogeneousConvexFunctionGenerated (fenchelConjugate n f)) := by
  classical
  have hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hf_proper
  have hclosedStar : ClosedConvexFunction (fenchelConjugate n f) :=
    ⟨(fenchelConjugate_closedConvex (n := n) (f := f)).2,
      (fenchelConjugate_closedConvex (n := n) (f := f)).1⟩
  have hdual :
      clConv n (positivelyHomogeneousConvexFunctionGenerated (fenchelConjugate n f)) =
        supportFunctionEReal
            {xStar : Fin n → Real |
              fenchelConjugate n (fenchelConjugate n f) xStar ≤ (0 : EReal)} :=
    section13_clConv_posHomGenerated_eq_supportFunctionEReal_setOf_fenchelConjugate_le_zero
      (n := n) (f := fenchelConjugate n f) hclosedStar hproperStar
  have hcl : clConv n f = f :=
    clConv_eq_of_closedProperConvex (n := n) (f := f) (hf_closed := hf_closed.2)
      (hf_proper := hf_proper)
  have hset :
      {xStar : Fin n → Real | fenchelConjugate n (fenchelConjugate n f) xStar ≤ (0 : EReal)} =
        {xStar : Fin n → Real | f xStar ≤ (0 : EReal)} := by
    ext xStar
    have hbiconj :
        fenchelConjugate n (fenchelConjugate n f) = clConv n f := by
      simpa using (fenchelConjugate_biconjugate_eq_clConv (n := n) (f := f))
    simp [hbiconj, hcl]
  simpa [hset] using hdual.symm

/-- Theorem 13.5. Let `f` be a closed proper convex function. The support function of
`{ x | f x ≤ 0 }` is `cl g`, where `g` is the positively homogeneous convex function generated by
`f*`. Dually, the closure of the positively homogeneous convex function `k` generated by `f` is
the support function of `{ xStar | f*(xStar) ≤ 0 }`.

Here `f*` is the Fenchel conjugate `fenchelConjugate n f`; the support function is represented by
`supportFunctionEReal`; the closure `cl` is represented by `clConv n`; and the positively
homogeneous convex function generated by a function `h` is
`positivelyHomogeneousConvexFunctionGenerated h`. -/
theorem supportFunctionEReal_setOf_le_zero_eq_clConv_posHomGenerated_fenchelConjugate_and_dual
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    supportFunctionEReal {x : Fin n → Real | f x ≤ (0 : EReal)} =
        clConv n (positivelyHomogeneousConvexFunctionGenerated (fenchelConjugate n f)) ∧
      clConv n (positivelyHomogeneousConvexFunctionGenerated f) =
        supportFunctionEReal {xStar : Fin n → Real | fenchelConjugate n f xStar ≤ (0 : EReal)} := by
  refine ⟨?_, ?_⟩
  · simpa using
      (section13_supportFunctionEReal_setOf_le_zero_eq_clConv_posHomGenerated_fenchelConjugate
        (n := n) (f := f) hf_closed hf_proper)
  · simpa using
      (section13_clConv_posHomGenerated_eq_supportFunctionEReal_setOf_fenchelConjugate_le_zero
        (n := n) (f := f) hf_closed hf_proper)

end Section13
end Chap03
