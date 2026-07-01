/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Zhiyan Wang, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section12_part10

section Chap03
section Section12

/-- `EReal`-valued monotone conjugate for an `EReal`-valued function on `ℝ^n_+` (modeled as
`Fin n → NNReal`). This version allows the input function to take the value `⊤`, so it can be
iterated. -/
noncomputable def monotoneConjugateERealEReal (n : Nat) (g : (Fin n → NNReal) → EReal) :
    (Fin n → NNReal) → EReal :=
  fun yStar =>
    sSup <|
      Set.range fun y : Fin n → NNReal =>
        (((fun i => (y i : Real)) ⬝ᵥ (fun i => (yStar i : Real)) : Real) : EReal) - g y

/-- Theorem 12.4. Let `g` be a non-decreasing lower semicontinuous convex function on the
nonnegative orthant `ℝ^n_+` (modeled as `Fin n → NNReal`) such that `g 0` is finite.

Then the monotone conjugate `g⁺` (here `g⁺ = monotoneConjugateEReal n g`) has the same properties, and
the monotone conjugate of `g⁺` is `g` (as an `EReal`-valued function). -/
theorem monotoneConjugate_properties_and_involutive (n : Nat) (g : (Fin n → NNReal) → Real)
    (hg_mono : Monotone g) (hg_lsc : LowerSemicontinuous g)
    (hg_convex : ConvexOn NNReal (Set.univ : Set (Fin n → NNReal)) g) (hg0 : ∃ c : Real, g 0 = c) :
    let gPlus : (Fin n → NNReal) → EReal := monotoneConjugateEReal n g
    (Monotone gPlus ∧ LowerSemicontinuous gPlus ∧
        (∀ x y : Fin n → NNReal, ∀ a b : NNReal, a + b = 1 →
          gPlus (a • x + b • y) ≤ ((a : Real) : EReal) * gPlus x + ((b : Real) : EReal) * gPlus y) ∧
          ∃ c : Real, gPlus 0 = (c : EReal)) ∧
      monotoneConjugateERealEReal n gPlus = fun y => (g y : EReal) := by
  classical
  intro gPlus
  -- `gPlus` is monotone since the dot product is monotone in the second argument on `ℝ^n_+`.
  have hgPlus_mono : Monotone gPlus := by
    intro yStar yStar' hyStar
    -- compare suprema pointwise
    refine sSup_le ?_
    rintro z ⟨y, rfl⟩
    have hdot :
        ((fun i => (y i : Real)) ⬝ᵥ (fun i => (yStar i : Real)) : Real) ≤
          ((fun i => (y i : Real)) ⬝ᵥ (fun i => (yStar' i : Real)) : Real) := by
      classical
      -- unfold the dot product and use termwise monotonicity
      simp [dotProduct]
      refine Finset.sum_le_sum ?_
      intro i _hi
      have hyi : 0 ≤ (y i : Real) := (y i).property
      have hyStar_i : (yStar i : Real) ≤ (yStar' i : Real) := by
        exact_mod_cast hyStar i
      exact mul_le_mul_of_nonneg_left hyStar_i hyi
    have hdotE : (((fun i => (y i : Real)) ⬝ᵥ (fun i => (yStar i : Real)) : Real) : EReal) ≤
        (((fun i => (y i : Real)) ⬝ᵥ (fun i => (yStar' i : Real)) : Real) : EReal) := by
      exact_mod_cast hdot
    have :
        (((fun i => (y i : Real)) ⬝ᵥ (fun i => (yStar i : Real)) : Real) : EReal) - (g y : EReal) ≤
          (((fun i => (y i : Real)) ⬝ᵥ (fun i => (yStar' i : Real)) : Real) : EReal) - (g y : EReal) := by
      simpa using EReal.sub_le_sub hdotE le_rfl
    exact le_trans this (le_sSup ⟨y, rfl⟩)

  -- `gPlus` is lower semicontinuous as a restriction of a Fenchel conjugate.
  have hgPlus_lsc : LowerSemicontinuous gPlus := by
    let f : (Fin n → Real) → EReal := fun x => (g (absVecNN n x) : EReal)
    have hfStar_lsc : LowerSemicontinuous (fenchelConjugate n f) :=
      (fenchelConjugate_closedConvex (n := n) (f := f)).1
    have hcomp :
        LowerSemicontinuous (fun yStar : Fin n → NNReal => fenchelConjugate n f (fun i => (yStar i : Real))) :=
      hfStar_lsc.comp_continuous (continuous_coeVecNN n)
    have hEq :
        (fun yStar : Fin n → NNReal => fenchelConjugate n f (fun i => (yStar i : Real))) = gPlus := by
      funext yStar
      have hconj :=
        (fenchelConjugate_abs_comp_eq_monotoneConjugate (n := n) (g := g))
          (xStar := fun i => (yStar i : Real))
      -- `absVecNN` of a nonnegative vector is itself.
      simpa [f, gPlus, absVecNN_coe (n := n) (y := yStar)] using hconj
    simpa [hEq] using hcomp

  -- A convexity inequality for `gPlus` on `ℝ^n_+`, phrased using multiplication in `EReal`.
  have hgPlus_conv :
      ∀ x y : Fin n → NNReal, ∀ a b : NNReal, a + b = 1 →
        gPlus (a • x + b • y) ≤ ((a : Real) : EReal) * gPlus x + ((b : Real) : EReal) * gPlus y := by
    intro x y a b hab
    -- Reduce to convexity of `fenchelConjugate n f` on `ℝ^n`.
    let f : (Fin n → Real) → EReal := fun x => (g (absVecNN n x) : EReal)
    have hfStar_conv : ConvexFunction (fenchelConjugate n f) :=
      (fenchelConjugate_closedConvex (n := n) (f := f)).2
    have hf_top : ∃ x0 : Fin n → Real, f x0 ≠ (⊤ : EReal) := by
      refine ⟨0, ?_⟩
      simp [f]
    have hfStar_notbot : ∀ xStar ∈ (Set.univ : Set (Fin n → Real)), fenchelConjugate n f xStar ≠ (⊥ : EReal) := by
      intro xStar _hxStar
      exact fenchelConjugate_ne_bot_of_exists_ne_top (n := n) (f := f) hf_top xStar
    have hfStar_seg :=
      (convexFunctionOn_iff_segment_inequality (C := (Set.univ : Set (Fin n → Real)))
          (f := fenchelConjugate n f) (hC := convex_univ) (hnotbot := hfStar_notbot)).1
        (by simpa [ConvexFunction] using hfStar_conv)
    -- Convert `a,b : NNReal` into a segment parameter `t = b`.
    by_cases hb0 : b = 0
    · have ha1 : a = 1 := by simpa [hb0] using hab
      subst ha1; subst hb0
      simp
    by_cases hb1 : b = 1
    · have ha0 : a = 0 := by simpa [hb1] using hab
      subst ha0; subst hb1
      simp
    have hb_le1 : b ≤ (1 : NNReal) := by
      have : b ≤ a + b := le_add_of_nonneg_left (by simp)
      simpa [hab] using this
    have hb_lt1 : (b : Real) < 1 := by
      have : b < 1 := lt_of_le_of_ne hb_le1 hb1
      exact_mod_cast this
    have hb_pos : (0 : Real) < b := by
      have : (0 : NNReal) < b := lt_of_le_of_ne (by simp) (Ne.symm hb0)
      exact_mod_cast this
    -- Apply the segment inequality to the coerced vectors.
    let xR : Fin n → Real := fun i => (x i : Real)
    let yR : Fin n → Real := fun i => (y i : Real)
    have haR : (a : Real) = 1 - (b : Real) := by
      have habR : (a : Real) + (b : Real) = 1 := by exact_mod_cast hab
      nlinarith
    let z : Fin n → NNReal := a • x + b • y
    let zR : Fin n → Real := fun i => (z i : Real)
    have hcomb : (1 - (b : Real)) • xR + (b : Real) • yR = zR := by
      ext i
      simp [xR, yR, z, zR, haR, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hseg :=
      hfStar_seg xR (by simp) yR (by simp) (b : Real) hb_pos hb_lt1
    have hx : fenchelConjugate n f xR = gPlus x := by
      have hconj :=
        (fenchelConjugate_abs_comp_eq_monotoneConjugate (n := n) (g := g)) (xStar := xR)
      -- `absVecNN n xR = x` since `x` is already nonnegative.
      simpa [f, gPlus, xR, absVecNN_coe (n := n) (y := x)] using hconj
    have hy : fenchelConjugate n f yR = gPlus y := by
      have hconj :=
        (fenchelConjugate_abs_comp_eq_monotoneConjugate (n := n) (g := g)) (xStar := yR)
      simpa [f, gPlus, yR, absVecNN_coe (n := n) (y := y)] using hconj
    have hz : fenchelConjugate n f zR = gPlus z := by
      have hconj :=
        (fenchelConjugate_abs_comp_eq_monotoneConjugate (n := n) (g := g))
          (xStar := zR)
      simpa [f, gPlus, zR, absVecNN_coe (n := n) (y := z)] using hconj
    -- Rewrite the convexity inequality.
    have hseg' :
        fenchelConjugate n f zR ≤
          ((1 - (b : Real) : Real) : EReal) * fenchelConjugate n f xR + ((b : Real) : EReal) * fenchelConjugate n f yR := by
      simpa [hcomb] using hseg
    have hE :
        gPlus z ≤ ((1 - (b : Real) : Real) : EReal) * gPlus x + ((b : Real) : EReal) * gPlus y := by
      simpa [hx, hy, hz] using hseg'
    simpa [z, haR] using hE

  -- `gPlus 0` is a real value, namely `- g 0`.
  have hgPlus0 : ∃ c : Real, gPlus 0 = (c : EReal) := by
    rcases hg0 with ⟨c0, hc0⟩
    refine ⟨-c0, ?_⟩
    -- show the supremum is `-g 0`
    have hge0 : ∀ y : Fin n → NNReal, g 0 ≤ g y := by
      intro y
      refine hg_mono ?_
      intro i
      exact (y i).property
    have hle :
        gPlus 0 ≤ (-c0 : EReal) := by
      -- every term is bounded above by `-g 0`
      refine sSup_le ?_
      rintro z ⟨y, rfl⟩
      have : (g y : EReal) ≥ (g 0 : EReal) := by
        exact_mod_cast (hge0 y)
      -- dot product is zero when `yStar = 0`
      have hdot0 :
          (((fun i => (y i : Real)) ⬝ᵥ (fun _ : Fin n => (0 : Real)) : Real) : EReal) = 0 := by
        simp [dotProduct]
      -- `0 - g y ≤ 0 - g 0`
      have hsub : (0 : EReal) - (g y : EReal) ≤ (0 : EReal) - (g 0 : EReal) := by
        simpa using
          (EReal.sub_le_sub (x := (0 : EReal)) (y := 0) (z := (g y : EReal)) (t := (g 0 : EReal))
            (le_rfl : (0 : EReal) ≤ 0) this)
      simpa [gPlus, monotoneConjugateEReal, hdot0, hc0] using hsub
    have hge :
        (-c0 : EReal) ≤ gPlus 0 := by
      -- use the witness `y = 0`
      have : ((0 : EReal) - (g 0 : EReal)) ∈
          Set.range (fun y : Fin n → NNReal =>
            (((fun i => (y i : Real)) ⬝ᵥ (fun _ : Fin n => (0 : Real)) : Real) : EReal) - (g y : EReal)) := by
        refine ⟨0, ?_⟩
        simp [dotProduct]
      have : (0 : EReal) - (g 0 : EReal) ≤ gPlus 0 := by
        exact le_sSup this
      simpa [gPlus, monotoneConjugateEReal, hc0] using this
    exact le_antisymm hle hge

  have hprops :
      (Monotone gPlus ∧ LowerSemicontinuous gPlus ∧
          (∀ x y : Fin n → NNReal, ∀ a b : NNReal, a + b = 1 →
            gPlus (a • x + b • y) ≤ ((a : Real) : EReal) * gPlus x + ((b : Real) : EReal) * gPlus y) ∧
            ∃ c : Real, gPlus 0 = (c : EReal)) := by
    refine ⟨hgPlus_mono, hgPlus_lsc, hgPlus_conv, hgPlus0⟩

  -- Biconjugation on the orthant: reduce to Fenchel biconjugation of `f(x) = g(|x|)`.
  have hbiconj :
      let f : (Fin n → Real) → EReal := fun x => (g (absVecNN n x) : EReal)
      fenchelConjugate n (fenchelConjugate n f) = f := by
    intro f
    have hf_props :
        LowerSemicontinuous f ∧ ConvexFunction f ∧ ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
      simpa [f] using (closedProperConvex_abs_comp_iff (n := n) (g := g)).2
        ⟨hg_lsc, hg_convex, hg0, hg_mono⟩
    have hf_ne_bot : ∀ x : Fin n → Real, f x ≠ (⊥ : EReal) := by
      intro x
      simp [f]
    exact
      fenchelConjugate_biconjugate_eq_of_closedConvex (n := n) (f := f) (hf_closed := hf_props.1)
        (hf_convex := hf_props.2.1) (hf_ne_bot := hf_ne_bot)

  have hbiconj_apply :
      ∀ y : Fin n → NNReal,
        monotoneConjugateERealEReal n gPlus y = (g y : EReal) := by
    intro y
    let f : (Fin n → Real) → EReal := fun x => (g (absVecNN n x) : EReal)
    have hb : fenchelConjugate n (fenchelConjugate n f) = f := by
      simpa [f] using hbiconj
    -- Evaluate the Fenchel biconjugate at the nonnegative vector `y`.
    have hb_at :
        fenchelConjugate n (fenchelConjugate n f) (fun i => (y i : Real)) = (g y : EReal) := by
      have : f (fun i => (y i : Real)) = (g y : EReal) := by
        simp [f, absVecNN_coe (n := n) (y := y)]
      simpa [this] using congrArg (fun h => h (fun i => (y i : Real))) hb
    -- Rewrite the left-hand side as a supremum over the orthant.
    have hLHS :
        fenchelConjugate n (fenchelConjugate n f) (fun i => (y i : Real)) =
          monotoneConjugateERealEReal n gPlus y := by
      classical
      let yR : Fin n → Real := fun i => (y i : Real)
      -- First, rewrite `f*` using Theorem 12.3.6 (2).
      have hconj : ∀ xStar : Fin n → Real, fenchelConjugate n f xStar = gPlus (absVecNN n xStar) := by
        intro xStar
        have h :=
          (fenchelConjugate_abs_comp_eq_monotoneConjugate (n := n) (g := g)) (xStar := xStar)
        simpa [f, gPlus] using h
      -- Unfold the outer Fenchel conjugate (but not the inner one) and `monotoneConjugateERealEReal`.
      change
        sSup
            (Set.range fun xStar : Fin n → Real =>
              ((xStar ⬝ᵥ yR : Real) : EReal) - fenchelConjugate n f xStar) =
          sSup
            (Set.range fun yStar : Fin n → NNReal =>
              (((fun i => (yStar i : Real)) ⬝ᵥ yR : Real) : EReal) - gPlus yStar)
      apply le_antisymm
      · refine sSup_le ?_
        rintro z ⟨xStar, rfl⟩
        -- rewrite `f*` in the integrand
        have hx : fenchelConjugate n f xStar = gPlus (absVecNN n xStar) := hconj xStar
        -- bound `xStar ⬝ᵥ yR` by `|xStar| ⬝ᵥ yR`
        have hdot :
            (xStar ⬝ᵥ yR : Real) ≤ (fun i => |xStar i|) ⬝ᵥ yR := by
          -- commute to put the nonnegative vector on the left
          have hdot' : (yR ⬝ᵥ xStar : Real) ≤ yR ⬝ᵥ (fun i => |xStar i|) := by
            classical
            simp [dotProduct]
            refine Finset.sum_le_sum ?_
            intro i _hi
            have hyi : 0 ≤ yR i := (y i).property
            exact mul_le_mul_of_nonneg_left (le_abs_self _) hyi
          simpa [dotProduct_comm] using hdot'
        have hdotE :
            ((xStar ⬝ᵥ yR : Real) : EReal) ≤ (((fun i => |xStar i|) ⬝ᵥ yR : Real) : EReal) := by
          exact_mod_cast hdot
        set yStar : Fin n → NNReal := absVecNN n xStar
        have hterm :
            ((xStar ⬝ᵥ yR : Real) : EReal) - gPlus yStar ≤
              (((fun i => |xStar i|) ⬝ᵥ yR : Real) : EReal) - gPlus yStar := by
          simpa using EReal.sub_le_sub hdotE le_rfl
        have hmem :
            (((fun i => (yStar i : Real)) ⬝ᵥ yR : Real) : EReal) - gPlus yStar ∈
              Set.range (fun yStar : Fin n → NNReal =>
                (((fun i => (yStar i : Real)) ⬝ᵥ yR : Real) : EReal) - gPlus yStar) := by
          exact ⟨yStar, rfl⟩
        have hsSup :
            (((fun i => (yStar i : Real)) ⬝ᵥ yR : Real) : EReal) - gPlus yStar ≤
              sSup
                (Set.range fun yStar : Fin n → NNReal =>
                  (((fun i => (yStar i : Real)) ⬝ᵥ yR : Real) : EReal) - gPlus yStar) :=
          le_sSup hmem
        have habs :
            (((fun i => |xStar i|) ⬝ᵥ yR : Real) : EReal) - gPlus yStar ≤
              sSup
                (Set.range fun yStar : Fin n → NNReal =>
                  (((fun i => (yStar i : Real)) ⬝ᵥ yR : Real) : EReal) - gPlus yStar) := by
          -- rewrite `|xStar|` as the coercion of `absVecNN n xStar`
          simpa [yStar, absVecNN] using hsSup
        -- combine everything
        simpa [hx, yStar] using le_trans hterm habs
      · refine sSup_le ?_
        rintro z ⟨yStar, rfl⟩
        -- choose `xStar = yStar` (coerced to `Real`)
        let xStar : Fin n → Real := fun i => (yStar i : Real)
        have hx : fenchelConjugate n f xStar = gPlus yStar := by
          simpa [xStar, absVecNN_coe (n := n) (y := yStar)] using (hconj xStar)
        have hmem :
            ((xStar ⬝ᵥ yR : Real) : EReal) - fenchelConjugate n f xStar ∈
              Set.range (fun xStar : Fin n → Real =>
                ((xStar ⬝ᵥ yR : Real) : EReal) - fenchelConjugate n f xStar) := by
          exact ⟨xStar, rfl⟩
        have : ((xStar ⬝ᵥ yR : Real) : EReal) - fenchelConjugate n f xStar ≤
            sSup
              (Set.range fun xStar : Fin n → Real =>
                ((xStar ⬝ᵥ yR : Real) : EReal) - fenchelConjugate n f xStar) :=
          le_sSup hmem
        simpa [xStar, hx] using this
    exact hLHS.symm.trans hb_at

  refine ⟨hprops, ?_⟩
  funext y
  exact hbiconj_apply y

end Section12
end Chap03
