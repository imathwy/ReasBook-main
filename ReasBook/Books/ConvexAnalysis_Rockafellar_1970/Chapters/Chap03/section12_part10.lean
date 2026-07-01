/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Zhiyan Wang, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section12_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section12_part9

section Chap03
section Section12

/- Text 12.3.5: For a radial function `f x = g (‖x‖)`, closed proper convexity of `f` is
equivalent to the conditions (1)–(4) on `g` along the nonnegative ray `{r | 0 ≤ r 0}` in `ℝ`. -/

/-- If `g` is monotone on `nonnegRay` and `g 0` is finite, then `x ↦ g (euclidNorm n x)` never
takes the value `⊥`. -/
lemma radial_ne_bot_of_mono_g0_finite {n : Nat} {g : (Fin 1 → Real) → EReal}
    (hg_mono : MonotoneOn g (nonnegRay))
    (hg0 : ∃ c : Real, g 0 = (c : EReal)) :
    ∀ x : Fin n → Real, g (fun _ : Fin 1 => euclidNorm n x) ≠ (⊥ : EReal) := by
  intro x hx
  rcases hg0 with ⟨c, hc⟩
  have h0mem : (0 : Fin 1 → Real) ∈ nonnegRay := by simp [nonnegRay]
  have hrmem : (fun _ : Fin 1 => euclidNorm n x) ∈ nonnegRay := by
    simp [nonnegRay, euclidNorm]
  have hle : g 0 ≤ g (fun _ : Fin 1 => euclidNorm n x) := by
    refine hg_mono h0mem hrmem ?_
    intro i
    fin_cases i
    simp [euclidNorm]
  have h0eq : g 0 = (⊥ : EReal) := by
    have : g 0 ≤ (⊥ : EReal) := by simpa [hx] using hle
    exact le_bot_iff.1 this
  have h0ne : (g 0) ≠ (⊥ : EReal) := by simp [hc]
  exact h0ne h0eq

/-- Convexity of the radial composition `x ↦ g (‖x‖)` from convexity and monotonicity of `g`
on the nonnegative ray, assuming `g 0` is finite. -/
lemma radial_convex_of_convexOn_monoOn (n : Nat) {g : (Fin 1 → Real) → EReal}
    (hg_conv : ConvexFunctionOn (nonnegRay) g)
    (hg_mono : MonotoneOn g (nonnegRay))
    (hg0 : ∃ c : Real, g 0 = (c : EReal)) :
    let f : (Fin n → Real) → EReal := fun x => g (fun _ : Fin 1 => euclidNorm n x)
    ConvexFunction f := by
  classical
  intro f
  have hnotbot_f : ∀ x ∈ (Set.univ : Set (Fin n → Real)), f x ≠ (⊥ : EReal) := by
    intro x hx
    simpa [f] using (radial_ne_bot_of_mono_g0_finite (n := n) (g := g) hg_mono hg0 x)
  have hnotbot_g : ∀ r ∈ nonnegRay, g r ≠ (⊥ : EReal) := by
    intro r hr hbot
    rcases hg0 with ⟨c, hc⟩
    have h0mem : (0 : Fin 1 → Real) ∈ nonnegRay := by simp [nonnegRay]
    have h0le : (0 : Fin 1 → Real) ≤ r := by
      intro i
      fin_cases i
      simpa [nonnegRay] using hr
    have hle : g 0 ≤ g r := hg_mono h0mem hr h0le
    have : g 0 = (⊥ : EReal) := by
      have : g 0 ≤ (⊥ : EReal) := by simpa [hbot] using hle
      exact le_bot_iff.1 this
    have h0ne : (g 0) ≠ (⊥ : EReal) := by simp [hc]
    exact h0ne this
  have hg_seg :=
    (convexFunctionOn_iff_segment_inequality (C := nonnegRay) (f := g)
      (hC := convex_nonnegRay) (hnotbot := hnotbot_g)).1 hg_conv
  have hf_seg :
      ∀ x ∈ (Set.univ : Set (Fin n → Real)), ∀ y ∈ (Set.univ : Set (Fin n → Real)),
        ∀ t : Real, 0 < t → t < 1 →
          f ((1 - t) • x + t • y) ≤
            ((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y := by
    intro x hx y hy t ht0 ht1
    have ht0' : 0 ≤ t := le_of_lt ht0
    have ht1' : 0 ≤ 1 - t := sub_nonneg.2 (le_of_lt ht1)
    have hnorm_le :
        euclidNorm n ((1 - t) • x + t • y) ≤
          (1 - t) * euclidNorm n x + t * euclidNorm n y := by
      let eL : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → Real) := EuclideanSpace.equiv (Fin n) ℝ
      have hlin :
          eL.symm ((1 - t) • x + t • y) =
            (1 - t) • eL.symm x + t • eL.symm y := by
        simp [eL, map_add, map_smul]
      calc
        euclidNorm n ((1 - t) • x + t • y) = ‖eL.symm ((1 - t) • x + t • y)‖ := by
          simp [euclidNorm, eL]
        _ = ‖(1 - t) • eL.symm x + t • eL.symm y‖ := by simp [hlin]
        _ ≤ ‖(1 - t) • eL.symm x‖ + ‖t • eL.symm y‖ := norm_add_le _ _
        _ = ‖1 - t‖ * ‖eL.symm x‖ + ‖t‖ * ‖eL.symm y‖ := by simp [norm_smul]
        _ = (1 - t) * ‖eL.symm x‖ + t * ‖eL.symm y‖ := by
              simp [Real.norm_of_nonneg ht1', Real.norm_of_nonneg ht0']
        _ = (1 - t) * euclidNorm n x + t * euclidNorm n y := by simp [euclidNorm, eL]
    let rx : Fin 1 → Real := fun _ => euclidNorm n x
    let ry : Fin 1 → Real := fun _ => euclidNorm n y
    let rz : Fin 1 → Real := fun _ => euclidNorm n ((1 - t) • x + t • y)
    have hrx : rx ∈ nonnegRay := by
      dsimp [nonnegRay, rx, euclidNorm]
      exact norm_nonneg _
    have hry : ry ∈ nonnegRay := by
      dsimp [nonnegRay, ry, euclidNorm]
      exact norm_nonneg _
    have hrz : rz ∈ nonnegRay := by
      dsimp [nonnegRay, rz, euclidNorm]
      exact norm_nonneg _
    have hcomb : ((1 - t) • rx + t • ry) ∈ nonnegRay := by
      have hxnonneg : 0 ≤ euclidNorm n x := by
        dsimp [euclidNorm]
        exact norm_nonneg _
      have hynonneg : 0 ≤ euclidNorm n y := by
        dsimp [euclidNorm]
        exact norm_nonneg _
      have : 0 ≤ ((1 - t) • rx + t • ry) 0 := by
        simpa [rx, ry, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
          add_nonneg (mul_nonneg ht1' hxnonneg) (mul_nonneg ht0' hynonneg)
      simpa [nonnegRay] using this
    have hmono : g rz ≤ g ((1 - t) • rx + t • ry) := by
      refine hg_mono hrz hcomb ?_
      intro i
      fin_cases i
      simpa [rz, rx, ry, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hnorm_le
    have hconv :
        g ((1 - t) • rx + t • ry) ≤
          ((1 - t : Real) : EReal) * g rx + ((t : Real) : EReal) * g ry := by
      exact hg_seg rx hrx ry hry t ht0 ht1
    simpa [f, rx, ry, rz] using le_trans hmono hconv
  have hf_on : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
    (convexFunctionOn_iff_segment_inequality (C := (Set.univ : Set (Fin n → Real))) (f := f)
      (hC := convex_univ) (hnotbot := hnotbot_f)).2 hf_seg
  simpa [ConvexFunction, f] using hf_on

/-- Lower semicontinuity of `g` on `nonnegRay` implies lower semicontinuity of the radial
composition `x ↦ g (‖x‖)`. -/
lemma radial_lsc_of_lscOn (n : Nat) (g : (Fin 1 → Real) → EReal)
    (hg : LowerSemicontinuousOn g (nonnegRay)) :
    let f : (Fin n → Real) → EReal := fun x => g (fun _ : Fin 1 => euclidNorm n x)
    LowerSemicontinuous f := by
  classical
  intro f
  let h : (Fin n → Real) → (Fin 1 → Real) := fun x => fun _ : Fin 1 => euclidNorm n x
  have hcont_scalar : Continuous fun x : Fin n → Real => euclidNorm n x := by
    simpa [euclidNorm] using
      (continuous_norm.comp (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous)
  have hcont : Continuous h := by
    classical
    refine continuous_pi ?_
    intro i
    fin_cases i
    simpa [h] using hcont_scalar
  have hmaps : Set.MapsTo h (Set.univ : Set (Fin n → Real)) (nonnegRay) := by
    intro x hx
    simp [h, nonnegRay, euclidNorm]
  have hg' : LowerSemicontinuousOn (g ∘ h) (Set.univ : Set (Fin n → Real)) :=
    hg.comp hcont.continuousOn hmaps
  have : LowerSemicontinuous (g ∘ h) := (lowerSemicontinuousOn_univ_iff).1 hg'
  simpa [f, h] using this

/-- Properness of the radial function follows from finiteness at `0` and monotonicity of `g` on
the ray, once convexity is known. -/
lemma radial_proper_of_mono_g0_finite (n : Nat) {g : (Fin 1 → Real) → EReal}
    (hg_mono : MonotoneOn g (nonnegRay)) (hg0 : ∃ c : Real, g 0 = (c : EReal))
    (hf_conv :
      let f : (Fin n → Real) → EReal := fun x => g (fun _ : Fin 1 => euclidNorm n x)
      ConvexFunction f) :
    let f : (Fin n → Real) → EReal := fun x => g (fun _ : Fin 1 => euclidNorm n x)
    ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
  classical
  intro f
  have hconv : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
    simpa [ConvexFunction] using hf_conv
  refine ⟨hconv, ?_, ?_⟩
  · rcases hg0 with ⟨c, hc⟩
    refine ⟨(0, c), ?_⟩
    refine And.intro (by trivial) ?_
    have hnorm0 : (fun _ : Fin 1 => euclidNorm n (0 : Fin n → Real)) = (0 : Fin 1 → Real) := by
      ext i
      fin_cases i
      simp [euclidNorm]
    simp [f, hnorm0, hc]
  · intro x hx
    simpa [f] using (radial_ne_bot_of_mono_g0_finite (n := n) (g := g) hg_mono hg0 x)

/-- From closed proper convexity of the radial function `x ↦ g (‖x‖)`, recover the one-dimensional
ray conditions on `g`. -/
lemma radial_ray_props_of_closedProperConvex (n : Nat) (hn : 0 < n) (g : (Fin 1 → Real) → EReal) :
    let f : (Fin n → Real) → EReal := fun x => g (fun _ : Fin 1 => euclidNorm n x)
    (LowerSemicontinuous f ∧ ConvexFunction f ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) →
      (ConvexFunctionOn (nonnegRay) g ∧
          MonotoneOn g (nonnegRay) ∧
          LowerSemicontinuousOn g (nonnegRay) ∧
          ∃ c : Real, g 0 = (c : EReal)) := by
  classical
  intro f hf
  rcases hf with ⟨hf_lsc, hf_conv, hf_proper⟩
  have hf_notbot : ∀ x ∈ (Set.univ : Set (Fin n → Real)), f x ≠ (⊥ : EReal) := hf_proper.2.2
  have hf_seg :=
    (convexFunctionOn_iff_segment_inequality (C := (Set.univ : Set (Fin n → Real))) (f := f)
      (hC := convex_univ) (hnotbot := hf_notbot)).1 (by simpa [ConvexFunction] using hf_conv)

  let eL : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → Real) := EuclideanSpace.equiv (Fin n) ℝ
  let i0 : Fin n := ⟨0, hn⟩
  let u0 : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i0 1
  have hu0 : ‖u0‖ = 1 := by simp [u0]
  let v0 : Fin n → Real := eL u0
  let φ : (Fin 1 → Real) → (Fin n → Real) := fun r => (r 0) • v0
  have hφ_cont : Continuous φ := by
    -- `r ↦ r 0` is continuous and scalar multiplication is continuous.
    simpa [φ] using ((continuous_apply (0 : Fin 1)).smul continuous_const)

  have hfg : ∀ r ∈ nonnegRay, f (φ r) = g r := by
    intro r hr
    have hr0 : 0 ≤ r 0 := hr
    have hr_eq : r = (fun _ : Fin 1 => r 0) := by
      ext i
      fin_cases i
      simp
    have hnorm : euclidNorm n (φ r) = r 0 := by
      have : eL.symm (φ r) = (r 0 : Real) • u0 := by
        -- `eL.symm` is linear.
        simp [φ, v0, eL]
      calc
        euclidNorm n (φ r) = ‖eL.symm (φ r)‖ := by simp [euclidNorm, eL]
        _ = ‖(r 0 : Real) • u0‖ := by simp [this]
        _ = ‖(r 0 : Real)‖ * ‖u0‖ := norm_smul _ _
        _ = r 0 := by simp [hu0, Real.norm_of_nonneg hr0]
    -- Unfold `f` and rewrite the `Fin 1` argument.
    have harg : (fun _ : Fin 1 => euclidNorm n (φ r)) = r := by
      ext i
      fin_cases i
      simp [hnorm]
    simp [f, harg]

  have hnotbot_g : ∀ r ∈ nonnegRay, g r ≠ (⊥ : EReal) := by
    intro r hr
    have : f (φ r) ≠ (⊥ : EReal) := hf_proper.2.2 (φ r) (by simp)
    simpa [hfg r hr] using this

  -- Convexity of `g` on the ray.
  have hg_conv : ConvexFunctionOn (nonnegRay) g := by
    refine
      (convexFunctionOn_iff_segment_inequality (C := nonnegRay) (f := g)
          (hC := convex_nonnegRay) (hnotbot := hnotbot_g)).2 ?_
    intro r hr s hs t ht0 ht1
    have hcomb : ((1 - t) • r + t • s) ∈ nonnegRay := by
      dsimp [nonnegRay] at hr hs ⊢
      have ht0' : 0 ≤ t := le_of_lt ht0
      have ht1' : 0 ≤ 1 - t := sub_nonneg.2 (le_of_lt ht1)
      have : 0 ≤ ((1 - t) • r + t • s) 0 := by
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
          add_nonneg (mul_nonneg ht1' hr) (mul_nonneg ht0' hs)
      simpa using this
    -- Apply convexity of `f` along the line `r0 • v`.
    have hφ_combo :
        (1 - t) • φ r + t • φ s = φ ((1 - t) • r + t • s) := by
      ext j
      simp [φ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hseg_f :
        f (φ ((1 - t) • r + t • s)) ≤
          ((1 - t : Real) : EReal) * f (φ r) + ((t : Real) : EReal) * f (φ s) := by
      -- `φ r`, `φ s` are in `Set.univ`, so memberships are trivial.
      simpa [hφ_combo] using
        hf_seg (φ r) (by simp) (φ s) (by simp) t ht0 ht1
    -- Rewrite `f (φ ·)` back into `g ·`.
    simpa [hfg r hr, hfg s hs, hfg ((1 - t) • r + t • s) hcomb] using hseg_f

  -- Monotonicity of `g` on the ray.
  have hg_mono : MonotoneOn g (nonnegRay) := by
    intro r hr s hs hrs
    have ha : 0 ≤ r 0 := hr
    have hb : 0 ≤ s 0 := hs
    have hab : r 0 ≤ s 0 := by
      have := hrs (0 : Fin 1)
      simpa using this
    by_cases hs0 : s 0 = 0
    · have hr0 : r 0 = 0 := le_antisymm (by simpa [hs0] using hab) ha
      have hrs' : r = s := by
        ext i
        fin_cases i
        simp [hr0, hs0]
      simp [hrs']
    · have hs0_pos : 0 < s 0 := lt_of_le_of_ne hb (Ne.symm hs0)
      by_cases hEq : r 0 = s 0
      · have hrs' : r = s := by
          ext i
          fin_cases i
          simp [hEq]
        simp [hrs']
      · have hr_lt : r 0 < s 0 := lt_of_le_of_ne hab hEq
        let t : Real := (s 0 - r 0) / (2 * s 0)
        have ht0 : 0 < t := by
          have hnum : 0 < s 0 - r 0 := sub_pos.2 hr_lt
          have hden : 0 < 2 * s 0 := by nlinarith [hs0_pos]
          exact div_pos hnum hden
        have ht1 : t < 1 := by
          have hspos : 0 < s 0 := hs0_pos
          have hnum : s 0 - r 0 < 2 * s 0 := by nlinarith [hspos, ha]
          have hden : 0 < 2 * s 0 := by nlinarith [hspos]
          exact (div_lt_one hden).2 hnum
        -- Work on the line spanned by `v0` (i.e. along `φ`).
        have hcomb : ((1 - t) • φ s + t • (-φ s) : Fin n → Real) = φ r := by
          ext j
          simp [φ, t, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, add_mul, sub_eq_add_neg,
            mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
          field_simp [hs0]
          ring
        have hseg_line :
            f (φ r) ≤
              ((1 - t : Real) : EReal) * f (φ s) + ((t : Real) : EReal) * f (-φ s) := by
          have := hf_seg (φ s) (by simp) (-φ s) (by simp) t ht0 ht1
          have hcomb' : ((1 - t) • φ s + -(t • φ s) : Fin n → Real) = φ r := by
            simpa [smul_neg] using hcomb
          simpa [hcomb', smul_neg] using this
        have h_even : f (-φ s) = f (φ s) := by
          simp [f, euclidNorm]
        by_cases htop : f (φ s) = (⊤ : EReal)
        ·
          have hgs : g s = (⊤ : EReal) := by
            calc
              g s = f (φ s) := (hfg s hs).symm
              _ = ⊤ := htop
          simp [hgs]
        ·
          have hnotbot_s : f (φ s) ≠ (⊥ : EReal) := hf_proper.2.2 (φ s) (by simp)
          have hs_toReal : ((f (φ s)).toReal : EReal) = f (φ s) := EReal.coe_toReal htop hnotbot_s
          have hRHS :
              ((1 - t : Real) : EReal) * f (φ s) + ((t : Real) : EReal) * f (-φ s) = f (φ s) := by
            let a : Real := (f (φ s)).toReal
            have ha : f (φ s) = (a : EReal) := by simpa [a] using hs_toReal.symm
            have ha' : f (-φ s) = (a : EReal) := by simp [h_even, ha]
            calc
              ((1 - t : Real) : EReal) * f (φ s) + ((t : Real) : EReal) * f (-φ s)
                  = ((1 - t : Real) : EReal) * (a : EReal) + ((t : Real) : EReal) * (a : EReal) := by
                        simp [ha, ha']
                  _ = (↑((1 - t) * a) : EReal) + (↑(t * a) : EReal) := by
                    have hx : ((1 - t : Real) : EReal) * (a : EReal) = (↑((1 - t) * a) : EReal) := by
                      simp
                    have hy : ((t : Real) : EReal) * (a : EReal) = (↑(t * a) : EReal) := by
                      simp
                    rw [hx, hy]
                  _ = (↑(((1 - t) * a) + (t * a)) : EReal) := by
                    simp
                  _ = (a : EReal) := by
                    have : ((1 - t) * a) + (t * a) = a := by ring
                    exact (EReal.coe_eq_coe_iff).2 this
                  _ = f (φ s) := by simp [ha]
          have hle' : f (φ r) ≤ f (φ s) := by
            have hs' : f (φ r) ≤ (1 - (↑t : EReal)) * f (φ s) + (↑t : EReal) * f (-φ s) := by
              simpa using hseg_line
            have hRHS' :
                (1 - (↑t : EReal)) * f (φ s) + (↑t : EReal) * f (-φ s) = f (φ s) := by
              simpa [EReal.coe_sub] using hRHS
            simpa [hRHS'] using hs'
          have hgr : g r = f (φ r) := (hfg r hr).symm
          have hgs : g s = f (φ s) := (hfg s hs).symm
          simpa [hgr, hgs] using hle'

  -- Lower semicontinuity of `g` on the ray: reduce to the restriction of `f` along `φ`.
  have hg_lsc : LowerSemicontinuousOn g (nonnegRay) := by
    have hh : LowerSemicontinuous (fun r : Fin 1 → Real => f (φ r)) :=
      hf_lsc.comp_continuous hφ_cont
    intro r hr
    have hh_within : LowerSemicontinuousWithinAt (fun r : Fin 1 → Real => f (φ r)) (nonnegRay) r :=
      hh.lowerSemicontinuousWithinAt (nonnegRay) r
    have hEq :
        ∀ᶠ r' in nhdsWithin r (nonnegRay), (fun r' : Fin 1 → Real => f (φ r')) r' = g r' := by
      filter_upwards [self_mem_nhdsWithin] with r' hr'
      exact hfg r' hr'
    -- Transfer along eventual equality.
    exact
      (LowerSemicontinuousWithinAt.congr_of_eventuallyEq hh_within hr hEq)

  -- Finiteness of `g 0`: `g 0 = f 0` is neither `⊥` (properness) nor `⊤` (epigraph nonempty).
  have hg0_ne_bot : g 0 ≠ (⊥ : EReal) := by
    have hnorm0 : (fun _ : Fin 1 => euclidNorm n (0 : Fin n → Real)) = (0 : Fin 1 → Real) := by
      ext i
      fin_cases i
      simp [euclidNorm]
    have hf0 : f (0 : Fin n → Real) = g 0 := by simp [f, hnorm0]
    have : f (0 : Fin n → Real) ≠ (⊥ : EReal) := hf_proper.2.2 0 (by simp)
    simpa [hf0] using this
  have hg0_ne_top : g 0 ≠ (⊤ : EReal) := by
    rcases hf_proper.2.1 with ⟨p, hp⟩
    have hp' : Set.univ p.1 ∧ f p.1 ≤ (p.2 : EReal) := by
      simpa [epigraph] using hp
    have hp_le : f p.1 ≤ (p.2 : EReal) := hp'.2
    -- `f 0 ≤ f p.1` from convexity and evenness.
    have h0_le : f (0 : Fin n → Real) ≤ f p.1 := by
      have hhalf0 : (0 : Real) < (1 / 2 : Real) := by norm_num
      have hhalf1 : (1 / 2 : Real) < 1 := by norm_num
      have hmid :
          f ((1 - (1 / 2 : Real)) • p.1 + (1 / 2 : Real) • (-p.1)) ≤
            ((1 - (1 / 2 : Real) : Real) : EReal) * f p.1 +
              ((1 / 2 : Real) : EReal) * f (-p.1) :=
        hf_seg p.1 (by simp) (-p.1) (by simp) (1 / 2 : Real) hhalf0 hhalf1
      -- The midpoint is `0`, and `f` is even.
      have hmid0 :
          (1 - (1 / 2 : Real)) • p.1 + (1 / 2 : Real) • (-p.1) = (0 : Fin n → Real) := by
        ext i
        simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      have hmid0' :
          (1 - (1 / 2 : Real)) • p.1 + -((1 / 2 : Real) • p.1) = (0 : Fin n → Real) := by
        simpa [smul_neg] using hmid0
      have hmid0'' :
          (1 - (2⁻¹ : Real)) • p.1 + -((2⁻¹ : Real) • p.1) = (0 : Fin n → Real) := by
        ext i
        have : (1 - (2⁻¹ : Real)) * p.1 i + -((2⁻¹ : Real) * p.1 i) = 0 := by ring
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
      have hEven : f (-p.1) = f p.1 := by simp [f, euclidNorm]
      -- Simplify RHS to `f p.1`.
      by_cases htop : f p.1 = (⊤ : EReal)
      · simp [htop]
      ·
        have hnotbot : f p.1 ≠ (⊥ : EReal) := hf_proper.2.2 p.1 (by simp)
        have hp_toReal : ((f p.1).toReal : EReal) = f p.1 := EReal.coe_toReal htop hnotbot
        have hRHS :
            ((1 - (1 / 2 : Real) : Real) : EReal) * f p.1 +
                ((1 / 2 : Real) : EReal) * f (-p.1) = f p.1 := by
          let a : Real := (f p.1).toReal
          have ha : f p.1 = (a : EReal) := by simpa [a] using hp_toReal.symm
          have ha' : f (-p.1) = (a : EReal) := by simp [hEven, ha]
          calc
            ((1 - (1 / 2 : Real) : Real) : EReal) * f p.1 +
                ((1 / 2 : Real) : EReal) * f (-p.1)
                = ((1 - (1 / 2 : Real) : Real) : EReal) * (a : EReal) +
                    ((1 / 2 : Real) : EReal) * (a : EReal) := by
                      simp [ha, ha']
            _ = (↑((1 - (1 / 2 : Real)) * a) : EReal) + (↑((1 / 2 : Real) * a) : EReal) := by
                  have hx :
                      ((1 - (1 / 2 : Real) : Real) : EReal) * (a : EReal) =
                        (↑((1 - (1 / 2 : Real)) * a) : EReal) := by
                    simp
                  have hy :
                      ((1 / 2 : Real) : EReal) * (a : EReal) = (↑((1 / 2 : Real) * a) : EReal) := by
                    simp
                  simp
            _ = (↑(((1 - (1 / 2 : Real)) * a) + ((1 / 2 : Real) * a)) : EReal) := by
                  simp
            _ = (a : EReal) := by
                  have : ((1 - (1 / 2 : Real)) * a) + ((1 / 2 : Real) * a) = a := by ring
                  exact (EReal.coe_eq_coe_iff).2 this
            _ = f p.1 := by simp [ha]
        have hRHS' :
            ((1 - (2⁻¹ : Real) : Real) : EReal) * f p.1 + ((2⁻¹ : Real) : EReal) * f (-p.1) = f p.1 := by
          simpa using hRHS
        have : f (0 : Fin n → Real) ≤
            ((1 - (1 / 2 : Real) : Real) : EReal) * f p.1 +
              ((1 / 2 : Real) : EReal) * f (-p.1) := by
          -- `simp` prefers the form `-(t • p.1)`, so we rewrite via `hmid0''`.
          have hmid' :
              f ((1 - (2⁻¹ : Real)) • p.1 + -((2⁻¹ : Real) • p.1)) ≤
                ((1 - (2⁻¹ : Real) : Real) : EReal) * f p.1 +
                  ((2⁻¹ : Real) : EReal) * f (-p.1) := by
            simpa [smul_neg] using hmid
          simpa [hmid0''] using hmid'
        have hRHS'' :
            (1 - (↑(2⁻¹ : Real) : EReal)) * f p.1 + ((2⁻¹ : Real) : EReal) * f (-p.1) = f p.1 := by
          simpa [EReal.coe_sub] using hRHS'
        simpa [hRHS''] using this
    have : f (0 : Fin n → Real) ≤ (p.2 : EReal) := le_trans h0_le hp_le
    intro htop
    have hnorm0 : (fun _ : Fin 1 => euclidNorm n (0 : Fin n → Real)) = (0 : Fin 1 → Real) := by
      ext i
      fin_cases i
      simp [euclidNorm]
    have hf0 : f (0 : Fin n → Real) = g 0 := by simp [f, hnorm0]
    have htop_le : (⊤ : EReal) ≤ (p.2 : EReal) := by
      have h := this
      simp [hf0, htop] at h
    exact (not_top_le_coe p.2) htop_le

  have hg0_finite : ∃ c : Real, g 0 = (c : EReal) := by
    refine ⟨(g 0).toReal, ?_⟩
    simpa using (EReal.coe_toReal (x := g 0) hg0_ne_top hg0_ne_bot).symm

  exact ⟨hg_conv, hg_mono, hg_lsc, hg0_finite⟩

theorem radial_closedProperConvex_iff (n : Nat) (hn : 0 < n) (g : (Fin 1 → Real) → EReal) :
    let f : (Fin n → Real) → EReal := fun x => g (fun _ : Fin 1 => euclidNorm n x)
    (LowerSemicontinuous f ∧ ConvexFunction f ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) ↔
      (ConvexFunctionOn {r : Fin 1 → Real | 0 ≤ r 0} g ∧
          MonotoneOn g {r : Fin 1 → Real | 0 ≤ r 0} ∧
          LowerSemicontinuousOn g {r : Fin 1 → Real | 0 ≤ r 0} ∧
          ∃ c : Real, g 0 = (c : EReal)) := by
  classical
  -- Work with the `nonnegRay` abbreviation.
  constructor
  · intro hf
    -- Recover the ray properties of `g`.
    have : (ConvexFunctionOn nonnegRay g ∧ MonotoneOn g nonnegRay ∧
        LowerSemicontinuousOn g nonnegRay ∧ ∃ c : Real, g 0 = (c : EReal)) :=
      radial_ray_props_of_closedProperConvex (n := n) (hn := hn) (g := g) (by simpa using hf)
    simpa [nonnegRay] using this
  · rintro ⟨hg_conv, hg_mono, hg_lsc, hg0⟩
    -- Build the closed proper convex properties of `f`.
    refine ⟨?_, ?_, ?_⟩
    ·
      -- Lower semicontinuity.
      simpa [nonnegRay] using (radial_lsc_of_lscOn (n := n) (g := g) (by simpa [nonnegRay] using hg_lsc))
    ·
      -- Convexity.
      simpa [nonnegRay] using
        (radial_convex_of_convexOn_monoOn (n := n) (g := g)
          (by simpa [nonnegRay] using hg_conv) (by simpa [nonnegRay] using hg_mono) hg0)
    ·
      -- Properness, using the convexity already obtained.
      have hf_conv :
          (let f : (Fin n → Real) → EReal := fun x => g (fun _ : Fin 1 => euclidNorm n x);
            ConvexFunction f) :=
        radial_convex_of_convexOn_monoOn (n := n) (g := g)
          (by simpa [nonnegRay] using hg_conv) (by simpa [nonnegRay] using hg_mono) hg0
      simpa [nonnegRay] using
        (radial_proper_of_mono_g0_finite (n := n) (g := g)
          (by simpa [nonnegRay] using hg_mono) hg0 hf_conv)

/-- Defn 12.4: Let `g` be a function on the nonnegative orthant `ℝ^n_+`. Its *monotone conjugate*
`g⁺` is defined for `y* ∈ ℝ^n_+` by
`g⁺(y*) = sup_{y ≥ 0} (⟪y, y*⟫ - g y)`. -/
noncomputable def monotoneConjugate (n : Nat) (g : (Fin n → NNReal) → Real) :
    (Fin n → NNReal) → Real :=
  fun yStar =>
    sSup <|
      Set.range fun y : Fin n → NNReal =>
        ((fun i => (y i : Real)) ⬝ᵥ (fun i => (yStar i : Real))) - g y

/-- `EReal`-valued monotone conjugate: same supremum, but living in `[-∞, ∞]` so it can take `⊤`. -/
noncomputable def monotoneConjugateEReal (n : Nat) (g : (Fin n → NNReal) → Real) :
    (Fin n → NNReal) → EReal :=
  fun yStar =>
    sSup <|
      Set.range fun y : Fin n → NNReal =>
        (((fun i => (y i : Real)) ⬝ᵥ (fun i => (yStar i : Real)) : Real) : EReal) - (g y : EReal)

/-- Text 12.3.6: For `x : ℝ^n`, define `abs x = (|x₁|, …, |xₙ|)` as an element of the nonnegative
orthant `ℝ^n_+` (modeled as `Fin n → NNReal`). -/
def absVecNN (n : Nat) (x : Fin n → Real) : Fin n → NNReal :=
  fun i => ⟨|x i|, abs_nonneg (x i)⟩

/-- Coercing a nonnegative vector to `Real` and taking componentwise absolute values recovers it. -/
lemma absVecNN_coe (n : Nat) (y : Fin n → NNReal) :
    absVecNN n (fun i => (y i : Real)) = y := by
  ext i
  simp [absVecNN]

/-- Componentwise absolute values ignore global sign changes. -/
lemma absVecNN_neg (n : Nat) (x : Fin n → Real) : absVecNN n (-x) = absVecNN n x := by
  ext i
  simp [absVecNN]

/-- Lower semicontinuity is preserved by coercion `Real → EReal`. -/
lemma lowerSemicontinuous_coe_real_toEReal {α : Type*} [TopologicalSpace α] {h : α → Real} :
    LowerSemicontinuous h → LowerSemicontinuous (fun x => (h x : EReal)) := by
  intro hh
  rw [lowerSemicontinuous_iff_isOpen_preimage] at hh ⊢
  intro y
  induction y using EReal.rec with
  | bot =>
      have : (fun x => (h x : EReal)) ⁻¹' Set.Ioi (⊥ : EReal) = (Set.univ : Set α) := by
        ext x
        simp
      simp [this]
  | coe r =>
      simpa [Set.preimage, EReal.coe_lt_coe_iff] using hh r
  | top =>
      have : (fun x => (h x : EReal)) ⁻¹' Set.Ioi (⊤ : EReal) = (∅ : Set α) := by
        ext x
        simp
      simp

/-- Lower semicontinuity of `Real → EReal` coercions implies lower semicontinuity of the real map. -/
lemma lowerSemicontinuous_of_coe_real_toEReal {α : Type*} [TopologicalSpace α] {h : α → Real} :
    LowerSemicontinuous (fun x => (h x : EReal)) → LowerSemicontinuous h := by
  intro hh
  rw [lowerSemicontinuous_iff_isOpen_preimage] at hh ⊢
  intro r
  simpa [Set.preimage, EReal.coe_lt_coe_iff] using hh (r : EReal)

/-- The coercion `Fin n → NNReal → Fin n → Real` is continuous. -/
lemma continuous_coeVecNN (n : Nat) :
    Continuous (fun y : Fin n → NNReal => fun i => (y i : Real)) := by
  classical
  refine continuous_pi ?_
  intro i
  exact continuous_subtype_val.comp (continuous_apply i)

/-- The map `x ↦ absVecNN n x` is continuous. -/
lemma continuous_absVecNN (n : Nat) : Continuous (absVecNN n) := by
  classical
  refine continuous_pi ?_
  intro i
  -- continuity into `NNReal` via the subtype constructor
  have hcont : Continuous fun x : Fin n → Real => |x i| :=
    continuous_abs.comp (continuous_apply i)
  simpa [absVecNN] using hcont.subtype_mk (fun x => abs_nonneg (x i))

/-- Pointwise triangle inequality for affine combinations: `| (1-t)x + t y |` is bounded by the
corresponding convex combination of `|x|` and `|y|` when `t ∈ [0,1]`. -/
lemma abs_combo_le (a b t : Real) (ht0 : 0 ≤ t) (ht1 : 0 ≤ 1 - t) :
    |(1 - t) * a + t * b| ≤ (1 - t) * |a| + t * |b| := by
  calc
    |(1 - t) * a + t * b| ≤ |(1 - t) * a| + |t * b| := by
      simpa [mul_assoc, mul_left_comm, mul_comm, add_comm, add_left_comm, add_assoc] using
        abs_add_le ((1 - t) * a) (t * b)
    _ = |1 - t| * |a| + |t| * |b| := by
      simp [abs_mul]
    _ = (1 - t) * |a| + t * |b| := by
      simp [abs_of_nonneg ht0, abs_of_nonneg ht1]

/-- Choose signs so that `x ⬝ᵥ xStar` becomes `|x| ⬝ᵥ |xStar|`. -/
lemma exists_sign_choice_dotProduct_eq (n : Nat) (xStar : Fin n → Real) (y : Fin n → NNReal) :
    ∃ x : Fin n → Real,
      absVecNN n x = y ∧
        (x ⬝ᵥ xStar : Real) =
          ((fun i => (y i : Real)) ⬝ᵥ (fun i => (absVecNN n xStar i : Real)) : Real) := by
  classical
  refine ⟨fun i => if 0 ≤ xStar i then (y i : Real) else -(y i : Real), ?_, ?_⟩
  · ext i
    by_cases h : 0 ≤ xStar i
    · simp [h, absVecNN]
    · have hy : 0 ≤ (y i : Real) := (y i).property
      simp [h, absVecNN, abs_neg, abs_of_nonneg hy]
  · -- dot product identity (termwise)
    simp [dotProduct, absVecNN]
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases h : 0 ≤ xStar i
    · simp [h, abs_of_nonneg h]
    · have hx : xStar i < 0 := lt_of_not_ge h
      simp [h, abs_of_neg hx]

/-- Text 12.3.6 (1): Let `f : ℝ^n → ℝ` be of the form `f(x) = g(abs x)` with
`g : ℝ^n_+ → ℝ` and `abs x = (|x₁|, …, |xₙ|)`.

Then `f` is closed proper convex on `ℝ^n` iff `g` is lower semicontinuous, convex, finite at `0`,
and non-decreasing (i.e. `0 ≤ y ≤ y' → g y ≤ g y'`). -/
theorem closedProperConvex_abs_comp_iff (n : Nat) (g : (Fin n → NNReal) → Real) :
    let f : (Fin n → Real) → EReal := fun x => (g (absVecNN n x) : EReal)
    (LowerSemicontinuous f ∧ ConvexFunction f ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) ↔
      (LowerSemicontinuous g ∧ ConvexOn NNReal (Set.univ : Set (Fin n → NNReal)) g ∧
          (∃ c : Real, g 0 = c) ∧ Monotone g) := by
  classical
  intro f
  constructor
  · rintro ⟨hf_lsc, hf_conv, _hf_proper⟩
    have hf_notbot : ∀ x ∈ (Set.univ : Set (Fin n → Real)), f x ≠ (⊥ : EReal) := by
      intro x hx
      simp [f]
    have hf_seg :=
      (convexFunctionOn_iff_segment_inequality (C := (Set.univ : Set (Fin n → Real))) (f := f)
          (hC := convex_univ) (hnotbot := hf_notbot)).1 (by simpa [ConvexFunction] using hf_conv)

    -- Lower semicontinuity of `g` from the restriction of `f` to the nonnegative orthant.
    have hg_lsc_coe :
        LowerSemicontinuous (fun y : Fin n → NNReal => (g y : EReal)) := by
      have hcomp :
          LowerSemicontinuous (fun y : Fin n → NNReal => f (fun i => (y i : Real))) :=
        hf_lsc.comp_continuous (continuous_coeVecNN n)
      have hEq :
          (fun y : Fin n → NNReal => f (fun i => (y i : Real))) = fun y => (g y : EReal) := by
        funext y
        simp [f, absVecNN_coe]
      simpa [hEq] using hcomp
    have hg_lsc : LowerSemicontinuous g :=
      lowerSemicontinuous_of_coe_real_toEReal (h := g) hg_lsc_coe

    -- Convexity of `g` from convexity of `f` restricted to the nonnegative orthant.
    have hg_conv : ConvexOn NNReal (Set.univ : Set (Fin n → NNReal)) g := by
      refine ⟨convex_univ, ?_⟩
      intro x hx y hy a b ha hb hab
      by_cases hb0 : b = 0
      · have ha1 : a = 1 := by simpa [hb0] using hab
        subst ha1; subst hb0
        simp
      by_cases hb1 : b = 1
      · have ha0 : a = 0 := by simpa [hb1] using hab
        subst ha0; subst hb1
        simp
      have hb_le1 : b ≤ (1 : NNReal) := by
        -- `b ≤ a + b = 1`
        have : b ≤ a + b := le_add_of_nonneg_left ha
        simpa [hab] using this
      have hb_lt1 : b < 1 := lt_of_le_of_ne hb_le1 hb1
      have ht0 : 0 < (b : Real) := by
        have : (0 : NNReal) < b := lt_of_le_of_ne (by simp) (Ne.symm hb0)
        exact_mod_cast this
      have ht1 : (b : Real) < 1 := by
        exact_mod_cast hb_lt1
      let xR : Fin n → Real := fun i => (x i : Real)
      let yR : Fin n → Real := fun i => (y i : Real)
      have haR : (a : Real) = 1 - (b : Real) := by
        have habR : (a : Real) + (b : Real) = 1 := by exact_mod_cast hab
        nlinarith
      have hzR :
          (fun i => ((a • x + b • y) i : Real)) = (1 - (b : Real)) • xR + (b : Real) • yR := by
        ext i
        simp [xR, yR, haR, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hseg :
          f ((1 - (b : Real)) • xR + (b : Real) • yR) ≤
            ((1 - (b : Real) : Real) : EReal) * f xR + ((b : Real) : EReal) * f yR :=
        hf_seg xR (by simp) yR (by simp) (b : Real) ht0 ht1
      have hx : f xR = (g x : EReal) := by simp [f, xR, absVecNN_coe]
      have hy : f yR = (g y : EReal) := by simp [f, yR, absVecNN_coe]
      have hz : f ((1 - (b : Real)) • xR + (b : Real) • yR) = (g (a • x + b • y) : EReal) := by
        have : absVecNN n ((1 - (b : Real)) • xR + (b : Real) • yR) = a • x + b • y := by
          -- rewrite the argument using `hzR.symm`, then use `absVecNN_coe`.
          have hzR' :
              (1 - (b : Real)) • xR + (b : Real) • yR =
                (fun i => ((a • x + b • y) i : Real)) := hzR.symm
          simpa [hzR'] using (absVecNN_coe (n := n) (y := a • x + b • y))
        simp [f, this]
      have hE :
          (g (a • x + b • y) : EReal) ≤
            ((1 - (b : Real) : Real) : EReal) * (g x : EReal) +
              ((b : Real) : EReal) * (g y : EReal) := by
        simpa [hx, hy, hz] using hseg
      have hE' :
          (g (a • x + b • y) : EReal) ≤
            (((1 - (b : Real)) * g x + (b : Real) * g y : Real) : EReal) := by
        -- Expand the `EReal` arithmetic on finite values.
        simpa [EReal.coe_add, EReal.coe_mul, add_assoc, add_left_comm, add_comm, mul_assoc,
          mul_left_comm, mul_comm] using hE
      have hreal : g (a • x + b • y) ≤ (1 - (b : Real)) * g x + (b : Real) * g y :=
        (EReal.coe_le_coe_iff).1 hE'
      have hreal' : g (a • x + b • y) ≤ (a : Real) * g x + (b : Real) * g y := by
        have : (1 - (b : Real)) * g x + (b : Real) * g y = (a : Real) * g x + (b : Real) * g y := by
          simp [haR]
        simpa [this] using hreal
      -- The `NNReal`-scalar action on `Real` is via coercion to `Real`.
      simpa [NNReal.smul_def, smul_eq_mul, add_assoc, add_left_comm, add_comm, mul_assoc,
        mul_left_comm, mul_comm] using hreal'

    -- Monotonicity of `g` from convexity of `f` and sign-symmetry in each coordinate.
    have hg_mono : Monotone g := by
      -- Monotonicity along one coordinate, holding the rest fixed.
      have h_update :
          ∀ (y : Fin n → NNReal) (i : Fin n) (a b : NNReal),
            a ≤ b → g (Function.update y i a) ≤ g (Function.update y i b) := by
        intro y i a b hab
        by_cases habEq : a = b
        · simp [habEq]
        by_cases hb0 : b = 0
        · have ha0 : a = 0 := le_antisymm (by simpa [hb0] using hab) (by simp)
          simp [hb0, ha0]
        have hbpos : 0 < (b : Real) := by
          have : (0 : NNReal) < b := lt_of_le_of_ne (by simp) (Ne.symm hb0)
          exact_mod_cast this
        have hablt : (a : Real) < (b : Real) := by
          have hable : (a : Real) ≤ (b : Real) := by exact_mod_cast hab
          have habne : (a : Real) ≠ (b : Real) := by
            intro hEq
            apply habEq
            ext
            exact hEq
          exact lt_of_le_of_ne hable habne
        let t : Real := ((b : Real) - (a : Real)) / (2 * (b : Real))
        have ht0 : 0 < t := by
          have hnum : 0 < (b : Real) - (a : Real) := sub_pos.2 hablt
          have hden : 0 < 2 * (b : Real) := by nlinarith [hbpos]
          exact div_pos hnum hden
        have ht1 : t < 1 := by
          have ha0 : 0 ≤ (a : Real) := by exact_mod_cast (show (0 : NNReal) ≤ a from by simp)
          have hnum : (b : Real) - (a : Real) < 2 * (b : Real) := by nlinarith [hbpos, ha0]
          have hden : 0 < 2 * (b : Real) := by nlinarith [hbpos]
          exact (div_lt_one hden).2 hnum
        let baseR : Fin n → Real := fun j => (y j : Real)
        let p : Fin n → Real := Function.update baseR i (b : Real)
        let q : Fin n → Real := Function.update baseR i (-(b : Real))
        let r : Fin n → Real := Function.update baseR i (a : Real)
        have hcomb : ((1 - t) • p + t • q : Fin n → Real) = r := by
          ext j
          by_cases hj : j = i
          · subst hj
            simp [p, q, r, t, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            field_simp [hb0]
            ring
          · simp [p, q, r, baseR, hj, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            ring
        have hp : f p = (g (Function.update y i b) : EReal) := by
          have : absVecNN n p = Function.update y i b := by
            have hp' : p = fun j => ((Function.update y i b) j : Real) := by
              ext j
              by_cases hj : j = i
              · subst hj
                simp [p, baseR]
              · simp [p, baseR, hj]
            simpa [hp'] using (absVecNN_coe (n := n) (y := Function.update y i b))
          simp [f, this]
        have hq : f q = (g (Function.update y i b) : EReal) := by
          have : absVecNN n q = Function.update y i b := by
            ext j
            by_cases hj : j = i
            · subst hj
              simp [q, absVecNN, abs_neg, abs_of_nonneg hbpos.le]
            · simp [q, baseR, hj, absVecNN]
          simp [f, this]
        have hr : f r = (g (Function.update y i a) : EReal) := by
          have : absVecNN n r = Function.update y i a := by
            have hr' : r = fun j => ((Function.update y i a) j : Real) := by
              ext j
              by_cases hj : j = i
              · subst hj
                simp [r, baseR]
              · simp [r, baseR, hj]
            simpa [hr'] using (absVecNN_coe (n := n) (y := Function.update y i a))
          simp [f, this]
        have hseg := hf_seg p (by simp) q (by simp) t ht0 ht1
        have hE :
            (g (Function.update y i a) : EReal) ≤
              ((1 - t : Real) : EReal) * (g (Function.update y i b) : EReal) +
                ((t : Real) : EReal) * (g (Function.update y i b) : EReal) := by
          simpa [hcomb, hp, hq, hr] using hseg
        have hE' : (g (Function.update y i a) : EReal) ≤ (g (Function.update y i b) : EReal) := by
          have hRHS :
              ((1 - t : Real) : EReal) * (g (Function.update y i b) : EReal) +
                  ((t : Real) : EReal) * (g (Function.update y i b) : EReal) =
                (g (Function.update y i b) : EReal) := by
            set c : Real := g (Function.update y i b)
            have : ((1 - t) * c + t * c : Real) = c := by ring
            simpa [c, EReal.coe_add, EReal.coe_mul] using congrArg (fun r : Real => (r : EReal)) this
          have hE' := hE
          -- rewrite the right-hand side of `hE` to a single term
          rw [hRHS] at hE'
          exact hE'
        exact (EReal.coe_le_coe_iff).1 hE'

      -- Upgrade to full monotonicity by successive coordinate updates.
      intro y y' hyy'
      let z : Finset (Fin n) → (Fin n → NNReal) := fun s j => if j ∈ s then y' j else y j
      have hz_empty : z ∅ = y := by
        ext j
        simp [z]
      have hz_univ : z Finset.univ = y' := by
        ext j
        simp [z]
      have hmono_s : ∀ s : Finset (Fin n), g y ≤ g (z s) := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
            simp [hz_empty]
        | @insert i s hi hs =>
            have hiz : z (insert i s) = Function.update (z s) i (y' i) := by
              ext j
              by_cases hj : j = i
              · subst hj
                simp [z]
              · simp [z, hj]
            have hzi : (z s) i = y i := by
              simp [z, hi]
            have hle_i : (z s) i ≤ y' i := by
              simpa [hzi] using hyy' i
            have hinc : g (z s) ≤ g (z (insert i s)) := by
              simpa [hiz] using h_update (y := z s) (i := i) (a := (z s) i) (b := y' i) hle_i
            exact le_trans hs hinc
      have : g y ≤ g (z Finset.univ) := hmono_s Finset.univ
      simpa [hz_univ] using this

    exact ⟨hg_lsc, hg_conv, ⟨g 0, rfl⟩, hg_mono⟩
  · rintro ⟨hg_lsc, hg_conv, hg0, hg_mono⟩
    -- Lower semicontinuity.
    have hf_lsc_real : LowerSemicontinuous (fun x : Fin n → Real => g (absVecNN n x)) :=
      hg_lsc.comp_continuous (continuous_absVecNN n)
    have hf_lsc : LowerSemicontinuous f := by
      simpa [f] using
        lowerSemicontinuous_coe_real_toEReal (h := fun x : Fin n → Real => g (absVecNN n x))
          hf_lsc_real

    -- Convexity.
    have hf_notbot : ∀ x ∈ (Set.univ : Set (Fin n → Real)), f x ≠ (⊥ : EReal) := by
      intro x hx
      simp [f]
    have hf_convOn :
        ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
      refine
        (convexFunctionOn_iff_segment_inequality (C := (Set.univ : Set (Fin n → Real))) (f := f)
            (hC := convex_univ) (hnotbot := hf_notbot)).2 ?_
      intro x hx y hy t ht0 ht1
      have ht0' : 0 ≤ t := le_of_lt ht0
      have ht1' : 0 ≤ 1 - t := sub_nonneg.2 (le_of_lt ht1)
      let a : NNReal := ⟨1 - t, ht1'⟩
      let b : NNReal := ⟨t, ht0'⟩
      have hab : a + b = 1 := by
        ext
        simp [a, b]
      let u : Fin n → NNReal := a • absVecNN n x + b • absVecNN n y
      have hle_abs : absVecNN n ((1 - t) • x + t • y) ≤ u := by
        intro i
        have htri :
            |(1 - t) * x i + t * y i| ≤ (1 - t) * |x i| + t * |y i| :=
          abs_combo_le (a := x i) (b := y i) (t := t) ht0' ht1'
        have hu : ((u i : NNReal) : Real) = (1 - t) * |x i| + t * |y i| := by
          simp [u, a, b, absVecNN, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact_mod_cast (by simpa [absVecNN, hu] using htri)
      have hmono : g (absVecNN n ((1 - t) • x + t • y)) ≤ g u := hg_mono hle_abs
      have hconv :
          g u ≤ a • g (absVecNN n x) + b • g (absVecNN n y) := by
        have hg_ineq := hg_conv.2
        have :=
          hg_ineq (x := absVecNN n x) (by simp) (y := absVecNN n y) (by simp) (a := a) (b := b)
            (by simp) (by simp) hab
        simpa [u] using this
      have hreal :
          g (absVecNN n ((1 - t) • x + t • y)) ≤ (1 - t) * g (absVecNN n x) + t * g (absVecNN n y) := by
        have h' :
            g (absVecNN n ((1 - t) • x + t • y)) ≤
              (a : Real) * g (absVecNN n x) + (b : Real) * g (absVecNN n y) :=
          le_trans hmono (by simpa [smul_eq_mul] using hconv)
        simpa [a, b, smul_eq_mul] using h'
      have hE :
          (g (absVecNN n ((1 - t) • x + t • y)) : EReal) ≤
            (((1 - t) * g (absVecNN n x) + t * g (absVecNN n y) : Real) : EReal) := by
        exact_mod_cast hreal
      have hE'' :
          (((1 - t) * g (absVecNN n x) + t * g (absVecNN n y) : Real) : EReal) =
            ((1 - t : Real) : EReal) * (g (absVecNN n x) : EReal) +
              ((t : Real) : EReal) * (g (absVecNN n y) : EReal) := by
        simp [EReal.coe_add, EReal.coe_mul]
      simpa [f, hE''] using hE
    have hf_conv : ConvexFunction f := by simpa [ConvexFunction] using hf_convOn

    -- Properness.
    have hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
      refine ⟨hf_convOn, ?_, ?_⟩
      · rcases hg0 with ⟨c, hc⟩
        refine ⟨(0, c), ?_⟩
        refine And.intro (by trivial) ?_
        have habs0 : absVecNN n (0 : Fin n → Real) = (0 : Fin n → NNReal) := by
          ext i
          simp [absVecNN]
        simp [f, habs0, hc]
      · intro x hx
        simp [f]

    exact ⟨hf_lsc, hf_conv, hf_proper⟩

/-- Text 12.3.6 (2): The conjugate of `f(x) = g(abs x)` is
`f*(x*) = g⁺(abs x*)`, where `g⁺` is the `EReal`-valued monotone conjugate (here
`g⁺ = monotoneConjugateEReal n g`). -/
theorem fenchelConjugate_abs_comp_eq_monotoneConjugate (n : Nat) (g : (Fin n → NNReal) → Real) :
    let f : (Fin n → Real) → EReal := fun x => (g (absVecNN n x) : EReal)
    ∀ xStar : Fin n → Real,
      fenchelConjugate n f xStar = monotoneConjugateEReal n g (absVecNN n xStar) := by
  classical
  intro f xStar
  unfold fenchelConjugate monotoneConjugateEReal
  refine le_antisymm ?_ ?_
  · -- `≤`: replace `x` by `|x|` in the dot product.
    refine sSup_le ?_
    rintro z ⟨x, rfl⟩
    let y : Fin n → NNReal := absVecNN n x
    have hdot :
        (x ⬝ᵥ xStar : Real) ≤
          ((fun i => (y i : Real)) ⬝ᵥ (fun i => (absVecNN n xStar i : Real)) : Real) := by
      classical
      have hterm : ∀ i : Fin n, x i * xStar i ≤ |x i| * |xStar i| := by
        intro i
        have : x i * xStar i ≤ |x i * xStar i| := le_abs_self _
        simpa [abs_mul] using this
      have :
          (∑ i : Fin n, x i * xStar i) ≤ ∑ i : Fin n, |x i| * |xStar i| :=
        Finset.sum_le_sum (fun i _hi => hterm i)
      simpa [dotProduct, y, absVecNN] using this
    have hE :
        (((x ⬝ᵥ xStar : Real) : EReal) - (g (absVecNN n x) : EReal)) ≤
          ((((fun i => (y i : Real)) ⬝ᵥ (fun i => (absVecNN n xStar i : Real)) : Real) : Real) : EReal) -
            (g y : EReal) := by
      have : ((x ⬝ᵥ xStar : Real) : EReal) ≤
          (((fun i => (y i : Real)) ⬝ᵥ (fun i => (absVecNN n xStar i : Real)) : Real) : EReal) := by
        exact_mod_cast hdot
      -- rewrite `f x = g y`
      simpa [y] using EReal.sub_le_sub this le_rfl
    exact le_trans hE (le_sSup ⟨y, rfl⟩)
  · -- `≥`: choose signs so the dot product becomes `⟪y, |xStar|⟫`.
    refine sSup_le ?_
    rintro z ⟨y, rfl⟩
    rcases exists_sign_choice_dotProduct_eq (n := n) (xStar := xStar) (y := y) with ⟨x, hxabs, hxdot⟩
    have : (((x ⬝ᵥ xStar : Real) : EReal) - (g (absVecNN n x) : EReal)) ≤
        sSup (Set.range fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal) - (g (absVecNN n x) : EReal)) :=
      le_sSup ⟨x, rfl⟩
    simpa [hxabs, hxdot] using this

end Section12
end Chap03
