/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yifan Bai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section04

section Chap01
section Section05

/-- Multiplying a non-`⊥` value by a positive real does not yield `⊥` in `EReal`. -/
lemma ereal_mul_ne_bot_of_pos {a : EReal} {r : Real} (hr : 0 < r) (ha : a ≠ ⊥) :
    ((r : Real) : EReal) * a ≠ ⊥ := by
  intro hbot
  have hcases := (EReal.mul_eq_bot ((r : Real) : EReal) a).1 hbot
  rcases hcases with h | h | h | h
  · exact (EReal.coe_ne_bot r) h.1
  · exact ha h.2
  · exact (EReal.coe_ne_top r) h.1
  · have hr' : ¬ ((r : Real) : EReal) < 0 := by
      have : (0 : EReal) ≤ (r : EReal) := by
        exact (le_of_lt ((EReal.coe_pos).2 hr))
      exact not_lt_of_ge this
    exact hr' h.1

/-- Segment inequality for a convex function on `Set.univ` with no `⊥` values. -/
lemma segment_inequality_f_univ {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f)
    (hnotbot : ∀ x, f x ≠ ⊥) :
    ∀ x y t, 0 < t → t < 1 →
      f ((1 - t) • x + t • y) ≤
        ((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y := by
  have hseg :=
    (convexFunctionOn_iff_segment_inequality (C := Set.univ) (f := f)
      (hC := convex_univ)
      (hnotbot := by
        intro x hx
        simpa using hnotbot x)).1 hf
  intro x y t ht0 ht1
  simpa using hseg x (by simp) y (by simp) t ht0 ht1

/-- Segment inequality for `phi` on real arguments from convexity on `Fin 1`. -/
lemma segment_inequality_phi_real {phi : EReal → EReal}
    (hphi : ConvexFunctionOn (S := (Set.univ : Set (Fin 1 → Real)))
      (fun x : Fin 1 → Real => phi (x 0)))
    (hphi_notbot : ∀ r : Real, phi r ≠ ⊥) :
    ∀ a b t : Real, 0 < t → t < 1 →
      phi (((1 - t) * a + t * b : Real)) ≤
        ((1 - t : Real) : EReal) * phi a + ((t : Real) : EReal) * phi b := by
  have hseg :=
    (convexFunctionOn_iff_segment_inequality (C := Set.univ)
      (f := fun x : Fin 1 → Real => phi (x 0))
      (hC := convex_univ)
      (hnotbot := by
        intro x hx
        simpa using hphi_notbot (x 0))).1 hphi
  intro a b t ht0 ht1
  have h' := hseg (fun _ => a) (by simp) (fun _ => b) (by simp) t ht0 ht1
  simpa [smul_eq_mul] using h'

/-- Theorem 5.1: Let `f` be a convex function from `R^n` to `(-infty, +infty]`,
and let `phi` be a convex function from `R` to `(-infty, +infty]` which is
non-decreasing (with `phi (+infty) = +infty`). Then `h x = phi (f x)` is convex
on `R^n`. -/
theorem convexFunctionOn_comp_nondecreasing {n : Nat} {f : (Fin n → Real) → EReal}
    {phi : EReal → EReal}
    (hf : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f)
    (hf_notbot : ∀ x, f x ≠ ⊥)
    (hphi : ConvexFunctionOn (S := (Set.univ : Set (Fin 1 → Real)))
      (fun x : Fin 1 → Real => phi (x 0)))
    (hphi_notbot : ∀ r : Real, phi r ≠ ⊥)
    (hphi_top : phi ⊤ = ⊤)
    (hmono : Monotone phi) :
    ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (fun x => phi (f x)) := by
  have hseg_f := segment_inequality_f_univ (hf := hf) (hnotbot := hf_notbot)
  have hseg_phi := segment_inequality_phi_real (hphi := hphi) (hphi_notbot := hphi_notbot)
  have hnotbot_h : ∀ x, phi (f x) ≠ ⊥ := by
    intro x
    by_cases hx_top : f x = ⊤
    · simp [hx_top, hphi_top]
    · have hx_bot : f x ≠ ⊥ := hf_notbot x
      have hfx : f x = ((f x).toReal : EReal) := by
        simpa using (EReal.coe_toReal hx_top hx_bot).symm
      have hphi_real : phi ((f x).toReal) ≠ ⊥ := hphi_notbot (f x).toReal
      rw [hfx]
      exact hphi_real
  have hseg_h :
      ∀ x y t, 0 < t → t < 1 →
        phi (f ((1 - t) • x + t • y)) ≤
          ((1 - t : Real) : EReal) * phi (f x) + ((t : Real) : EReal) * phi (f y) := by
    intro x y t ht0 ht1
    have h_f := hseg_f x y t ht0 ht1
    have h_mono := hmono h_f
    have h_phi :
        phi (((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y) ≤
          ((1 - t : Real) : EReal) * phi (f x) + ((t : Real) : EReal) * phi (f y) := by
      have ht0E : (0 : EReal) < (t : EReal) := (EReal.coe_pos).2 ht0
      have ht1E : (0 : EReal) < ((1 - t) : EReal) := (EReal.coe_pos).2 (sub_pos.mpr ht1)
      by_cases hx_top : f x = ⊤
      · have hx_phi : phi (f x) = ⊤ := by simp [hx_top, hphi_top]
        have hne :
            ((t : Real) : EReal) * phi (f y) ≠ ⊥ :=
          ereal_mul_ne_bot_of_pos ht0 (hnotbot_h y)
        have htop :
            ((1 - t : Real) : EReal) * phi (f x) + ((t : Real) : EReal) * phi (f y) = ⊤ := by
          have hx_mul :
              ((1 - t : Real) : EReal) * phi (f x) = ⊤ := by
            simpa [hx_phi] using (EReal.mul_top_of_pos ht1E)
          calc
            ((1 - t : Real) : EReal) * phi (f x) + ((t : Real) : EReal) * phi (f y)
                = ⊤ + ((t : Real) : EReal) * phi (f y) := by rw [hx_mul]
            _ = ⊤ := EReal.top_add_of_ne_bot hne
        calc
          phi (((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y) ≤ ⊤ := le_top
          _ = ((1 - t : Real) : EReal) * phi (f x) + ((t : Real) : EReal) * phi (f y) := by
                symm
                exact htop
      · by_cases hy_top : f y = ⊤
        · have hy_phi : phi (f y) = ⊤ := by simp [hy_top, hphi_top]
          have hne :
              ((1 - t : Real) : EReal) * phi (f x) ≠ ⊥ :=
            ereal_mul_ne_bot_of_pos (sub_pos.mpr ht1) (hnotbot_h x)
          have htop :
              ((1 - t : Real) : EReal) * phi (f x) + ((t : Real) : EReal) * phi (f y) = ⊤ := by
            have hy_mul :
                ((t : Real) : EReal) * phi (f y) = ⊤ := by
              simpa [hy_phi] using (EReal.mul_top_of_pos ht0E)
            calc
              ((1 - t : Real) : EReal) * phi (f x) + ((t : Real) : EReal) * phi (f y)
                  = ((1 - t : Real) : EReal) * phi (f x) + ⊤ := by rw [hy_mul]
              _ = ⊤ := EReal.add_top_of_ne_bot hne
          calc
            phi (((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y) ≤ ⊤ := le_top
            _ = ((1 - t : Real) : EReal) * phi (f x) + ((t : Real) : EReal) * phi (f y) := by
                  symm
                  exact htop
        · have hx_bot : f x ≠ ⊥ := hf_notbot x
          have hy_bot : f y ≠ ⊥ := hf_notbot y
          have hfx : f x = ((f x).toReal : EReal) := by
            simpa using (EReal.coe_toReal hx_top hx_bot).symm
          have hfy : f y = ((f y).toReal : EReal) := by
            simpa using (EReal.coe_toReal hy_top hy_bot).symm
          have hcombo :
              ((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y =
                (((1 - t) * (f x).toReal + t * (f y).toReal : Real) : EReal) := by
            have hx_mul :
                ((1 - t : Real) : EReal) * ((f x).toReal : EReal) =
                  (((1 - t) * (f x).toReal : Real) : EReal) := by
              simp
            have hy_mul :
                ((t : Real) : EReal) * ((f y).toReal : EReal) =
                  (((t) * (f y).toReal : Real) : EReal) := by
              simp
            calc
              ((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y
                  = ((1 - t : Real) : EReal) * ((f x).toReal : EReal) +
                      ((t : Real) : EReal) * ((f y).toReal : EReal) := by
                        rw [hfx, hfy]
                        simp
              _ = (((1 - t) * (f x).toReal : Real) : EReal) +
                    (((t) * (f y).toReal : Real) : EReal) := by
                        rw [hx_mul, hy_mul]
              _ = (((1 - t) * (f x).toReal + t * (f y).toReal : Real) : EReal) := by
                        simp [EReal.coe_add]
          have hphi_seg := hseg_phi (f x).toReal (f y).toReal t ht0 ht1
          have hphi_fx : phi (f x) = phi ((f x).toReal) := by
            simpa using congrArg phi hfx
          have hphi_fy : phi (f y) = phi ((f y).toReal) := by
            simpa using congrArg phi hfy
          have hphi_rhs :
              ((1 - t : Real) : EReal) * phi (f x) + ((t : Real) : EReal) * phi (f y) =
                ((1 - t : Real) : EReal) * phi ((f x).toReal) +
                  ((t : Real) : EReal) * phi ((f y).toReal) := by
            rw [hphi_fx, hphi_fy]
          calc
            phi (((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y) =
                phi ((1 - t) * (f x).toReal + t * (f y).toReal) := by
                  rw [hcombo]
                  rfl
            _ ≤ ((1 - t : Real) : EReal) * phi ((f x).toReal) +
                  ((t : Real) : EReal) * phi ((f y).toReal) := hphi_seg
            _ = ((1 - t : Real) : EReal) * phi (f x) + ((t : Real) : EReal) * phi (f y) := by
                  symm
                  exact hphi_rhs
    exact le_trans h_mono h_phi
  have hnotbot_h' :
      ∀ x ∈ (Set.univ : Set (Fin n → Real)), phi (f x) ≠ ⊥ := by
    intro x hx
    simpa using hnotbot_h x
  refine (convexFunctionOn_iff_segment_inequality (C := Set.univ)
    (f := fun x => phi (f x))
    (hC := convex_univ)
    (hnotbot := hnotbot_h')).2 ?_
  intro x hx y hy t ht0 ht1
  simpa using hseg_h x y t ht0 ht1

/-- Extended-real exponential with `expEReal ⊤ = ⊤` and `expEReal ⊥ = 0`. -/
noncomputable def expEReal (z : EReal) : EReal :=
  if z = ⊥ then (0 : Real) else if z = ⊤ then (⊤ : EReal) else (Real.exp z.toReal : EReal)

/-- On real inputs, `expEReal` agrees with `Real.exp`. -/
@[simp] lemma expEReal_coe (r : Real) : expEReal (r : EReal) = (Real.exp r : EReal) := by
  simp [expEReal]

/-- `expEReal` is monotone on `EReal`. -/
lemma expEReal_monotone : Monotone expEReal := by
  intro a b hab
  by_cases ha_bot : a = ⊥
  · subst ha_bot
    by_cases hb_bot : b = ⊥
    · subst hb_bot; rfl
    · by_cases hb_top : b = ⊤
      · subst hb_top
        simp [expEReal]
      · have hbpos : 0 ≤ Real.exp b.toReal := le_of_lt (Real.exp_pos _)
        have hbpos' : ((0 : Real) : EReal) ≤ (Real.exp b.toReal : EReal) := by
          simpa [EReal.coe_le_coe_iff] using hbpos
        simpa [expEReal, hb_bot, hb_top] using hbpos'
  · by_cases ha_top : a = ⊤
    · subst ha_top
      have hb : b = ⊤ := top_le_iff.mp hab
      subst hb
      simp [expEReal]
    · by_cases hb_bot : b = ⊥
      · exfalso
        have : a = ⊥ := (le_bot_iff).1 (by simpa [hb_bot] using hab)
        exact ha_bot this
      · by_cases hb_top : b = ⊤
        · subst hb_top
          simp [expEReal, ha_bot, ha_top]
        · have hab' : a.toReal ≤ b.toReal :=
            EReal.toReal_le_toReal hab ha_bot hb_top
          have hexp : Real.exp a.toReal ≤ Real.exp b.toReal := Real.exp_monotone hab'
          have hexp' : (Real.exp a.toReal : EReal) ≤ (Real.exp b.toReal : EReal) := by
            simpa [EReal.coe_le_coe_iff] using hexp
          simpa [expEReal, ha_bot, ha_top, hb_bot, hb_top] using hexp'

/-- Convexity of `expEReal` on `Fin 1` over `Set.univ`. -/
lemma convexFunctionOn_expEReal_univ :
    ConvexFunctionOn (S := (Set.univ : Set (Fin 1 → Real)))
      (fun x : Fin 1 → Real => expEReal (x 0)) := by
  have hconv :
      ConvexOn ℝ (Set.univ : Set (Fin 1 → Real)) (fun x : Fin 1 → Real => Real.exp (x 0)) := by
    simpa using
      (convexOn_comp_proj (s := Set.univ) (f := Real.exp) (convexOn_exp))
  have hconvE :
      ConvexFunctionOn (S := (Set.univ : Set (Fin 1 → Real)))
        (fun x : Fin 1 → Real => (Real.exp (x 0) : EReal)) :=
    convexFunctionOn_of_convexOn_real (S := (Set.univ : Set (Fin 1 → Real))) hconv
  simpa using hconvE

/-- Text 5.1.1: The function `h x = exp (f x)` is a proper convex function on `R^n`
if `f` is a proper convex function. -/
lemma properConvexFunctionOn_exp {n : Nat} {f : (Fin n → Real) → Real}
    (hf : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real)))
      (fun x => (f x : EReal))) :
    ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real)))
      (fun x => (Real.exp (f x) : EReal)) := by
  have hf_notbot : ∀ x, (f x : EReal) ≠ ⊥ := by
    intro x
    exact hf.2.2 x (by simp)
  have hconv' :
      ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real)))
        (fun x => expEReal (f x)) := by
    refine convexFunctionOn_comp_nondecreasing
      (f := fun x => (f x : EReal)) (phi := expEReal)
      (hf := hf.1) (hf_notbot := hf_notbot)
      (hphi := convexFunctionOn_expEReal_univ)
      (hphi_notbot := ?_) (hphi_top := by simp [expEReal]) (hmono := expEReal_monotone)
    intro r
    simp [expEReal]
  have hconv :
      ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real)))
        (fun x => (Real.exp (f x) : EReal)) := by
    simpa using hconv'
  refine ⟨hconv, ?_, ?_⟩
  · refine ⟨(fun _ => 0, Real.exp (f (fun _ => 0))), ?_⟩
    refine
      (mem_epigraph_univ_iff (f := fun x => (Real.exp (f x) : EReal))).2 le_rfl
  · intro x _
    simp

/-- The function `r ↦ max r 0` is convex on `ℝ`. -/
lemma convexOn_max_zero :
    ConvexOn ℝ (Set.univ : Set ℝ) (fun r : ℝ => max r 0) := by
  have hid : ConvexOn ℝ (Set.univ : Set ℝ) (fun r : ℝ => r) := by
    simpa using (convexOn_id (s := (Set.univ : Set ℝ)) (𝕜 := ℝ) convex_univ)
  have hconst : ConvexOn ℝ (Set.univ : Set ℝ) (fun _ : ℝ => (0 : ℝ)) := by
    simpa using
      (convexOn_const (s := (Set.univ : Set ℝ)) (𝕜 := ℝ) (c := (0 : ℝ))
        (hs := convex_univ))
  have hsup :
      ConvexOn ℝ (Set.univ : Set ℝ) ((fun r : ℝ => r) ⊔ fun _ : ℝ => (0 : ℝ)) :=
    ConvexOn.sup (s := (Set.univ : Set ℝ)) (f := fun r : ℝ => r)
      (g := fun _ : ℝ => (0 : ℝ)) hid hconst
  have hsup' :
      ((fun r : ℝ => r) ⊔ fun _ : ℝ => (0 : ℝ)) = fun r : ℝ => max r 0 := by
    funext r
    simp [max_def]
  simpa [hsup'] using hsup

/-- Convexity of `r ↦ (max r 0) ^ p` on `ℝ` for `p ≥ 1`. -/
lemma convexOn_rpow_max_zero {p : Real} (hp1 : 1 ≤ p) :
    ConvexOn ℝ (Set.univ : Set ℝ) (fun r : ℝ => Real.rpow (max r 0) p) := by
  have himage :
      (fun r : ℝ => max r 0) '' (Set.univ : Set ℝ) = Set.Ici 0 := by
    ext y; constructor
    · rintro ⟨x, -, rfl⟩
      exact le_max_right (a := x) (b := (0 : ℝ))
    · intro hy
      refine ⟨y, by simp, ?_⟩
      have hy' : (0 : ℝ) ≤ y := by simpa using hy
      simp [max_eq_left hy']
  have hconv_rpow :
      ConvexOn ℝ ((fun r : ℝ => max r 0) '' (Set.univ : Set ℝ))
        (fun r : ℝ => r ^ p) := by
    simpa [himage] using (convexOn_rpow (p := p) hp1)
  have hmono :
      MonotoneOn (fun r : ℝ => r ^ p) ((fun r : ℝ => max r 0) '' (Set.univ : Set ℝ)) := by
    have hp0 : 0 ≤ p := by linarith
    have hmono' : MonotoneOn (fun r : ℝ => r ^ p) (Set.Ici 0) := by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow hx hxy hp0
    simpa [himage] using hmono'
  have hcomp :
      ConvexOn ℝ (Set.univ : Set ℝ) (fun r : ℝ => (max r 0) ^ p) :=
    (ConvexOn.comp (s := (Set.univ : Set ℝ)) (f := fun r : ℝ => max r 0)
      (g := fun r : ℝ => r ^ p) hconv_rpow (convexOn_max_zero) hmono)
  simpa using hcomp

/-- The map `r ↦ (max r 0) ^ p` is monotone for `p ≥ 0`. -/
lemma monotone_rpow_max_zero {p : Real} (hp0 : 0 ≤ p) :
    Monotone (fun r : ℝ => Real.rpow (max r 0) p) := by
  intro a b hab
  have hmax : max a 0 ≤ max b 0 := max_le_max hab (le_rfl)
  have hnonneg : 0 ≤ max a 0 := le_max_right _ _
  have hle : (max a 0) ^ p ≤ (max b 0) ^ p :=
    Real.rpow_le_rpow hnonneg hmax hp0
  simpa using hle

/-- Text 5.1.2: The function `h x = f x ^ p` is convex for `p > 1` when `f` is
convex and non-negative. -/
lemma convexFunctionOn_rpow_of_convex_nonneg {n : Nat} {f : (Fin n → Real) → Real}
    {p : Real} (hp : 1 < p)
    (hf : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real)))
      (fun x => (f x : EReal)))
    (h_nonneg : ∀ x, 0 ≤ f x) :
    ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real)))
      (fun x => (Real.rpow (f x) p : EReal)) := by
  classical
  have hp1 : 1 ≤ p := le_of_lt hp
  have hp0 : 0 ≤ p := by linarith
  let phi : EReal → EReal := fun z =>
    if z = ⊥ then (0 : Real) else
      if z = ⊤ then (⊤ : EReal) else (Real.rpow (max z.toReal 0) p : EReal)
  have hphi_coe : ∀ r : Real, phi (r : EReal) = (Real.rpow (max r 0) p : EReal) := by
    intro r
    simp [phi]
  have hphi_notbot : ∀ r : Real, phi r ≠ ⊥ := by
    intro r
    simp [phi]
  have hphi_top : phi ⊤ = ⊤ := by
    simp [phi]
  have hphi_convex :
      ConvexFunctionOn (S := (Set.univ : Set (Fin 1 → Real)))
        (fun x : Fin 1 → Real => phi (x 0)) := by
    have hconv_real :
        ConvexOn ℝ (Set.univ : Set ℝ) (fun r : ℝ => Real.rpow (max r 0) p) :=
      convexOn_rpow_max_zero (p := p) hp1
    have hconv_fin :
        ConvexOn ℝ (Set.univ : Set (Fin 1 → Real))
          (fun x : Fin 1 → Real => Real.rpow (max (x 0) 0) p) := by
      simpa using
        (convexOn_comp_proj (s := Set.univ)
          (f := fun r : ℝ => Real.rpow (max r 0) p) hconv_real)
    have hconvE :
        ConvexFunctionOn (S := (Set.univ : Set (Fin 1 → Real)))
          (fun x : Fin 1 → Real => (Real.rpow (max (x 0) 0) p : EReal)) :=
      convexFunctionOn_of_convexOn_real (S := (Set.univ : Set (Fin 1 → Real))) hconv_fin
    have hphi_eq :
        (fun x : Fin 1 → Real => phi (x 0)) =
          (fun x : Fin 1 → Real => (Real.rpow (max (x 0) 0) p : EReal)) := by
      funext x
      simp [phi]
    simpa [hphi_eq] using hconvE
  have hphi_mono : Monotone phi := by
    have hmono_real : Monotone (fun r : Real => Real.rpow (max r 0) p) :=
      monotone_rpow_max_zero (p := p) hp0
    intro a b hab
    by_cases ha_bot : a = ⊥
    · subst ha_bot
      by_cases hb_bot : b = ⊥
      · subst hb_bot
        simp [phi]
      · by_cases hb_top : b = ⊤
        · subst hb_top
          simp [phi]
        · have h0 : (0 : Real) ≤ Real.rpow (max b.toReal 0) p := by
            have : 0 ≤ max b.toReal 0 := le_max_right _ _
            exact Real.rpow_nonneg this p
          simpa [phi, hb_bot, hb_top, EReal.coe_le_coe_iff] using h0
    · by_cases ha_top : a = ⊤
      · subst ha_top
        have hb : b = ⊤ := top_le_iff.mp hab
        subst hb
        simp [phi]
      · by_cases hb_bot : b = ⊥
        · exfalso
          have : a = ⊥ := (le_bot_iff).1 (by simpa [hb_bot] using hab)
          exact ha_bot this
        · by_cases hb_top : b = ⊤
          · subst hb_top
            simp [phi, ha_bot, ha_top, hb_bot]
          · have hab' : a.toReal ≤ b.toReal :=
              EReal.toReal_le_toReal hab ha_bot hb_top
            have hmono' :
                Real.rpow (max a.toReal 0) p ≤ Real.rpow (max b.toReal 0) p :=
              hmono_real hab'
            have hmono'' :
                (Real.rpow (max a.toReal 0) p : EReal) ≤
                  (Real.rpow (max b.toReal 0) p : EReal) := by
              simpa [EReal.coe_le_coe_iff] using hmono'
            simpa [phi, ha_bot, ha_top, hb_bot, hb_top] using hmono''
  have hf_notbot : ∀ x, (f x : EReal) ≠ ⊥ := by
    intro x
    exact EReal.coe_ne_bot _
  have hconv_comp :
      ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real)))
        (fun x => phi (f x : EReal)) :=
    convexFunctionOn_comp_nondecreasing
      (f := fun x => (f x : EReal)) (phi := phi) (hf := hf)
      (hf_notbot := hf_notbot) (hphi := hphi_convex)
      (hphi_notbot := hphi_notbot) (hphi_top := hphi_top) (hmono := hphi_mono)
  have hphi_fx :
      (fun x : Fin n → Real => phi (f x : EReal)) =
        (fun x : Fin n → Real => (Real.rpow (f x) p : EReal)) := by
    funext x
    have hx : 0 ≤ f x := h_nonneg x
    simpa [max_eq_left hx] using hphi_coe (f x)
  simpa [hphi_fx] using hconv_comp

/-- Text 5.1.3: In particular, `h(x) = |x|^p` is convex on `R^n` for `p ≥ 1`
(`|x|` being the Euclidean norm). -/
lemma convexOn_univ_euclidean_norm_rpow {n : Nat} {p : Real} (hp : 1 ≤ p) :
    ConvexOn ℝ (Set.univ)
      (fun x : EuclideanSpace ℝ (Fin n) => Real.rpow ‖x‖ p) := by
  classical
  by_cases hn : n = 0
  · subst hn
    have hconst :
        (fun x : EuclideanSpace ℝ (Fin 0) => ‖x‖ ^ p) =
          fun _ => (0 : ℝ) ^ p := by
      funext x
      have hx : x = 0 := Subsingleton.elim x 0
      simp [hx]
    simpa [Real.rpow_eq_pow, hconst] using
      (convexOn_const (s := (Set.univ : Set (EuclideanSpace ℝ (Fin 0))))
        (𝕜 := ℝ) (c := (0 : ℝ) ^ p) (hs := convex_univ))
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    haveI : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
    haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := by infer_instance
    have hp0 : 0 ≤ p := by linarith
    have hnorm :
        ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n)))
          (fun x => ‖x‖) := by
      simpa using
        (convexOn_univ_norm :
          ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) (norm))
    have h_range :
        (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) '' (Set.univ : Set (EuclideanSpace ℝ (Fin n))) =
          Set.Ici 0 := by
      simp [Set.image_univ]
    have hconv_rpow :
        ConvexOn ℝ ((fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) '' Set.univ)
          (fun r : ℝ => r ^ p) := by
      simpa [h_range] using (convexOn_rpow (p := p) hp)
    have hmono :
        MonotoneOn (fun r : ℝ => r ^ p)
          ((fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) '' Set.univ) := by
      have hmono' : MonotoneOn (fun r : ℝ => r ^ p) (Set.Ici 0) := by
        intro x hx y hy hxy
        exact Real.rpow_le_rpow hx hxy hp0
      simpa [h_range] using hmono'
    simpa [Real.rpow_eq_pow] using (ConvexOn.comp hconv_rpow hnorm hmono)

/-! Helper lemmas for Text 5.1.4. -/

/-- Positivity domain of a concave function on `Set.univ` is convex. -/
lemma convex_pos_set_of_concave {n : Nat} {g : (Fin n → Real) → Real}
    (hg : ConcaveOn ℝ (Set.univ : Set (Fin n → Real)) g) :
    Convex ℝ {x : Fin n → Real | 0 < g x} := by
  intro x hx y hy a b ha hb hab
  have hconc : a * g x + b * g y ≤ g (a • x + b • y) := by
    simpa [smul_eq_mul] using hg.2 (by simp) (by simp) ha hb hab
  have hpos_sum : 0 < a * g x + b * g y := by
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using hy
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hpos1 : 0 < a * g x := mul_pos ha_pos hx
      have hnonneg : 0 ≤ b * g y := mul_nonneg hb (le_of_lt hy)
      exact add_pos_of_pos_of_nonneg hpos1 hnonneg
  exact lt_of_lt_of_le hpos_sum hconc

/-- The reciprocal function is convex on `(0, +∞)`. -/
lemma convexOn_inv_Ioi : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun r : ℝ => r⁻¹) := by
  have hD : Convex ℝ (Set.Ioi (0 : ℝ)) := convex_Ioi (0 : ℝ)
  have hf' : DifferentiableOn ℝ (fun r : ℝ => r⁻¹) (Set.Ioi (0 : ℝ)) := by
    refine (differentiableOn_inv :
      DifferentiableOn ℝ (fun r : ℝ => r⁻¹) {r : ℝ | r ≠ 0}).mono ?_
    intro x hx
    exact ne_of_gt hx
  have hf'' : DifferentiableOn ℝ (deriv (fun r : ℝ => r⁻¹)) (Set.Ioi (0 : ℝ)) := by
    have hpow : DifferentiableOn ℝ (fun r : ℝ => r ^ 2) (Set.Ioi (0 : ℝ)) := by
      simpa using (differentiableOn_pow (𝕜 := ℝ) (n := 2) (s := Set.Ioi (0 : ℝ)))
    have hpow_ne : ∀ x ∈ Set.Ioi (0 : ℝ), (x ^ 2) ≠ 0 := by
      intro x hx
      exact pow_ne_zero _ (ne_of_gt hx)
    have hinv :
        DifferentiableOn ℝ (fun x : ℝ => (x ^ 2)⁻¹) (Set.Ioi (0 : ℝ)) :=
      DifferentiableOn.fun_inv hpow hpow_ne
    have hderiv : deriv (fun r : ℝ => r⁻¹) = fun r => -(r ^ 2)⁻¹ := by
      funext r
      simp
    simpa [hderiv] using hinv.neg
  have hnonneg :
      ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ (deriv^[2] (fun r : ℝ => r⁻¹)) x := by
    intro x hx
    have hxpos : 0 < x := hx
    have hxpow : 0 ≤ x ^ (-1 - (2 : ℕ) : ℤ) := by
      exact le_of_lt (zpow_pos hxpos _)
    have hnonneg' :
        0 ≤ (-1 : ℝ) ^ (2 : ℕ) * (Nat.factorial 2 : ℝ) * x ^ (-1 - (2 : ℕ) : ℤ) := by
      have h1 : 0 ≤ (-1 : ℝ) ^ (2 : ℕ) := by norm_num
      have h2 : 0 ≤ (Nat.factorial 2 : ℝ) := by norm_num
      exact mul_nonneg (mul_nonneg h1 h2) hxpow
    simpa [iter_deriv_inv] using hnonneg'
  exact convexOn_of_deriv2_nonneg' hD hf' hf'' hnonneg

/-- Text 5.1.4: If `g` is a concave function, then `h x = 1 / g x` is convex on
`C = {x | g x > 0}`. -/
lemma convexOn_inv_of_concave_pos {n : Nat} {g : (Fin n → Real) → Real}
    (hg : ConcaveOn ℝ (Set.univ : Set (Fin n → Real)) g) :
    ConvexOn ℝ {x : Fin n → Real | 0 < g x} (fun x => (g x)⁻¹) := by
  refine ⟨convex_pos_set_of_concave hg, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxpos : 0 < g x := hx
  have hypos : 0 < g y := hy
  have hconc : a * g x + b * g y ≤ g (a • x + b • y) := by
    simpa [smul_eq_mul] using hg.2 (by simp) (by simp) ha hb hab
  have hpos_sum : 0 < a * g x + b * g y := by
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simp [ha0, hb1, hypos]
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hpos1 : 0 < a * g x := mul_pos ha_pos hxpos
      have hnonneg : 0 ≤ b * g y := mul_nonneg hb (le_of_lt hypos)
      exact add_pos_of_pos_of_nonneg hpos1 hnonneg
  have hpos_comb : 0 < g (a • x + b • y) := lt_of_lt_of_le hpos_sum hconc
  have hanti :
      (g (a • x + b • y))⁻¹ ≤ (a * g x + b * g y)⁻¹ := by
    have hanti' :
        AntitoneOn (fun r : ℝ => r⁻¹) (Set.Ioi (0 : ℝ)) :=
      inv_antitoneOn_Ioi
    exact hanti' hpos_sum hpos_comb hconc
  have hconv :
      (a * g x + b * g y)⁻¹ ≤ a * (g x)⁻¹ + b * (g y)⁻¹ := by
    have h :=
      (convexOn_inv_Ioi).2 (by exact hxpos) (by exact hypos) ha hb hab
    simpa [smul_eq_mul] using h
  calc
    (g (a • x + b • y))⁻¹ ≤ (a * g x + b * g y)⁻¹ := hanti
    _ ≤ a * (g x)⁻¹ + b * (g y)⁻¹ := hconv

/-- Segment inequality on `ℝ` obtained from convexity of the `EReal` coercion. -/
lemma segment_inequality_real_of_ereal {n : Nat} {f : (Fin n → Real) → Real}
    (hf : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real)))
      (fun x => (f x : EReal))) :
    ∀ x y t, 0 < t → t < 1 →
      f ((1 - t) • x + t • y) ≤ (1 - t) * f x + t * f y := by
  have hnotbot : ∀ x, (f x : EReal) ≠ ⊥ := by
    intro x
    exact EReal.coe_ne_bot (f x)
  have hseg := segment_inequality_f_univ (hf := hf) (hnotbot := hnotbot)
  intro x y t ht0 ht1
  have hseg' := hseg x y t ht0 ht1
  have hseg'' :
      (f ((1 - t) • x + t • y) : EReal) ≤
        (( (1 - t) * f x + t * f y : Real) : EReal) := by
    calc
      (f ((1 - t) • x + t • y) : EReal) ≤
          ((1 - t : Real) : EReal) * (f x : EReal) +
            ((t : Real) : EReal) * (f y : EReal) := hseg'
      _ = (( (1 - t) * f x + t * f y : Real) : EReal) := by
        calc
          ((1 - t : Real) : EReal) * (f x : EReal) +
              ((t : Real) : EReal) * (f y : EReal) =
            (( (1 - t) * f x : Real) : EReal) + ((t * f y : Real) : EReal) := by
              simp [EReal.coe_mul]
          _ = (( (1 - t) * f x + t * f y : Real) : EReal) := by
              simp
  exact (EReal.coe_le_coe_iff).1 hseg''

/-- A nonnegative affine map preserves convex-combination inequalities on `ℝ`. -/
lemma affine_le_affine_combo {a b c t lam alpha : Real} (hlam : 0 ≤ lam)
    (h : a ≤ (1 - t) * b + t * c) :
    lam * a + alpha ≤ (1 - t) * (lam * b + alpha) + t * (lam * c + alpha) := by
  have hmul : lam * a ≤ lam * ((1 - t) * b + t * c) :=
    mul_le_mul_of_nonneg_left h hlam
  have hmul' : lam * a + alpha ≤ lam * ((1 - t) * b + t * c) + alpha := by
    simpa [add_comm, add_left_comm, add_assoc] using (add_le_add_right hmul alpha)
  have h_eq :
      lam * ((1 - t) * b + t * c) + alpha =
        (1 - t) * (lam * b + alpha) + t * (lam * c + alpha) := by
    ring
  simpa [h_eq] using hmul'

/-- Text 5.1.5: `(lambda f + alpha)` is a proper convex function when `f` is a proper
convex function and `lambda` and `alpha` are real numbers with `lambda ≥ 0`. -/
lemma properConvexFunctionOn_mul_add_const {n : Nat} {f : (Fin n → Real) → Real}
    {lam alpha : Real} (hlam : 0 ≤ lam)
    (hf : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real)))
      (fun x => (f x : EReal))) :
    ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real)))
      (fun x => ((lam * f x + alpha : Real) : EReal)) := by
  have hconv :
      ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real)))
        (fun x => ((lam * f x + alpha : Real) : EReal)) := by
    refine
      (convexFunctionOn_iff_segment_inequality (C := Set.univ) (hC := convex_univ)
        (hnotbot := ?_)).2 ?_
    · intro x hx
      exact EReal.coe_ne_bot (lam * f x + alpha)
    · intro x hx y hy t ht0 ht1
      have hseg_real :=
        segment_inequality_real_of_ereal (f := f) (hf := hf.1) x y t ht0 ht1
      have hseg_affine :
          lam * f ((1 - t) • x + t • y) + alpha ≤
            (1 - t) * (lam * f x + alpha) + t * (lam * f y + alpha) := by
        simpa using
          (affine_le_affine_combo (a := f ((1 - t) • x + t • y))
            (b := f x) (c := f y) (t := t) (lam := lam) (alpha := alpha) hlam
            hseg_real)
      have hseg_affine_ereal :
          ((lam * f ((1 - t) • x + t • y) + alpha : Real) : EReal) ≤
            ((1 - t : Real) : EReal) * ((lam * f x + alpha : Real) : EReal) +
              ((t : Real) : EReal) * ((lam * f y + alpha : Real) : EReal) := by
        have hseg_affine' :
            ((lam * f ((1 - t) • x + t • y) + alpha : Real) : EReal) ≤
              (( (1 - t) * (lam * f x + alpha) + t * (lam * f y + alpha) : Real) : EReal) := by
          exact (EReal.coe_le_coe_iff).2 hseg_affine
        have hR :
            (( (1 - t) * (lam * f x + alpha) + t * (lam * f y + alpha) : Real) : EReal) =
              ((1 - t : Real) : EReal) * ((lam * f x + alpha : Real) : EReal) +
                ((t : Real) : EReal) * ((lam * f y + alpha : Real) : EReal) := by
          calc
            (( (1 - t) * (lam * f x + alpha) + t * (lam * f y + alpha) : Real) : EReal) =
                (( (1 - t) * (lam * f x + alpha) : Real) : EReal) +
                  ((t * (lam * f y + alpha) : Real) : EReal) := by
              simp
            _ = ((1 - t : Real) : EReal) * ((lam * f x + alpha : Real) : EReal) +
                ((t : Real) : EReal) * ((lam * f y + alpha : Real) : EReal) := by
              simp [EReal.coe_mul]
        simpa [hR] using hseg_affine'
      simpa using hseg_affine_ereal
  refine ⟨hconv, ?_, ?_⟩
  · refine ⟨(fun _ => 0, lam * f (fun _ => 0) + alpha), ?_⟩
    refine
      (mem_epigraph_univ_iff
        (f := fun x => ((lam * f x + alpha : Real) : EReal))).2 ?_
    exact le_rfl
  · intro x hx
    exact EReal.coe_ne_bot (lam * f x + alpha)

/-! Helper lemmas for Theorem 5.2. -/

/-- The sum of two non-`⊥` values in `EReal` is non-`⊥`. -/
lemma add_ne_bot_of_notbot {a b : EReal} (ha : a ≠ ⊥) (hb : b ≠ ⊥) : a + b ≠ ⊥ := by
  exact (EReal.add_ne_bot_iff).2 ⟨ha, hb⟩

/-- Segment inequality for the sum of convex functions on `Set.univ`. -/
lemma segment_inequality_add_univ {n : Nat} {f1 f2 : (Fin n → Real) → EReal}
    (hf1 : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f1)
    (hf2 : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f2)
    (hnotbot1 : ∀ x, f1 x ≠ ⊥) (hnotbot2 : ∀ x, f2 x ≠ ⊥) :
    ∀ x y t, 0 < t → t < 1 →
      f1 ((1 - t) • x + t • y) + f2 ((1 - t) • x + t • y) ≤
        ((1 - t : Real) : EReal) * (f1 x + f2 x) + ((t : Real) : EReal) * (f1 y + f2 y) := by
  have hseg1 := segment_inequality_f_univ (hf := hf1) (hnotbot := hnotbot1)
  have hseg2 := segment_inequality_f_univ (hf := hf2) (hnotbot := hnotbot2)
  intro x y t ht0 ht1
  have h1 := hseg1 x y t ht0 ht1
  have h2 := hseg2 x y t ht0 ht1
  have hsum :
      f1 ((1 - t) • x + t • y) + f2 ((1 - t) • x + t • y) ≤
        (((1 - t : Real) : EReal) * f1 x + ((t : Real) : EReal) * f1 y) +
          (((1 - t : Real) : EReal) * f2 x + ((t : Real) : EReal) * f2 y) := by
    exact add_le_add h1 h2
  have ha_nonneg : (0 : EReal) ≤ ((1 - t : Real) : EReal) := by
    exact (EReal.coe_nonneg).2 (sub_nonneg.mpr (le_of_lt ht1))
  have hb_nonneg : (0 : EReal) ≤ ((t : Real) : EReal) := by
    exact (EReal.coe_nonneg).2 (le_of_lt ht0)
  have ha_ne_top : ((1 - t : Real) : EReal) ≠ ⊤ := by
    exact EReal.coe_ne_top (1 - t)
  have hb_ne_top : ((t : Real) : EReal) ≠ ⊤ := by
    exact EReal.coe_ne_top t
  have h_a :
      ((1 - t : Real) : EReal) * (f1 x + f2 x) =
        ((1 - t : Real) : EReal) * f1 x + ((1 - t : Real) : EReal) * f2 x := by
    simpa using
      (EReal.left_distrib_of_nonneg_of_ne_top ha_nonneg ha_ne_top (f1 x) (f2 x))
  have h_b :
      ((t : Real) : EReal) * (f1 y + f2 y) =
        ((t : Real) : EReal) * f1 y + ((t : Real) : EReal) * f2 y := by
    simpa using
      (EReal.left_distrib_of_nonneg_of_ne_top hb_nonneg hb_ne_top (f1 y) (f2 y))
  have hsum_eq :
      (((1 - t : Real) : EReal) * f1 x + ((t : Real) : EReal) * f1 y) +
          (((1 - t : Real) : EReal) * f2 x + ((t : Real) : EReal) * f2 y) =
        ((1 - t : Real) : EReal) * (f1 x + f2 x) + ((t : Real) : EReal) * (f1 y + f2 y) := by
    calc
      (((1 - t : Real) : EReal) * f1 x + ((t : Real) : EReal) * f1 y) +
          (((1 - t : Real) : EReal) * f2 x + ((t : Real) : EReal) * f2 y) =
        ((1 - t : Real) : EReal) * f1 x + ((1 - t : Real) : EReal) * f2 x +
          (((t : Real) : EReal) * f1 y + ((t : Real) : EReal) * f2 y) := by
        simp [add_assoc, add_left_comm, add_comm]
      _ = ((1 - t : Real) : EReal) * (f1 x + f2 x) + ((t : Real) : EReal) * (f1 y + f2 y) := by
        rw [h_a.symm, h_b.symm]
  refine hsum.trans ?_
  rw [hsum_eq]

/-- Theorem 5.2: If `f1` and `f2` are proper convex functions on `R^n`, then
`f1 + f2` is convex. -/
theorem convexFunctionOn_add_of_proper {n : Nat} {f1 f2 : (Fin n → Real) → EReal}
    (hf1 : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f1)
    (hf2 : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f2) :
    ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (fun x => f1 x + f2 x) := by
  have hnotbot1 : ∀ x, f1 x ≠ ⊥ := by
    intro x
    exact hf1.2.2 x (by simp)
  have hnotbot2 : ∀ x, f2 x ≠ ⊥ := by
    intro x
    exact hf2.2.2 x (by simp)
  have hnotbot_sum :
      ∀ x ∈ (Set.univ : Set (Fin n → Real)), f1 x + f2 x ≠ ⊥ := by
    intro x hx
    exact add_ne_bot_of_notbot (hnotbot1 x) (hnotbot2 x)
  refine
    (convexFunctionOn_iff_segment_inequality (C := Set.univ)
      (f := fun x => f1 x + f2 x)
      (hC := convex_univ)
      (hnotbot := hnotbot_sum)).2 ?_
  intro x hx y hy t ht0 ht1
  have hseg :=
    segment_inequality_add_univ (hf1 := hf1.1) (hf2 := hf2.1)
      (hnotbot1 := hnotbot1) (hnotbot2 := hnotbot2) x y t ht0 ht1
  simpa using hseg

/-- Text 5.2.1: A linear combination `lambda_1 f_1 + ... + lambda_m f_m` of proper convex functions
with non-negative coefficients is convex. -/
theorem convexFunctionOn_linearCombination_of_proper {n m : Nat}
    {f : Fin m → (Fin n → Real) → EReal} {lam : Fin m → Real}
    (hlam : ∀ i, 0 ≤ lam i)
    (hf : ∀ i, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (f i)) :
    ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real)))
      (fun x => Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i x)) := by
  classical
  have hnotbot_term : ∀ i x, ((lam i : Real) : EReal) * f i x ≠ ⊥ := by
    intro i x
    by_cases h0 : lam i = 0
    · simp [h0]
    · have hpos : 0 < lam i := lt_of_le_of_ne (hlam i) (Ne.symm h0)
      exact ereal_mul_ne_bot_of_pos hpos ((hf i).2.2 x (by simp))
  have hnotbot_sum' :
      ∀ s : Finset (Fin m), ∀ x,
        s.sum (fun i => ((lam i : Real) : EReal) * f i x) ≠ ⊥ := by
    intro s x
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha hs
      have hterm : ((lam a : Real) : EReal) * f a x ≠ ⊥ := hnotbot_term a x
      have hsum : s.sum (fun i => ((lam i : Real) : EReal) * f i x) ≠ ⊥ := hs
      simpa [Finset.sum_insert, ha] using add_ne_bot_of_notbot hterm hsum
  have hnotbot_sum :
      ∀ x ∈ (Set.univ : Set (Fin n → Real)),
        Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i x) ≠ ⊥ := by
    intro x hx
    exact hnotbot_sum' Finset.univ x
  refine
    (convexFunctionOn_iff_segment_inequality (C := Set.univ)
      (f := fun x => Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i x))
      (hC := convex_univ)
      (hnotbot := hnotbot_sum)).2 ?_
  intro x hx y hy t ht0 ht1
  have hseg :
      ∀ i, f i ((1 - t) • x + t • y) ≤
        ((1 - t : Real) : EReal) * f i x + ((t : Real) : EReal) * f i y := by
    intro i
    have hnotbot_i : ∀ x, f i x ≠ ⊥ := by
      intro x
      exact (hf i).2.2 x (by simp)
    exact segment_inequality_f_univ (hf := (hf i).1) (hnotbot := hnotbot_i) x y t ht0 ht1
  have hsum_le :
      Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i ((1 - t) • x + t • y)) ≤
        Finset.univ.sum (fun i =>
          ((lam i : Real) : EReal) *
            (((1 - t : Real) : EReal) * f i x + ((t : Real) : EReal) * f i y)) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hlamE : (0 : EReal) ≤ (lam i : EReal) := (EReal.coe_nonneg).2 (hlam i)
    exact mul_le_mul_of_nonneg_left (hseg i) hlamE
  have hsum_rhs :
      Finset.univ.sum (fun i =>
        ((lam i : Real) : EReal) *
          (((1 - t : Real) : EReal) * f i x + ((t : Real) : EReal) * f i y)) =
        ((1 - t : Real) : EReal) *
          (Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i x)) +
        ((t : Real) : EReal) *
          (Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i y)) := by
    have hnonneg1 : (0 : EReal) ≤ ((1 - t : Real) : EReal) :=
      (EReal.coe_nonneg).2 (sub_nonneg.mpr (le_of_lt ht1))
    have hnonneg2 : (0 : EReal) ≤ ((t : Real) : EReal) :=
      (EReal.coe_nonneg).2 (le_of_lt ht0)
    calc
      Finset.univ.sum (fun i =>
        ((lam i : Real) : EReal) *
          (((1 - t : Real) : EReal) * f i x + ((t : Real) : EReal) * f i y)) =
        Finset.univ.sum (fun i =>
          ((1 - t : Real) : EReal) * (((lam i : Real) : EReal) * f i x) +
          ((t : Real) : EReal) * (((lam i : Real) : EReal) * f i y)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hlamE : (0 : EReal) ≤ (lam i : EReal) := (EReal.coe_nonneg).2 (hlam i)
          have hlam_ne_top : (lam i : EReal) ≠ ⊤ := EReal.coe_ne_top (lam i)
          calc
            ((lam i : Real) : EReal) *
                (((1 - t : Real) : EReal) * f i x + ((t : Real) : EReal) * f i y) =
              ((lam i : Real) : EReal) * (((1 - t : Real) : EReal) * f i x) +
                ((lam i : Real) : EReal) * (((t : Real) : EReal) * f i y) := by
                  exact
                    EReal.left_distrib_of_nonneg_of_ne_top
                      (x := ((lam i : Real) : EReal)) hlamE hlam_ne_top
                      (((1 - t : Real) : EReal) * f i x) (((t : Real) : EReal) * f i y)
            _ = ((1 - t : Real) : EReal) * (((lam i : Real) : EReal) * f i x) +
                ((t : Real) : EReal) * (((lam i : Real) : EReal) * f i y) := by
                  simp [mul_comm, mul_left_comm, mul_assoc]
      _ =
        Finset.univ.sum (fun i =>
            ((1 - t : Real) : EReal) * (((lam i : Real) : EReal) * f i x)) +
          Finset.univ.sum (fun i =>
            ((t : Real) : EReal) * (((lam i : Real) : EReal) * f i y)) := by
          exact
            (Finset.sum_add_distrib (s := Finset.univ)
              (f := fun i => ((1 - t : Real) : EReal) * (((lam i : Real) : EReal) * f i x))
              (g := fun i => ((t : Real) : EReal) * (((lam i : Real) : EReal) * f i y)))
      _ =
        ((1 - t : Real) : EReal) *
            (Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i x)) +
          ((t : Real) : EReal) *
            (Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i y)) := by
          have hmul1 :
              Finset.univ.sum (fun i =>
                ((1 - t : Real) : EReal) * (((lam i : Real) : EReal) * f i x)) =
                ((1 - t : Real) : EReal) *
                  (Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i x)) := by
            exact
              (EReal.mul_sum_of_nonneg_of_ne_top (s := Finset.univ)
                (a := ((1 - t : Real) : EReal)) hnonneg1 (EReal.coe_ne_top (1 - t))
                (f := fun i => ((lam i : Real) : EReal) * f i x)).symm
          have hmul2 :
              Finset.univ.sum (fun i =>
                ((t : Real) : EReal) * (((lam i : Real) : EReal) * f i y)) =
                ((t : Real) : EReal) *
                  (Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i y)) := by
            exact
              (EReal.mul_sum_of_nonneg_of_ne_top (s := Finset.univ)
                (a := ((t : Real) : EReal)) hnonneg2 (EReal.coe_ne_top t)
                (f := fun i => ((lam i : Real) : EReal) * f i y)).symm
          rw [hmul1, hmul2]
  calc
    Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i ((1 - t) • x + t • y)) ≤
        Finset.univ.sum (fun i =>
          ((lam i : Real) : EReal) *
            (((1 - t : Real) : EReal) * f i x + ((t : Real) : EReal) * f i y)) := hsum_le
    _ =
        ((1 - t : Real) : EReal) *
          (Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i x)) +
        ((t : Real) : EReal) *
          (Finset.univ.sum (fun i => ((lam i : Real) : EReal) * f i y)) := hsum_rhs

/-- Text 5.2.2: If `f` is a finite convex function and `C` is a nonempty convex set, then
`f x + δ(x | C) = f x` for `x ∈ C` and `f x + δ(x | C) = +∞` for `x ∉ C`, where
`δ(· | C)` is the indicator function of `C`. -/
lemma add_indicatorFunction_eq {n : Nat} {f : (Fin n → Real) → Real} {C : Set (Fin n → Real)} :
    ∀ x, (f x : EReal) + indicatorFunction C x =
      (by
        classical
        exact if x ∈ C then (f x : EReal) else (⊤ : EReal)) := by
  classical
  intro x
  by_cases hx : x ∈ C
  · simp [indicatorFunction, hx]
  · have hne : (f x : EReal) ≠ ⊥ := EReal.coe_ne_bot _
    have htop : (f x : EReal) + indicatorFunction C x = (⊤ : EReal) := by
      calc
        (f x : EReal) + indicatorFunction C x = (f x : EReal) + (⊤ : EReal) := by
          simp [indicatorFunction, hx]
        _ = ⊤ := EReal.add_top_of_ne_bot hne
    simpa [hx] using htop

end Section05
end Chap01
