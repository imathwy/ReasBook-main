/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yifan Bai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part4

open scoped Pointwise

section Chap01
section Section05

/-- The sInf over right scalar multiples reduces to the scaling set where `x ∈ lam • C`. -/
lemma sInf_rightScalarMultiple_indicator_add_one_eq_sInf_scaling {n : Nat}
    {C : Set (Fin n → Real)} (hCne : C.Nonempty) (hCconv : Convex ℝ C) :
    ∀ x : Fin n → Real,
      sInf { z : EReal | ∃ lam : Real, 0 ≤ lam ∧
        z = rightScalarMultiple (fun y => indicatorFunction C y + (1 : EReal)) lam x } =
        sInf ((fun r : ℝ => (r : EReal)) ''
          { r : ℝ | 0 ≤ r ∧ x ∈ (fun y => r • y) '' C }) := by
  classical
  intro x
  set S : Set EReal :=
    { z : EReal | ∃ lam : Real, 0 ≤ lam ∧
      z = rightScalarMultiple (fun y => indicatorFunction C y + (1 : EReal)) lam x }
  set T : Set EReal :=
    (fun r : ℝ => (r : EReal)) '' { r : ℝ | 0 ≤ r ∧ x ∈ (fun y => r • y) '' C }
  have hsubset : T ⊆ S := by
    intro z hz
    rcases hz with ⟨r, ⟨hr0, hx⟩, rfl⟩
    refine ⟨r, hr0, ?_⟩
    have hform :=
      rightScalarMultiple_indicator_add_one_nonneg (C := C) hCne hCconv (lam := r) hr0 x
    have hval : indicatorFunction (r • C) x = (0 : EReal) := by
      have hx' : x ∈ r • C := by
        simpa using hx
      simp [indicatorFunction, hx']
    simp [hform, hval]
  have hle : sInf S ≤ sInf T := sInf_le_sInf hsubset
  have hge : sInf T ≤ sInf S := by
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨lam, hlam, rfl⟩
    have hform :=
      rightScalarMultiple_indicator_add_one_nonneg (C := C) hCne hCconv (lam := lam) hlam x
    by_cases hx : x ∈ (fun y => lam • y) '' C
    · have hmem : ((lam : Real) : EReal) ∈ T := by
        exact ⟨lam, ⟨hlam, hx⟩, rfl⟩
      have hleT : sInf T ≤ ((lam : Real) : EReal) := sInf_le hmem
      have hval : indicatorFunction (lam • C) x = (0 : EReal) := by
        have hx' : x ∈ lam • C := by
          simpa using hx
        simp [indicatorFunction, hx']
      have hval' :
          rightScalarMultiple (fun y => indicatorFunction C y + (1 : EReal)) lam x =
            ((lam : Real) : EReal) := by
        simp [hform, hval]
      simpa [hval'] using hleT
    · have hval : indicatorFunction (lam • C) x = (⊤ : EReal) := by
        have hx' : x ∉ lam • C := by
          simpa using hx
        simp [indicatorFunction, hx']
      have hval' :
          rightScalarMultiple (fun y => indicatorFunction C y + (1 : EReal)) lam x =
            (⊤ : EReal) := by
        simp [hform, hval]
      simp [hval']
  exact le_antisymm hle hge

/-- The sInf of the `EReal`-coerced scaling set matches the gauge under absorbency. -/
lemma sInf_coe_image_eq_gauge {n : Nat} {C : Set (Fin n → Real)}
    (hCabs : ∀ x : Fin n → Real, ∃ lam : Real, 0 ≤ lam ∧ x ∈ (fun y => lam • y) '' C) :
    ∀ x : Fin n → Real,
      sInf ((fun r : ℝ => (r : EReal)) ''
        { r : ℝ | 0 ≤ r ∧ x ∈ (fun y => r • y) '' C }) =
        (gaugeOfConvexSet C x : EReal) := by
  classical
  intro x
  set A : Set ℝ := { r : ℝ | 0 ≤ r ∧ x ∈ r • C }
  set S : Set EReal := (fun r : ℝ => (r : EReal)) '' A
  have hAne : A.Nonempty := by
    rcases hCabs x with ⟨lam, hlam, hx⟩
    have hx' : x ∈ lam • C := by
      simpa using hx
    exact ⟨lam, ⟨hlam, hx'⟩⟩
  have hAbdd : BddBelow A := by
    refine ⟨0, ?_⟩
    intro r hr
    exact hr.1
  have hle : ((sInf A : ℝ) : EReal) ≤ sInf S := by
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨r, hr, rfl⟩
    have hle' : sInf A ≤ r := csInf_le hAbdd hr
    exact (EReal.coe_le_coe_iff).2 hle'
  have hge : sInf S ≤ ((sInf A : ℝ) : EReal) := by
    have hSne : S.Nonempty := by
      rcases hAne with ⟨r, hr⟩
      exact ⟨(r : EReal), ⟨r, hr, rfl⟩⟩
    have hnot_top : sInf S ≠ (⊤ : EReal) := by
      rcases hSne with ⟨z, hz⟩
      rcases hz with ⟨r, hr, rfl⟩
      intro htop
      have hle' : sInf S ≤ (r : EReal) := sInf_le ⟨r, hr, rfl⟩
      rw [htop] at hle'
      exact (not_top_le_coe r) hle'
    have h0le : (0 : EReal) ≤ sInf S := by
      refine le_sInf ?_
      intro z hz
      rcases hz with ⟨r, hr, rfl⟩
      exact (EReal.coe_nonneg).2 hr.1
    have hnot_bot : sInf S ≠ (⊥ : EReal) := by
      intro hbot
      rw [hbot] at h0le
      exact (not_le_of_gt (EReal.bot_lt_coe 0)) h0le
    have hlower :
        ∀ r ∈ A, (sInf S).toReal ≤ r := by
      intro r hr
      have hle' : sInf S ≤ (r : EReal) := sInf_le ⟨r, hr, rfl⟩
      exact EReal.toReal_le_toReal hle' hnot_bot (EReal.coe_ne_top r)
    have hle_real : (sInf S).toReal ≤ (sInf A : ℝ) :=
      le_csInf hAne (by intro r hr; exact hlower r hr)
    have hcoe :
        ((sInf S).toReal : EReal) ≤ ((sInf A : ℝ) : EReal) :=
      (EReal.coe_le_coe_iff).2 hle_real
    have hcoe_eq : ((sInf S).toReal : EReal) = (sInf S : EReal) :=
      EReal.coe_toReal hnot_top hnot_bot
    simpa [hcoe_eq] using hcoe
  have hSinf : sInf S = ((sInf A : ℝ) : EReal) := le_antisymm hge hle
  have hsimp : (gaugeOfConvexSet C x : EReal) = ((sInf A : ℝ) : EReal) := by
    simp [gaugeOfConvexSet, A]
  calc
    sInf ((fun r : ℝ => (r : EReal)) '' { r : ℝ | 0 ≤ r ∧ x ∈ r • C }) =
        ((sInf A : ℝ) : EReal) := by
          simpa [S, A] using hSinf
    _ = (gaugeOfConvexSet C x : EReal) := by
          simp [hsimp]

/-- The sInf of right scalar multiples of `indicatorFunction C + 1` matches the gauge. -/
lemma sInf_rightScalarMultiple_indicator_add_one_eq_gauge {n : Nat} {C : Set (Fin n → Real)}
    (hCne : C.Nonempty) (hCconv : Convex ℝ C)
    (hCabs : ∀ x : Fin n → Real, ∃ lam : Real, 0 ≤ lam ∧ x ∈ (fun y => lam • y) '' C) :
    ∀ x : Fin n → Real,
      sInf { z : EReal | ∃ lam : Real, 0 ≤ lam ∧
        z = rightScalarMultiple (fun y => indicatorFunction C y + (1 : EReal)) lam x } =
        (gaugeOfConvexSet C x : EReal) := by
  intro x
  calc
    sInf { z : EReal | ∃ lam : Real, 0 ≤ lam ∧
        z = rightScalarMultiple (fun y => indicatorFunction C y + (1 : EReal)) lam x } =
        sInf ((fun r : ℝ => (r : EReal)) ''
          { r : ℝ | 0 ≤ r ∧ x ∈ (fun y => r • y) '' C }) := by
          simpa using
            (sInf_rightScalarMultiple_indicator_add_one_eq_sInf_scaling
              (C := C) hCne hCconv x)
    _ = (gaugeOfConvexSet C x : EReal) := by
          simpa using (sInf_coe_image_eq_gauge (C := C) hCabs x)

/-- Text 5.4.11 (Gauge as a positively homogeneous hull): Let `C ⊆ ℝ^n` be nonempty and convex,
and assume every `x` is contained in some nonnegative scaling of `C`. Define `h(x)=δ(x|C)+1`.
Then for `λ ≥ 0`, `(h λ)(x)=δ(x|λ C)+λ`, and the positively homogeneous convex function
generated by `h` equals the gauge:
`inf { (h λ)(x) | λ ≥ 0 } = inf { λ ≥ 0 | x ∈ λ C } = γ(x|C)`. -/
theorem gauge_posHomogeneousHull_indicator_add_one {n : Nat} {C : Set (Fin n → Real)}
    (hCne : Set.Nonempty C) (hCconv : Convex ℝ C)
    (hCabs : ∀ x : Fin n → Real, ∃ lam : Real, 0 ≤ lam ∧ x ∈ (fun y => lam • y) '' C) :
    let h : (Fin n → Real) → EReal := fun x => indicatorFunction C x + (1 : EReal)
    (∀ lam : Real, 0 ≤ lam → ∀ x : Fin n → Real,
      rightScalarMultiple h lam x =
        indicatorFunction ((fun y => lam • y) '' C) x + ((lam : Real) : EReal))
    ∧
    (∀ x : Fin n → Real,
      sInf { z : EReal | ∃ lam : Real, 0 ≤ lam ∧ z = rightScalarMultiple h lam x } =
        (gaugeOfConvexSet C x : EReal)) := by
  classical
  let h : (Fin n → Real) → EReal := fun x => indicatorFunction C x + (1 : EReal)
  have hfirst :
      ∀ lam : Real, 0 ≤ lam → ∀ x : Fin n → Real,
        rightScalarMultiple h lam x =
          indicatorFunction ((fun y => lam • y) '' C) x + ((lam : Real) : EReal) := by
    intro lam hlam x
    by_cases h0 : lam = 0
    · subst h0
      simpa [h] using
        (rightScalarMultiple_indicator_add_one_zero (C := C) hCne hCconv x)
    · have hlam' : 0 < lam := lt_of_le_of_ne hlam (Ne.symm h0)
      simpa [h] using
        (rightScalarMultiple_indicator_add_one_pos (C := C) hCne hCconv
          (lam := lam) hlam' x)
  refine And.intro ?_ ?_
  · intro lam hlam x
    exact hfirst lam hlam x
  · intro x
    simpa [h] using
      (sInf_rightScalarMultiple_indicator_add_one_eq_gauge (C := C) hCne hCconv hCabs x)

/-- Text 5.5.0: The support function `delta*(· | C)` of a set `C` in `R^n` is convex. -/
lemma convexOn_supportFunction {n : Nat} (C : Set (Fin n → Real))
    (hCbd : ∀ x : Fin n → Real,
      BddAbove { r : ℝ | ∃ y ∈ C, r = dotProduct x y }) :
    ConvexOn ℝ (Set.univ : Set (Fin n → Real)) (supportFunction C) := by
  classical
  unfold ConvexOn
  refine And.intro ?_ ?_
  · simpa using (convex_univ : Convex ℝ (Set.univ : Set (Fin n → Real)))
  · intro x _ y _ a b ha hb hab
    by_cases hCne : C.Nonempty
    · have hne :
          Set.Nonempty { r : ℝ | ∃ z ∈ C, r = dotProduct (a • x + b • y) z } := by
          rcases hCne with ⟨z, hz⟩
          exact ⟨dotProduct (a • x + b • y) z, ⟨z, hz, rfl⟩⟩
      refine csSup_le hne ?_
      intro r hr
      rcases hr with ⟨z, hzC, rfl⟩
      have hxle : dotProduct x z ≤ supportFunction C x := by
        exact le_csSup (hCbd x) ⟨z, hzC, rfl⟩
      have hyle : dotProduct y z ≤ supportFunction C y := by
        exact le_csSup (hCbd y) ⟨z, hzC, rfl⟩
      have hdot :
          dotProduct (a • x + b • y) z = a * dotProduct x z + b * dotProduct y z := by
        simp
      calc
        dotProduct (a • x + b • y) z
            = a * dotProduct x z + b * dotProduct y z := hdot
        _ ≤ a * supportFunction C x + b * supportFunction C y := by
            exact add_le_add (mul_le_mul_of_nonneg_left hxle ha)
              (mul_le_mul_of_nonneg_left hyle hb)
    · have hCempty : C = (∅ : Set (Fin n → Real)) := by
        ext z
        by_cases hz : z ∈ C
        · exact (hCne ⟨z, hz⟩).elim
        · simp [hz]
      simp [supportFunction, hCempty]

/-- Epigraphs of convex functions on `univ` are convex. -/
lemma convex_epigraph_of_convexFunctionOn {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hf : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f) :
    Convex ℝ (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
  simpa [ConvexFunctionOn] using hf

/-- Intersections of epigraphs of convex functions on `univ` are convex. -/
lemma convex_iInter_epigraph {n : Nat} {ι : Sort _}
    {f : ι → (Fin n → Real) → EReal}
    (hf : ∀ i, ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (f i)) :
    Convex ℝ (⋂ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)) := by
  refine convex_iInter ?_
  intro i
  exact convex_epigraph_of_convexFunctionOn (hf i)

/-- The epigraph of a pointwise supremum equals the intersection of epigraphs. -/
lemma epigraph_iSup_eq_iInter_univ {n : Nat} {ι : Sort _}
    {f : ι → (Fin n → Real) → EReal} :
    epigraph (S := (Set.univ : Set (Fin n → Real)))
        (fun x => iSup (fun i => f i x)) =
      ⋂ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i) := by
  ext p
  constructor
  · intro hp
    have hp' :
        Set.univ p.1 ∧ iSup (fun i => f i p.1) ≤ (p.2 : EReal) := by
      simpa [epigraph] using hp
    have hp'' : ∀ i, f i p.1 ≤ (p.2 : EReal) := by
      intro i
      exact le_trans (le_iSup (fun j => f j p.1) i) hp'.2
    refine Set.mem_iInter.2 ?_
    intro i
    exact And.intro (by trivial) (hp'' i)
  · intro hp
    have hp' : ∀ i, f i p.1 ≤ (p.2 : EReal) := by
      intro i
      have hpi :
          p ∈ epigraph (S := (Set.univ : Set (Fin n → Real))) (f i) :=
        (Set.mem_iInter.1 hp) i
      have hpi' :
          Set.univ p.1 ∧ f i p.1 ≤ (p.2 : EReal) := by
        simpa [epigraph] using hpi
      exact hpi'.2
    have hsup : iSup (fun i => f i p.1) ≤ (p.2 : EReal) :=
      (iSup_le_iff).2 hp'
    exact And.intro (by trivial) hsup

/-- Theorem 5.5: The pointwise supremum of an arbitrary collection of convex functions is
convex. -/
theorem convexFunctionOn_iSup {n : Nat} {ι : Sort _}
    {f : ι → (Fin n → Real) → EReal}
    (hf : ∀ i, ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (f i)) :
    ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real)))
      (fun x => iSup (fun i => f i x)) := by
  have hconv_inter :
      Convex ℝ (⋂ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)) :=
    convex_iInter_epigraph (f := f) hf
  have h_epi :
      epigraph (S := (Set.univ : Set (Fin n → Real)))
          (fun x => iSup (fun i => f i x)) =
        ⋂ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i) :=
    epigraph_iSup_eq_iInter_univ (f := f)
  simpa [ConvexFunctionOn, h_epi] using hconv_inter
end Section05
end Chap01
