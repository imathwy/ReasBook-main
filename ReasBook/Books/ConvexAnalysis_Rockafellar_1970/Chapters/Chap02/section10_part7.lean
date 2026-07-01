/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Guangxuan Pan, Siyuan Shao, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section10_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section10_part6

noncomputable section

section Chap02
section Section10

open scoped BigOperators Pointwise

/-- Definition 10.5.4. Let `S ⊆ ℝ^n` and let `{f i | i ∈ I}` be a family of real-valued functions
defined on `S`. The family is *uniformly equicontinuous relative to `S`* if for every `ε > 0`
there exists `δ > 0` such that for all `x ∈ S`, `y ∈ S`, and all indices `i`, if `‖y - x‖ ≤ δ`
then `|f i y - f i x| ≤ ε`. -/
def Function.UniformlyEquicontinuousRelativeTo {n : ℕ} {I : Type*}
    (f : I → EuclideanSpace Real (Fin n) → Real) (S : Set (EuclideanSpace Real (Fin n))) : Prop :=
  UniformEquicontinuousOn f S

/-- Theorem 10.5.5. Let `S ⊆ ℝ^n` and let `{f i | i ∈ I}` be a collection of real-valued
functions on `S`. If the family is equi-Lipschitzian relative to `S`, then it is uniformly
equicontinuous relative to `S`. -/
theorem Function.uniformlyEquicontinuousRelativeTo_of_equiLipschitzRelativeTo {n : ℕ} {I : Type*}
    {f : I → EuclideanSpace Real (Fin n) → Real} {S : Set (EuclideanSpace Real (Fin n))}
    (hf : Function.EquiLipschitzRelativeTo f S) :
    Function.UniformlyEquicontinuousRelativeTo f S := by
  rcases hf with ⟨K, hK⟩
  simpa [Function.UniformlyEquicontinuousRelativeTo] using
    (LipschitzOnWith.uniformEquicontinuousOn (f := f) (s := S) (K := K) hK)

/-- Definition 10.5.6. Let `S ⊆ ℝ^n` and let `{f i | i ∈ I}` be a collection of real-valued
functions on `S`. The collection `{f i | i ∈ I}` is *pointwise bounded on `S`* if for each
`x ∈ S` the set of real numbers `{f i x | i ∈ I}` is bounded. -/
def Function.PointwiseBoundedOn {n : ℕ} {I : Type*}
    (f : I → EuclideanSpace Real (Fin n) → Real) (S : Set (EuclideanSpace Real (Fin n))) : Prop :=
  ∀ x ∈ S, Bornology.IsBounded (Set.range fun i : I => f i x)

/-- Definition 10.5.7. Let `S ⊆ ℝ^n` and let `{f i | i ∈ I}` be a collection of real-valued
functions on `S`. The collection `{f i | i ∈ I}` is *uniformly bounded on `S`* if there exist
real numbers `α₁` and `α₂` such that
`α₁ ≤ f i x ≤ α₂` for all `x ∈ S` and all indices `i`. -/
def Function.UniformlyBoundedOn {n : ℕ} {I : Type*}
    (f : I → EuclideanSpace Real (Fin n) → Real) (S : Set (EuclideanSpace Real (Fin n))) : Prop :=
  ∃ α₁ α₂ : Real, ∀ i x, x ∈ S → α₁ ≤ f i x ∧ f i x ≤ α₂

/-- A closed and bounded subset of `ℝ^n` is compact. -/
lemma Section10.isCompact_of_isClosed_isBounded {n : ℕ}
    {S : Set (EuclideanSpace Real (Fin n))} (hSclosed : IsClosed S)
    (hSbdd : Bornology.IsBounded S) : IsCompact S := by
  rcases hSbdd.subset_closedBall (0 : EuclideanSpace Real (Fin n)) with ⟨R, hR⟩
  exact (isCompact_closedBall (0 : EuclideanSpace Real (Fin n)) R).of_isClosed_subset hSclosed hR

/-- A uniform two-sided bound implies a uniform absolute bound. -/
lemma Section10.exists_abs_le_of_uniformlyBoundedOn {n : ℕ} {I : Type*}
    {f : I → EuclideanSpace Real (Fin n) → Real} {S : Set (EuclideanSpace Real (Fin n))}
    (h : Function.UniformlyBoundedOn f S) :
    ∃ M : Real, ∀ i x, x ∈ S → |f i x| ≤ M := by
  rcases h with ⟨α₁, α₂, hα⟩
  refine ⟨max |α₁| |α₂|, ?_⟩
  intro i x hx
  have hbounds := hα i x hx
  have hxle : f i x ≤ max |α₁| |α₂| :=
    le_trans hbounds.2 (le_trans (le_abs_self α₂) (le_max_right _ _))
  have hlehx : -max |α₁| |α₂| ≤ f i x := by
    have : -max |α₁| |α₂| ≤ α₁ := by
      have : -|α₁| ≤ α₁ := by
        simpa using (neg_abs_le α₁)
      exact le_trans (neg_le_neg (le_max_left |α₁| |α₂|)) this
    exact le_trans this hbounds.1
  exact abs_le.2 ⟨hlehx, hxle⟩

/-- If all functions in a convex family are uniformly bounded by `M` on a closed thickening of `S`
contained in `C`, then the family is uniformly bounded on `S` and equi-Lipschitzian relative to
`S`. -/
lemma Section10.uniformlyBoundedOn_and_equiLipschitzRelativeTo_of_abs_le_cthickening
    {n : ℕ} {I : Type*} {C S : Set (EuclideanSpace Real (Fin n))}
    {f : I → EuclideanSpace Real (Fin n) → Real} (hfconv : ∀ i, ConvexOn ℝ C (f i))
    {δ M : Real} (hδ : 0 < δ) (hcthick : Metric.cthickening δ S ⊆ C)
    (hM : ∀ i x, x ∈ Metric.cthickening δ S → |f i x| ≤ M) :
    Function.UniformlyBoundedOn f S ∧ Function.EquiLipschitzRelativeTo f S := by
  classical
  -- Uniform boundedness on `S` is immediate from the absolute bound on the thickening.
  have hSsub_ct : S ⊆ Metric.cthickening δ S :=
    (subset_closure.trans (Metric.closure_subset_cthickening δ S))
  have hM' : ∀ i x, x ∈ S → |f i x| ≤ max M 0 := by
    intro i x hx
    have : |f i x| ≤ M := hM i x (hSsub_ct hx)
    exact le_trans this (le_max_left _ _)
  have hUbdd : Function.UniformlyBoundedOn f S := by
    refine ⟨-(max M 0), (max M 0), ?_⟩
    intro i x hx
    have habs : |f i x| ≤ max M 0 := hM' i x hx
    exact ⟨(neg_le.1 (le_trans (neg_le_abs (f i x)) habs)), le_trans (le_abs_self (f i x)) habs⟩
  -- Equi-Lipschitz on `S` with constant `4 * (max M 0) / δ`.
  refine ⟨hUbdd, ?_⟩
  refine ⟨(2 * (max M 0) / (δ / 2)).toNNReal, ?_⟩
  intro i
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro x hx y hy
  by_cases hxy : dist x y < δ / 2
  · -- Local Lipschitz near `x` from convexity + uniform bound on `ball x δ`.
    have hball_ct : Metric.ball x δ ⊆ Metric.cthickening δ S := by
      exact
        (Metric.ball_subset_thickening hx δ).trans (Metric.thickening_subset_cthickening δ S)
    have hball_C : Metric.ball x δ ⊆ C := hball_ct.trans hcthick
    have hconv_ball : ConvexOn ℝ (Metric.ball x δ) (f i) :=
      (hfconv i).subset hball_C (convex_ball x δ)
    have hε : 0 < δ / 2 := by linarith
    have hMball : ∀ a, dist a x < δ → |f i a| ≤ max M 0 := by
      intro a ha
      have ha' : a ∈ Metric.ball x δ := by simpa [Metric.mem_ball] using ha
      have habs : |f i a| ≤ M := hM i a (hball_ct ha')
      exact habs.trans (le_max_left _ _)
    have hlip_ball :
        LipschitzOnWith (2 * (max M 0) / (δ / 2)).toNNReal (f i) (Metric.ball x (δ - δ / 2)) :=
      (ConvexOn.lipschitzOnWith_of_abs_le (hf := hconv_ball) (hε := hε) (M := max M 0) hMball)
    have hxball : x ∈ Metric.ball x (δ / 2) := by
      -- `dist x x = 0 < δ/2`.
      simpa [Metric.mem_ball, dist_self] using (half_pos hδ)
    have hyball : y ∈ Metric.ball x (δ / 2) := by
      have : dist y x < δ / 2 := by simpa [dist_comm] using hxy
      simpa [Metric.mem_ball] using this
    have hradius : δ - δ / 2 = δ / 2 := by ring
    have hxball' : x ∈ Metric.ball x (δ - δ / 2) := by simpa [hradius] using hxball
    have hyball' : y ∈ Metric.ball x (δ - δ / 2) := by simpa [hradius] using hyball
    -- Apply the Lipschitz bound on the ball and rewrite the radius.
    simpa [hradius] using (hlip_ball.dist_le_mul x hxball' y hyball')
  · -- Far points: use uniform boundedness to control the difference.
    have hge : δ / 2 ≤ dist x y := le_of_not_gt hxy
    have hx_ct : x ∈ Metric.cthickening δ S := hSsub_ct hx
    have hy_ct : y ∈ Metric.cthickening δ S := hSsub_ct hy
    have hxabs : |f i x| ≤ max M 0 := (hM i x hx_ct).trans (le_max_left _ _)
    have hyabs : |f i y| ≤ max M 0 := (hM i y hy_ct).trans (le_max_left _ _)
    have hdist_le : dist (f i x) (f i y) ≤ 2 * (max M 0) := by
      -- `|a - b| ≤ |a| + |b| ≤ 2M`.
      have habs_sub : |f i x - f i y| ≤ |f i x| + |f i y| := by
        simpa using (abs_sub_le (f i x) 0 (f i y))
      have habs_sum : |f i x| + |f i y| ≤ (max M 0) + (max M 0) := by
        gcongr
      have : |f i x - f i y| ≤ (max M 0) + (max M 0) :=
        le_trans habs_sub (le_trans habs_sum (by rfl))
      -- turn `|f x - f y|` into `dist (f x) (f y)`
      simpa [Real.dist_eq, two_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hδne : δ ≠ 0 := ne_of_gt hδ
    have hKnonneg : 0 ≤ 2 * (max M 0) / (δ / 2) := by
      have : 0 ≤ max M 0 := le_max_right _ _
      have : 0 ≤ 2 * (max M 0) := mul_nonneg (by norm_num) this
      exact div_nonneg this (by linarith)
    have hKcoe :
        ((2 * (max M 0) / (δ / 2)).toNNReal : ℝ) = 2 * (max M 0) / (δ / 2) :=
      Real.coe_toNNReal _ hKnonneg
    have hlarge :
        2 * (max M 0) ≤ (2 * (max M 0) / (δ / 2)) * dist x y := by
      calc
        2 * (max M 0) = (2 * (max M 0) / (δ / 2)) * (δ / 2) := by
          -- `a = (a / (δ/2)) * (δ/2)`
          field_simp [hδne]
        _ ≤ (2 * (max M 0) / (δ / 2)) * dist x y := by
          gcongr
    exact le_trans hdist_le (by simpa [hKcoe, mul_assoc] using hlarge)

/-- For a convex set `S` in `ℝ^n`, taking the closure does not create new interior points:
`interior (closure S) ⊆ S`. -/
lemma Section10.interior_closure_subset_of_convex {n : ℕ}
    (S : Set (EuclideanSpace Real (Fin n))) (hS : Convex ℝ S) :
    interior (closure S) ⊆ S := by
  by_cases hne : (interior (closure S)).Nonempty
  · -- If `interior (closure S)` is nonempty, then `S` has full affine span, hence
    -- `ri S = interior S`. Theorem 6.3 then identifies `interior (closure S)` with `interior S`.
    have hspan_int : affineSpan ℝ (interior (closure S)) = ⊤ :=
      (isOpen_interior.affineSpan_eq_top hne)
    have hspan_closure : affineSpan ℝ (closure S) = ⊤ := by
      apply top_unique
      have :
          (affineSpan ℝ (interior (closure S)) : AffineSubspace ℝ (EuclideanSpace Real (Fin n))) ≤
            affineSpan ℝ (closure S) :=
        affineSpan_mono ℝ interior_subset
      simpa [hspan_int] using this
    have hspan : affineSpan ℝ S = ⊤ := by
      -- `affineSpan (closure S) = affineSpan S`.
      simpa [affineSpan_closure_eq (n := n) (C := S)] using hspan_closure
    have hri_closure :
        euclideanRelativeInterior n (closure S) = interior (closure S) := by
      apply euclideanRelativeInterior_eq_interior_of_affineSpan_eq_univ (n := n) (C := closure S)
      simp [hspan_closure]
    have hri :
        euclideanRelativeInterior n S = interior S := by
      apply euclideanRelativeInterior_eq_interior_of_affineSpan_eq_univ (n := n) (C := S)
      simp [hspan]
    have h63 :=
      (euclidean_closure_relativeInterior_eq_and_relativeInterior_closure_eq (n := n) (C := S) hS).2
    -- Convert `interior (closure S)` to `interior S` via relative interior, then conclude.
    have : interior (closure S) = interior S := by
      calc
        interior (closure S) = euclideanRelativeInterior n (closure S) := by simp [hri_closure]
        _ = euclideanRelativeInterior n S := by simpa using h63
        _ = interior S := by simp [hri]
    simpa [this] using (interior_subset : interior S ⊆ S)
  · -- If the interior is empty, the inclusion is trivial.
    have hempty : interior (closure S) = (∅ : Set (EuclideanSpace Real (Fin n))) :=
      Set.eq_empty_iff_forall_notMem.2 (by
        intro x hx
        exact (hne ⟨x, hx⟩).elim)
    simp [hempty]

/-- Under hypothesis (a) from Theorem 10.6, the family is uniformly bounded above on any compact
subset `K ⊆ C`. -/
lemma Section10.exists_uniform_upper_bound_on_compact_of_exists_subset
    {n : ℕ} {I : Type*} {C : Set (EuclideanSpace Real (Fin n))}
    (hCopen : IsOpen C) (hCconv : Convex ℝ C) (f : I → EuclideanSpace Real (Fin n) → Real)
    (hfconv : ∀ i, ConvexOn ℝ C (f i))
    {C' : Set (EuclideanSpace Real (Fin n))} (hC'sub : C' ⊆ C)
    (hC'hull : C ⊆ convexHull ℝ (closure C'))
    (hC'bdAbove : ∀ x ∈ C', BddAbove (Set.range fun i : I => f i x))
    {K : Set (EuclideanSpace Real (Fin n))} (hKcomp : IsCompact K) (hKsubset : K ⊆ C) :
    ∃ M : ℝ, ∀ i x, x ∈ K → f i x ≤ M := by
  classical
  by_cases hI : IsEmpty I
  · refine ⟨0, ?_⟩
    intro i
    exact (IsEmpty.elim hI i)
  haveI : Nonempty I := (not_isEmpty_iff.1 hI)
  -- Transport the family to an extended-real convex function on the coordinate space.
  let e : EuclideanSpace Real (Fin n) ≃L[Real] (Fin n → Real) :=
    EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)
  let C0 : Set (Fin n → Real) := e '' C
  let C0' : Set (Fin n → Real) := e '' C'
  let K0 : Set (Fin n → Real) := e '' K
  have hK0comp : IsCompact K0 := hKcomp.image e.continuous
  have hK0sub : K0 ⊆ C0 := by
    rintro _ ⟨x, hxK, rfl⟩
    exact ⟨x, hKsubset hxK, rfl⟩
  -- Extend each `f i` by `⊤` outside `C0`.
  let G : I → (Fin n → Real) → EReal :=
    fun i x => if x ∈ C0 then (f i (e.symm x) : EReal) else (⊤ : EReal)
  have hGconv : ∀ i : I, ConvexFunctionOn (Set.univ : Set (Fin n → Real)) (G i) := by
    intro i
    have hgi :
        ConvexOn ℝ (e.symm ⁻¹' C) (fun x : Fin n → Real => f i (e.symm x)) :=
      (hfconv i).comp_linearMap e.symm.toLinearMap
    have hpre : e.symm ⁻¹' C = C0 := by
      ext x
      constructor
      · intro hx
        refine ⟨e.symm x, hx, ?_⟩
        simp
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    have hgi' : ConvexOn ℝ C0 (fun x : Fin n → Real => f i (e.symm x)) := by
      simpa [hpre] using hgi
    simpa [G] using
      (convexFunctionOn_univ_if_top (C := C0) (g := fun x : Fin n → Real => f i (e.symm x)) hgi')
  let F : (Fin n → Real) → EReal := fun x => iSup fun i : I => G i x
  have hFconv : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) F :=
    convexFunctionOn_iSup (f := fun i x => G i x) hGconv
  let domF : Set (Fin n → Real) := effectiveDomain (Set.univ : Set (Fin n → Real)) F
  -- `C0' ⊆ domF`: pointwise boundedness above at points of `C'`.
  have hC0'sub_dom : C0' ⊆ domF := by
    rintro _ ⟨x, hxC', rfl⟩
    -- Choose an upper bound `M` for the family at `x`.
    rcases (hC'bdAbove x hxC') with ⟨M, hM⟩
    have hxC0 : e x ∈ C0 := ⟨x, hC'sub hxC', rfl⟩
    have hle : F (e x) ≤ (M : EReal) := by
      refine iSup_le ?_
      intro i
      have : f i x ≤ M := by
        have : f i x ∈ Set.range (fun j : I => f j x) := ⟨i, rfl⟩
        exact hM this
      have hGx : G i (e x) = (f i x : EReal) := by
        simp [G, hxC0]
      simpa [F, hGx] using (EReal.coe_le_coe_iff.2 this)
    have hlt : F (e x) < (⊤ : EReal) := lt_of_le_of_lt hle (EReal.coe_lt_top M)
    have : e x ∈ (Set.univ : Set (Fin n → Real)) ∧ F (e x) < (⊤ : EReal) := ⟨by simp, hlt⟩
    simpa [domF, effectiveDomain_eq] using this
  -- Show `C0 ⊆ domF` using convexity of the effective domain and the hull condition on `C`.
  have hdomFconv : Convex ℝ domF := effectiveDomain_convex (S := Set.univ) hFconv
  let CE : Set (EuclideanSpace Real (Fin n)) := (fun x => e x) ⁻¹' domF
  have hCEconv : Convex ℝ CE := hdomFconv.linear_preimage e.toLinearMap
  have hC'sub_CE : C' ⊆ CE := by
    intro x hx
    have : e x ∈ domF := hC0'sub_dom ⟨x, hx, rfl⟩
    simpa [CE] using this
  have hCsub_closure_CE : C ⊆ closure CE := by
    intro x hxC
    have hx_hull : x ∈ convexHull ℝ (closure C') := hC'hull hxC
    have hcl : closure C' ⊆ closure CE := closure_mono hC'sub_CE
    have hclC : Convex ℝ (closure CE) := hCEconv.closure
    have : convexHull ℝ (closure C') ⊆ closure CE :=
      convexHull_min (s := closure C') (t := closure CE) hcl hclC
    exact this hx_hull
  have hCsub_CE : C ⊆ CE := by
    -- `C` is open and contained in `closure CE`, hence `C ⊆ interior (closure CE) ⊆ CE`.
    have hCsub_int : C ⊆ interior (closure CE) := by
      exact (hCopen.subset_interior_iff).2 hCsub_closure_CE
    have hint_sub : interior (closure CE) ⊆ CE :=
      Section10.interior_closure_subset_of_convex (n := n) CE hCEconv
    exact hCsub_int.trans hint_sub
  have hC0sub_dom : C0 ⊆ domF := by
    rintro _ ⟨x, hxC, rfl⟩
    have : x ∈ CE := hCsub_CE hxC
    simpa [CE] using this
  -- Continuity of `F` on `C0` (Theorem 10.1) and boundedness on `K0`.
  have hC0conv : Convex ℝ C0 := hCconv.linear_image e.toLinearMap
  have hCrelOpen : euclideanRelativelyOpen n ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹' C0) := by
    -- The preimage of `C0 = e '' C` is just `C`.
    have hpre : ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹' C0) = C := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, hyC, hyEq⟩
        have : e.symm (x : Fin n → Real) ∈ C := by
          -- rewrite the witness using the inverse equivalence
          have : e.symm (x : Fin n → Real) = y := by
            -- `hyEq : e y = x`, apply `e.symm` and simplify.
            simpa using (congrArg e.symm hyEq).symm
          simpa [this] using hyC
        simpa using this
      · intro hx
        refine ⟨x, hx, ?_⟩
        -- `e x` is definitional to `(x : Fin n → Real)` via the chosen equivalence.
        simp [e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv]
    -- Since `C` is open, it is relatively open.
    by_cases hCempty : C = ∅
    · subst hCempty
      -- Relative interior of `∅` is `∅`.
      have hri_empty : euclideanRelativeInterior n (∅ : Set (EuclideanSpace Real (Fin n))) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have : x ∈ (∅ : Set (EuclideanSpace Real (Fin n))) :=
          (euclideanRelativeInterior_subset_closure n (∅ : Set (EuclideanSpace Real (Fin n)))).1 hx
        exact this
      simp [euclideanRelativelyOpen, hpre, hri_empty]
    · have hCne : C.Nonempty := Set.nonempty_iff_ne_empty.2 hCempty
      have hspanC : affineSpan ℝ C = ⊤ := hCopen.affineSpan_eq_top hCne
      have hriC : euclideanRelativeInterior n C = interior C := by
        apply euclideanRelativeInterior_eq_interior_of_affineSpan_eq_univ (n := n) (C := C)
        simp [hspanC]
      simp [euclideanRelativelyOpen, hpre, hCopen.interior_eq, hriC]
  have hcontF : ContinuousOn F C0 :=
    convexFunctionOn_continuousOn_of_relOpen_effectiveDomain (n := n) (f := F)
      hFconv hC0conv hC0sub_dom hCrelOpen
  -- Convert the EReal bound into a real bound via `toReal` on `C0`.
  let g : (Fin n → Real) → Real := fun x => (F x).toReal
  have hmaps :
      Set.MapsTo F C0 ({⊥, ⊤}ᶜ : Set EReal) := by
    intro x hx
    have hneTop : F x ≠ (⊤ : EReal) := by
      have hxdom : x ∈ domF := hC0sub_dom hx
      have hxlt : F x < (⊤ : EReal) := (by
        have : x ∈ (Set.univ : Set (Fin n → Real)) ∧ F x < (⊤ : EReal) := by
          simpa [domF, effectiveDomain_eq] using hxdom
        exact this.2)
      exact (lt_top_iff_ne_top).1 hxlt
    have hneBot : F x ≠ (⊥ : EReal) := by
      classical
      -- Pick an index and compare with a finite value.
      let i0 : I := Classical.choice ‹Nonempty I›
      have hxC0 : x ∈ C0 := hx
      have : (f i0 (e.symm x) : EReal) ≤ F x := by
        have hGx : G i0 x = (f i0 (e.symm x) : EReal) := by simp [G, hxC0]
        simpa [F, hGx] using (le_iSup (fun i : I => G i x) i0)
      intro hbot
      have hlebot := this
      rw [hbot] at hlebot
      have : (f i0 (e.symm x) : EReal) = (⊥ : EReal) := (le_bot_iff.1 hlebot)
      exact (EReal.coe_ne_bot _ this).elim
    simp [Set.mem_compl_iff, Set.mem_insert_iff, hneBot, hneTop]
  have hcontg : ContinuousOn g C0 :=
    (EReal.continuousOn_toReal).comp hcontF hmaps
  have hgbdd : BddAbove (g '' K0) := by
    have hK0comp' : IsCompact K0 := hK0comp
    have hcontgK : ContinuousOn g K0 := hcontg.mono hK0sub
    exact (hK0comp'.image_of_continuousOn hcontgK).bddAbove
  rcases hgbdd with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro i x hxK
  have hxK0 : e x ∈ K0 := ⟨x, hxK, rfl⟩
  have hxC0 : e x ∈ C0 := hK0sub hxK0
  have hFneTop : F (e x) ≠ (⊤ : EReal) := by
    have hxdom : e x ∈ domF := hC0sub_dom hxC0
    have hxlt : F (e x) < (⊤ : EReal) := (by
      have : e x ∈ (Set.univ : Set (Fin n → Real)) ∧ F (e x) < (⊤ : EReal) := by
        simpa [domF, effectiveDomain_eq] using hxdom
      exact this.2)
    exact (lt_top_iff_ne_top).1 hxlt
  have hFneBot : F (e x) ≠ (⊥ : EReal) := by
    have : (f i x : EReal) ≤ F (e x) := by
      have hGx : G i (e x) = (f i x : EReal) := by
        simp [G, hxC0]
      simpa [F, hGx] using (le_iSup (fun j : I => G j (e x)) i)
    intro hbot
    have hlebot := this
    rw [hbot] at hlebot
    have : (f i x : EReal) = (⊥ : EReal) := (le_bot_iff.1 hlebot)
    exact (EReal.coe_ne_bot _ this).elim
  have hFx : F (e x) = (g (e x) : EReal) := by
    simpa [g] using (EReal.coe_toReal hFneTop hFneBot).symm
  have hle_g : g (e x) ≤ M := by
    have : g (e x) ∈ g '' K0 := ⟨e x, hxK0, rfl⟩
    exact hM this
  have hFle : F (e x) ≤ (M : EReal) := by
    simpa [hFx] using (EReal.coe_le_coe_iff.2 hle_g)
  have hfi : (f i x : EReal) ≤ F (e x) := by
    have hGx : G i (e x) = (f i x : EReal) := by simp [G, hxC0]
    simpa [F, hGx] using (le_iSup (fun j : I => G j (e x)) i)
  have : (f i x : EReal) ≤ (M : EReal) := le_trans hfi hFle
  exact (EReal.coe_le_coe_iff.1 this)

/-- Under hypothesis (b) from Theorem 10.6 and the uniform upper bound on a compact neighborhood of
`x₀`, the family is uniformly bounded below on any compact subset `K ⊆ C`. -/
lemma Section10.exists_uniform_lower_bound_on_compact_of_point_bddBelow
    {n : ℕ} {I : Type*} {C : Set (EuclideanSpace Real (Fin n))}
    (hCopen : IsOpen C) (f : I → EuclideanSpace Real (Fin n) → Real)
    (hfconv : ∀ i, ConvexOn ℝ C (f i))
    (hexists_bddBelow : ∃ x₀ ∈ C, BddBelow (Set.range fun i : I => f i x₀))
    (hUpper :
      ∀ {K : Set (EuclideanSpace Real (Fin n))},
        IsCompact K → K ⊆ C → ∃ M : ℝ, ∀ i x, x ∈ K → f i x ≤ M)
    {K : Set (EuclideanSpace Real (Fin n))} (hKcomp : IsCompact K) (hKsubset : K ⊆ C) :
    ∃ m : ℝ, ∀ i x, x ∈ K → m ≤ f i x := by
  classical
  by_cases hKempty : K = ∅
  · subst hKempty
    refine ⟨0, ?_⟩
    intro i x hx
    simpa using hx.elim
  rcases hexists_bddBelow with ⟨x₀, hx₀C, hx₀bdd⟩
  rcases hx₀bdd with ⟨m₀, hm₀⟩
  -- Choose a small closed ball around `x₀` contained in `C`.
  rcases Metric.isOpen_iff.1 hCopen x₀ hx₀C with ⟨r, hrpos, hrsub⟩
  let r₀ : ℝ := r / 2
  have hr₀pos : 0 < r₀ := by simpa [r₀] using (half_pos hrpos)
  have hballsub : Metric.closedBall x₀ r₀ ⊆ C := by
    intro y hy
    apply hrsub
    have hylt : dist y x₀ < r := by
      have hy' : dist y x₀ ≤ r₀ := by simpa [Metric.mem_closedBall, dist_comm] using hy
      have : r₀ < r := by
        dsimp [r₀]
        linarith [hrpos]
      exact lt_of_le_of_lt hy' this
    simpa [Metric.mem_ball, dist_comm] using hylt
  have hballcomp : IsCompact (Metric.closedBall x₀ r₀) :=
    isCompact_closedBall x₀ r₀
  rcases hUpper (K := Metric.closedBall x₀ r₀) hballcomp hballsub with ⟨M₁, hM₁⟩
  -- Enclose `K` in a closed ball around `x₀`.
  have hKbdd : Bornology.IsBounded K := hKcomp.isBounded
  rcases hKbdd.subset_closedBall x₀ with ⟨R, hR⟩
  have hKne : K.Nonempty := Set.nonempty_iff_ne_empty.2 hKempty
  have hRnonneg : 0 ≤ R := by
    rcases hKne with ⟨x, hxK⟩
    have hxR : x ∈ Metric.closedBall x₀ R := hR hxK
    have : dist x x₀ ≤ R := by simpa [Metric.mem_closedBall] using hxR
    exact le_trans dist_nonneg this
  let μ : ℝ := r₀ / (R + 1)
  have hμpos : 0 < μ := by
    have hden : 0 < R + 1 := by linarith [hRnonneg]
    exact div_pos hr₀pos hden
  refine ⟨((1 + μ) / μ) * m₀ - (1 / μ) * M₁, ?_⟩
  intro i x hxK
  -- Define the "reflected" point `y` near `x₀`.
  let y : EuclideanSpace Real (Fin n) := x₀ + μ • (x₀ - x)
  have hyball : y ∈ Metric.closedBall x₀ r₀ := by
    have hxR : x ∈ Metric.closedBall x₀ R := hR hxK
    have hxle : dist x₀ x ≤ R := by
      have : dist x x₀ ≤ R := by simpa [Metric.mem_closedBall] using hxR
      simpa [dist_comm] using this
    have hy_le : dist y x₀ ≤ r₀ := by
      have hy0 : dist y x₀ = ‖y - x₀‖ := by simp [dist_eq_norm]
      have hy1 : y - x₀ = μ • (x₀ - x) := by
        -- `y = x₀ + μ • (x₀ - x)`
        simp [y]
      have hy2 : ‖y - x₀‖ = μ * ‖x₀ - x‖ := by
        calc
          ‖y - x₀‖ = ‖μ • (x₀ - x)‖ := by simp [hy1]
          _ = |μ| * ‖x₀ - x‖ := by simp [norm_smul]
          _ = μ * ‖x₀ - x‖ := by simp [abs_of_pos hμpos]
      have hxle' : ‖x₀ - x‖ ≤ R := by
        -- `‖x₀ - x‖ = dist x₀ x`
        simpa [dist_eq_norm] using hxle
      have hμnonneg : 0 ≤ μ := le_of_lt hμpos
      have hy3 : μ * ‖x₀ - x‖ ≤ μ * R := by gcongr
      have hRle : R ≤ R + 1 := by linarith
      have hμR : μ * R ≤ μ * (R + 1) := by
        exact mul_le_mul_of_nonneg_left hRle hμnonneg
      have hμmul : μ * (R + 1) = r₀ := by
        have hden : R + 1 ≠ 0 := by linarith [hRnonneg]
        dsimp [μ]
        field_simp [hden]
      have : μ * ‖x₀ - x‖ ≤ r₀ := by
        exact le_trans hy3 (by simpa [hμmul] using hμR)
      -- convert back to `dist`.
      simpa [hy0, hy2] using this
    simpa [Metric.mem_closedBall, dist_comm] using hy_le
  have hyC : y ∈ C := hballsub hyball
  have hxC : x ∈ C := hKsubset hxK
  have hm0i : m₀ ≤ f i x₀ := hm₀ ⟨i, rfl⟩
  have hM1i : f i y ≤ M₁ := hM₁ i y hyball
  -- Express `x₀` as a convex combination of `x` and `y`, then rearrange convexity.
  let a : ℝ := μ / (1 + μ)
  let b : ℝ := (1 : ℝ) / (1 + μ)
  have hden : (1 + μ) ≠ 0 := by linarith [hμpos]
  have ha0 : 0 ≤ a := by
    have hpos : 0 < 1 + μ := by linarith [hμpos]
    exact div_nonneg (le_of_lt hμpos) (le_of_lt hpos)
  have hb0 : 0 ≤ b := by
    have hpos : 0 < 1 + μ := by linarith [hμpos]
    exact div_nonneg (by norm_num) (le_of_lt hpos)
  have hab : a + b = (1 : ℝ) := by
    dsimp [a, b]
    field_simp [hden]
    ring
  have hx0comb : a • x + b • y = x₀ := by
    -- Coordinate-wise computation in the underlying `Fin n → ℝ`.
    ext j
    -- Reduce to a scalar identity and clear denominators.
    simp [a, b, y, sub_eq_add_neg, add_left_comm, smul_add, smul_smul, mul_assoc,
      mul_comm, div_eq_mul_inv]
    field_simp [hden]
  have hconv :=
    (hfconv i).2 hxC hyC ha0 hb0 hab
  have hconv' : f i x₀ ≤ a * f i x + b * f i y := by
    -- Rewrite the `•`-form inequality as multiplication and use `hx0comb`.
    simpa [hx0comb, smul_eq_mul] using hconv
  -- Rearrange using the bounds at `x₀` and `y`.
  have hμne : μ ≠ 0 := ne_of_gt hμpos
  have : ((1 + μ) / μ) * m₀ - (1 / μ) * M₁ ≤ f i x := by
    have htpos : 0 < 1 + μ := by linarith [hμpos]
    -- From `hconv'`, clear denominators by multiplying by `1+μ`.
    have hconv'' : (1 + μ) * f i x₀ ≤ μ * f i x + f i y := by
      have hmul : (1 + μ) * f i x₀ ≤ (1 + μ) * (a * f i x + b * f i y) :=
        mul_le_mul_of_nonneg_left hconv' (by linarith [hμpos])
      have hcoef1 : (1 + μ) * a = μ := by
        dsimp [a]
        field_simp [hden]
      have hcoef2 : (1 + μ) * b = 1 := by
        dsimp [b]
        field_simp [hden]
      have hrhs : (1 + μ) * (a * f i x + b * f i y) = μ * f i x + f i y := by
        calc
          (1 + μ) * (a * f i x + b * f i y)
              = (1 + μ) * (a * f i x) + (1 + μ) * (b * f i y) := by ring
          _ = ((1 + μ) * a) * f i x + ((1 + μ) * b) * f i y := by ring
          _ = μ * f i x + (1 : ℝ) * f i y := by simp [hcoef1, hcoef2]
          _ = μ * f i x + f i y := by simp
      simpa [hrhs] using hmul
    -- Now use the pointwise bounds at `x₀` and `y` and rearrange.
    have hm0' : (1 + μ) * m₀ ≤ (1 + μ) * f i x₀ := by
      exact mul_le_mul_of_nonneg_left hm0i (by linarith [hμpos])
    have hupper' : f i y ≤ M₁ := hM1i
    have hμfx : (1 + μ) * m₀ - M₁ ≤ μ * f i x := by
      linarith [hconv'', hm0', hupper']
    have hdiv : ((1 + μ) * m₀ - M₁) / μ ≤ f i x := by
      have : (1 + μ) * m₀ - M₁ ≤ f i x * μ := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hμfx
      exact (div_le_iff₀ hμpos).2 this
    have hre : ((1 + μ) * m₀ - M₁) / μ = ((1 + μ) / μ) * m₀ - (1 / μ) * M₁ := by
      field_simp [hμne]
    simpa [hre] using hdiv
  exact this

/-- Under hypotheses (a) and (b) from Theorem 10.6, the family is uniformly
bounded on any compact subset `K ⊆ C`. -/
lemma Section10.uniformlyBoundedOn_on_compact_of_exists_subset
    {n : ℕ} {I : Type*} {C : Set (EuclideanSpace Real (Fin n))}
    (hCopen : IsOpen C) (hCconv : Convex ℝ C) (f : I → EuclideanSpace Real (Fin n) → Real)
    (hfconv : ∀ i, ConvexOn ℝ C (f i))
    {C' : Set (EuclideanSpace Real (Fin n))} (hC'sub : C' ⊆ C)
    (hC'hull : C ⊆ convexHull ℝ (closure C'))
    (hC'bdAbove : ∀ x ∈ C', BddAbove (Set.range fun i : I => f i x))
    (hexists_bddBelow : ∃ x ∈ C, BddBelow (Set.range fun i : I => f i x))
    {K : Set (EuclideanSpace Real (Fin n))} (hKcomp : IsCompact K) (hKsubset : K ⊆ C) :
    Function.UniformlyBoundedOn f K := by
  classical
  by_cases hI : IsEmpty I
  · refine ⟨0, 0, ?_⟩
    intro i
    exact (IsEmpty.elim hI i)
  -- Uniform upper bound on `K` from (a).
  rcases
      Section10.exists_uniform_upper_bound_on_compact_of_exists_subset (n := n) (I := I) (C := C)
        hCopen hCconv f hfconv hC'sub hC'hull hC'bdAbove (K := K) hKcomp hKsubset with
    ⟨M, hM⟩
  -- Uniform lower bound on `K` from (b) and the upper-bound lemma.
  rcases
      Section10.exists_uniform_lower_bound_on_compact_of_point_bddBelow (n := n) (I := I) (C := C)
        hCopen f hfconv hexists_bddBelow
        (hUpper := fun {K} hKc hKsub =>
      Section10.exists_uniform_upper_bound_on_compact_of_exists_subset (n := n) (I := I) (C := C)
        hCopen hCconv f hfconv hC'sub hC'hull hC'bdAbove (K := K) hKc hKsub)
        (K := K) hKcomp hKsubset with
    ⟨m, hm⟩
  refine ⟨m, M, ?_⟩
  intro i x hxK
  exact ⟨hm i x hxK, hM i x hxK⟩

/-- Theorem 10.6 (variant, auxiliary proof): reduce uniform boundedness + equi-Lipschitz to uniform
boundedness on a compact thickening of `S`. -/
lemma Section10.convexOn_family_uniformlyBoundedOn_and_equiLipschitzRelativeTo_of_exists_subset_aux
    {n : ℕ} {I : Type*} {C : Set (EuclideanSpace Real (Fin n))}
    (hCopen : IsOpen C) (hCconv : Convex ℝ C) (f : I → EuclideanSpace Real (Fin n) → Real)
    (hfconv : ∀ i, ConvexOn ℝ C (f i))
    {C' : Set (EuclideanSpace Real (Fin n))} (hC'sub : C' ⊆ C)
    (hC'hull : C ⊆ convexHull ℝ (closure C'))
    (hC'bdAbove : ∀ x ∈ C', BddAbove (Set.range fun i : I => f i x))
    (hexists_bddBelow : ∃ x ∈ C, BddBelow (Set.range fun i : I => f i x))
    {S : Set (EuclideanSpace Real (Fin n))} (hSclosed : IsClosed S) (hSbdd : Bornology.IsBounded S)
    (hSsubset : S ⊆ C) :
    Function.UniformlyBoundedOn f S ∧ Function.EquiLipschitzRelativeTo f S := by
  classical
  by_cases hSem : S = ∅
  · subst hSem
    refine ⟨?_, ?_⟩
    · refine ⟨0, 0, ?_⟩
      intro i x hx
      simpa using hx.elim
    · refine ⟨0, ?_⟩
      intro i
      simp
  -- Compactness of `S` and a compact thickening inside `C`.
  have hScomp : IsCompact S :=
    Section10.isCompact_of_isClosed_isBounded (n := n) (S := S) hSclosed hSbdd
  obtain ⟨δ, hδpos, hδsub⟩ := hScomp.exists_cthickening_subset_open hCopen hSsubset
  have hKcomp : IsCompact (Metric.cthickening δ S) := hScomp.cthickening
  have hKsub : Metric.cthickening δ S ⊆ C := hδsub
  -- Uniform boundedness on the compact thickening (the main nontrivial step).
  have hUbddK :
      Function.UniformlyBoundedOn f (Metric.cthickening δ S) :=
    Section10.uniformlyBoundedOn_on_compact_of_exists_subset (n := n) (I := I) (C := C)
      hCopen hCconv f hfconv hC'sub hC'hull hC'bdAbove hexists_bddBelow hKcomp hKsub
  -- Convert to an absolute bound on the thickening and apply the Lipschitz lemma.
  rcases Section10.exists_abs_le_of_uniformlyBoundedOn (n := n) (I := I) (f := f)
      (S := Metric.cthickening δ S) hUbddK with ⟨M, hM⟩
  exact
    Section10.uniformlyBoundedOn_and_equiLipschitzRelativeTo_of_abs_le_cthickening (n := n)
      (I := I) (C := C) (S := S) (f := f) hfconv hδpos hδsub (by
        intro i x hx
        exact hM i x hx)

/-- Theorem 10.6. Let `C` be a relatively open convex set, and let `{f i | i ∈ I}` be an
arbitrary collection of convex functions finite and pointwise bounded on `C`.
Let `S` be any closed bounded subset of `C`. Then `{f i | i ∈ I}` is uniformly bounded on `S`
and equi-Lipschitzian relative to `S`.

The conclusion remains valid if the pointwise boundedness assumption is weakened to the following
pair of assumptions:

(a) There exists a subset `C'` of `C` such that `conv (cl C') ⊇ C` and `sup {f i x | i ∈ I}` is
finite for every `x ∈ C'`;

(b) There exists at least one `x ∈ C` such that `inf {f i x | i ∈ I}` is finite. -/
theorem convexOn_family_uniformlyBoundedOn_and_equiLipschitzRelativeTo_of_pointwiseBoundedOn
    {n : ℕ} {I : Type*} {C : Set (EuclideanSpace Real (Fin n))}
    (hCopen : IsOpen C) (hCconv : Convex ℝ C) (f : I → EuclideanSpace Real (Fin n) → Real)
    (hfconv : ∀ i, ConvexOn ℝ C (f i)) (hfpt : Function.PointwiseBoundedOn f C)
    {S : Set (EuclideanSpace Real (Fin n))} (hSclosed : IsClosed S) (hSbdd : Bornology.IsBounded S)
    (hSsubset : S ⊆ C) :
    Function.UniformlyBoundedOn f S ∧ Function.EquiLipschitzRelativeTo f S := by
  classical
  by_cases hCempty : C = ∅
  · subst hCempty
    have hSem : S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro x hx
      exact (hSsubset hx).elim
    subst hSem
    refine ⟨?_, ?_⟩
    · refine ⟨0, 0, ?_⟩
      intro i x hx
      simpa using hx.elim
    · refine ⟨0, ?_⟩
      intro i
      simp
  have hCne : C.Nonempty := Set.nonempty_iff_ne_empty.2 hCempty
  -- Use the variant with `C' = C`. Hypothesis (a) comes from pointwise boundedness.
  have hC'bdAbove : ∀ x ∈ C, BddAbove (Set.range fun i : I => f i x) := by
    intro x hx
    have hbdd : Bornology.IsBounded (Set.range fun i : I => f i x) := hfpt x hx
    rcases hbdd.subset_closedBall (0 : Real) with ⟨R, hR⟩
    refine ⟨R, ?_⟩
    intro y hy
    have hy' : y ∈ Metric.closedBall (0 : Real) R := hR hy
    have : |y| ≤ R := by
      simpa [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hy'
    exact le_trans (le_abs_self y) this
  -- Hypothesis (b) also comes from pointwise boundedness at any `x₀ ∈ C`.
  rcases hCne with ⟨x₀, hx₀⟩
  have hexists_bddBelow : ∃ x ∈ C, BddBelow (Set.range fun i : I => f i x) := by
    refine ⟨x₀, hx₀, ?_⟩
    have hbdd : Bornology.IsBounded (Set.range fun i : I => f i x₀) := hfpt x₀ hx₀
    rcases hbdd.subset_closedBall (0 : Real) with ⟨R, hR⟩
    refine ⟨-R, ?_⟩
    intro y hy
    have hy' : y ∈ Metric.closedBall (0 : Real) R := hR hy
    have : |y| ≤ R := by
      simpa [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hy'
    exact (abs_le.mp this).1
  have hC'hull : C ⊆ convexHull ℝ (closure C) :=
    (subset_closure.trans (subset_convexHull ℝ (closure C)))
  exact
    Section10.convexOn_family_uniformlyBoundedOn_and_equiLipschitzRelativeTo_of_exists_subset_aux
      (n := n) (I := I) (C := C) hCopen hCconv f hfconv (C' := C) (by intro x hx; exact hx)
      hC'hull hC'bdAbove hexists_bddBelow hSclosed hSbdd hSsubset

/-- Theorem 10.6 (variant). The same conclusion under the weaker assumptions (a) and (b) stated
in Theorem 10.6. -/
theorem convexOn_family_uniformlyBoundedOn_and_equiLipschitzRelativeTo_of_exists_subset
    {n : ℕ} {I : Type*} {C : Set (EuclideanSpace Real (Fin n))}
    (hCopen : IsOpen C) (hCconv : Convex ℝ C) (f : I → EuclideanSpace Real (Fin n) → Real)
    (hfconv : ∀ i, ConvexOn ℝ C (f i))
    {C' : Set (EuclideanSpace Real (Fin n))} (hC'sub : C' ⊆ C)
    (hC'hull : C ⊆ convexHull ℝ (closure C'))
    (hC'bdAbove : ∀ x ∈ C', BddAbove (Set.range fun i : I => f i x))
    (hexists_bddBelow : ∃ x ∈ C, BddBelow (Set.range fun i : I => f i x))
    {S : Set (EuclideanSpace Real (Fin n))} (hSclosed : IsClosed S) (hSbdd : Bornology.IsBounded S)
    (hSsubset : S ⊆ C) :
    Function.UniformlyBoundedOn f S ∧ Function.EquiLipschitzRelativeTo f S := by
  exact
    Section10.convexOn_family_uniformlyBoundedOn_and_equiLipschitzRelativeTo_of_exists_subset_aux
      (n := n) (I := I) (C := C) hCopen hCconv f hfconv hC'sub hC'hull hC'bdAbove
      hexists_bddBelow hSclosed hSbdd hSsubset

end Section10
end Chap02
