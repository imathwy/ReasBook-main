/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xinyi Guo, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section04_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part9

noncomputable section
open scoped Topology
open scoped Pointwise

section Chap02
section Section07

/-- Convexity of `t ↦ -sqrt (1 - t)` on `(-∞, 1)`. -/
lemma convexOn_neg_sqrt_one_sub :
    ConvexOn ℝ (Set.Iio (1 : ℝ)) (fun t => -Real.sqrt (1 - t)) := by
  have hconcave :
      ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ => Real.sqrt t) :=
    (Real.strictConcaveOn_sqrt).concaveOn
  have hconv0 :
      ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ => -Real.sqrt t) :=
    (neg_convexOn_iff).2 hconcave
  have hconvIic :
      ConvexOn ℝ (Set.Iic (1 : ℝ)) (fun t => -Real.sqrt (1 - t)) := by
    have h :
        ConvexOn ℝ (Set.Iic (1 : ℝ))
          ((fun t : ℝ => -Real.sqrt t) ∘ (AffineMap.lineMap (1 : ℝ) (0 : ℝ))) := by
      simpa [Set.preimage, Set.Ici, Set.Iic, AffineMap.lineMap_apply_ring] using
        (ConvexOn.comp_affineMap (g := AffineMap.lineMap (1 : ℝ) (0 : ℝ))
          (s := Set.Ici (0 : ℝ)) hconv0)
    refine h.congr ?_
    intro t ht
    simp [Function.comp, AffineMap.lineMap_apply_ring]
  exact hconvIic.subset Set.Iio_subset_Iic_self (convex_Iio (1 : ℝ))

/-- Monotonicity of `t ↦ -sqrt (1 - t)` on `(-∞, 1)`. -/
lemma monotoneOn_neg_sqrt_one_sub :
    MonotoneOn (fun t => -Real.sqrt (1 - t)) (Set.Iio (1 : ℝ)) := by
  intro x hx y hy hxy
  have hle : 1 - y ≤ 1 - x := by linarith
  have hsqrt : Real.sqrt (1 - y) ≤ Real.sqrt (1 - x) :=
    Real.sqrt_monotone hle
  linarith

/-- Convexity of the squared norm on the whole space. -/
lemma convexOn_norm_sq_univ {n : Nat} :
    ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) (fun x => ‖x‖ ^ (2 : ℕ)) := by
  have hnorm :
      ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) (fun x => ‖x‖) := by
    simpa using
      (convexOn_univ_norm :
        ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) (fun x => ‖x‖))
  have hnorm0 : ∀ ⦃x⦄, x ∈ (Set.univ : Set (Fin n → ℝ)) → 0 ≤ ‖x‖ := by
    intro x hx
    exact norm_nonneg _
  simpa using (hnorm.pow hnorm0 (2 : ℕ))

/-- Convexity of `x ↦ -sqrt(1 - ‖x‖^2)` on the open unit ball. -/
lemma convexOn_neg_sqrt_one_sub_norm_sq {n : Nat} :
    ConvexOn ℝ {x : Fin n → ℝ | ‖x‖ < 1}
      (fun x => -Real.sqrt (1 - ‖x‖ ^ (2 : ℕ))) := by
  classical
  set C : Set (Fin n → ℝ) := {x | ‖x‖ < 1} with hC
  set f : (Fin n → ℝ) → ℝ := fun x => ‖x‖ ^ (2 : ℕ) with hf
  set g : ℝ → ℝ := fun t => -Real.sqrt (1 - t) with hg
  have hconv_C : Convex ℝ C := by
    have hball : Convex ℝ (Metric.ball (0 : Fin n → ℝ) (1 : ℝ)) :=
      convex_ball (0 : Fin n → ℝ) (1 : ℝ)
    simpa [hC, Metric.ball, dist_eq_norm] using hball
  have hconv_f_univ : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f := by
    simpa [hf] using (convexOn_norm_sq_univ (n := n))
  have hconv_f : ConvexOn ℝ C f :=
    hconv_f_univ.subset (by intro x hx; exact Set.mem_univ x) hconv_C
  have hconv_g : ConvexOn ℝ (Set.Iio (1 : ℝ)) g := by
    simpa [hg] using (convexOn_neg_sqrt_one_sub)
  have hmono_g : MonotoneOn g (Set.Iio (1 : ℝ)) := by
    simpa [hg] using (monotoneOn_neg_sqrt_one_sub)
  refine ⟨hconv_C, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx_lt : ‖x‖ < 1 := by simpa [hC] using hx
  have hy_lt : ‖y‖ < 1 := by simpa [hC] using hy
  have hx_mem : f x ∈ Set.Iio (1 : ℝ) := by
    have hx' : ‖x‖ ^ (2 : ℕ) < (1 : ℝ) := by
      have h0 : 0 ≤ ‖x‖ := norm_nonneg _
      simpa using (pow_lt_one₀ (a := ‖x‖) h0 hx_lt (n := 2) (by decide))
    simpa [hf] using hx'
  have hy_mem : f y ∈ Set.Iio (1 : ℝ) := by
    have hy' : ‖y‖ ^ (2 : ℕ) < (1 : ℝ) := by
      have h0 : 0 ≤ ‖y‖ := norm_nonneg _
      simpa using (pow_lt_one₀ (a := ‖y‖) h0 hy_lt (n := 2) (by decide))
    simpa [hf] using hy'
  have hcomb_mem : a • f x + b • f y ∈ Set.Iio (1 : ℝ) :=
    (convex_Iio (1 : ℝ)) hx_mem hy_mem ha hb hab
  have hfa_le : f (a • x + b • y) ≤ a • f x + b • f y :=
    hconv_f.2 hx hy ha hb hab
  have hfa_mem : f (a • x + b • y) ∈ Set.Iio (1 : ℝ) := by
    have hcomb_lt : a • f x + b • f y < (1 : ℝ) := by
      simpa using hcomb_mem
    exact lt_of_le_of_lt hfa_le hcomb_lt
  have hmono_ineq : g (f (a • x + b • y)) ≤ g (a • f x + b • f y) :=
    hmono_g hfa_mem hcomb_mem hfa_le
  have hconv_ineq :
      g (a • f x + b • f y) ≤ a • g (f x) + b • g (f y) :=
    hconv_g.2 hx_mem hy_mem ha hb hab
  have hle := hmono_ineq.trans hconv_ineq
  simpa [hf, hg] using hle

/-- Remark 7.0.25: Theorem 7.5 can be used to show convexity. For example, the function
`f(x) = -(1 - |x|^2)^{1/2}` on `ℝ^n` (with `f(x) = +∞` for `|x| ≥ 1`) is convex by
verifying the limit relation in Theorem 7.5 at boundary points. -/
theorem convexFunction_negativeSqrt_unitBall {n : Nat} :
    ConvexFunction (fun x : (Fin n → Real) =>
      if ‖x‖ < 1 then ((-(Real.sqrt (1 - ‖x‖ ^ 2))) : Real) else (⊤ : EReal)) := by
  classical
  set C : Set (Fin n → ℝ) := {x | ‖x‖ < 1} with hC
  set g : (Fin n → ℝ) → ℝ := fun x => -Real.sqrt (1 - ‖x‖ ^ (2 : ℕ)) with hg
  have hconv : ConvexOn ℝ C g := by
    simpa [hC, hg] using (convexOn_neg_sqrt_one_sub_norm_sq (n := n))
  have hconvFun :
      ConvexFunctionOn Set.univ (fun x : Fin n → ℝ =>
        if x ∈ C then (g x : EReal) else (⊤ : EReal)) :=
    convexFunctionOn_univ_if_top (C := C) (g := g) hconv
  simpa [ConvexFunction, hC, hg] using hconvFun

/-- If `iInf f < α`, then some point in `ri (dom f)` satisfies `f x < α`. -/
lemma exists_lt_on_ri_effectiveDomain_of_iInf_lt {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) {α : Real}
    (hα : iInf (fun x => f x) < (α : EReal)) :
    ∃ x ∈
      euclideanRelativeInterior n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f),
      f x < (α : EReal) := by
  have hconv : ConvexFunction f := by
    simpa [ConvexFunction] using hf.1
  have hex : ∃ x, f x < (α : EReal) := (iInf_lt_iff).1 hα
  exact
    exists_lt_on_ri_effectiveDomain_of_convexFunction (n := n) (f := f) hconv hex

/-- Horizontal section of the embedded epigraph corresponds to the `≤`-sublevel set. -/
lemma levelSets_horizontal_section_mem_iff {n : Nat} {f : (Fin n → Real) → EReal}
    (α : Real) (x : EuclideanSpace Real (Fin n)) :
    let C : Set (EuclideanSpace Real (Fin (n + 1))) :=
      (appendAffineEquiv n 1) ''
        ((fun p : (Fin n → Real) × Real =>
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => p.2))) ''
          epigraph (S := (Set.univ : Set (Fin n → Real))) f)
    let y : EuclideanSpace Real (Fin n) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real)
    let zα : EuclideanSpace Real (Fin 1) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => α)
    appendAffineEquiv n 1 (y, zα) ∈ C ↔ f (x : Fin n → Real) ≤ (α : EReal) := by
  classical
  set C :
      Set (EuclideanSpace Real (Fin (n + 1))) :=
    (appendAffineEquiv n 1) ''
      ((fun p : (Fin n → Real) × Real =>
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => p.2))) ''
        epigraph (S := (Set.univ : Set (Fin n → Real))) f) with hC
  set y : EuclideanSpace Real (Fin n) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real) with hy
  set zα : EuclideanSpace Real (Fin 1) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => α) with hzα
  set Cy : EuclideanSpace Real (Fin n) → Set (EuclideanSpace Real (Fin 1)) :=
    fun y => {z | appendAffineEquiv n 1 (y, z) ∈ C} with hCy
  let coords1 := EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)
  let first1 : EuclideanSpace Real (Fin 1) → Real := fun z => coords1 z 0
  have hmem :
      zα ∈ Cy y ↔ f (x : Fin n → Real) ≤ (first1 zα : EReal) := by
    have hmem' :=
      (embedded_epigraph_section_mem_iff (n := n) (f := f) (x := (x : Fin n → Real)))
    simpa [C, y, Cy, coords1, first1, zα] using (hmem' zα)
  have hzα_first : first1 zα = α := by
    simp [first1, coords1, zα]
  have hmem'' :
      appendAffineEquiv n 1 (y, zα) ∈ C ↔ f (x : Fin n → Real) ≤ (first1 zα : EReal) := by
    simpa [Cy] using hmem
  simpa [hzα_first] using hmem''

/-- A point in `ri (dom f)` with `f x < α` yields a point of `ri (epi f)` at height `α`. -/
lemma exists_riEpigraph_point_at_height {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) {α : Real}
    (hα : iInf (fun x => f x) < (α : EReal)) :
    ∃ x ∈
      euclideanRelativeInterior n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f),
      f x < (α : EReal) ∧
        (appendAffineEquiv n 1)
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real),
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => α)) ∈ riEpigraph f := by
  have hconv : ConvexFunction f := by
    simpa [ConvexFunction] using hf.1
  obtain ⟨x, hxri, hxlt⟩ :=
    exists_lt_on_ri_effectiveDomain_of_iInf_lt (n := n) (f := f) hf hα
  have hxri' :
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real) ∈
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
    simpa using hxri
  have hri :
      (appendAffineEquiv n 1)
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real),
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => α)) ∈ riEpigraph f := by
    exact
      (riEpigraph_mem_iff (n := n) (f := f) hconv (x := (x : Fin n → Real)) (μ := α)).2
        ⟨hxri', hxlt, riEpigraph_mu_lt_top α⟩
  exact ⟨x, hxri, hxlt, hri⟩

/-- The horizontal hyperplane at height `α` meets `ri (epi f)` when `α > inf f`. -/
lemma levelSets_plane_meets_riEpigraph {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) {α : Real}
    (hα : iInf (fun x => f x) < (α : EReal)) :
    let C : Set (EuclideanSpace Real (Fin (n + 1))) :=
      (appendAffineEquiv n 1) ''
        ((fun p : (Fin n → Real) × Real =>
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => p.2))) ''
          epigraph (S := (Set.univ : Set (Fin n → Real))) f)
    let zα : EuclideanSpace Real (Fin 1) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => α)
    let φ : EuclideanSpace Real (Fin (n + 1)) →ₗ[Real] EuclideanSpace Real (Fin 1) :=
      (LinearMap.snd (R := Real) (M := EuclideanSpace Real (Fin n))
            (M₂ := EuclideanSpace Real (Fin 1))).comp
        (appendAffineEquiv n 1).symm.linear.toLinearMap
    let M : AffineSubspace Real (EuclideanSpace Real (Fin (n + 1))) :=
      AffineSubspace.mk' (appendAffineEquiv n 1 (0, zα)) (LinearMap.ker φ)
    ((M : Set _) ∩ euclideanRelativeInterior (n + 1) C).Nonempty := by
  classical
  intro C zα φ M
  obtain ⟨x, hxri, hxlt, hri⟩ :=
    exists_riEpigraph_point_at_height (n := n) (f := f) hf hα
  set y : EuclideanSpace Real (Fin n) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real) with hy
  have hlin : ∀ u, appendAffineEquiv n 1 u = (appendAffineEquiv n 1).linear u := by
    intro u
    simpa using congrArg (fun g => g u) (appendAffineEquiv_eq_linear_toAffineEquiv n 1)
  have hsymm_linear :
      (appendAffineEquiv n 1).linear.symm (appendAffineEquiv n 1 (y, zα)) = (y, zα) := by
    simp [hlin]
  have hphi : φ (appendAffineEquiv n 1 (y, zα)) = zα := by
    simp [φ, LinearMap.comp_apply, hsymm_linear]
  have hphi0 : φ (appendAffineEquiv n 1 (0, zα)) = zα := by
    have hsymm_linear0 :
        (appendAffineEquiv n 1).linear.symm (appendAffineEquiv n 1 (0, zα)) = (0, zα) := by
      simp [hlin]
    simp [φ, LinearMap.comp_apply, hsymm_linear0]
  have hker :
      appendAffineEquiv n 1 (y, zα) -ᵥ appendAffineEquiv n 1 (0, zα) ∈ LinearMap.ker φ := by
    have :
        φ (appendAffineEquiv n 1 (y, zα) -ᵥ appendAffineEquiv n 1 (0, zα)) = 0 := by
      simp [vsub_eq_sub, map_sub, hphi, hphi0]
    simpa [LinearMap.mem_ker] using this
  have hmemM : appendAffineEquiv n 1 (y, zα) ∈ (M : Set _) := by
    simpa [M] using hker
  have hri' : appendAffineEquiv n 1 (y, zα) ∈ euclideanRelativeInterior (n + 1) C := by
    simpa [riEpigraph, C, y, zα] using hri
  exact ⟨appendAffineEquiv n 1 (y, zα), ⟨hmemM, hri'⟩⟩

/-- Points of the form `appendAffineEquiv n 1 (y, zα)` lie in the horizontal plane `M`. -/
lemma appendAffineEquiv_mem_horizontal_plane {n : Nat} {α : Real}
    (y : EuclideanSpace Real (Fin n)) :
    let zα : EuclideanSpace Real (Fin 1) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => α)
    let φ : EuclideanSpace Real (Fin (n + 1)) →ₗ[Real] EuclideanSpace Real (Fin 1) :=
      (LinearMap.snd (R := Real) (M := EuclideanSpace Real (Fin n))
            (M₂ := EuclideanSpace Real (Fin 1))).comp
        (appendAffineEquiv n 1).symm.linear.toLinearMap
    let M : AffineSubspace Real (EuclideanSpace Real (Fin (n + 1))) :=
      AffineSubspace.mk' (appendAffineEquiv n 1 (0, zα)) (LinearMap.ker φ)
    appendAffineEquiv n 1 (y, zα) ∈ (M : Set _) := by
  classical
  intro zα φ M
  have hlin : ∀ u, appendAffineEquiv n 1 u = (appendAffineEquiv n 1).linear u := by
    intro u
    simpa using congrArg (fun g => g u) (appendAffineEquiv_eq_linear_toAffineEquiv n 1)
  have hsymm_linear :
      (appendAffineEquiv n 1).linear.symm (appendAffineEquiv n 1 (y, zα)) = (y, zα) := by
    simp [hlin]
  have hphi : φ (appendAffineEquiv n 1 (y, zα)) = zα := by
    simp [φ, LinearMap.comp_apply, hsymm_linear]
  have hphi0 : φ (appendAffineEquiv n 1 (0, zα)) = zα := by
    have hsymm_linear0 :
        (appendAffineEquiv n 1).linear.symm (appendAffineEquiv n 1 (0, zα)) = (0, zα) := by
      simp [hlin]
    simp [φ, LinearMap.comp_apply, hsymm_linear0]
  have hker :
      appendAffineEquiv n 1 (y, zα) -ᵥ appendAffineEquiv n 1 (0, zα) ∈ LinearMap.ker φ := by
    have :
        φ (appendAffineEquiv n 1 (y, zα) -ᵥ appendAffineEquiv n 1 (0, zα)) = 0 := by
      simp [vsub_eq_sub, map_sub, hphi, hphi0]
    simpa [LinearMap.mem_ker] using this
  simpa [M] using hker

/-- The horizontal slice of the embedded epigraph is the image of the `≤`-sublevel set. -/
lemma levelSets_horizontal_slice_image {n : Nat} {f : (Fin n → Real) → EReal} {α : Real} :
    let sublevel : Set (EuclideanSpace Real (Fin n)) :=
      {x | f (x : Fin n → Real) ≤ (α : EReal)}
    let C : Set (EuclideanSpace Real (Fin (n + 1))) :=
      (appendAffineEquiv n 1) ''
        ((fun p : (Fin n → Real) × Real =>
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => p.2))) ''
          epigraph (S := (Set.univ : Set (Fin n → Real))) f)
    let zα : EuclideanSpace Real (Fin 1) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => α)
    let φ : EuclideanSpace Real (Fin (n + 1)) →ₗ[Real] EuclideanSpace Real (Fin 1) :=
      (LinearMap.snd (R := Real) (M := EuclideanSpace Real (Fin n))
            (M₂ := EuclideanSpace Real (Fin 1))).comp
        (appendAffineEquiv n 1).symm.linear.toLinearMap
    let M : AffineSubspace Real (EuclideanSpace Real (Fin (n + 1))) :=
      AffineSubspace.mk' (appendAffineEquiv n 1 (0, zα)) (LinearMap.ker φ)
    let g : EuclideanSpace Real (Fin n) → EuclideanSpace Real (Fin (n + 1)) :=
      fun x =>
        appendAffineEquiv n 1
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real), zα)
    g '' sublevel = (M : Set _) ∩ C := by
  classical
  intro sublevel C zα φ M g
  ext w; constructor
  · rintro ⟨x, hx, rfl⟩
    have hC' :
        appendAffineEquiv n 1
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real), zα) ∈ C := by
      exact
        (levelSets_horizontal_section_mem_iff (n := n) (f := f) (α := α) (x := x)).2 hx
    have hC : g x ∈ C := by
      simpa [g] using hC'
    have hM : g x ∈ (M : Set _) := by
      set y : EuclideanSpace Real (Fin n) :=
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real)
      have hM' : appendAffineEquiv n 1 (y, zα) ∈ (M : Set _) := by
        simpa [M, zα, φ] using
          (appendAffineEquiv_mem_horizontal_plane (n := n) (α := α) (y := y))
      simpa [g, y] using hM'
    exact ⟨hM, hC⟩
  · rintro ⟨hwM, hwC⟩
    rcases (appendAffineEquiv n 1).surjective w with ⟨⟨y, z⟩, rfl⟩
    have hlin : ∀ u, appendAffineEquiv n 1 u = (appendAffineEquiv n 1).linear u := by
      intro u
      simpa using congrArg (fun g => g u) (appendAffineEquiv_eq_linear_toAffineEquiv n 1)
    have hsymm_linear :
        (appendAffineEquiv n 1).linear.symm (appendAffineEquiv n 1 (y, z)) = (y, z) := by
      simp [hlin]
    have hphi : φ (appendAffineEquiv n 1 (y, z)) = z := by
      simp [φ, LinearMap.comp_apply, hsymm_linear]
    have hsymm_linear0 :
        (appendAffineEquiv n 1).linear.symm (appendAffineEquiv n 1 (0, zα)) = (0, zα) := by
      simp [hlin]
    have hphi0 : φ (appendAffineEquiv n 1 (0, zα)) = zα := by
      simp [φ, LinearMap.comp_apply, hsymm_linear0]
    have hker :
        appendAffineEquiv n 1 (y, z) -ᵥ appendAffineEquiv n 1 (0, zα) ∈ LinearMap.ker φ := by
      have hmem : appendAffineEquiv n 1 (y, z) ∈ (M : Set _) := by
        simpa using hwM
      simpa [M] using (AffineSubspace.mem_mk').1 hmem
    have hphi_sub :
        φ (appendAffineEquiv n 1 (y, z) -ᵥ appendAffineEquiv n 1 (0, zα)) = 0 := by
      simpa [LinearMap.mem_ker] using hker
    have hphi_eq :
        φ (appendAffineEquiv n 1 (y, z)) = φ (appendAffineEquiv n 1 (0, zα)) := by
      have hphi_sub' :
          φ (appendAffineEquiv n 1 (y, z)) -
              φ (appendAffineEquiv n 1 (0, zα)) = 0 := by
        simpa [vsub_eq_sub, map_sub] using hphi_sub
      exact sub_eq_zero.mp hphi_sub'
    have hz : z = zα := by
      simpa [hphi, hphi0] using hphi_eq
    have hwC' : appendAffineEquiv n 1 (y, zα) ∈ C := by
      simpa [hz] using hwC
    have hy_mem : f (y : Fin n → Real) ≤ (α : EReal) := by
      have hwC'' : appendAffineEquiv n 1 (y, zα) ∈ C := hwC'
      have := (levelSets_horizontal_section_mem_iff (n := n) (f := f) (α := α) (x := y)).1 hwC''
      simpa using this
    refine ⟨y, ?_, ?_⟩
    · simpa [sublevel] using hy_mem
    · simp [g, hz]

/-- The horizontal slice map is a homeomorphism onto the plane `M`. -/
lemma horizontal_slice_homeomorph {n : Nat} {α : Real} :
    let zα : EuclideanSpace Real (Fin 1) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => α)
    let φ : EuclideanSpace Real (Fin (n + 1)) →ₗ[Real] EuclideanSpace Real (Fin 1) :=
      (LinearMap.snd (R := Real) (M := EuclideanSpace Real (Fin n))
            (M₂ := EuclideanSpace Real (Fin 1))).comp
        (appendAffineEquiv n 1).symm.linear.toLinearMap
    let M : AffineSubspace Real (EuclideanSpace Real (Fin (n + 1))) :=
      AffineSubspace.mk' (appendAffineEquiv n 1 (0, zα)) (LinearMap.ker φ)
    let g : EuclideanSpace Real (Fin n) → EuclideanSpace Real (Fin (n + 1)) :=
      fun x =>
        appendAffineEquiv n 1
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real), zα)
    ∃ gM : EuclideanSpace Real (Fin n) ≃ₜ M,
      ∀ x, (gM x).1 = g x := by
  classical
  intro zα φ M g
  have hg_mem : ∀ x, g x ∈ (M : Set _) := by
    intro x
    set y : EuclideanSpace Real (Fin n) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real)
    have hy : appendAffineEquiv n 1 (y, zα) ∈ (M : Set _) := by
      simpa [M, zα, φ] using
        (appendAffineEquiv_mem_horizontal_plane (n := n) (α := α) (y := y))
    simpa [g, y] using hy
  let gM_fun : EuclideanSpace Real (Fin n) → M :=
    fun x => ⟨g x, hg_mem x⟩
  let gM_inv : M → EuclideanSpace Real (Fin n) :=
    fun w => ((appendAffineEquiv n 1).symm w.1).1
  have hleft : ∀ x, gM_inv (gM_fun x) = x := by
    intro x
    simp [gM_fun, gM_inv, g]
  have hright : ∀ w, gM_fun (gM_inv w) = w := by
    rintro ⟨w, hwM⟩
    rcases (appendAffineEquiv n 1).surjective w with ⟨⟨y, z⟩, rfl⟩
    have hlin : ∀ u, appendAffineEquiv n 1 u = (appendAffineEquiv n 1).linear u := by
      intro u
      simpa using congrArg (fun g => g u) (appendAffineEquiv_eq_linear_toAffineEquiv n 1)
    have hsymm_linear :
        (appendAffineEquiv n 1).linear.symm (appendAffineEquiv n 1 (y, z)) = (y, z) := by
      simp [hlin]
    have hphi : φ (appendAffineEquiv n 1 (y, z)) = z := by
      simp [φ, LinearMap.comp_apply, hsymm_linear]
    have hsymm_linear0 :
        (appendAffineEquiv n 1).linear.symm (appendAffineEquiv n 1 (0, zα)) = (0, zα) := by
      simp [hlin]
    have hphi0 : φ (appendAffineEquiv n 1 (0, zα)) = zα := by
      simp [φ, LinearMap.comp_apply, hsymm_linear0]
    have hker :
        appendAffineEquiv n 1 (y, z) -ᵥ appendAffineEquiv n 1 (0, zα) ∈ LinearMap.ker φ := by
      have hmem : appendAffineEquiv n 1 (y, z) ∈ (M : Set _) := by
        simpa using hwM
      simpa [M] using (AffineSubspace.mem_mk').1 hmem
    have hphi_sub :
        φ (appendAffineEquiv n 1 (y, z) -ᵥ appendAffineEquiv n 1 (0, zα)) = 0 := by
      simpa [LinearMap.mem_ker] using hker
    have hphi_eq :
        φ (appendAffineEquiv n 1 (y, z)) = φ (appendAffineEquiv n 1 (0, zα)) := by
      have hphi_sub' :
          φ (appendAffineEquiv n 1 (y, z)) -
              φ (appendAffineEquiv n 1 (0, zα)) = 0 := by
        simpa [vsub_eq_sub, map_sub] using hphi_sub
      exact sub_eq_zero.mp hphi_sub'
    have hz : z = zα := by
      simpa [hphi, hphi0] using hphi_eq
    apply Subtype.ext
    simp [gM_fun, gM_inv, g, hz]
  have hcont_g : Continuous g := by
    have hcont_append : Continuous (appendAffineEquiv n 1 : _ → _) :=
      (appendAffineEquiv n 1).continuous_of_finiteDimensional
    have hcont_inner :
        Continuous fun x : EuclideanSpace Real (Fin n) => (x, zα) := by
      fun_prop
    have hg' : g = fun x => appendAffineEquiv n 1 (x, zα) := by
      funext x
      simp [g]
    simpa [hg'] using hcont_append.comp hcont_inner
  refine ⟨
    { toEquiv :=
        { toFun := gM_fun
          invFun := gM_inv
          left_inv := hleft
          right_inv := hright }
      continuous_toFun := (hcont_g.subtype_mk fun x => hg_mem x)
      continuous_invFun := by
        have hcont_append_symm : Continuous ((appendAffineEquiv n 1).symm : _ → _) :=
          (appendAffineEquiv n 1).symm.continuous_of_finiteDimensional
        have hcont_comp :
            Continuous fun w : M => (appendAffineEquiv n 1).symm w.1 :=
          hcont_append_symm.comp continuous_subtype_val
        simpa [gM_inv] using (continuous_fst.comp hcont_comp) }, ?_⟩
  intro x
  rfl

set_option maxHeartbeats 600000 in
/-- Pull back closure and relative interior across the horizontal slice homeomorphism. -/
lemma levelSets_horizontal_slice_preimage_closure_ri {n : Nat} {f : (Fin n → Real) → EReal}
    {α : Real} :
    let sublevel : Set (EuclideanSpace Real (Fin n)) :=
      {x | f (x : Fin n → Real) ≤ (α : EReal)}
    let C : Set (EuclideanSpace Real (Fin (n + 1))) :=
      (appendAffineEquiv n 1) ''
        ((fun p : (Fin n → Real) × Real =>
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => p.2))) ''
          epigraph (S := (Set.univ : Set (Fin n → Real))) f)
    let zα : EuclideanSpace Real (Fin 1) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => α)
    let φ : EuclideanSpace Real (Fin (n + 1)) →ₗ[Real] EuclideanSpace Real (Fin 1) :=
      (LinearMap.snd (R := Real) (M := EuclideanSpace Real (Fin n))
            (M₂ := EuclideanSpace Real (Fin 1))).comp
        (appendAffineEquiv n 1).symm.linear.toLinearMap
    let M : AffineSubspace Real (EuclideanSpace Real (Fin (n + 1))) :=
      AffineSubspace.mk' (appendAffineEquiv n 1 (0, zα)) (LinearMap.ker φ)
    let g : EuclideanSpace Real (Fin n) → EuclideanSpace Real (Fin (n + 1)) :=
      fun x =>
        appendAffineEquiv n 1
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real), zα)
    Convex Real C →
    ((M : Set _) ∩ euclideanRelativeInterior (n + 1) C).Nonempty →
    closure sublevel = g ⁻¹' ((M : Set _) ∩ closure C) ∧
      euclideanRelativeInterior n sublevel =
        g ⁻¹' ((M : Set _) ∩ euclideanRelativeInterior (n + 1) C) := by
  classical
  intro sublevel C zα φ M g hC hM
  obtain ⟨gM, hgM⟩ := horizontal_slice_homeomorph (n := n) (α := α)
  have himage : g '' sublevel = (M : Set _) ∩ C := by
    simpa [sublevel, C, zα, φ, M, g] using
      (levelSets_horizontal_slice_image (n := n) (f := f) (α := α))
  have himage_sub :
      gM '' sublevel = {x : M | (x : EuclideanSpace Real (Fin (n + 1))) ∈ C} := by
    ext w; constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : g x ∈ (M : Set _) ∩ C := by
        have : g x ∈ g '' sublevel := ⟨x, hx, rfl⟩
        simpa [himage] using this
      change (gM x : EuclideanSpace Real (Fin (n + 1))) ∈ C
      have hxg : (gM x : EuclideanSpace Real (Fin (n + 1))) = g x := by
        simpa using hgM x
      rw [hxg]
      exact hx'.2
    · intro hwC
      have hwMC : (w : EuclideanSpace Real (Fin (n + 1))) ∈ (M : Set _) ∩ C :=
        ⟨w.property, hwC⟩
      have hwimage : (w : EuclideanSpace Real (Fin (n + 1))) ∈ g '' sublevel := by
        simpa [himage] using hwMC
      rcases hwimage with ⟨x, hx, hxg⟩
      refine ⟨x, hx, ?_⟩
      apply Subtype.ext
      have hxg' : (gM x : EuclideanSpace Real (Fin (n + 1))) = g x := by
        simpa using hgM x
      -- compare underlying points in the ambient space
      calc
        (gM x : EuclideanSpace Real (Fin (n + 1))) = g x := hxg'
        _ = w := hxg
  have hri_cl :
      euclideanRelativeInterior (n + 1) ((M : Set _) ∩ C) =
          (M : Set _) ∩ euclideanRelativeInterior (n + 1) C ∧
        closure ((M : Set _) ∩ C) = (M : Set _) ∩ closure C :=
    euclideanRelativeInterior_inter_affineSubspace_eq_and_closure_eq
      (n := n + 1) (C := C) hC M hM
  have hclosure_sub :
      closure sublevel = g ⁻¹' ((M : Set _) ∩ closure C) := by
    set sM : Set M := {x : M | (x : EuclideanSpace Real (Fin (n + 1))) ∈ C}
    have hpreimage : gM ⁻¹' sM = sublevel := by
      -- rewrite the target using the image description
      rw [←himage_sub]
      exact Set.preimage_image_eq (f := gM) (s := sublevel) gM.injective
    have hpre : gM ⁻¹' closure sM = closure sublevel := by
      calc
        gM ⁻¹' closure sM = closure (gM ⁻¹' sM) := gM.preimage_closure (s := sM)
        _ = closure sublevel := by rw [hpreimage]
    have hclosure_subtype :
        closure sM =
          (Subtype.val : M → EuclideanSpace Real (Fin (n + 1))) ⁻¹'
            closure ((Subtype.val : M → EuclideanSpace Real (Fin (n + 1))) '' sM) := by
      simpa using
        (Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image (s := sM))
    have himage_subtype :
        (Subtype.val : M → EuclideanSpace Real (Fin (n + 1))) '' sM =
          (M : Set _) ∩ C := by
      ext x; constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.property, hx⟩
      · rintro ⟨hxM, hxC⟩
        exact ⟨⟨x, hxM⟩, hxC, rfl⟩
    have hpre0 : closure sublevel = gM ⁻¹' closure sM := by
      simpa using hpre.symm
    calc
      closure sublevel = gM ⁻¹' closure sM := hpre0
      _ =
          gM ⁻¹' ((Subtype.val : M → EuclideanSpace Real (Fin (n + 1))) ⁻¹'
            closure ((M : Set _) ∩ C)) := by
        simp [hclosure_subtype, himage_subtype]
      _ = g ⁻¹' closure ((M : Set _) ∩ C) := by
        ext x; constructor
        · intro hx
          have hx' :
              (gM x : EuclideanSpace Real (Fin (n + 1))) ∈ closure ((M : Set _) ∩ C) := by
            simpa [Set.mem_preimage] using hx
          have hxg : (gM x : EuclideanSpace Real (Fin (n + 1))) = g x := by
            dsimp [g]
            exact hgM x
          have : g x ∈ closure ((M : Set _) ∩ C) := by
            rw [← hxg]
            exact hx'
          simpa [Set.mem_preimage] using this
        · intro hx
          have hx' : g x ∈ closure ((M : Set _) ∩ C) := by
            simpa [Set.mem_preimage] using hx
          have hxg : (gM x : EuclideanSpace Real (Fin (n + 1))) = g x := by
            dsimp [g]
            exact hgM x
          have : (gM x : EuclideanSpace Real (Fin (n + 1))) ∈ closure ((M : Set _) ∩ C) := by
            rw [hxg]
            exact hx'
          simpa [Set.mem_preimage] using this
      _ = g ⁻¹' ((M : Set _) ∩ closure C) := by
        simp [hri_cl.2]
  have hri_sub :
      euclideanRelativeInterior n sublevel =
        g ⁻¹' ((M : Set _) ∩ euclideanRelativeInterior (n + 1) C) := by
    have hri_image :
        euclideanRelativeInterior (n + 1) ((M : Set _) ∩ C) =
          g '' euclideanRelativeInterior n sublevel := by
      -- Use linear part of the horizontal slice and translation.
      let Lprod :
          EuclideanSpace Real (Fin n) →ₗ[Real]
            (EuclideanSpace Real (Fin n) × EuclideanSpace Real (Fin 1)) :=
        LinearMap.inl (R := Real)
          (M := EuclideanSpace Real (Fin n)) (M₂ := EuclideanSpace Real (Fin 1))
      let L :
          EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin (n + 1)) :=
        (appendAffineEquiv n 1).linear.comp Lprod
      let A : EuclideanSpace Real (Fin n) →ᵃ[Real] EuclideanSpace Real (Fin (n + 1)) :=
        L.toAffineMap
      have hA0 : A 0 = 0 := by
        simp [A, L, Lprod]
      let p : EuclideanSpace Real (Fin (n + 1)) := appendAffineEquiv n 1 (0, zα)
      let e : EuclideanSpace Real (Fin (n + 1)) ≃ᵃ[Real] EuclideanSpace Real (Fin (n + 1)) :=
        AffineEquiv.vaddConst (k := Real)
          (V₁ := EuclideanSpace Real (Fin (n + 1)))
          (P₁ := EuclideanSpace Real (Fin (n + 1))) (b := p)
      have hg_eq : ∀ x, g x = e (A x) := by
        intro x
        have hlin : ∀ u, appendAffineEquiv n 1 u = (appendAffineEquiv n 1).linear u := by
          intro u
          simpa using
            congrArg (fun g => g u) (appendAffineEquiv_eq_linear_toAffineEquiv n 1)
        have hx :
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real) = x := by
          simp
        have hg' : g x = (appendAffineEquiv n 1).linear (x, zα) := by
          simp [g, hlin]
        have hA' : A x = (appendAffineEquiv n 1).linear (x, 0) := by
          simp [A, L, Lprod]
        have hp' : p = (appendAffineEquiv n 1).linear (0, zα) := by
          simp [p, hlin]
        have hsum : (x, zα) = (x, 0) + (0, zα) := by
          ext <;> simp
        calc
          g x = (appendAffineEquiv n 1).linear (x, zα) := hg'
          _ =
              (appendAffineEquiv n 1).linear (x, 0) +
                (appendAffineEquiv n 1).linear (0, zα) := by
              calc
                (appendAffineEquiv n 1).linear (x, zα) =
                    (appendAffineEquiv n 1).linear ((x, 0) + (0, zα)) := by
                      rw [hsum]
                _ =
                    (appendAffineEquiv n 1).linear (x, 0) +
                      (appendAffineEquiv n 1).linear (0, zα) := by
                      simpa using
                        (map_add (appendAffineEquiv n 1).linear (x, 0) (0, zα))
          _ = A x + p := by
            simp [hA', hp']
          _ = e (A x) := by
            simp [e, vadd_eq_add]
      have hconv_sub :
          Convex ℝ sublevel := by
        have hconv_MC : Convex ℝ ((M : Set _) ∩ C) := by
          exact (AffineSubspace.convex (Q := M)).inter hC
        have hg_inj : Function.Injective g := by
          intro x y hxy
          have hgm : gM x = gM y := by
            apply Subtype.ext
            have hxg : (gM x : EuclideanSpace Real (Fin (n + 1))) = g x := by
              dsimp [g]
              exact hgM x
            have hyg : (gM y : EuclideanSpace Real (Fin (n + 1))) = g y := by
              dsimp [g]
              exact hgM y
            rw [hxg, hyg]
            exact hxy
          exact gM.injective hgm
        have hpreimage :
            sublevel = g ⁻¹' ((M : Set _) ∩ C) := by
          calc
            sublevel = g ⁻¹' (g '' sublevel) := by
              simpa using (Set.preimage_image_eq (f := g) (s := sublevel) hg_inj).symm
            _ = g ⁻¹' ((M : Set _) ∩ C) := by
              simp [himage]
        have hconv_pre :
            Convex ℝ (g ⁻¹' ((M : Set _) ∩ C)) := by
          let g_aff :
              EuclideanSpace Real (Fin n) →ᵃ[Real] EuclideanSpace Real (Fin (n + 1)) :=
            (e.toAffineMap).comp A
          have hgaff : Convex ℝ (g_aff ⁻¹' ((M : Set _) ∩ C)) :=
            (Convex.affine_preimage (f := g_aff) hconv_MC)
          have hg_aff : ∀ x, g_aff x = g x := by
            intro x
            simp [g_aff, AffineMap.comp_apply, hg_eq]
          have hpre :
              g_aff ⁻¹' ((M : Set _) ∩ C) = g ⁻¹' ((M : Set _) ∩ C) := by
            ext x; constructor <;> intro hx
            · simpa [Set.mem_preimage, hg_aff] using hx
            · simpa [Set.mem_preimage, (hg_aff x).symm] using hx
          simpa [hpre] using hgaff
        simpa [hpreimage] using hconv_pre
      have hri_A :
          euclideanRelativeInterior (n + 1) (A '' sublevel) =
            A '' euclideanRelativeInterior n sublevel :=
        ri_image_linearMap_eq (n := n + 1) (m := n) (D := sublevel) hconv_sub A hA0
      have hri_trans :
          euclideanRelativeInterior (n + 1) (g '' sublevel) =
            e '' euclideanRelativeInterior (n + 1) (A '' sublevel) := by
        simpa [hg_eq, Set.image_image] using
          (euclideanRelativeInterior_image_affineEquiv (n := n + 1)
            (C := A '' sublevel) (e := e))
      have hri_trans' :
          euclideanRelativeInterior (n + 1) (g '' sublevel) =
            g '' euclideanRelativeInterior n sublevel := by
        simpa [hg_eq, Set.image_image, hri_A] using hri_trans
      simpa [himage] using hri_trans'
    have hpreimage :
        g ⁻¹' (euclideanRelativeInterior (n + 1) ((M : Set _) ∩ C)) =
          euclideanRelativeInterior n sublevel := by
      -- use injectivity of g to pull back the image
      have hg_inj : Function.Injective g := by
        intro x y hxy
        have hgm : gM x = gM y := by
          apply Subtype.ext
          have hxg : (gM x : EuclideanSpace Real (Fin (n + 1))) = g x := by
            dsimp [g]
            exact hgM x
          have hyg : (gM y : EuclideanSpace Real (Fin (n + 1))) = g y := by
            dsimp [g]
            exact hgM y
          rw [hxg, hyg]
          exact hxy
        exact gM.injective hgm
      have hpre :
          g ⁻¹' (g '' euclideanRelativeInterior n sublevel) =
            euclideanRelativeInterior n sublevel := by
        ext x; constructor
        · intro hx
          rcases hx with ⟨y, hy, hgy⟩
          have hxy : x = y := by
            exact hg_inj hgy.symm
          simpa [hxy] using hy
        · intro hx
          exact ⟨x, hx, rfl⟩
      rw [hri_image]
      exact hpre
    have hpreimage' := hpreimage.symm
    rw [hri_cl.1] at hpreimage'
    exact hpreimage'
  exact ⟨hclosure_sub, hri_sub⟩

/-- The non-strict sublevel lies in the closure of the strict sublevel. -/
lemma sublevel_subset_closure_strictSublevel {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) {α : Real}
    (hα : iInf (fun x => f x) < (α : EReal)) :
    let sublevel : Set (EuclideanSpace Real (Fin n)) :=
      {x | f (x : Fin n → Real) ≤ (α : EReal)}
    let strictSublevel : Set (EuclideanSpace Real (Fin n)) :=
      {x | f (x : Fin n → Real) < (α : EReal)}
    sublevel ⊆ closure strictSublevel := by
  classical
  intro sublevel strictSublevel
  have hex : ∃ y : Fin n → Real, f y < (α : EReal) := (iInf_lt_iff).1 hα
  rcases hex with ⟨y, hy⟩
  set yE : EuclideanSpace Real (Fin n) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm y
  have hy' : f (yE : Fin n → Real) < (α : EReal) := by
    simpa [yE] using hy
  rcases ereal_exists_real_between_of_lt (h := hy') with ⟨v, hvle, hvlt⟩
  have hconv_epi : Convex ℝ (epigraph (Set.univ : Set (Fin n → Real)) f) := by
    simpa [ConvexFunctionOn] using hf.1
  intro x hx
  have hxle : f (x : Fin n → Real) ≤ (α : EReal) := by
    simpa [sublevel] using hx
  have hsegment : openSegment ℝ x yE ⊆ strictSublevel := by
    intro z hz
    have hz' :
        z ∈ (fun t => (1 - t) • x + t • yE) '' Set.Ioo (0 : Real) 1 := by
      simpa [openSegment_eq_image (𝕜 := Real) x yE] using hz
    rcases hz' with ⟨t, ht, rfl⟩
    have ht0 : 0 < t := ht.1
    have ht1 : t < 1 := ht.2
    have hle :
        f ((1 - t) • x + t • yE) ≤ (((1 - t) * α + t * v : Real) : EReal) := by
      have ht0' : 0 ≤ t := le_of_lt ht0
      have ht1' : t ≤ 1 := le_of_lt ht1
      simpa using
        (epigraph_combo_ineq_aux (S := (Set.univ : Set (Fin n → Real))) (f := f)
          (x := (x : Fin n → Real)) (y := (yE : Fin n → Real)) (μ := α) (v := v)
          hconv_epi (by simp) (by simp) hxle hvle ht0' ht1')
    have hlt_real : (1 - t) * α + t * v < α := by
      nlinarith
    have hlt : (((1 - t) * α + t * v : Real) : EReal) < (α : EReal) :=
      (EReal.coe_lt_coe_iff).2 hlt_real
    have hlt' : f ((1 - t) • x + t • yE) < (α : EReal) := lt_of_le_of_lt hle hlt
    simpa [strictSublevel] using hlt'
  have hxcl :
      x ∈ closure (openSegment ℝ x yE) :=
    (segment_subset_closure_openSegment (𝕜 := Real) (x := x) (y := yE))
      (left_mem_segment (𝕜 := Real) x yE)
  exact (closure_mono hsegment) hxcl

/-- The strict inequality set is relatively open in `affineSpan domf`. -/
lemma ri_domf_lt_open {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) {α : Real} :
    let domf : Set (EuclideanSpace Real (Fin n)) :=
      (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → Real)) f
    let s : Set (EuclideanSpace Real (Fin n)) :=
      {x | x ∈ euclideanRelativeInterior n domf ∧ f (x : Fin n → Real) < (α : EReal)}
    IsOpen {x : affineSpan Real domf | (x : EuclideanSpace Real (Fin n)) ∈ s} := by
  classical
  intro domf s
  have hri_open :
      IsOpen {x : affineSpan Real domf |
        (x : EuclideanSpace Real (Fin n)) ∈ euclideanRelativeInterior n domf} := by
    refine Metric.isOpen_iff.2 ?_
    intro x hx
    have hxri :
        (x : EuclideanSpace Real (Fin n)) ∈ euclideanRelativeInterior n domf := hx
    rcases
        euclideanRelativeInterior_ball_subset (n := n) (C := domf)
          (x := (x : EuclideanSpace Real (Fin n))) hxri with
      ⟨ε, hε, hsubset⟩
    refine ⟨ε, hε, ?_⟩
    intro y hy
    have hy' :
        (y : EuclideanSpace Real (Fin n)) ∈
          (fun v => (x : EuclideanSpace Real (Fin n)) + v) '' (ε • euclideanUnitBall n) := by
      have hy' :
          dist (y : EuclideanSpace Real (Fin n)) (x : EuclideanSpace Real (Fin n)) < ε := by
        simpa [Subtype.dist_eq] using hy
      have hnorm :
          ‖(y : EuclideanSpace Real (Fin n)) - (x : EuclideanSpace Real (Fin n))‖ ≤ ε := by
        have hnorm' :
            ‖(y : EuclideanSpace Real (Fin n)) - (x : EuclideanSpace Real (Fin n))‖ < ε := by
          simpa [dist_eq_norm] using hy'
        exact le_of_lt hnorm'
      have hmem :
          (y : EuclideanSpace Real (Fin n)) - (x : EuclideanSpace Real (Fin n)) ∈
            ε • euclideanUnitBall n :=
        mem_smul_unitBall_of_norm_le (n := n) (ε := ε) hε hnorm
      refine ⟨(y : EuclideanSpace Real (Fin n)) - (x : EuclideanSpace Real (Fin n)), hmem, ?_⟩
      simp [sub_eq_add_neg]
    have hy_aff :
        (y : EuclideanSpace Real (Fin n)) ∈
          (affineSpan Real domf : Set (EuclideanSpace Real (Fin n))) := y.property
    have hyri :
        (y : EuclideanSpace Real (Fin n)) ∈ euclideanRelativeInterior n domf :=
      hsubset ⟨hy', hy_aff⟩
    simpa using hyri
  let A : AffineSubspace Real (EuclideanSpace Real (Fin n)) := affineSpan Real domf
  have hcont :
      ContinuousOn (fun x : EuclideanSpace Real (Fin n) => f x)
        (euclideanRelativeInterior n domf) := by
    simpa [domf] using
      (convexFunction_continuousOn_ri_effectiveDomain_of_proper (f := f) hf)
  have hcont_sub :
      ContinuousOn (fun x : A => f (x : EuclideanSpace Real (Fin n)))
        {x : A | (x : EuclideanSpace Real (Fin n)) ∈ euclideanRelativeInterior n domf} := by
    refine hcont.comp (s := {x : A |
      (x : EuclideanSpace Real (Fin n)) ∈ euclideanRelativeInterior n domf}) ?_ ?_
    · simpa using
        (continuous_subtype_val : Continuous (fun x : A =>
          (x : EuclideanSpace Real (Fin n)))).continuousOn
    · intro x hx
      simpa using hx
  have hpre :
      {x : A | (x : EuclideanSpace Real (Fin n)) ∈ s} =
        {x : A | (x : EuclideanSpace Real (Fin n)) ∈ euclideanRelativeInterior n domf} ∩
          (fun x : A => f (x : EuclideanSpace Real (Fin n))) ⁻¹' Set.Iio (α : EReal) := by
    ext x; constructor
    · intro hx
      exact ⟨hx.1, hx.2⟩
    · intro hx
      exact ⟨hx.1, hx.2⟩
  have hopen_Iio : IsOpen (Set.Iio (α : EReal)) := isOpen_Iio
  have hsopen :
      IsOpen
        ({x : A | (x : EuclideanSpace Real (Fin n)) ∈ euclideanRelativeInterior n domf} ∩
          (fun x : A => f (x : EuclideanSpace Real (Fin n))) ⁻¹' Set.Iio (α : EReal)) :=
    hcont_sub.isOpen_inter_preimage hri_open hopen_Iio
  simpa [hpre] using hsopen

/-- A nonempty relatively open subset of an affine subspace has full affine span. -/
lemma affineSpan_eq_of_nonempty_relOpen {n : Nat}
    (A : AffineSubspace Real (EuclideanSpace Real (Fin n)))
    {s : Set (EuclideanSpace Real (Fin n))}
    (hsA : s ⊆ (A : Set (EuclideanSpace Real (Fin n))))
    (hsne : s.Nonempty)
    (hsopen : IsOpen {x : A | (x : EuclideanSpace Real (Fin n)) ∈ s}) :
    affineSpan Real s = A := by
  classical
  let s' : Set A := {x : A | (x : EuclideanSpace Real (Fin n)) ∈ s}
  have hs'ne : s'.Nonempty := by
    rcases hsne with ⟨x, hx⟩
    exact ⟨⟨x, hsA hx⟩, by simpa [s'] using hx⟩
  haveI : Nonempty A := by
    rcases hs'ne with ⟨x, hx⟩
    exact ⟨x⟩
  have hs'open : IsOpen s' := hsopen
  have hspan' : affineSpan Real s' = (⊤ : AffineSubspace Real A) :=
    (IsOpen.affineSpan_eq_top hs'open hs'ne)
  have himage :
      (fun x : A => (x : EuclideanSpace Real (Fin n))) '' s' = s := by
    ext x; constructor
    · rintro ⟨x', hx', rfl⟩
      exact hx'
    · intro hx
      exact ⟨⟨x, hsA hx⟩, by simpa [s'] using hx, rfl⟩
  have hmap :
      (affineSpan Real s').map (AffineSubspace.subtype A) = affineSpan Real s := by
    simpa [himage] using
      (AffineSubspace.map_span (k := Real)
        (f := (AffineSubspace.subtype A)) (s := s'))
  have hmap_top :
      (⊤ : AffineSubspace Real A).map (AffineSubspace.subtype A) = A := by
    ext x; constructor
    · rintro ⟨x', -, rfl⟩
      exact x'.property
    · intro hx
      exact ⟨⟨x, hx⟩, by simp, rfl⟩
  calc
    affineSpan Real s =
        (affineSpan Real s').map (AffineSubspace.subtype A) := by
          symm
          exact hmap
    _ = (⊤ : AffineSubspace Real A).map (AffineSubspace.subtype A) := by
          simp [hspan']
    _ = A := hmap_top

/-- The closure of the embedded epigraph equals the embedded epigraph of the closure. -/
lemma closure_embedded_epigraph_eq_convexFunctionClosure {n : Nat}
    {f : (Fin n → Real) → EReal} (hbot : ∀ x, f x ≠ (⊥ : EReal)) :
    let C : Set (EuclideanSpace Real (Fin (n + 1))) :=
      (appendAffineEquiv n 1) ''
        ((fun p : (Fin n → Real) × Real =>
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => p.2))) ''
          epigraph (S := (Set.univ : Set (Fin n → Real))) f)
    closure C =
        (appendAffineEquiv n 1) ''
          ((fun p : (Fin n → Real) × Real =>
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
                (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                  (fun _ : Fin 1 => p.2))) ''
            epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f)) := by
  classical
  intro C
  let eN : (Fin n → Real) ≃ᵃ[Real] EuclideanSpace Real (Fin n) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm.toLinearEquiv.toAffineEquiv
  let e1 : Real ≃ᵃ[Real] EuclideanSpace Real (Fin 1) :=
    ((ContinuousLinearEquiv.funUnique (ι := Fin 1) (R := Real) (M := Real)).symm.toLinearEquiv.trans
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm.toLinearEquiv).toAffineEquiv
  let g_aff : (Fin n → Real) × Real ≃ᵃ[Real]
      (EuclideanSpace Real (Fin n) × EuclideanSpace Real (Fin 1)) :=
    AffineEquiv.prodCongr eN e1
  have hphi :
      ((fun p : (Fin n → Real) × Real =>
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => p.2))) ''
        epigraph (S := (Set.univ : Set (Fin n → Real))) f) =
        g_aff '' epigraph (S := (Set.univ : Set (Fin n → Real))) f := by
    ext q; constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p, hp, ?_⟩
      simp [g_aff, eN, e1]
      rfl
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p, hp, ?_⟩
      simp [g_aff, eN, e1]
      rfl
  have hphi_cl :
      ((fun p : (Fin n → Real) × Real =>
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => p.2))) ''
        epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f)) =
        g_aff '' epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f) := by
    ext q; constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p, hp, ?_⟩
      simp [g_aff, eN, e1]
      rfl
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p, hp, ?_⟩
      simp [g_aff, eN, e1]
      rfl
  have hcl_epi :
      closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) =
        epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f) := by
    simpa using (epigraph_convexFunctionClosure_eq_closure_epigraph (f := f) hbot).1.symm
  have hcl_C :
      closure C =
        (appendAffineEquiv n 1) ''
          closure ((fun p : (Fin n → Real) × Real =>
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => p.2))) ''
            epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
    simpa [C] using
      (Homeomorph.image_closure (appendAffineEquiv n 1).toHomeomorphOfFiniteDimensional
        ((fun p : (Fin n → Real) × Real =>
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => p.2))) ''
          epigraph (S := (Set.univ : Set (Fin n → Real))) f)).symm
  have hcl_inner :
      closure ((fun p : (Fin n → Real) × Real =>
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => p.2))) ''
        epigraph (S := (Set.univ : Set (Fin n → Real))) f) =
        g_aff '' closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
    calc
      closure ((fun p : (Fin n → Real) × Real =>
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => p.2))) ''
        epigraph (S := (Set.univ : Set (Fin n → Real))) f) =
          closure (g_aff '' epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
            simpa using congrArg closure hphi
      _ =
          g_aff '' closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
            simpa using
              (Homeomorph.image_closure (g_aff.toHomeomorphOfFiniteDimensional)
                (epigraph (S := (Set.univ : Set (Fin n → Real))) f)).symm
  calc
    closure C =
        (appendAffineEquiv n 1) ''
          closure ((fun p : (Fin n → Real) × Real =>
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => p.2))) ''
            epigraph (S := (Set.univ : Set (Fin n → Real))) f) := hcl_C
    _ =
        (appendAffineEquiv n 1) ''
          (g_aff '' closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f)) := by
          simpa using
            congrArg (fun s => (appendAffineEquiv n 1) '' s) hcl_inner
    _ =
        (appendAffineEquiv n 1) ''
          (g_aff '' epigraph (S := (Set.univ : Set (Fin n → Real)))
            (convexFunctionClosure f)) := by
          simp [hcl_epi]
    _ =
        (appendAffineEquiv n 1) ''
          ((fun p : (Fin n → Real) × Real =>
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
                (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                  (fun _ : Fin 1 => p.2))) ''
            epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f)) := by
          simpa using
            congrArg (fun s => (appendAffineEquiv n 1) '' s) hphi_cl.symm

/-! ### Theorem 7.6 auxiliary proof -/

/-- Auxiliary proof for Theorem 7.6. -/
lemma properConvexFunction_levelSets_same_closure_ri_dim_aux {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {α : Real} (hα : iInf (fun x => f x) < (α : EReal)) :
    let sublevel : Set (EuclideanSpace Real (Fin n)) :=
      {x | f (x : Fin n → Real) ≤ (α : EReal)}
    let strictSublevel : Set (EuclideanSpace Real (Fin n)) :=
      {x | f (x : Fin n → Real) < (α : EReal)}
    let domf : Set (EuclideanSpace Real (Fin n)) :=
      (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → Real)) f
    closure sublevel =
        {x : EuclideanSpace Real (Fin n) |
          convexFunctionClosure f (x : Fin n → Real) ≤ (α : EReal)} ∧
      closure strictSublevel =
        {x : EuclideanSpace Real (Fin n) |
          convexFunctionClosure f (x : Fin n → Real) ≤ (α : EReal)} ∧
      euclideanRelativeInterior n sublevel =
        {x | x ∈ euclideanRelativeInterior n domf ∧
          f (x : Fin n → Real) < (α : EReal)} ∧
      euclideanRelativeInterior n strictSublevel =
        {x | x ∈ euclideanRelativeInterior n domf ∧
          f (x : Fin n → Real) < (α : EReal)} ∧
      Module.finrank Real (affineSpan Real sublevel).direction =
      Module.finrank Real (affineSpan Real domf).direction ∧
      Module.finrank Real (affineSpan Real strictSublevel).direction =
        Module.finrank Real (affineSpan Real domf).direction := by
  classical
  intro sublevel strictSublevel domf
  set C : Set (EuclideanSpace Real (Fin (n + 1))) :=
    (appendAffineEquiv n 1) ''
      ((fun p : (Fin n → Real) × Real =>
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => p.2))) ''
        epigraph (S := (Set.univ : Set (Fin n → Real))) f) with hC
  set zα : EuclideanSpace Real (Fin 1) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => α) with hzα
  set φ : EuclideanSpace Real (Fin (n + 1)) →ₗ[Real] EuclideanSpace Real (Fin 1) :=
    (LinearMap.snd (R := Real) (M := EuclideanSpace Real (Fin n))
          (M₂ := EuclideanSpace Real (Fin 1))).comp
      (appendAffineEquiv n 1).symm.linear.toLinearMap with hφ
  set M : AffineSubspace Real (EuclideanSpace Real (Fin (n + 1))) :=
    AffineSubspace.mk' (appendAffineEquiv n 1 (0, zα)) (LinearMap.ker φ) with hM
  set g : EuclideanSpace Real (Fin n) → EuclideanSpace Real (Fin (n + 1)) :=
    fun x =>
      appendAffineEquiv n 1
        ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real), zα) with hg
  have hconv : ConvexFunction f := by
    simpa [ConvexFunction] using hf.1
  have hbot : ∀ x : Fin n → Real, f x ≠ (⊥ : EReal) := by
    intro x
    exact hf.2.2 x (by simp)
  have hCconv : Convex ℝ C := by
    simpa [hC] using (convex_embedded_epigraph (n := n) (f := f) hconv)
  have hMne : ((M : Set _) ∩ euclideanRelativeInterior (n + 1) C).Nonempty := by
    simpa [hC, hzα, hφ, hM] using
      (levelSets_plane_meets_riEpigraph (n := n) (f := f) hf hα)
  have hpre :
      closure sublevel = g ⁻¹' ((M : Set _) ∩ closure C) ∧
        euclideanRelativeInterior n sublevel =
          g ⁻¹' ((M : Set _) ∩ euclideanRelativeInterior (n + 1) C) := by
    simpa [sublevel, hC, hzα, hφ, hM, hg] using
      (levelSets_horizontal_slice_preimage_closure_ri (n := n) (f := f) (α := α) hCconv hMne)
  have hg_mem_M : ∀ x, g x ∈ (M : Set _) := by
    intro x
    set y : EuclideanSpace Real (Fin n) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real)
    have hy : appendAffineEquiv n 1 (y, zα) ∈ (M : Set _) := by
      simpa [hM, hzα, hφ] using
        (appendAffineEquiv_mem_horizontal_plane (n := n) (α := α) (y := y))
    simpa [hg, y] using hy
  set Ccl : Set (EuclideanSpace Real (Fin (n + 1))) :=
    (appendAffineEquiv n 1) ''
      ((fun p : (Fin n → Real) × Real =>
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => p.2))) ''
        epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f)) with hCcl
  have hcl_C : closure C = Ccl := by
    simpa [hC, hCcl] using
      (closure_embedded_epigraph_eq_convexFunctionClosure (n := n) (f := f) hbot)
  have hpre_cl' :
      g ⁻¹' ((M : Set _) ∩ closure C) =
        {x : EuclideanSpace Real (Fin n) |
          convexFunctionClosure f (x : Fin n → Real) ≤ (α : EReal)} := by
    ext x; constructor
    · intro hx
      have hxC : g x ∈ closure C := hx.2
      have hxC' : g x ∈ Ccl := by
        simpa [hcl_C, hCcl] using hxC
      have hxC'' :
          appendAffineEquiv n 1
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real), zα) ∈
            Ccl := by
        simpa [hg] using hxC'
      have hiff :
          appendAffineEquiv n 1
                ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real), zα) ∈
              Ccl ↔
            convexFunctionClosure f (x : Fin n → Real) ≤ (α : EReal) := by
        simpa [hCcl, hzα] using
          (levelSets_horizontal_section_mem_iff (n := n) (f := convexFunctionClosure f)
            (α := α) (x := x))
      exact (hiff).1 hxC''
    · intro hx
      have hiff :
          appendAffineEquiv n 1
                ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real), zα) ∈
              Ccl ↔
            convexFunctionClosure f (x : Fin n → Real) ≤ (α : EReal) := by
        simpa [hCcl, hzα] using
          (levelSets_horizontal_section_mem_iff (n := n) (f := convexFunctionClosure f)
            (α := α) (x := x))
      have hxC'' :
          appendAffineEquiv n 1
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real), zα) ∈
            Ccl :=
        (hiff).2 hx
      have hxC' : g x ∈ Ccl := by
        simpa [hg] using hxC''
      have hxC : g x ∈ closure C := by
        simpa [hcl_C, hCcl] using hxC'
      exact ⟨hg_mem_M x, hxC⟩
  have hcl_sublevel :
      closure sublevel =
        {x : EuclideanSpace Real (Fin n) |
          convexFunctionClosure f (x : Fin n → Real) ≤ (α : EReal)} := by
    calc
      closure sublevel = g ⁻¹' ((M : Set _) ∩ closure C) := hpre.1
      _ = _ := hpre_cl'
  have hsubset_closure : sublevel ⊆ closure strictSublevel := by
    simpa [sublevel, strictSublevel] using
      (sublevel_subset_closure_strictSublevel (n := n) (f := f) hf hα)
  have hstrict_sub : strictSublevel ⊆ sublevel := by
    intro x hx
    have hx' : f (x : Fin n → Real) < (α : EReal) := by
      simpa [strictSublevel] using hx
    have hxle : f (x : Fin n → Real) ≤ (α : EReal) := le_of_lt hx'
    simpa [sublevel] using hxle
  have hcl_sublevel_le : closure sublevel ⊆ closure strictSublevel :=
    closure_minimal hsubset_closure isClosed_closure
  have hcl_strict_le : closure strictSublevel ⊆ closure sublevel :=
    closure_mono hstrict_sub
  have hcl_eq : closure strictSublevel = closure sublevel :=
    le_antisymm hcl_strict_le hcl_sublevel_le
  have hcl_strict :
      closure strictSublevel =
        {x : EuclideanSpace Real (Fin n) |
          convexFunctionClosure f (x : Fin n → Real) ≤ (α : EReal)} := by
    calc
      closure strictSublevel = closure sublevel := hcl_eq
      _ = _ := hcl_sublevel
  have hri_sublevel :
      euclideanRelativeInterior n sublevel =
        {x : EuclideanSpace Real (Fin n) |
          x ∈ euclideanRelativeInterior n domf ∧ f (x : Fin n → Real) < (α : EReal)} := by
    ext x; constructor
    · intro hx
      have hx' :
          x ∈ g ⁻¹' ((M : Set _) ∩ euclideanRelativeInterior (n + 1) C) := by
        simpa [hpre.2] using hx
      have hxriC : g x ∈ euclideanRelativeInterior (n + 1) C := hx'.2
      have hxriE :
          appendAffineEquiv n 1
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real), zα) ∈
            riEpigraph f := by
        simpa [riEpigraph, hC, hg, hzα] using hxriC
      have hiff :=
        (riEpigraph_mem_iff (n := n) (f := f) hconv (x := (x : Fin n → Real)) (μ := α))
      rcases (hiff).1 hxriE with ⟨hxri, hxlt, _⟩
      have hxri' : x ∈ euclideanRelativeInterior n domf := by
        simpa using hxri
      exact ⟨hxri', hxlt⟩
    · intro hx
      have hxri : x ∈ euclideanRelativeInterior n domf := hx.1
      have hxlt : f (x : Fin n → Real) < (α : EReal) := hx.2
      have hxri' :
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real) ∈
            euclideanRelativeInterior n domf := by
        simpa using hxri
      have hiff :=
        (riEpigraph_mem_iff (n := n) (f := f) hconv (x := (x : Fin n → Real)) (μ := α))
      have hxriE :
          appendAffineEquiv n 1
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real), zα) ∈
            riEpigraph f := by
        exact (hiff).2 ⟨hxri', hxlt, riEpigraph_mu_lt_top α⟩
      have hxriC : g x ∈ euclideanRelativeInterior (n + 1) C := by
        simpa [riEpigraph, hC, hg, hzα] using hxriE
      have hxpre :
          x ∈ g ⁻¹' ((M : Set _) ∩ euclideanRelativeInterior (n + 1) C) := by
        exact ⟨hg_mem_M x, hxriC⟩
      simpa [hpre.2] using hxpre
  have hconv_strict : Convex ℝ strictSublevel := by
    let A : EuclideanSpace Real (Fin n) →ₗ[Real] (Fin n → Real) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).toLinearMap
    have hconv' : Convex ℝ {x : Fin n → Real | f x < (α : EReal)} :=
      convex_sublevel_lt_real_of_convexFunction (f := f) hconv α
    simpa [A, strictSublevel] using hconv'.linear_preimage A
  have hconv_sublevel : Convex ℝ sublevel := by
    let A : EuclideanSpace Real (Fin n) →ₗ[Real] (Fin n → Real) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).toLinearMap
    have hconv_family :
        ∀ β : {β : Real // (α : EReal) < β},
          Convex ℝ {x : EuclideanSpace Real (Fin n) | f (x : Fin n → Real) < (β : EReal)} := by
      intro β
      have hconv' :
          Convex ℝ {x : Fin n → Real | f x < (β : EReal)} :=
        convex_sublevel_lt_real_of_convexFunction (f := f) hconv (β : Real)
      simpa [A] using hconv'.linear_preimage A
    have hconv_iInter :
        Convex ℝ
          (⋂ β : {β : Real // (α : EReal) < β},
            {x : EuclideanSpace Real (Fin n) | f (x : Fin n → Real) < (β : EReal)}) :=
      convex_iInter hconv_family
    have hsublevel_eq :
        sublevel =
          ⋂ β : {β : Real // (α : EReal) < β},
            {x : EuclideanSpace Real (Fin n) | f (x : Fin n → Real) < (β : EReal)} := by
      have hsublevel_eq' :
          {x : Fin n → Real | f x ≤ (α : EReal)} =
            ⋂ β : {β : Real // (α : EReal) < β}, {x : Fin n → Real | f x < (β : EReal)} :=
        sublevel_le_eq_iInter_lt_real (f := f) (α := (α : EReal))
      have hpre :=
        congrArg (fun s => (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹' s)
          hsublevel_eq'
      simpa [sublevel, Set.preimage_iInter] using hpre
    simpa [hsublevel_eq] using hconv_iInter
  have hri_eq :
      euclideanRelativeInterior n strictSublevel =
        euclideanRelativeInterior n sublevel := by
    exact
      euclideanRelativeInterior_eq_of_closure_eq n strictSublevel sublevel
        hconv_strict hconv_sublevel hcl_eq
  have hri_strict :
      euclideanRelativeInterior n strictSublevel =
        {x : EuclideanSpace Real (Fin n) |
          x ∈ euclideanRelativeInterior n domf ∧ f (x : Fin n → Real) < (α : EReal)} := by
    simpa [hri_sublevel] using hri_eq
  set s : Set (EuclideanSpace Real (Fin n)) :=
    {x | x ∈ euclideanRelativeInterior n domf ∧ f (x : Fin n → Real) < (α : EReal)} with hs
  have hsA : s ⊆ (affineSpan Real domf : Set (EuclideanSpace Real (Fin n))) := by
    intro x hx
    have hxri : x ∈ euclideanRelativeInterior n domf := hx.1
    have hxcl : x ∈ closure domf :=
      subset_closure ((euclideanRelativeInterior_subset_closure n domf).1 hxri)
    have hdomfA : domf ⊆ (affineSpan Real domf : Set (EuclideanSpace Real (Fin n))) := by
      intro y hy
      exact subset_affineSpan (k := Real) (s := domf) hy
    have hclosedA :
        IsClosed (affineSpan Real domf : Set (EuclideanSpace Real (Fin n))) := by
      simpa using (AffineSubspace.closed_of_finiteDimensional (s := affineSpan Real domf))
    have hclosureA :
        closure domf ⊆ (affineSpan Real domf : Set (EuclideanSpace Real (Fin n))) :=
      closure_minimal hdomfA hclosedA
    exact hclosureA hxcl
  have hsne : s.Nonempty := by
    obtain ⟨x, hxri, hxlt⟩ :=
      exists_lt_on_ri_effectiveDomain_of_iInf_lt (n := n) (f := f) hf hα
    refine ⟨x, ?_⟩
    exact ⟨by simpa [domf] using hxri, hxlt⟩
  have hsopen :
      IsOpen {x : affineSpan Real domf | (x : EuclideanSpace Real (Fin n)) ∈ s} := by
    simpa [domf, s] using
      (ri_domf_lt_open (n := n) (f := f) hf (α := α))
  have hspan_s : affineSpan Real s = affineSpan Real domf :=
    affineSpan_eq_of_nonempty_relOpen (n := n) (A := affineSpan Real domf) hsA hsne hsopen
  have hs_sublevel : s ⊆ sublevel := by
    intro x hx
    exact le_of_lt hx.2
  have hs_strict : s ⊆ strictSublevel := by
    intro x hx
    exact hx.2
  have hαtop : (α : EReal) < ⊤ := riEpigraph_mu_lt_top α
  have hsublevel_sub_domf : sublevel ⊆ domf := by
    intro x hx
    have hx_top : f (x : Fin n → Real) < (⊤ : EReal) := lt_of_le_of_lt hx hαtop
    have hx_dom :
        (x : Fin n → Real) ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
      have hx' :
          (x : Fin n → Real) ∈ (Set.univ : Set (Fin n → Real)) ∧
            f (x : Fin n → Real) < (⊤ : EReal) := by
        exact ⟨by simp, hx_top⟩
      simpa [effectiveDomain_eq] using hx'
    simpa [domf] using hx_dom
  have hstrict_sub_domf : strictSublevel ⊆ domf := by
    intro x hx
    have hx_top : f (x : Fin n → Real) < (⊤ : EReal) := lt_trans hx hαtop
    have hx_dom :
        (x : Fin n → Real) ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
      have hx' :
          (x : Fin n → Real) ∈ (Set.univ : Set (Fin n → Real)) ∧
            f (x : Fin n → Real) < (⊤ : EReal) := by
        exact ⟨by simp, hx_top⟩
      simpa [effectiveDomain_eq] using hx'
    simpa [domf] using hx_dom
  have hspan_sublevel : affineSpan Real sublevel = affineSpan Real domf := by
    have hspan_le : affineSpan Real domf ≤ affineSpan Real sublevel := by
      have hspan_le' : affineSpan Real s ≤ affineSpan Real sublevel :=
        affineSpan_mono Real hs_sublevel
      simpa [hspan_s] using hspan_le'
    have hspan_ge : affineSpan Real sublevel ≤ affineSpan Real domf :=
      affineSpan_mono Real hsublevel_sub_domf
    exact le_antisymm hspan_ge hspan_le
  have hspan_strict : affineSpan Real strictSublevel = affineSpan Real domf := by
    have hspan_le : affineSpan Real domf ≤ affineSpan Real strictSublevel := by
      have hspan_le' : affineSpan Real s ≤ affineSpan Real strictSublevel :=
        affineSpan_mono Real hs_strict
      simpa [hspan_s] using hspan_le'
    have hspan_ge : affineSpan Real strictSublevel ≤ affineSpan Real domf :=
      affineSpan_mono Real hstrict_sub_domf
    exact le_antisymm hspan_ge hspan_le
  have hfinrank_sublevel :
      Module.finrank Real (affineSpan Real sublevel).direction =
        Module.finrank Real (affineSpan Real domf).direction := by
    rw [hspan_sublevel]
  have hfinrank_strict :
      Module.finrank Real (affineSpan Real strictSublevel).direction =
        Module.finrank Real (affineSpan Real domf).direction := by
    rw [hspan_strict]
  exact ⟨hcl_sublevel, hcl_strict, hri_sublevel, hri_strict, hfinrank_sublevel, hfinrank_strict⟩

/-- Theorem 7.6: Let `f` be a proper convex function, and let `α ∈ ℝ` with
`α > inf f`. The convex level sets `{x | f x ≤ α}` and `{x | f x < α}` have the same
closure and the same relative interior, namely `{x | (cl f) x ≤ α}` and
`{x ∈ ri (dom f) | f x < α}`. Furthermore, they have the same dimension as `dom f`. -/
theorem properConvexFunction_levelSets_same_closure_ri_dim {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {α : Real} (hα : iInf (fun x => f x) < (α : EReal)) :
    let sublevel : Set (EuclideanSpace Real (Fin n)) :=
      {x | f (x : Fin n → Real) ≤ (α : EReal)}
    let strictSublevel : Set (EuclideanSpace Real (Fin n)) :=
      {x | f (x : Fin n → Real) < (α : EReal)}
    let domf : Set (EuclideanSpace Real (Fin n)) :=
      (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → Real)) f
    closure sublevel =
        {x : EuclideanSpace Real (Fin n) |
          convexFunctionClosure f (x : Fin n → Real) ≤ (α : EReal)} ∧
      closure strictSublevel =
        {x : EuclideanSpace Real (Fin n) |
          convexFunctionClosure f (x : Fin n → Real) ≤ (α : EReal)} ∧
      euclideanRelativeInterior n sublevel =
        {x | x ∈ euclideanRelativeInterior n domf ∧
          f (x : Fin n → Real) < (α : EReal)} ∧
      euclideanRelativeInterior n strictSublevel =
        {x | x ∈ euclideanRelativeInterior n domf ∧
          f (x : Fin n → Real) < (α : EReal)} ∧
      Module.finrank Real (affineSpan Real sublevel).direction =
      Module.finrank Real (affineSpan Real domf).direction ∧
      Module.finrank Real (affineSpan Real strictSublevel).direction =
        Module.finrank Real (affineSpan Real domf).direction := by
  simpa using
    (properConvexFunction_levelSets_same_closure_ri_dim_aux (n := n) (f := f) hf hα)

/-- The infimum of the constant zero `EReal` function is zero. -/
lemma iInf_const_zero_ereal {n : Nat} :
    iInf (fun _ : (Fin n → Real) => (0 : EReal)) = (0 : EReal) := by
  refine le_antisymm ?_ ?_
  · exact iInf_le (fun _ : (Fin n → Real) => (0 : EReal)) (0 : Fin n → Real)
  · refine le_iInf ?_
    intro x
    exact le_rfl

/-- The strict sublevel set for the constant zero function at zero is empty. -/
lemma strictSublevel_const_zero_eq_empty {n : Nat} :
    {x : EuclideanSpace Real (Fin n) | (0 : EReal) < (0 : EReal) ∧ x = x} =
      (∅ : Set (EuclideanSpace Real (Fin n))) := by
  ext x
  simp

/-- The right-hand side of the strict-sublevel closure formula is nonempty for the zero
function. -/
lemma rhs_nonempty_via_closure_le_self {n : Nat} :
    ∃ x : EuclideanSpace Real (Fin n),
      convexFunctionClosure (fun _ : (Fin n → Real) => (0 : EReal)) (x : Fin n → Real) ≤
        (0 : EReal) := by
  refine ⟨0, ?_⟩
  have hle := convexFunctionClosure_le_self (f := fun _ : (Fin n → Real) => (0 : EReal))
  simpa using (hle (0 : Fin n → Real))

/-- Text 7.0.17: The closure and relative interior formulas in Theorem 7.6 can fail when
`α = inf f`. -/
theorem properConvexFunction_levelSets_formulas_fail_at_inf :
    ∃ (n : Nat) (f : (Fin n → Real) → EReal) (α : Real),
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f ∧
      (α : EReal) = iInf (fun x => f x) ∧
      let sublevel : Set (EuclideanSpace Real (Fin n)) :=
        {x | f (x : Fin n → Real) ≤ (α : EReal)}
      let strictSublevel : Set (EuclideanSpace Real (Fin n)) :=
        {x | f (x : Fin n → Real) < (α : EReal)}
      let domf : Set (EuclideanSpace Real (Fin n)) :=
        (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f
      ¬(closure sublevel =
            {x : EuclideanSpace Real (Fin n) |
              convexFunctionClosure f (x : Fin n → Real) ≤ (α : EReal)} ∧
        closure strictSublevel =
            {x : EuclideanSpace Real (Fin n) |
              convexFunctionClosure f (x : Fin n → Real) ≤ (α : EReal)} ∧
        euclideanRelativeInterior n sublevel =
            {x | x ∈ euclideanRelativeInterior n domf ∧
              f (x : Fin n → Real) < (α : EReal)} ∧
        euclideanRelativeInterior n strictSublevel =
            {x | x ∈ euclideanRelativeInterior n domf ∧
              f (x : Fin n → Real) < (α : EReal)}) := by
  classical
  refine ⟨1, (fun _ : (Fin 1 → Real) => (0 : EReal)), 0, ?_⟩
  refine ⟨properConvexFunctionOn_const (n := 1) 0, ?_, ?_⟩
  · simp
  · dsimp
    intro h
    rcases h with ⟨-, hstrict, -, -⟩
    rcases rhs_nonempty_via_closure_le_self (n := 1) with ⟨x, hx⟩
    have hstrict' :
        closure ({x : EuclideanSpace Real (Fin 1) | (0 : EReal) < (0 : EReal)}) =
          {x : EuclideanSpace Real (Fin 1) |
            convexFunctionClosure (fun _ : (Fin 1 → Real) => (0 : EReal)) (x : Fin 1 → Real) ≤
              (0 : EReal)} := by
      simpa using hstrict
    have hx' :
        x ∈ closure ({x : EuclideanSpace Real (Fin 1) | (0 : EReal) < (0 : EReal)}) := by
      have hxset :
          x ∈
            {x : EuclideanSpace Real (Fin 1) |
              convexFunctionClosure (fun _ : (Fin 1 → Real) => (0 : EReal))
                  (x : Fin 1 → Real) ≤
                (0 : EReal)} := by
        simpa using hx
      rw [hstrict']
      exact hxset
    have hclosure_empty :
        closure ({x : EuclideanSpace Real (Fin 1) | (0 : EReal) < (0 : EReal)}) =
          (∅ : Set (EuclideanSpace Real (Fin 1))) := by
      simp
    have : x ∈ (∅ : Set (EuclideanSpace Real (Fin 1))) := by
      rw [hclosure_empty] at hx'
      exact hx'
    exact (Set.notMem_empty x) this

/-- If `α < iInf f`, then `α < f x` for every `x`. -/
lemma lt_f_of_lt_iInf {n : Nat} {f : (Fin n → Real) → EReal} {α : Real}
    (hα : (α : EReal) < iInf (fun x => f x)) (x : Fin n → Real) :
    (α : EReal) < f x := by
  exact lt_of_lt_of_le hα (iInf_le (fun x => f x) x)

/-- A strict lower bound excludes membership in the `≤`-sublevel set. -/
lemma not_mem_sublevel_of_lt {n : Nat} {f : (Fin n → Real) → EReal} {α : Real}
    {x : Fin n → Real} (h : (α : EReal) < f x) :
    ¬ f x ≤ (α : EReal) := by
  exact not_le_of_gt h

/-- If no point satisfies the sublevel predicate, the sublevel set is empty. -/
lemma sublevel_eq_empty_of_forall_not_mem {n : Nat} {f : (Fin n → Real) → EReal} {α : Real}
    (h : ∀ x : Fin n → Real, ¬ f x ≤ (α : EReal)) :
    {x : Fin n → Real | f x ≤ (α : EReal)} = (∅ : Set (Fin n → Real)) := by
  ext x
  constructor
  · intro hx
    exact (h x) hx
  · intro hx
    cases hx

/-- Text 7.0.18: If `α < inf f` then `{x | f x ≤ α}` is empty and the formulas are
trivial. The case `α = inf f` is more subtle and can also lead to failure of the
formulas; see the example above. -/
theorem sublevel_eq_empty_of_lt_inf {n : Nat} (f : (Fin n → Real) → EReal) {α : Real}
    (hα : (α : EReal) < iInf (fun x => f x)) :
    {x : Fin n → Real | f x ≤ (α : EReal)} = (∅ : Set (Fin n → Real)) := by
  have hlt : ∀ x : Fin n → Real, (α : EReal) < f x :=
    lt_f_of_lt_iInf (f := f) (α := α) hα
  have hnot : ∀ x : Fin n → Real, ¬ f x ≤ (α : EReal) := by
    intro x
    exact not_mem_sublevel_of_lt (x := x) (α := α) (f := f) (hlt x)
  exact sublevel_eq_empty_of_forall_not_mem (f := f) (α := α) hnot

/-- If `α < ⊤`, the strict sublevel already lies in the effective domain. -/
lemma strictSublevel_eq_domf_inter_of_lt_top {n : Nat} {f : (Fin n → Real) → EReal} {α : Real}
    (hαtop : (α : EReal) < ⊤) :
    {x : EuclideanSpace Real (Fin n) | f (x : Fin n → Real) < (α : EReal)} =
      {x : EuclideanSpace Real (Fin n) |
        x ∈ (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f ∧
        f (x : Fin n → Real) < (α : EReal)} := by
  ext x; constructor
  · intro hx
    have hx_top : f (x : Fin n → Real) < (⊤ : EReal) := lt_trans hx hαtop
    have hx_dom :
        (x : Fin n → Real) ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
      have hx' :
          (x : Fin n → Real) ∈ (Set.univ : Set (Fin n → Real)) ∧
            f (x : Fin n → Real) < (⊤ : EReal) := by
        exact ⟨by simp, hx_top⟩
      simpa [effectiveDomain_eq] using hx'
    have hx_dom' :
        x ∈ (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
      simpa using hx_dom
    exact ⟨hx_dom', hx⟩
  · intro hx
    exact hx.2

/-- Relative openness means the relative interior agrees with the set. -/
lemma ri_domf_eq_of_relOpen {n : Nat} {domf : Set (EuclideanSpace Real (Fin n))}
    (hopen : euclideanRelativelyOpen n domf) :
    euclideanRelativeInterior n domf = domf := by
  simpa [euclideanRelativelyOpen] using hopen

/-- Closedness lets us replace `cl f` with `f` in sublevel sets. -/
lemma sublevel_eq_set_of_convexFunctionClosure_of_closed {n : Nat}
    {f : (Fin n → Real) → EReal} {α : Real} (hfclosed : ClosedConvexFunction f)
    (hbot : ∀ x, f x ≠ (⊥ : EReal)) :
    {x : EuclideanSpace Real (Fin n) |
        convexFunctionClosure f (x : Fin n → Real) ≤ (α : EReal)} =
      {x : EuclideanSpace Real (Fin n) | f (x : Fin n → Real) ≤ (α : EReal)} := by
  ext x
  simp [convexFunctionClosure_eq_of_closedConvexFunction (f := f) hfclosed hbot]

/-- Corollary 7.6.1: If `f` is a closed proper convex function whose effective domain is
relatively open (in particular if `effectiveDomain Set.univ f` is an affine set), then for
`inf f < α < +∞` one has `ri {x | f x ≤ α} = {x | f x < α}` and
`cl {x | f x < α} = {x | f x ≤ α}`. -/
theorem closedProperConvexFunction_ri_sublevel_eq_strictSublevel_and_closure {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hfclosed : ClosedConvexFunction f)
    (hfproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hopen :
      euclideanRelativelyOpen n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f))
    {α : Real} (hαinf : iInf (fun x => f x) < (α : EReal))
    (hαtop : (α : EReal) < ⊤) :
    let sublevel : Set (EuclideanSpace Real (Fin n)) :=
      {x | f (x : Fin n → Real) ≤ (α : EReal)}
    let strictSublevel : Set (EuclideanSpace Real (Fin n)) :=
      {x | f (x : Fin n → Real) < (α : EReal)}
    euclideanRelativeInterior n sublevel = strictSublevel ∧
      closure strictSublevel = sublevel := by
  classical
  let sublevel : Set (EuclideanSpace Real (Fin n)) :=
    {x | f (x : Fin n → Real) ≤ (α : EReal)}
  let strictSublevel : Set (EuclideanSpace Real (Fin n)) :=
    {x | f (x : Fin n → Real) < (α : EReal)}
  let domf : Set (EuclideanSpace Real (Fin n)) :=
    (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
      effectiveDomain (Set.univ : Set (Fin n → Real)) f
  have hmain :=
    (properConvexFunction_levelSets_same_closure_ri_dim (n := n) (f := f) hfproper
      (α := α) hαinf)
  have hmain' :
      closure sublevel =
          {x : EuclideanSpace Real (Fin n) |
            convexFunctionClosure f (x : Fin n → Real) ≤ (α : EReal)} ∧
        closure strictSublevel =
          {x : EuclideanSpace Real (Fin n) |
            convexFunctionClosure f (x : Fin n → Real) ≤ (α : EReal)} ∧
        euclideanRelativeInterior n sublevel =
          {x | x ∈ euclideanRelativeInterior n domf ∧
            f (x : Fin n → Real) < (α : EReal)} ∧
        euclideanRelativeInterior n strictSublevel =
          {x | x ∈ euclideanRelativeInterior n domf ∧
            f (x : Fin n → Real) < (α : EReal)} ∧
        Module.finrank Real (affineSpan Real sublevel).direction =
          Module.finrank Real (affineSpan Real domf).direction ∧
        Module.finrank Real (affineSpan Real strictSublevel).direction =
          Module.finrank Real (affineSpan Real domf).direction := by
    simpa [sublevel, strictSublevel, domf] using hmain
  have hri_domf : euclideanRelativeInterior n domf = domf :=
    ri_domf_eq_of_relOpen (n := n) (domf := domf) hopen
  have hstrict_eq :
      strictSublevel =
        {x : EuclideanSpace Real (Fin n) |
          x ∈ domf ∧ f (x : Fin n → Real) < (α : EReal)} := by
    simpa [strictSublevel, domf] using
      (strictSublevel_eq_domf_inter_of_lt_top (n := n) (f := f) (α := α) hαtop)
  have hri_sublevel :
      euclideanRelativeInterior n sublevel =
        {x : EuclideanSpace Real (Fin n) |
          x ∈ domf ∧ f (x : Fin n → Real) < (α : EReal)} := by
    simpa [hri_domf] using hmain'.2.2.1
  have hri_final : euclideanRelativeInterior n sublevel = strictSublevel := by
    calc
      euclideanRelativeInterior n sublevel =
          {x : EuclideanSpace Real (Fin n) |
            x ∈ domf ∧ f (x : Fin n → Real) < (α : EReal)} := hri_sublevel
      _ = strictSublevel := by
        simpa using hstrict_eq.symm
  have hcl_set :
      {x : EuclideanSpace Real (Fin n) |
          convexFunctionClosure f (x : Fin n → Real) ≤ (α : EReal)} =
        sublevel := by
    have hbot : ∀ x, f x ≠ (⊥ : EReal) := by
      intro x
      exact hfproper.2.2 x (by simp)
    simpa [sublevel] using
      (sublevel_eq_set_of_convexFunctionClosure_of_closed (n := n) (f := f) (α := α)
        hfclosed hbot)
  have hclosure_final : closure strictSublevel = sublevel :=
    (hmain'.2.1).trans hcl_set
  have hresult : euclideanRelativeInterior n sublevel = strictSublevel ∧
      closure strictSublevel = sublevel := by
    exact ⟨hri_final, hclosure_final⟩
  simpa [sublevel, strictSublevel] using hresult

end Section07
end Chap02
