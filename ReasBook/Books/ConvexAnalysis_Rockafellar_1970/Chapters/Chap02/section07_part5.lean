/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xinyi Guo, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part4

noncomputable section
open scoped Topology

section Chap02
section Section07

/-- The base of nonempty vertical sections equals the effective domain. -/
lemma riEpigraph_D_eq_effectiveDomain {n : Nat} {f : (Fin n → Real) → EReal} :
    let C : Set (EuclideanSpace Real (Fin (n + 1))) :=
      (appendAffineEquiv n 1) ''
        ((fun p : (Fin n → Real) × Real =>
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => p.2))) ''
          epigraph (S := (Set.univ : Set (Fin n → Real))) f)
    let Cy : EuclideanSpace Real (Fin n) → Set (EuclideanSpace Real (Fin 1)) :=
      fun y => {z | appendAffineEquiv n 1 (y, z) ∈ C}
    let D : Set (EuclideanSpace Real (Fin n)) := {y | (Cy y).Nonempty}
    D =
      (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
  classical
  dsimp
  set C :
      Set (EuclideanSpace Real (Fin (n + 1))) :=
    (appendAffineEquiv n 1) ''
      ((fun p : (Fin n → Real) × Real =>
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => p.2))) ''
        epigraph (S := (Set.univ : Set (Fin n → Real))) f) with hC
  set Cy : EuclideanSpace Real (Fin n) → Set (EuclideanSpace Real (Fin 1)) :=
    fun y => {z | appendAffineEquiv n 1 (y, z) ∈ C} with hCy
  set D : Set (EuclideanSpace Real (Fin n)) := {y | (Cy y).Nonempty} with hD
  let coords1 := EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)
  let first1 : EuclideanSpace Real (Fin 1) → Real := fun z => coords1 z 0
  ext y; constructor
  · intro hy
    rcases hy with ⟨z, hz⟩
    let μ : Real := first1 z
    have hz_eq :
        z =
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
            (fun _ : Fin 1 => μ) := by
      ext i
      fin_cases i
      simp [μ, first1, coords1]
    have hy_eq :
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (y : Fin n → Real) = y := by
      exact (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm_apply_apply y
    have hz' :
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => μ) ∈
          Cy ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (y : Fin n → Real)) := by
      have hz' := hz
      rw [hz_eq] at hz'
      rw [← hy_eq] at hz'
      exact hz'
    have hle :
        f (y : Fin n → Real) ≤ (μ : EReal) :=
      (riEpigraph_section_mem_iff (x := (y : Fin n → Real)) (μ := μ)).1 hz'
    have hy' :
        (y : Fin n → Real) ∈
          effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
      exact ⟨μ, (mem_epigraph_univ_iff (f := f)).2 hle⟩
    simpa using hy'
  · intro hy
    have hy' :
        (y : Fin n → Real) ∈
          effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
      simpa using hy
    rcases hy' with ⟨μ, hμ⟩
    have hle :
        f (y : Fin n → Real) ≤ (μ : EReal) := (mem_epigraph_univ_iff (f := f)).1 hμ
    have hz' :
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => μ) ∈
          Cy ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (y : Fin n → Real)) :=
      (riEpigraph_section_mem_iff (x := (y : Fin n → Real)) (μ := μ)).2 hle
    have hz'' :
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => μ) ∈ Cy y := by
      simpa using hz'
    exact ⟨(EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => μ), hz''⟩

/-- Relative interior of a vertical section is the strict inequality when `f x < ⊤`. -/
lemma riEpigraph_section_ri_iff {n : Nat} {f : (Fin n → Real) → EReal}
    (x : Fin n → Real) (μ : Real) (hfx : f x < (⊤ : EReal)) :
    let C : Set (EuclideanSpace Real (Fin (n + 1))) :=
      (appendAffineEquiv n 1) ''
        ((fun p : (Fin n → Real) × Real =>
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => p.2))) ''
          epigraph (S := (Set.univ : Set (Fin n → Real))) f)
    let y : EuclideanSpace Real (Fin n) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x
    let z : EuclideanSpace Real (Fin 1) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => μ)
    let Cy : EuclideanSpace Real (Fin n) → Set (EuclideanSpace Real (Fin 1)) :=
      fun y => {z | appendAffineEquiv n 1 (y, z) ∈ C}
    z ∈ euclideanRelativeInterior 1 (Cy y) ↔ f x < (μ : EReal) := by
  classical
  dsimp
  set C :
      Set (EuclideanSpace Real (Fin (n + 1))) :=
    (appendAffineEquiv n 1) ''
      ((fun p : (Fin n → Real) × Real =>
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => p.2))) ''
        epigraph (S := (Set.univ : Set (Fin n → Real))) f) with hC
  set y : EuclideanSpace Real (Fin n) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x with hy
  set z : EuclideanSpace Real (Fin 1) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => μ) with hz
  set Cy : EuclideanSpace Real (Fin n) → Set (EuclideanSpace Real (Fin 1)) :=
    fun y => {z | appendAffineEquiv n 1 (y, z) ∈ C} with hCy
  let coords1 := EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)
  let first1 : EuclideanSpace Real (Fin 1) → Real := fun z => coords1 z 0
  have hCy_mem :
      Cy y = {z | f x ≤ (first1 z : EReal)} := by
    ext z'
    have hz_eq :
        z' =
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
            (fun _ : Fin 1 => first1 z') := by
      ext i
      fin_cases i
      simp [first1, coords1]
    have hmem :
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => first1 z') ∈ Cy y ↔
          f x ≤ (first1 z' : EReal) :=
      (riEpigraph_section_mem_iff (x := x) (μ := first1 z'))
    constructor
    · intro hz'
      have hz'' := hz'
      rw [hz_eq] at hz''
      exact hmem.1 hz''
    · intro hz'
      have hz'' :
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => first1 z') ∈ Cy y :=
        hmem.2 hz'
      rw [hz_eq]
      exact hz''
  by_cases hbot : f x = (⊥ : EReal)
  · have hCy' : Cy y = Set.univ := by
      ext z'
      simp [hCy_mem, hbot]
    have hspan :
        (affineSpan Real (Cy y) : Set (EuclideanSpace Real (Fin 1))) = Set.univ := by
      ext z; constructor
      · intro _; trivial
      · intro _
        have hz : z ∈ Cy y := by
          simp [hCy']
        exact (subset_affineSpan (k := Real) (s := Cy y) hz)
    have hri :
        euclideanRelativeInterior 1 (Cy y) = Set.univ := by
      calc
        euclideanRelativeInterior 1 (Cy y) =
            interior (Cy y) :=
          euclideanRelativeInterior_eq_interior_of_affineSpan_eq_univ 1 (Cy y) hspan
        _ = Set.univ := by
          simp [hCy', interior_univ]
    constructor
    · intro _
      simp [hbot]
    · intro _
      have hz' : z ∈ euclideanRelativeInterior 1 (Cy y) := by
        rw [hri]
        trivial
      simpa [hCy, hC, hy, hz] using hz'
  · cases hfx' : f x using EReal.rec with
    | bot =>
        exact (hbot (by simp [hfx'])).elim
    | top =>
        have hfx'' := hfx
        rw [hfx'] at hfx''
        exact (lt_irrefl _ hfx'').elim
    | coe r =>
        have hCy' : Cy y = {z | (r : EReal) ≤ (first1 z : EReal)} := by
          simp [hfx', hCy_mem]
        have hcont : Continuous first1 := by
          simpa [first1] using
            (continuous_apply 0).comp
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).continuous
        have hopen : IsOpen (first1 ⁻¹' Set.Ioi r) := by
          simpa using (isOpen_Ioi.preimage hcont)
        have hne : (first1 ⁻¹' Set.Ioi r).Nonempty := by
          refine ⟨(EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ => r + 1), ?_⟩
          have : r < r + 1 := by linarith
          simp [first1, coords1, this]
        have hsubset : first1 ⁻¹' Set.Ioi r ⊆ Cy y := by
          intro z' hz'
          have hz'' : r ≤ first1 z' := le_of_lt hz'
          have hz''' : (r : EReal) ≤ (first1 z' : EReal) :=
            (EReal.coe_le_coe_iff).2 hz''
          simpa [hCy'] using hz'''
        have hspan_open :
            affineSpan Real (first1 ⁻¹' Set.Ioi r) =
              (⊤ : AffineSubspace Real (EuclideanSpace Real (Fin 1))) :=
          IsOpen.affineSpan_eq_top hopen hne
        have hspan_le :
            (⊤ : AffineSubspace Real (EuclideanSpace Real (Fin 1))) ≤
              affineSpan Real (Cy y) := by
          simpa [hspan_open] using (affineSpan_mono (k := Real) hsubset)
        have hspan : affineSpan Real (Cy y) = ⊤ :=
          le_antisymm le_top hspan_le
        have hspan_set :
            (affineSpan Real (Cy y) : Set (EuclideanSpace Real (Fin 1))) = Set.univ := by
          simp [hspan]
        have hri :
            euclideanRelativeInterior 1 (Cy y) = interior (Cy y) :=
          euclideanRelativeInterior_eq_interior_of_affineSpan_eq_univ 1 (Cy y) hspan_set
        have hCy'' : Cy y = {z | r ≤ first1 z} := by
          ext z'
          constructor
          · intro hz'
            have hz'' : (r : EReal) ≤ (first1 z' : EReal) := by
              simpa [hCy'] using hz'
            exact (EReal.coe_le_coe_iff).1 hz''
          · intro hz'
            have hz'' : (r : EReal) ≤ (first1 z' : EReal) :=
              (EReal.coe_le_coe_iff).2 hz'
            simpa [hCy'] using hz''
        let e1 :
            EuclideanSpace Real (Fin 1) ≃L[Real] Real :=
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).toContinuousLinearEquiv.trans
            (ContinuousLinearEquiv.funUnique (ι := Fin 1) (R := Real) (M := Real))
        have hfirst1 : (fun z => e1 z) = first1 := by
          ext z'
          simp [e1, first1, coords1, PiLp.coe_continuousLinearEquiv]
        have hCy_e1 : Cy y = e1 ⁻¹' Set.Ici r := by
          ext z'
          constructor
          · intro hz'
            have hz'' : r ≤ first1 z' := by simpa [hCy''] using hz'
            simpa [hfirst1] using hz''
          · intro hz'
            have hz'' : r ≤ first1 z' := by simpa [hfirst1] using hz'
            simpa [hCy''] using hz''
        have hinterior : interior (Cy y) = e1 ⁻¹' Set.Ioi r := by
          have hpre :
              e1 ⁻¹' interior (Set.Ici r) = interior (e1 ⁻¹' Set.Ici r) :=
            (e1.toHomeomorph.preimage_interior (Set.Ici r))
          have hpre' : interior (e1 ⁻¹' Set.Ici r) = e1 ⁻¹' interior (Set.Ici r) :=
            hpre.symm
          simpa [hCy_e1, interior_Ici] using hpre'
        have hmem :
            z ∈ euclideanRelativeInterior 1 (Cy y) ↔ r < μ := by
          have hmem' : z ∈ interior (Cy y) ↔ r < μ := by
            have : z ∈ e1 ⁻¹' Set.Ioi r ↔ r < μ := by
              simp [hz, hfirst1, first1, coords1]
            rw [hinterior]
            exact this
          rw [hri]
          exact hmem'
        simpa [hCy, hC, hy, hz, hfx', EReal.coe_lt_coe_iff] using hmem

/-- Real points are always strictly below `⊤`. -/
lemma riEpigraph_mu_lt_top (μ : Real) : (μ : EReal) < ⊤ := by
  exact EReal.coe_lt_top μ

/-- Lemma 7.3. For any convex function `f`, `ri (epi f)` consists of the pairs `(x, μ)`
such that `x ∈ ri (dom f)` and `f x < μ < ∞`. -/
theorem riEpigraph_mem_iff {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ConvexFunction f) (x : Fin n → Real) (μ : Real) :
    (appendAffineEquiv n 1)
        ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x,
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
            (fun _ : Fin 1 => μ)) ∈ riEpigraph f ↔
      ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x) ∈
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f) ∧
        f x < (μ : EReal) ∧ (μ : EReal) < ⊤ := by
  classical
  let C :
      Set (EuclideanSpace Real (Fin (n + 1))) :=
    (appendAffineEquiv n 1) ''
      ((fun p : (Fin n → Real) × Real =>
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => p.2))) ''
        epigraph (S := (Set.univ : Set (Fin n → Real))) f)
  let y : EuclideanSpace Real (Fin n) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x
  let z : EuclideanSpace Real (Fin 1) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
      (fun _ : Fin 1 => μ)
  let Cy : EuclideanSpace Real (Fin n) → Set (EuclideanSpace Real (Fin 1)) :=
    fun y => {z | appendAffineEquiv n 1 (y, z) ∈ C}
  let D : Set (EuclideanSpace Real (Fin n)) := {y | (Cy y).Nonempty}
  have hconv_epi :
      Convex ℝ (epigraph (Set.univ : Set (Fin n → Real)) f) := by
    simpa [ConvexFunction] using
      (convex_epigraph_of_convexFunctionOn (f := f) (hf := hf))
  let eN : (Fin n → Real) ≃ᵃ[Real] EuclideanSpace Real (Fin n) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm.toLinearEquiv.toAffineEquiv
  let e1 : Real ≃ᵃ[Real] EuclideanSpace Real (Fin 1) :=
    ((ContinuousLinearEquiv.funUnique (ι := Fin 1) (R := Real) (M := Real)).symm.toLinearEquiv.trans
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm.toLinearEquiv).toAffineEquiv
  let g : (Fin n → Real) × Real ≃ᵃ[Real]
      (EuclideanSpace Real (Fin n) × EuclideanSpace Real (Fin 1)) :=
    AffineEquiv.prodCongr eN e1
  have hC_eq :
      ((fun p : (Fin n → Real) × Real =>
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => p.2))) ''
        epigraph (S := (Set.univ : Set (Fin n → Real))) f) =
        g '' epigraph (S := (Set.univ : Set (Fin n → Real))) f := by
    ext q; constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p, hp, ?_⟩
      simp [g, eN, e1]
      rfl
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p, hp, ?_⟩
      simp [g, eN, e1]
      rfl
  have hconv_C : Convex ℝ C := by
    have hconv_g :
        Convex ℝ (g '' epigraph (S := (Set.univ : Set (Fin n → Real))) f) :=
      by
        simpa using (Convex.affine_image (f := g.toAffineMap) hconv_epi)
    simpa [C, hC_eq] using
      (Convex.affine_image (f := (appendAffineEquiv n 1).toAffineMap) hconv_g)
  have hsection :
      appendAffineEquiv n 1 (y, z) ∈ euclideanRelativeInterior (n + 1) C ↔
        y ∈ euclideanRelativeInterior n D ∧ z ∈ euclideanRelativeInterior 1 (Cy y) := by
    simpa [Cy, D, appendAffineEquiv_apply] using
      (euclideanRelativeInterior_mem_iff_relativeInterior_section (m := n) (p := 1)
        (C := C) hconv_C y z)
  have hD_eq :
      D =
        (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
    simpa [C, Cy, D] using (riEpigraph_D_eq_effectiveDomain (f := f))
  constructor
  · intro hmem
    have hmem' :
        y ∈ euclideanRelativeInterior n D ∧ z ∈ euclideanRelativeInterior 1 (Cy y) :=
      (hsection).1 hmem
    rcases hmem' with ⟨hyD, hzCy⟩
    have hyD' : y ∈ D := (euclideanRelativeInterior_subset_closure n D).1 hyD
    have hy_eff :
        (y : Fin n → Real) ∈
          effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
      simpa [hD_eq] using hyD'
    have hfx_top : f x < (⊤ : EReal) := by
      have : x ∈ {x | x ∈ (Set.univ : Set (Fin n → Real)) ∧ f x < (⊤ : EReal)} := by
        simpa [effectiveDomain_eq] using hy_eff
      exact this.2
    have hz' :
        f x < (μ : EReal) :=
      (riEpigraph_section_ri_iff (x := x) (μ := μ) hfx_top).1 hzCy
    refine ⟨?_, hz', riEpigraph_mu_lt_top μ⟩
    simpa [hD_eq] using hyD
  · rintro ⟨hxri, hlt, hlt_top⟩
    have hyD : y ∈ euclideanRelativeInterior n D := by
      simpa [hD_eq] using hxri
    have hfx_top : f x < (⊤ : EReal) := lt_trans hlt hlt_top
    have hzCy :
        z ∈ euclideanRelativeInterior 1 (Cy y) :=
      (riEpigraph_section_ri_iff (x := x) (μ := μ) hfx_top).2 hlt
    exact (hsection).2 ⟨hyD, hzCy⟩

/-- Find a real height strictly between `f x` and `α`. -/
lemma exists_real_between_fx_alpha {n : Nat} {f : (Fin n → Real) → EReal}
    {α : Real} {x : Fin n → Real} (h : f x < (α : EReal)) :
    ∃ μ : Real, f x < (μ : EReal) ∧ (μ : EReal) < (α : EReal) := by
  rcases EReal.exists_between_coe_real h with ⟨μ, hlt, hlt'⟩
  exact ⟨μ, hlt, hlt'⟩

/-- The embedded epigraph used in `riEpigraph` is convex. -/
lemma convex_embedded_epigraph {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ConvexFunction f) :
    let C : Set (EuclideanSpace Real (Fin (n + 1))) :=
      (appendAffineEquiv n 1) ''
        ((fun p : (Fin n → Real) × Real =>
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => p.2))) ''
          epigraph (S := (Set.univ : Set (Fin n → Real))) f)
    Convex ℝ C := by
  classical
  dsimp
  have hconv_epi :
      Convex ℝ (epigraph (Set.univ : Set (Fin n → Real)) f) := by
    simpa [ConvexFunction] using
      (convex_epigraph_of_convexFunctionOn (f := f) (hf := hf))
  let eN : (Fin n → Real) ≃ᵃ[Real] EuclideanSpace Real (Fin n) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm.toLinearEquiv.toAffineEquiv
  let e1 : Real ≃ᵃ[Real] EuclideanSpace Real (Fin 1) :=
    ((ContinuousLinearEquiv.funUnique (ι := Fin 1) (R := Real) (M := Real)).symm.toLinearEquiv.trans
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm.toLinearEquiv).toAffineEquiv
  let g : (Fin n → Real) × Real ≃ᵃ[Real]
      (EuclideanSpace Real (Fin n) × EuclideanSpace Real (Fin 1)) :=
    AffineEquiv.prodCongr eN e1
  have hC_eq :
      ((fun p : (Fin n → Real) × Real =>
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => p.2))) ''
        epigraph (S := (Set.univ : Set (Fin n → Real))) f) =
        g '' epigraph (S := (Set.univ : Set (Fin n → Real))) f := by
    ext q; constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p, hp, ?_⟩
      simp [g, eN, e1]
      rfl
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p, hp, ?_⟩
      simp [g, eN, e1]
      rfl
  have hconv_g :
      Convex ℝ (g '' epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
    simpa using (Convex.affine_image (f := g.toAffineMap) hconv_epi)
  simpa [hC_eq] using
    (Convex.affine_image (f := (appendAffineEquiv n 1).toAffineMap) hconv_g)

/-- The open half-space defined by the last coordinate is open. -/
lemma isOpen_openHalfspace_lastCoord {n : Nat} {α : Real} :
    IsOpen
      {p : EuclideanSpace Real (Fin (n + 1)) |
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)
              ((appendAffineEquiv n 1).symm p).2) 0 < α} := by
  let μ_of : EuclideanSpace Real (Fin (n + 1)) → Real := fun p =>
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1) ((appendAffineEquiv n 1).symm p).2) 0
  have hcont_symm :
      Continuous (fun p : EuclideanSpace Real (Fin (n + 1)) =>
        (appendAffineEquiv n 1).symm p) := by
    simpa using
      (AffineEquiv.continuous_of_finiteDimensional (f := (appendAffineEquiv n 1).symm))
  have hcont_snd :
      Continuous (fun p : EuclideanSpace Real (Fin (n + 1)) =>
        ((appendAffineEquiv n 1).symm p).2) :=
    continuous_snd.comp hcont_symm
  have hcont_coords :
      Continuous (fun z : EuclideanSpace Real (Fin 1) =>
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1) z) 0) := by
    simpa using
      (continuous_apply 0).comp
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).continuous
  have hcont : Continuous μ_of := by
    simpa [μ_of] using hcont_coords.comp hcont_snd
  simpa [μ_of] using (isOpen_Iio.preimage hcont)

/-- Build a point of the embedded epigraph lying strictly below height `α`. -/
lemma exists_point_openHalfspace_inter_embedded_epigraph {n : Nat}
    {f : (Fin n → Real) → EReal} {α : Real} (hα : ∃ x, f x < (α : EReal)) :
    let C : Set (EuclideanSpace Real (Fin (n + 1))) :=
      (appendAffineEquiv n 1) ''
        ((fun p : (Fin n → Real) × Real =>
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => p.2))) ''
          epigraph (S := (Set.univ : Set (Fin n → Real))) f)
    let U : Set (EuclideanSpace Real (Fin (n + 1))) :=
      {p : EuclideanSpace Real (Fin (n + 1)) |
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1) ((appendAffineEquiv n 1).symm p).2) 0 < α}
    (U ∩ C).Nonempty := by
  classical
  dsimp
  rcases hα with ⟨x, hx⟩
  obtain ⟨μ, hfxμ, hμα⟩ :=
    exists_real_between_fx_alpha (f := f) (α := α) (x := x) hx
  let y : EuclideanSpace Real (Fin n) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x
  let z : EuclideanSpace Real (Fin 1) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => μ)
  let p : EuclideanSpace Real (Fin (n + 1)) := appendAffineEquiv n 1 (y, z)
  have hmem_epi :
      (x, μ) ∈ epigraph (S := (Set.univ : Set (Fin n → Real))) f := by
    have hle : f x ≤ (μ : EReal) := le_of_lt hfxμ
    exact (mem_epigraph_univ_iff (f := f)).2 hle
  have hpC : p ∈
      (appendAffineEquiv n 1) ''
        ((fun p : (Fin n → Real) × Real =>
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => p.2))) ''
          epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
    refine ⟨(y, z), ?_, rfl⟩
    refine ⟨(x, μ), hmem_epi, ?_⟩
    simp [y, z]
  have hμα' : μ < α := (EReal.coe_lt_coe_iff).1 hμα
  have hpU :
      p ∈
        {p : EuclideanSpace Real (Fin (n + 1)) |
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)
                ((appendAffineEquiv n 1).symm p).2) 0 < α} := by
    simpa [p, z] using hμα'
  exact ⟨p, hpU, hpC⟩

/-- Corollary 7.3.1: Let `α` be a real number, and let `f` be a convex function such that,
for some `x`, `f x < α`. Then there exists `x ∈ ri (dom f)` with `f x < α`. -/
theorem exists_lt_on_ri_effectiveDomain_of_convexFunction {n : Nat}
    {f : (Fin n → Real) → EReal} (hf : ConvexFunction f) {α : Real}
    (hα : ∃ x, f x < (α : EReal)) :
    ∃ x ∈
      euclideanRelativeInterior n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f),
      f x < (α : EReal) := by
  classical
  set C :
      Set (EuclideanSpace Real (Fin (n + 1))) :=
    (appendAffineEquiv n 1) ''
      ((fun p : (Fin n → Real) × Real =>
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => p.2))) ''
        epigraph (S := (Set.univ : Set (Fin n → Real))) f) with hC
  set U :
      Set (EuclideanSpace Real (Fin (n + 1))) :=
    {p : EuclideanSpace Real (Fin (n + 1)) |
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1) ((appendAffineEquiv n 1).symm p).2) 0 < α}
    with hU
  have hUopen : IsOpen U := by
    simpa [hU] using (isOpen_openHalfspace_lastCoord (n := n) (α := α))
  have hconvC : Convex ℝ C := by
    simpa [hC] using (convex_embedded_epigraph (n := n) (f := f) hf)
  have hmeetC : (U ∩ closure C).Nonempty := by
    have hmeet' : (U ∩ C).Nonempty := by
      simpa [hC, hU] using
        (exists_point_openHalfspace_inter_embedded_epigraph (n := n) (f := f) (α := α) hα)
    rcases hmeet' with ⟨p, hpU, hpC⟩
    exact ⟨p, hpU, subset_closure hpC⟩
  have hmeetRi :
      (U ∩ euclideanRelativeInterior (n + 1) C).Nonempty :=
    (euclidean_open_meets_closure_meets_relativeInterior (n := n + 1) (C := C) (U := U)
      hconvC hUopen hmeetC)
  rcases hmeetRi with ⟨p, hpU, hpRi⟩
  have hpRi' : p ∈ riEpigraph f := by
    simpa [riEpigraph, hC] using hpRi
  let y : EuclideanSpace Real (Fin n) := ((appendAffineEquiv n 1).symm p).1
  let z : EuclideanSpace Real (Fin 1) := ((appendAffineEquiv n 1).symm p).2
  let x : Fin n → Real := (y : Fin n → Real)
  let μ : Real := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) z 0
  have hy_eq :
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x = y := by
    exact (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm_apply_apply y
  have hz_fun :
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) z = fun _ : Fin 1 => μ := by
    ext i
    fin_cases i
    simp [μ]
  have hz_eq :
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => μ) = z := by
    simpa [hz_fun] using
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm_apply_apply z
  have hp_repr :
      (appendAffineEquiv n 1)
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x,
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => μ)) = p := by
    have hp' : (appendAffineEquiv n 1) (y, z) = p := by
      simp [y, z]
    simpa [hy_eq.symm, hz_eq.symm] using hp'
  have hp_repr' :
      (appendAffineEquiv n 1) (WithLp.toLp 2 x, WithLp.toLp 2 (fun _ : Fin 1 => μ)) = p := by
    simpa using hp_repr
  have hpRi'' :
      (appendAffineEquiv n 1)
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x,
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => μ)) ∈ riEpigraph f := by
    simpa [hp_repr'] using hpRi'
  have hxri :
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x ∈
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f) ∧
        f x < (μ : EReal) ∧ (μ : EReal) < ⊤ :=
    (riEpigraph_mem_iff (n := n) (f := f) hf x μ).1 hpRi''
  rcases hxri with ⟨hxri, hfxμ, -⟩
  have hyri :
      y ∈
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
    simpa [hy_eq] using hxri
  have hμα' : μ < α := by
    simpa [hU, z, μ] using hpU
  have hμα : (μ : EReal) < (α : EReal) := (EReal.coe_lt_coe_iff).2 hμα'
  have hfxα : f x < (α : EReal) := lt_trans hfxμ hμα
  refine ⟨y, hyri, ?_⟩
  simpa [x] using hfxα

/-- Corollary 7.3.2. Let `f` be a convex function, and let `C` be a convex set such that
`ri C ⊆ dom f`. Let `α ∈ ℝ` be such that `f x < α` for some `x ∈ cl C`. Then `f x < α`
for some `x ∈ ri C`. -/
theorem exists_lt_on_ri_of_convexFunction_convexSet {n : Nat}
    {f : (Fin n → Real) → EReal} (hf : ConvexFunction f)
    {C : Set (EuclideanSpace Real (Fin n))} (hC : Convex ℝ C)
    (hri :
      euclideanRelativeInterior n C ⊆
        (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    {α : Real} (hα : ∃ x ∈ closure C, f (x : Fin n → Real) < (α : EReal)) :
    ∃ x ∈ euclideanRelativeInterior n C, f (x : Fin n → Real) < (α : EReal) := by
  classical
  rcases hα with ⟨x0, hx0_closure, hfx0α⟩
  have hCne : C.Nonempty := by
    by_contra hCne
    have hCempty : C = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using hCne
    simp [hCempty] at hx0_closure
  obtain ⟨y, hyri⟩ :=
    (euclideanRelativeInterior_closure_convex_affineSpan n C hC).2.2.2.2 hCne
  have hy_dom_pre :
      y ∈
        (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f :=
    hri hyri
  have hy_dom :
      (y : Fin n → Real) ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
    simpa using hy_dom_pre
  rcases hy_dom with ⟨μy, hμy⟩
  have hy_le : f (y : Fin n → Real) ≤ (μy : EReal) :=
    (mem_epigraph_univ_iff (f := f)).1 hμy
  obtain ⟨μx, hfx0μx, hμxα⟩ :=
    exists_real_between_fx_alpha (f := f) (α := α) (x := (x0 : Fin n → Real)) hfx0α
  have hx_le : f (x0 : Fin n → Real) ≤ (μx : EReal) := le_of_lt hfx0μx
  have hμxα_real : μx < α := (EReal.coe_lt_coe_iff).1 hμxα
  set δ : Real := α - μx
  have hδpos : 0 < δ := by
    dsimp [δ]
    linarith [hμxα_real]
  set d : Real := μy - μx
  set s : Real := δ / (δ + |d|)
  set t : Real := 1 - s
  have hs_pos : 0 < s := by
    dsimp [s]
    have hden : 0 < δ + |d| := by linarith [hδpos, abs_nonneg d]
    exact div_pos hδpos hden
  have hs_le_one : s ≤ 1 := by
    dsimp [s]
    have hden : 0 < δ + |d| := by linarith [hδpos, abs_nonneg d]
    have hnum_le : δ ≤ δ + |d| := by linarith [abs_nonneg d]
    exact (div_le_one hden).2 hnum_le
  have ht0 : 0 ≤ t := by
    dsimp [t]
    linarith [hs_le_one]
  have ht1 : t < 1 := by
    dsimp [t]
    linarith [hs_pos]
  have hzri :
      (1 - t) • y + t • x0 ∈ euclideanRelativeInterior n C :=
    euclideanRelativeInterior_convex_combination_mem n C hC y x0 hyri hx0_closure t ht0 ht1
  have hconv_epi :
      Convex ℝ (epigraph (Set.univ : Set (Fin n → Real)) f) := by
    simpa [ConvexFunction, ConvexFunctionOn] using hf
  have hle :
      f ((1 - t) • (y : Fin n → Real) + t • (x0 : Fin n → Real)) ≤
        (((1 - t) * μy + t * μx : Real) : EReal) :=
    epigraph_combo_ineq_aux (S := (Set.univ : Set (Fin n → Real))) (f := f)
      (x := (y : Fin n → Real)) (y := (x0 : Fin n → Real)) (μ := μy) (v := μx)
      hconv_epi (by simp) (by simp) hy_le hx_le ht0 (le_of_lt ht1)
  have hlt_real : (1 - t) * μy + t * μx < α := by
    have hcalc :
        (1 - t) * μy + t * μx = μx + s * d := by
      simp [t, d]
      ring
    have hsd_lt : s * d < δ := by
      by_cases hd : d ≤ 0
      · have hsd_le : s * d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hs_pos) hd
        exact lt_of_le_of_lt hsd_le hδpos
      · have hdpos : 0 < d := lt_of_not_ge hd
        have hden : 0 < δ + d := by linarith [hδpos, hdpos]
        have hs_eq : s = δ / (δ + d) := by
          simp [s, abs_of_pos hdpos]
        have hfrac : d / (δ + d) < 1 := by
          have hlt : d < δ + d := by linarith [hδpos]
          exact (div_lt_one hden).2 hlt
        have hmul : δ * (d / (δ + d)) < δ := by
          simpa using (mul_lt_mul_of_pos_left hfrac hδpos)
        have hsd_eq : s * d = δ * (d / (δ + d)) := by
          calc
            s * d = (δ / (δ + d)) * d := by simp [hs_eq]
            _ = δ * d / (δ + d) := by
              simp [div_mul_eq_mul_div]
            _ = δ * (d / (δ + d)) := by
              simp [mul_div_assoc]
        simpa [hsd_eq] using hmul
    have hlt' : μx + s * d < μx + δ := by linarith [hsd_lt]
    have hα_eq : μx + δ = α := by
      simp [δ]
    simpa [hcalc, hα_eq] using hlt'
  have hlt_ereal :
      (((1 - t) * μy + t * μx : Real) : EReal) < (α : EReal) := by
    exact (EReal.coe_lt_coe_iff).2 hlt_real
  refine ⟨(1 - t) • y + t • x0, hzri, ?_⟩
  exact lt_of_le_of_lt hle hlt_ereal

/-- If `f` is finite on `C`, then `ri C` lies in the effective domain of `f`. -/
lemma ri_subset_effectiveDomain_of_finite_on_C {n : Nat}
    {f : (Fin n → Real) → EReal} {C : Set (EuclideanSpace Real (Fin n))}
    (hfinite : ∀ x ∈ C,
      f (x : Fin n → Real) ≠ (⊤ : EReal) ∧ f (x : Fin n → Real) ≠ (⊥ : EReal)) :
    euclideanRelativeInterior n C ⊆
      (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
  intro x hx
  have hxC : x ∈ C := (euclideanRelativeInterior_subset_closure n C).1 hx
  have hne_top : f (x : Fin n → Real) ≠ (⊤ : EReal) := (hfinite x hxC).1
  have hlt_top : f (x : Fin n → Real) < (⊤ : EReal) := (lt_top_iff_ne_top).2 hne_top
  have hx_eff :
      (x : Fin n → Real) ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
    have hx_mem :
        (x : Fin n → Real) ∈
          {x | x ∈ (Set.univ : Set (Fin n → Real)) ∧ f x < (⊤ : EReal)} := by
      exact ⟨by simp, hlt_top⟩
    simpa [effectiveDomain_eq] using hx_mem
  simpa using hx_eff

/-- Corollary 7.3.3. Let `f` be a convex function on `ℝ^n`, and let `C` be a convex set on
which `f` is finite. If `f x ≥ α` for every `x ∈ C`, then also `f x ≥ α` for every
`x ∈ cl C`. -/
theorem convexFunction_ge_on_closure_of_convexSet {n : Nat}
    {f : (Fin n → Real) → EReal} (hf : ConvexFunction f)
    {C : Set (EuclideanSpace Real (Fin n))} (hC : Convex ℝ C)
    (hfinite : ∀ x ∈ C,
      f (x : Fin n → Real) ≠ (⊤ : EReal) ∧ f (x : Fin n → Real) ≠ (⊥ : EReal))
    {α : Real} (hα : ∀ x ∈ C, f (x : Fin n → Real) ≥ (α : EReal)) :
    ∀ x ∈ closure C, f (x : Fin n → Real) ≥ (α : EReal) := by
  classical
  intro x hx_closure
  by_contra hge
  have hlt : f (x : Fin n → Real) < (α : EReal) := lt_of_not_ge hge
  have hri :
      euclideanRelativeInterior n C ⊆
        (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f :=
    ri_subset_effectiveDomain_of_finite_on_C (C := C) (f := f) hfinite
  have hα' : ∃ x ∈ closure C, f (x : Fin n → Real) < (α : EReal) :=
    ⟨x, hx_closure, hlt⟩
  rcases
      exists_lt_on_ri_of_convexFunction_convexSet (n := n) (f := f) hf hC hri hα'
    with ⟨y, hyri, hfylt⟩
  have hyC : y ∈ C := (euclideanRelativeInterior_subset_closure n C).1 hyri
  have hge_y : (α : EReal) ≤ f (y : Fin n → Real) := hα y hyC
  exact (not_lt_of_ge hge_y) hfylt

/-- If a convex function has a bottom value, then it attains `⊥` on `ri (dom f)`. -/
lemma exists_bot_on_ri_effectiveDomain_of_exists_bot {n : Nat}
    {f : (Fin n → Real) → EReal} (hf : ConvexFunction f)
    (hbot : ∃ x, f x = (⊥ : EReal)) :
    ∃ y ∈
      euclideanRelativeInterior n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f),
      f (y : Fin n → Real) = (⊥ : EReal) := by
  classical
  have hf_improper :
      ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
    refine ⟨?_, ?_⟩
    · simpa [ConvexFunction] using hf
    · intro hproper
      rcases hproper with ⟨_, _, hnotbot⟩
      rcases hbot with ⟨x0, hx0⟩
      exact (hnotbot x0 (by simp) hx0)
  set C :
      Set (EuclideanSpace Real (Fin n)) :=
    (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
      effectiveDomain (Set.univ : Set (Fin n → Real)) f with hC
  have hconv_dom :
      Convex Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
    effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real))) (f := f)
      (by simpa [ConvexFunction] using hf)
  have hCconv : Convex Real C := by
    simpa [hC] using
      (Convex.linear_preimage
        (s := effectiveDomain (Set.univ : Set (Fin n → Real)) f)
        hconv_dom
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).toLinearMap)
  rcases hbot with ⟨x0, hx0⟩
  have hx0_ne_top : f x0 ≠ (⊤ : EReal) := by
    simp [hx0]
  have hx0_lt_top : f x0 < (⊤ : EReal) :=
    (lt_top_iff_ne_top).2 hx0_ne_top
  have hx0_eff :
      x0 ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
    have hx0_mem :
        x0 ∈ {x | x ∈ (Set.univ : Set (Fin n → Real)) ∧ f x < (⊤ : EReal)} := by
      exact ⟨by simp, hx0_lt_top⟩
    simpa [effectiveDomain_eq] using hx0_mem
  have hCne : C.Nonempty := by
    refine ⟨(EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x0, ?_⟩
    simpa [hC] using hx0_eff
  have hri_ne :
      (euclideanRelativeInterior n C).Nonempty :=
    (euclideanRelativeInterior_closure_convex_affineSpan n C hCconv).2.2.2.2 hCne
  rcases hri_ne with ⟨y, hyri⟩
  have hbot_ri :=
    improperConvexFunctionOn_eq_bot_on_ri_effectiveDomain (f := f) hf_improper
  have hybot : f y = (⊥ : EReal) := hbot_ri y (by simpa [hC] using hyri)
  exact ⟨y, by simpa [hC] using hyri, hybot⟩

/-- Agreement on `ri (dom f)` yields equality of `ri (epi f)`. -/
lemma riEpigraph_eq_of_agree_on_ri_effectiveDomain {n : Nat}
    {f g : (Fin n → Real) → EReal} (hf : ConvexFunction f) (hg : ConvexFunction g)
    (hri :
      euclideanRelativeInterior n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f) =
      euclideanRelativeInterior n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) g))
    (hagree :
      ∀ x ∈
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f),
        f (x : Fin n → Real) = g (x : Fin n → Real)) :
    riEpigraph f = riEpigraph g := by
  classical
  ext p; constructor
  · intro hp
    rcases (appendAffineEquiv n 1).surjective p with ⟨yz, rfl⟩
    rcases yz with ⟨y, z⟩
    set x : Fin n → Real := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) y
    set μ : Real := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) z 0
    have hy :
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x = y := by
      simp [x]
    have hz :
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => μ) = z := by
      ext i
      fin_cases i
      simp [μ]
    have hp' :
        (appendAffineEquiv n 1)
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x,
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => μ)) ∈ riEpigraph f := by
      simpa [hy, hz] using hp
    have hmem :=
      (riEpigraph_mem_iff (n := n) (f := f) hf x μ).1 hp'
    rcases hmem with ⟨hxri, hlt, hlt_top⟩
    have hxri' :
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x ∈
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → Real)) g) := by
      simpa [hri] using hxri
    have hfg : f x = g x := by
      have hfg' :=
        hagree ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x) hxri
      simpa [x] using hfg'
    have hlt' : g x < (μ : EReal) := by
      simpa [hfg] using hlt
    have hp'' :
        (appendAffineEquiv n 1)
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x,
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => μ)) ∈ riEpigraph g := by
      exact (riEpigraph_mem_iff (n := n) (f := g) hg x μ).2 ⟨hxri', hlt', hlt_top⟩
    simpa [hy, hz] using hp''
  · intro hp
    rcases (appendAffineEquiv n 1).surjective p with ⟨yz, rfl⟩
    rcases yz with ⟨y, z⟩
    set x : Fin n → Real := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) y
    set μ : Real := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)) z 0
    have hy :
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x = y := by
      simp [x]
    have hz :
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => μ) = z := by
      ext i
      fin_cases i
      simp [μ]
    have hp' :
        (appendAffineEquiv n 1)
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x,
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => μ)) ∈ riEpigraph g := by
      simpa [hy, hz] using hp
    have hmem :=
      (riEpigraph_mem_iff (n := n) (f := g) hg x μ).1 hp'
    rcases hmem with ⟨hxri, hlt, hlt_top⟩
    have hxri' :
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x ∈
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
      simpa [hri.symm] using hxri
    have hfg : f x = g x := by
      have hfg' :=
        hagree ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x) hxri'
      simpa [x] using hfg'
    have hlt' : f x < (μ : EReal) := by
      simpa [hfg] using hlt
    have hp'' :
        (appendAffineEquiv n 1)
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x,
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => μ)) ∈ riEpigraph f := by
      exact (riEpigraph_mem_iff (n := n) (f := f) hf x μ).2 ⟨hxri', hlt', hlt_top⟩
    simpa [hy, hz] using hp''

/-- Relative interior equality gives closure equality for embedded epigraphs. -/
lemma closure_embedded_epigraph_eq_of_riEpigraph_eq {n : Nat}
    {f g : (Fin n → Real) → EReal} (hf : ConvexFunction f) (hg : ConvexFunction g)
    (hri_epi : riEpigraph f = riEpigraph g) :
    let C_f : Set (EuclideanSpace Real (Fin (n + 1))) :=
      (appendAffineEquiv n 1) ''
        ((fun p : (Fin n → Real) × Real =>
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => p.2))) ''
          epigraph (S := (Set.univ : Set (Fin n → Real))) f)
    let C_g : Set (EuclideanSpace Real (Fin (n + 1))) :=
      (appendAffineEquiv n 1) ''
        ((fun p : (Fin n → Real) × Real =>
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => p.2))) ''
          epigraph (S := (Set.univ : Set (Fin n → Real))) g)
    closure C_f = closure C_g := by
  classical
  dsimp
  set C_f :
      Set (EuclideanSpace Real (Fin (n + 1))) :=
    (appendAffineEquiv n 1) ''
      ((fun p : (Fin n → Real) × Real =>
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => p.2))) ''
        epigraph (S := (Set.univ : Set (Fin n → Real))) f) with hC_f
  set C_g :
      Set (EuclideanSpace Real (Fin (n + 1))) :=
    (appendAffineEquiv n 1) ''
      ((fun p : (Fin n → Real) × Real =>
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => p.2))) ''
        epigraph (S := (Set.univ : Set (Fin n → Real))) g) with hC_g
  have hconv_f : Convex ℝ C_f := by
    simpa [hC_f] using (convex_embedded_epigraph (n := n) (f := f) hf)
  have hconv_g : Convex ℝ C_g := by
    simpa [hC_g] using (convex_embedded_epigraph (n := n) (f := g) hg)
  have hri :
      euclideanRelativeInterior (n + 1) C_f =
        euclideanRelativeInterior (n + 1) C_g := by
    simpa [riEpigraph, hC_f, hC_g] using hri_epi
  exact
    euclidean_closure_eq_of_relativeInterior_eq (n := n + 1) C_f C_g hconv_f hconv_g hri

end Section07
end Chap02
