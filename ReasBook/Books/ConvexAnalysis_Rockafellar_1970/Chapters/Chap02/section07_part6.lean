/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xinyi Guo, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part5

noncomputable section
open scoped Topology

section Chap02
section Section07

/-- Equality of embedded epigraph closures yields equality of epigraph closures. -/
lemma closure_epigraph_eq_of_embedded_closure_eq {n : Nat}
    {f g : (Fin n → Real) → EReal} :
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
    closure C_f = closure C_g →
      closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) =
        closure (epigraph (S := (Set.univ : Set (Fin n → Real))) g) := by
  classical
  dsimp
  intro hcl
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
  have hcl' : closure C_f = closure C_g := by
    simpa [hC_f, hC_g] using hcl
  let eN : (Fin n → Real) ≃ᵃ[Real] EuclideanSpace Real (Fin n) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm.toLinearEquiv.toAffineEquiv
  let e1 : Real ≃ᵃ[Real] EuclideanSpace Real (Fin 1) :=
    ((ContinuousLinearEquiv.funUnique (ι := Fin 1) (R := Real) (M := Real)).symm.toLinearEquiv.trans
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm.toLinearEquiv).toAffineEquiv
  let g_aff : (Fin n → Real) × Real ≃ᵃ[Real]
      (EuclideanSpace Real (Fin n) × EuclideanSpace Real (Fin 1)) :=
    AffineEquiv.prodCongr eN e1
  have hphi_f :
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
  have hphi_g :
      ((fun p : (Fin n → Real) × Real =>
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => p.2))) ''
        epigraph (S := (Set.univ : Set (Fin n → Real))) g) =
        g_aff '' epigraph (S := (Set.univ : Set (Fin n → Real))) g := by
    ext q; constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p, hp, ?_⟩
      simp [g_aff, eN, e1]
      rfl
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p, hp, ?_⟩
      simp [g_aff, eN, e1]
      rfl
  have hpre_f :
      closure
          ((fun p : (Fin n → Real) × Real =>
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
                (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                  (fun _ : Fin 1 => p.2))) ''
            epigraph (S := (Set.univ : Set (Fin n → Real))) f) =
        (appendAffineEquiv n 1).toHomeomorphOfFiniteDimensional ⁻¹' (closure C_f) := by
    simpa [hC_f, Set.preimage_image_eq, (appendAffineEquiv n 1).injective] using
      (Homeomorph.preimage_closure
          (h := (appendAffineEquiv n 1).toHomeomorphOfFiniteDimensional)
          (s := C_f)).symm
  have hpre_g :
      closure
          ((fun p : (Fin n → Real) × Real =>
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
                (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                  (fun _ : Fin 1 => p.2))) ''
            epigraph (S := (Set.univ : Set (Fin n → Real))) g) =
        (appendAffineEquiv n 1).toHomeomorphOfFiniteDimensional ⁻¹' (closure C_g) := by
    simpa [hC_g, Set.preimage_image_eq, (appendAffineEquiv n 1).injective] using
      (Homeomorph.preimage_closure
          (h := (appendAffineEquiv n 1).toHomeomorphOfFiniteDimensional)
          (s := C_g)).symm
  have hcl_inner :
      closure
          ((fun p : (Fin n → Real) × Real =>
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
                (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                  (fun _ : Fin 1 => p.2))) ''
            epigraph (S := (Set.univ : Set (Fin n → Real))) f) =
        closure
          ((fun p : (Fin n → Real) × Real =>
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
                (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                  (fun _ : Fin 1 => p.2))) ''
            epigraph (S := (Set.univ : Set (Fin n → Real))) g) := by
    calc
      closure
          ((fun p : (Fin n → Real) × Real =>
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
                (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                  (fun _ : Fin 1 => p.2))) ''
            epigraph (S := (Set.univ : Set (Fin n → Real))) f) =
          (appendAffineEquiv n 1).toHomeomorphOfFiniteDimensional ⁻¹' (closure C_f) := hpre_f
      _ =
          (appendAffineEquiv n 1).toHomeomorphOfFiniteDimensional ⁻¹' (closure C_g) := by
            exact
              congrArg
                (fun s => (appendAffineEquiv n 1).toHomeomorphOfFiniteDimensional ⁻¹' s) hcl'
      _ =
          closure
            ((fun p : (Fin n → Real) × Real =>
                ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
                  (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                    (fun _ : Fin 1 => p.2))) ''
              epigraph (S := (Set.univ : Set (Fin n → Real))) g) := by
        symm
        exact hpre_g
  have hcl_g :
      closure (g_aff '' epigraph (S := (Set.univ : Set (Fin n → Real))) f) =
        closure (g_aff '' epigraph (S := (Set.univ : Set (Fin n → Real))) g) := by
    simpa [hphi_f, hphi_g] using hcl_inner
  have hpre_gf :
      closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) =
        g_aff.toHomeomorphOfFiniteDimensional ⁻¹'
          (closure (g_aff '' epigraph (S := (Set.univ : Set (Fin n → Real))) f)) := by
    simpa [Set.preimage_image_eq, g_aff.injective] using
      (Homeomorph.preimage_closure
          (h := g_aff.toHomeomorphOfFiniteDimensional)
          (s := g_aff '' epigraph (S := (Set.univ : Set (Fin n → Real))) f)).symm
  have hpre_gg :
      closure (epigraph (S := (Set.univ : Set (Fin n → Real))) g) =
        g_aff.toHomeomorphOfFiniteDimensional ⁻¹'
          (closure (g_aff '' epigraph (S := (Set.univ : Set (Fin n → Real))) g)) := by
    simpa [Set.preimage_image_eq, g_aff.injective] using
      (Homeomorph.preimage_closure
          (h := g_aff.toHomeomorphOfFiniteDimensional)
          (s := g_aff '' epigraph (S := (Set.univ : Set (Fin n → Real))) g)).symm
  calc
    closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) =
        g_aff.toHomeomorphOfFiniteDimensional ⁻¹'
          (closure (g_aff '' epigraph (S := (Set.univ : Set (Fin n → Real))) f)) := hpre_gf
    _ =
        g_aff.toHomeomorphOfFiniteDimensional ⁻¹'
          (closure (g_aff '' epigraph (S := (Set.univ : Set (Fin n → Real))) g)) := by
        simp [hcl_g]
    _ =
        closure (epigraph (S := (Set.univ : Set (Fin n → Real))) g) := by
        symm
        exact hpre_gg

/-- Equality of epigraph closures yields equality of convex closures. -/
lemma convexFunctionClosure_eq_of_epigraph_closure_eq {n : Nat}
    {f g : (Fin n → Real) → EReal} (hbf : ∀ x, f x ≠ (⊥ : EReal))
    (hbg : ∀ x, g x ≠ (⊥ : EReal))
    (hcl :
      closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) =
        closure (epigraph (S := (Set.univ : Set (Fin n → Real))) g)) :
    convexFunctionClosure f = convexFunctionClosure g := by
  classical
  have h_epi_f :=
    (epigraph_convexFunctionClosure_eq_closure_epigraph (f := f) hbf).1
  have h_epi_g :=
    (epigraph_convexFunctionClosure_eq_closure_epigraph (f := g) hbg).1
  have h_epi :
      epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f) =
        epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure g) := by
    calc
      epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f) =
          closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := h_epi_f
      _ = closure (epigraph (S := (Set.univ : Set (Fin n → Real))) g) := hcl
      _ =
          epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure g) := by
            symm
            exact h_epi_g
  funext x
  have hle_iff :
      ∀ μ : Real,
        convexFunctionClosure f x ≤ (μ : EReal) ↔
          convexFunctionClosure g x ≤ (μ : EReal) := by
    intro μ
    have hmem :
        (x, μ) ∈
            epigraph (S := (Set.univ : Set (Fin n → Real)))
              (convexFunctionClosure f) ↔
          (x, μ) ∈
            epigraph (S := (Set.univ : Set (Fin n → Real)))
              (convexFunctionClosure g) := by
      constructor
      · intro hx
        simpa [h_epi] using hx
      · intro hx
        simpa [h_epi] using hx
    simpa [mem_epigraph_univ_iff] using hmem
  cases hfx : convexFunctionClosure f x using EReal.rec with
  | bot =>
      have hforall : ∀ μ : Real, convexFunctionClosure g x ≤ (μ : EReal) := by
        intro μ
        have hle :
            convexFunctionClosure f x ≤ (μ : EReal) := by
          simp [hfx]
        exact (hle_iff μ).1 hle
      have hbot : convexFunctionClosure g x = (⊥ : EReal) := by
        by_contra hne
        rcases exists_real_not_le_of_ne_bot (x := convexFunctionClosure g x) hne with ⟨α, hα⟩
        exact hα (hforall α)
      simp [hbot]
  | top =>
      cases hgx : convexFunctionClosure g x using EReal.rec with
      | bot =>
          have h := (hle_iff 0).2 (by simp [hgx])
          have : False := by
            simp [hfx] at h
          exact (False.elim this)
      | top =>
          simp
      | coe r =>
          have h := (hle_iff r).2 (by simp [hgx])
          have : False := by
            simp [hfx] at h
          exact (False.elim this)
  | coe r =>
      cases hgx : convexFunctionClosure g x using EReal.rec with
      | bot =>
          have h := (hle_iff (r - 1)).2 (by simp [hgx])
          have hle' : (r : EReal) ≤ (r - 1 : EReal) := by
            simpa [hfx] using h
          have hle : (r : Real) ≤ r - 1 := (EReal.coe_le_coe_iff).1 hle'
          have : False := by linarith
          exact (False.elim this)
      | top =>
          have hle_f : convexFunctionClosure f x ≤ (r : EReal) := by
            simp [hfx]
          have h := (hle_iff r).1 hle_f
          have : False := by
            simp [hgx] at h
          exact (False.elim this)
      | coe s =>
          have hf_le_s :
              convexFunctionClosure f x ≤ (s : EReal) :=
            (hle_iff s).2 (by simp [hgx])
          have hr_le_s : r ≤ s := by
            simp [hfx, EReal.coe_le_coe_iff] at hf_le_s
            exact hf_le_s
          have hf_le_r :
              convexFunctionClosure f x ≤ (r : EReal) := by
            simp [hfx]
          have hg_le_r :=
            (hle_iff r).1 hf_le_r
          have hs_le_r : s ≤ r := by
            simp [hgx, EReal.coe_le_coe_iff] at hg_le_r
            exact hg_le_r
          have hsr : (s : Real) = r := le_antisymm hs_le_r hr_le_s
          simp [hsr]

/-- Corollary 7.3.4. If `f` and `g` are convex functions on `ℝ^n` such that
`ri (dom f) = ri (dom g)`, and `f` and `g` agree on the latter set, then
`cl f = cl g`. -/
theorem convexFunctionClosure_eq_of_agree_on_ri_effectiveDomain {n : Nat}
    {f g : (Fin n → Real) → EReal}
    (hf : ConvexFunction f) (hg : ConvexFunction g)
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
    convexFunctionClosure f = convexFunctionClosure g := by
  classical
  have hri_epi :=
    riEpigraph_eq_of_agree_on_ri_effectiveDomain (n := n) (f := f) (g := g) hf hg hri hagree
  have hcl_embedded :=
    closure_embedded_epigraph_eq_of_riEpigraph_eq (n := n) (f := f) (g := g) hf hg hri_epi
  have hcl_epi :
      closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) =
        closure (epigraph (S := (Set.univ : Set (Fin n → Real))) g) :=
    closure_epigraph_eq_of_embedded_closure_eq (n := n) (f := f) (g := g) hcl_embedded
  by_cases hbot : ∃ x, f x = (⊥ : EReal)
  · have hbot_ri :=
      exists_bot_on_ri_effectiveDomain_of_exists_bot (n := n) (f := f) hf hbot
    rcases hbot_ri with ⟨y, hyri, hybot⟩
    have hbot_g : ∃ x, g x = (⊥ : EReal) := by
      refine ⟨y, ?_⟩
      have hfg : f y = g y := hagree y hyri
      simpa [hfg] using hybot
    have hcl_f :
        convexFunctionClosure f = (fun _ => (⊥ : EReal)) :=
      convexFunctionClosure_eq_bot_of_exists_bot (f := f) hbot
    have hcl_g :
        convexFunctionClosure g = (fun _ => (⊥ : EReal)) :=
      convexFunctionClosure_eq_bot_of_exists_bot (f := g) hbot_g
    simp [hcl_f, hcl_g]
  · have hbf : ∀ x, f x ≠ (⊥ : EReal) := by
      intro x hx
      exact hbot ⟨x, hx⟩
    have hbg : ∀ x, g x ≠ (⊥ : EReal) := by
      intro x hx
      have hbot_g : ∃ x, g x = (⊥ : EReal) := ⟨x, hx⟩
      rcases
          exists_bot_on_ri_effectiveDomain_of_exists_bot (n := n) (f := g) hg hbot_g with
        ⟨y, hyri, hybot⟩
      have hyri_f :
          y ∈
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
        simpa [hri.symm] using hyri
      have hfg : f y = g y := hagree y hyri_f
      exact hbot ⟨y, by simpa [hfg] using hybot⟩
    exact
      convexFunctionClosure_eq_of_epigraph_closure_eq (n := n) (f := f) (g := g)
        hbf hbg hcl_epi

/- Theorem 7.4. Let `f` be a proper convex function on `ℝ^n`. Then `cl f` is a closed
proper convex function. Moreover, `cl f` agrees with `f` except perhaps at relative
boundary points of `dom f`. -/
/-- A point of `ri (dom f)` lifts to a point of `ri (epi f)` on the vertical line. -/
lemma exists_riEpigraph_point_on_vertical_line {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {x : EuclideanSpace Real (Fin n)}
    (hx :
      x ∈
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    ∃ μ : Real,
      appendAffineEquiv n 1
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real),
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => μ)) ∈ riEpigraph f := by
  classical
  have hconv : ConvexFunction f := by
    simpa [ConvexFunction] using hf.1
  have hx_pre :
      x ∈
        (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f :=
    (euclideanRelativeInterior_subset_closure n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f)).1 hx
  have hx_eff :
      (x : Fin n → Real) ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
    simpa using hx_pre
  have hx_lt_top : f (x : Fin n → Real) < (⊤ : EReal) := by
    have hx' :
        (x : Fin n → Real) ∈
          {x | x ∈ (Set.univ : Set (Fin n → Real)) ∧ f x < (⊤ : EReal)} := by
      simpa [effectiveDomain_eq] using hx_eff
    exact hx'.2
  have hx_ne_bot : f (x : Fin n → Real) ≠ (⊥ : EReal) :=
    hf.2.2 _ (by simp)
  have hx_real : ∃ r : Real, f (x : Fin n → Real) = (r : EReal) := by
    cases hfx : f (x : Fin n → Real) using EReal.rec with
    | bot =>
        exact (False.elim (hx_ne_bot (by simp [hfx])))
    | top =>
        exfalso
        simp [hfx] at hx_lt_top
    | coe r =>
        exact ⟨r, rfl⟩
  rcases hx_real with ⟨r, hfx⟩
  refine ⟨r + 1, ?_⟩
  have hlt : f (x : Fin n → Real) < ((r + 1) : EReal) := by
    have : (r : EReal) < (r + 1 : EReal) := by
      exact (EReal.coe_lt_coe_iff).2 (by linarith)
    simpa [hfx] using this
  have hri :
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x : Fin n → Real) ∈
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
    simpa using hx
  exact
    (riEpigraph_mem_iff (n := n) (f := f) hconv (x : Fin n → Real) (r + 1)).2
      ⟨hri, hlt, riEpigraph_mu_lt_top (r + 1)⟩

/-- The vertical section of the embedded epigraph is the inequality in the last coordinate. -/
lemma embedded_epigraph_section_mem_iff {n : Nat} {f : (Fin n → Real) → EReal}
    (x : Fin n → Real) :
    let C : Set (EuclideanSpace Real (Fin (n + 1))) :=
      (appendAffineEquiv n 1) ''
        ((fun p : (Fin n → Real) × Real =>
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => p.2))) ''
          epigraph (S := (Set.univ : Set (Fin n → Real))) f)
    let y : EuclideanSpace Real (Fin n) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x
    let Cy : EuclideanSpace Real (Fin n) → Set (EuclideanSpace Real (Fin 1)) :=
      fun y => {z | appendAffineEquiv n 1 (y, z) ∈ C}
    let coords1 := EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)
    let first1 : EuclideanSpace Real (Fin 1) → Real := fun z => coords1 z 0
    ∀ z, z ∈ Cy y ↔ f x ≤ (first1 z : EReal) := by
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
  set Cy : EuclideanSpace Real (Fin n) → Set (EuclideanSpace Real (Fin 1)) :=
    fun y => {z | appendAffineEquiv n 1 (y, z) ∈ C} with hCy
  let coords1 := EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)
  let first1 : EuclideanSpace Real (Fin 1) → Real := fun z => coords1 z 0
  intro z
  have hz_eq :
      z =
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
          (fun _ : Fin 1 => first1 z) := by
    ext i
    fin_cases i
    simp [first1, coords1]
  have hmem :
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
            (fun _ : Fin 1 => first1 z) ∈ Cy y ↔
        f x ≤ (first1 z : EReal) :=
    (riEpigraph_section_mem_iff (x := x) (μ := first1 z))
  constructor
  · intro hz
    have hz' := hz
    rw [hz_eq] at hz'
    exact hmem.1 hz'
  · intro hz
    have hz' := hmem.2 hz
    rw [hz_eq]
    exact hz'

set_option maxHeartbeats 400000 in
-- needed for the closure/affine equivalence argument below
/-- On the relative interior of the effective domain, `cl f` agrees with `f`. -/
lemma convexFunctionClosure_eq_on_ri {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    ∀ x ∈
      euclideanRelativeInterior n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f),
      convexFunctionClosure f x = f x := by
  classical
  intro x hx
  have hconv : ConvexFunction f := by
    simpa [ConvexFunction] using hf.1
  set C : Set (EuclideanSpace Real (Fin (n + 1))) :=
    (appendAffineEquiv n 1) ''
      ((fun p : (Fin n → Real) × Real =>
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => p.2))) ''
        epigraph (S := (Set.univ : Set (Fin n → Real))) f) with hC
  set y : EuclideanSpace Real (Fin n) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x with hy
  let coords1 := EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)
  let first1 : EuclideanSpace Real (Fin 1) → Real := fun z => coords1 z 0
  let Cy : EuclideanSpace Real (Fin n) → Set (EuclideanSpace Real (Fin 1)) :=
    fun y => {z | appendAffineEquiv n 1 (y, z) ∈ C}
  let P : EuclideanSpace Real (Fin (n + 1)) →ₗ[Real] EuclideanSpace Real (Fin n) :=
    (LinearMap.fst (R := Real) (M := EuclideanSpace Real (Fin n))
        (M₂ := EuclideanSpace Real (Fin 1))).comp
      (appendAffineEquiv n 1).symm.linear.toLinearMap
  let M : AffineSubspace Real (EuclideanSpace Real (Fin (n + 1))) :=
    AffineSubspace.mk' (appendAffineEquiv n 1 (y, 0)) (LinearMap.ker P)
  have hM_eq :
      (M : Set _) = {w | P w = y} ∧
        (M : Set _) ∩ C = (fun z => appendAffineEquiv n 1 (y, z)) '' (Cy y) := by
    simpa [C, y, Cy, P, M] using
      (section_fiber_affineSubspace_eq (m := n) (p := 1) (C := C) (y := y))
  have hconv_C : Convex ℝ C := by
    simpa [C] using (convex_embedded_epigraph (n := n) (f := f) hconv)
  rcases
      exists_riEpigraph_point_on_vertical_line (n := n) (f := f) hf
        (x := x) hx with
    ⟨μ0, hri0⟩
  set z0 : EuclideanSpace Real (Fin 1) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => μ0) with hz0
  set p0 : EuclideanSpace Real (Fin (n + 1)) := appendAffineEquiv n 1 (y, z0) with hp0
  have hp0_ri : p0 ∈ euclideanRelativeInterior (n + 1) C := by
    simpa [riEpigraph, C, y, z0, p0] using hri0
  have hp0C : p0 ∈ C :=
    (euclideanRelativeInterior_subset_closure (n + 1) C).1 hp0_ri
  have hz0Cy : z0 ∈ Cy y := by
    simpa [Cy, p0] using hp0C
  have hp0MC : p0 ∈ (M : Set _) ∩ C := by
    have hMC : (M : Set _) ∩ C = (fun z => appendAffineEquiv n 1 (y, z)) '' (Cy y) :=
      hM_eq.2
    have : p0 ∈ (fun z => appendAffineEquiv n 1 (y, z)) '' (Cy y) :=
      ⟨z0, hz0Cy, rfl⟩
    simpa [hMC, p0] using this
  have hp0M : p0 ∈ (M : Set _) := hp0MC.1
  have hM_nonempty :
      ((M : Set _) ∩ euclideanRelativeInterior (n + 1) C).Nonempty :=
    ⟨p0, ⟨hp0M, hp0_ri⟩⟩
  have hcl_eq :
      closure ((M : Set _) ∩ C) = (M : Set _) ∩ closure C :=
    (euclideanRelativeInterior_inter_affineSubspace_eq_and_closure_eq
        (n := n + 1) (C := C) hconv_C M hM_nonempty).2
  have hx_pre :
      x ∈
        (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f :=
    (euclideanRelativeInterior_subset_closure n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f)).1 hx
  have hx_eff :
      (x : Fin n → Real) ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
    simpa using hx_pre
  have hx_lt_top : f (x : Fin n → Real) < (⊤ : EReal) := by
    have hx' :
        (x : Fin n → Real) ∈
          {x | x ∈ (Set.univ : Set (Fin n → Real)) ∧ f x < (⊤ : EReal)} := by
      simpa [effectiveDomain_eq] using hx_eff
    exact hx'.2
  have hx_ne_bot : f (x : Fin n → Real) ≠ (⊥ : EReal) :=
    hf.2.2 _ (by simp)
  have hx_real : ∃ r : Real, f (x : Fin n → Real) = (r : EReal) := by
    cases hfx : f (x : Fin n → Real) using EReal.rec with
    | bot =>
        exact (False.elim (hx_ne_bot (by simp [hfx])))
    | top =>
        exfalso
        simp [hfx] at hx_lt_top
    | coe r =>
        exact ⟨r, rfl⟩
  rcases hx_real with ⟨r, hfx⟩
  have hCy_mem :
      ∀ z, z ∈ Cy y ↔ f (x : Fin n → Real) ≤ (first1 z : EReal) := by
    simpa [C, y, Cy, first1] using
      (embedded_epigraph_section_mem_iff (n := n) (f := f) (x : Fin n → Real))
  have hCy_eq : Cy y = {z | r ≤ first1 z} := by
    ext z
    have h := hCy_mem z
    simpa [hfx, EReal.coe_le_coe_iff] using h
  have hcont_first1 : Continuous first1 := by
    simpa [first1] using
      (continuous_apply 0).comp
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).continuous
  have hCy_closed : IsClosed (Cy y) := by
    have hclosed : IsClosed (first1 ⁻¹' Set.Ici r) :=
      (isClosed_Ici.preimage hcont_first1)
    simpa [hCy_eq] using hclosed
  let φ : EuclideanSpace Real (Fin (n + 1)) → Real :=
    fun w => first1 ((appendAffineEquiv n 1).linear.symm w).2
  have hcont_phi : Continuous φ := by
    have hcont_symm :
        Continuous (fun w : EuclideanSpace Real (Fin (n + 1)) =>
          (appendAffineEquiv n 1).linear.symm w) := by
      simpa using
        (appendAffineEquiv n 1).linear.symm.toContinuousLinearEquiv.continuous
    have hcont_snd :
        Continuous (fun w : EuclideanSpace Real (Fin (n + 1)) =>
          ((appendAffineEquiv n 1).linear.symm w).2) := by
      simpa using (continuous_snd.comp hcont_symm)
    exact hcont_first1.comp hcont_snd
  have hMC_eq' :
      (M : Set _) ∩ C = {w | w ∈ (M : Set _) ∧ f (x : Fin n → Real) ≤ (φ w : EReal)} := by
    ext w; constructor
    · rintro ⟨hwM, hwC⟩
      have hwM' : w ∈ {w | P w = y} := by
        simpa [hM_eq.1] using hwM
      have hwP : P w = y := by
        simpa [Set.mem_setOf_eq] using hwM'
      set z : EuclideanSpace Real (Fin 1) := ((appendAffineEquiv n 1).linear.symm w).2 with hz
      have hwP' : ((appendAffineEquiv n 1).linear.symm w).1 = y := by
        simpa [P] using hwP
      have hpair : (appendAffineEquiv n 1).linear.symm w = (y, z) := by
        ext <;> simp [hwP', hz]
      have hw_eq_linear : w = (appendAffineEquiv n 1).linear (y, z) := by
        have := congrArg (fun v => (appendAffineEquiv n 1).linear v) hpair
        simpa using this
      have hw_eq : w = appendAffineEquiv n 1 (y, z) := by
        have happ :
            (appendAffineEquiv n 1).linear (y, z) = appendAffineEquiv n 1 (y, z) := by
          have h :=
            congrArg (fun f => f (y, z)) (appendAffineEquiv_eq_linear_toAffineEquiv n 1)
          simpa using h.symm
        calc
          w = (appendAffineEquiv n 1).linear (y, z) := hw_eq_linear
          _ = appendAffineEquiv n 1 (y, z) := happ
      have hzCy : z ∈ Cy y := by
        simpa [Cy, hw_eq] using hwC
      have hle : f (x : Fin n → Real) ≤ (first1 z : EReal) := (hCy_mem z).1 hzCy
      have hphi : φ w = first1 z := by
        simp [φ, hz]
      exact ⟨hwM, by simpa [hphi] using hle⟩
    · rintro ⟨hwM, hle⟩
      have hwM' : w ∈ {w | P w = y} := by
        simpa [hM_eq.1] using hwM
      have hwP : P w = y := by
        simpa [Set.mem_setOf_eq] using hwM'
      set z : EuclideanSpace Real (Fin 1) := ((appendAffineEquiv n 1).linear.symm w).2 with hz
      have hwP' : ((appendAffineEquiv n 1).linear.symm w).1 = y := by
        simpa [P] using hwP
      have hpair : (appendAffineEquiv n 1).linear.symm w = (y, z) := by
        ext <;> simp [hwP', hz]
      have hw_eq_linear : w = (appendAffineEquiv n 1).linear (y, z) := by
        have := congrArg (fun v => (appendAffineEquiv n 1).linear v) hpair
        simpa using this
      have hw_eq : w = appendAffineEquiv n 1 (y, z) := by
        have happ :
            (appendAffineEquiv n 1).linear (y, z) = appendAffineEquiv n 1 (y, z) := by
          have h :=
            congrArg (fun f => f (y, z)) (appendAffineEquiv_eq_linear_toAffineEquiv n 1)
          simpa using h.symm
        calc
          w = (appendAffineEquiv n 1).linear (y, z) := hw_eq_linear
          _ = appendAffineEquiv n 1 (y, z) := happ
      have hphi : φ w = first1 z := by
        simp [φ, hz]
      have hzCy : z ∈ Cy y := (hCy_mem z).2 (by simpa [hphi] using hle)
      have hwC : w ∈ C := by
        simpa [Cy, hw_eq] using hzCy
      exact ⟨hwM, hwC⟩
  have hMC_closed : IsClosed ((M : Set _) ∩ C) := by
    have hM_closed :
        IsClosed (M : Set (EuclideanSpace Real (Fin (n + 1)))) := by
      simpa using (affineSubspace_isClosed (n + 1) M)
    have hpre : IsClosed {w | f (x : Fin n → Real) ≤ (φ w : EReal)} := by
      have hpre' : IsClosed (φ ⁻¹' Set.Ici r) :=
        (isClosed_Ici.preimage hcont_phi)
      have hpre'' : {w | f (x : Fin n → Real) ≤ (φ w : EReal)} = φ ⁻¹' Set.Ici r := by
        ext w
        simp [hfx, EReal.coe_le_coe_iff, Set.mem_setOf_eq]
      simpa [hpre''] using hpre'
    have hpre'' :
        {w | w ∈ (M : Set _) ∧ f (x : Fin n → Real) ≤ (φ w : EReal)} =
          (M : Set _) ∩ {w | f (x : Fin n → Real) ≤ (φ w : EReal)} := by
        ext w; constructor <;> intro hw <;> exact hw
    have hclosed' :
        IsClosed {w | w ∈ (M : Set _) ∧ f (x : Fin n → Real) ≤ (φ w : EReal)} := by
      simpa [hpre''] using hM_closed.inter hpre
    simpa [hMC_eq'] using hclosed'
  have hMC_eq :
      (M : Set _) ∩ closure C = (M : Set _) ∩ C := by
    have hcl' : closure ((M : Set _) ∩ C) = (M : Set _) ∩ C := hMC_closed.closure_eq
    calc
      (M : Set _) ∩ closure C = closure ((M : Set _) ∩ C) := by
        symm
        exact hcl_eq
      _ = (M : Set _) ∩ C := hcl'
  have hle_iff :
      ∀ μ : Real,
        convexFunctionClosure f (x : Fin n → Real) ≤ (μ : EReal) ↔
          f (x : Fin n → Real) ≤ (μ : EReal) := by
    intro μ
    set z : EuclideanSpace Real (Fin 1) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => μ) with hz
    set p : EuclideanSpace Real (Fin (n + 1)) := appendAffineEquiv n 1 (y, z) with hp
    have hpM : p ∈ (M : Set _) := by
      have hproj :
          let e := appendAffineEquiv n 1
          let P' : EuclideanSpace Real (Fin (n + 1)) →ₗ[Real] EuclideanSpace Real (Fin n) :=
            (LinearMap.fst (R := Real) (M := EuclideanSpace Real (Fin n))
                (M₂ := EuclideanSpace Real (Fin 1))).comp e.symm.linear.toLinearMap
          let Cy' : EuclideanSpace Real (Fin n) → Set (EuclideanSpace Real (Fin 1)) :=
            fun y => {z | e (y, z) ∈ C}
          let D : Set (EuclideanSpace Real (Fin n)) := {y | (Cy' y).Nonempty}
          P' (e (y, z)) = y := by
        simpa [C] using
          (section_D_eq_image_projection (m := n) (p := 1) (C := C) (y := y) (z := z)).2
      have hproj' : P p = y := by
        simpa [p, P] using hproj
      have hpM' : p ∈ {w | P w = y} := by
        simpa [Set.mem_setOf_eq] using hproj'
      simpa [hM_eq.1] using hpM'
    have hp_closure :
        p ∈ closure C ↔ p ∈ C := by
      have hpM' : p ∈ (M : Set _) := hpM
      have hpM_cl :
          p ∈ (M : Set _) ∩ closure C ↔ p ∈ (M : Set _) ∩ C := by
        simpa [hpM'] using congrArg (fun s => p ∈ s) hMC_eq
      constructor
      · intro hpC
        have : p ∈ (M : Set _) ∩ closure C := ⟨hpM, hpC⟩
        have : p ∈ (M : Set _) ∩ C := (hpM_cl).1 this
        exact this.2
      · intro hpC
        have : p ∈ (M : Set _) ∩ C := ⟨hpM, hpC⟩
        have : p ∈ (M : Set _) ∩ closure C := (hpM_cl).2 this
        exact this.2
    have hmem :
        ((x : Fin n → Real), μ) ∈
            epigraph (S := (Set.univ : Set (Fin n → Real)))
              (convexFunctionClosure f) ↔
          ((x : Fin n → Real), μ) ∈
            epigraph (S := (Set.univ : Set (Fin n → Real))) f := by
      have hbot : ∀ x, f x ≠ (⊥ : EReal) := by
        intro x
        exact hf.2.2 x (by simp)
      have h_epi :
          epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f) =
            closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) :=
        (epigraph_convexFunctionClosure_eq_closure_epigraph (f := f) hbot).1
      have hmem' :
          ((x : Fin n → Real), μ) ∈
              closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) ↔
            ((x : Fin n → Real), μ) ∈ epigraph (S := (Set.univ : Set (Fin n → Real))) f := by
        -- translate to the embedded epigraph
        have hCmem :
            ((x : Fin n → Real), μ) ∈
                epigraph (S := (Set.univ : Set (Fin n → Real))) f ↔
              p ∈ C := by
          have hle :
              ((x : Fin n → Real), μ) ∈
                  epigraph (S := (Set.univ : Set (Fin n → Real))) f ↔
                f (x : Fin n → Real) ≤ (μ : EReal) := by
            simp [mem_epigraph_univ_iff]
          have hle' :
              f (x : Fin n → Real) ≤ (μ : EReal) ↔ p ∈ C := by
            have hzCy : z ∈ Cy y ↔ f (x : Fin n → Real) ≤ (μ : EReal) := by
              have h' := hCy_mem z
              simpa [hz, first1, coords1] using h'
            constructor
            · intro hle
              have hz' : z ∈ Cy y := (hzCy).2 hle
              simpa [Cy, p] using hz'
            · intro hpC
              have hz' : z ∈ Cy y := by
                simpa [Cy, p] using hpC
              exact (hzCy).1 hz'
          constructor
          · intro hmem
            exact (hle'.1 (hle.1 hmem))
          · intro hpC
            exact (hle.2 (hle'.2 hpC))
        have hCmem_cl :
            ((x : Fin n → Real), μ) ∈
                closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) ↔
              p ∈ closure C := by
          -- use the product affine equivalence to compare closure membership
          let eN : (Fin n → Real) ≃ᵃ[Real] EuclideanSpace Real (Fin n) :=
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm.toLinearEquiv.toAffineEquiv
          let e1CL : (Fin 1 → Real) ≃L[Real] Real :=
            ContinuousLinearEquiv.funUnique (ι := Fin 1) (R := Real) (M := Real)
          let e1L : Real ≃ₗ[Real] EuclideanSpace Real (Fin 1) :=
            LinearEquiv.trans e1CL.symm.toLinearEquiv
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm.toLinearEquiv)
          let e1 : Real ≃ᵃ[Real] EuclideanSpace Real (Fin 1) := e1L.toAffineEquiv
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
            · rintro ⟨p', hp', rfl⟩
              refine ⟨p', hp', ?_⟩
              simp [g_aff, eN, e1]
              rfl
            · rintro ⟨p', hp', rfl⟩
              refine ⟨p', hp', ?_⟩
              simp [g_aff, eN, e1]
              rfl
          have hpre :
              closure C =
                (appendAffineEquiv n 1) '' closure
                  ((fun p : (Fin n → Real) × Real =>
                      ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
                        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                          (fun _ : Fin 1 => p.2))) ''
                    epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
            have hpre' :
                closure
                    ((fun p : (Fin n → Real) × Real =>
                        ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
                          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                            (fun _ : Fin 1 => p.2))) ''
                      epigraph (S := (Set.univ : Set (Fin n → Real))) f) =
                  (appendAffineEquiv n 1).toHomeomorphOfFiniteDimensional ⁻¹' (closure C) := by
              simpa [C, Set.preimage_image_eq, (appendAffineEquiv n 1).injective] using
                (Homeomorph.preimage_closure
                    (h := (appendAffineEquiv n 1).toHomeomorphOfFiniteDimensional)
                    (s := C)).symm
            have hpre'' :
                closure C =
                  (appendAffineEquiv n 1) ''
                    ((appendAffineEquiv n 1).toHomeomorphOfFiniteDimensional ⁻¹' (closure C)) := by
              symm
              refine Set.image_preimage_eq_of_subset ?_
              intro w hw
              rcases (appendAffineEquiv n 1).surjective w with ⟨v, rfl⟩
              exact ⟨v, rfl⟩
            calc
              closure C =
                  (appendAffineEquiv n 1) ''
                    ((appendAffineEquiv n 1).toHomeomorphOfFiniteDimensional ⁻¹'
                      (closure C)) := hpre''
              _ =
                  (appendAffineEquiv n 1) '' closure
                    ((fun p : (Fin n → Real) × Real =>
                        ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
                          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                            (fun _ : Fin 1 => p.2))) ''
                      epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
                exact congrArg (fun s => (appendAffineEquiv n 1) '' s) hpre'.symm
          have hpre' :
              closure C =
                (appendAffineEquiv n 1) '' closure
                  (g_aff '' epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
            simpa [hphi] using hpre
          have hp_mem :
              p ∈ closure C ↔
                (y, z) ∈
                  closure (g_aff '' epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
            constructor
            · intro hpC
              have hpC' :
                  p ∈ (appendAffineEquiv n 1) '' closure
                      (g_aff '' epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
                simpa [hpre'] using hpC
              rcases hpC' with ⟨q, hq, hqeq⟩
              have : q = (y, z) := by
                apply (appendAffineEquiv n 1).injective
                simpa [p] using hqeq
              simpa [this] using hq
            · intro hyz
              have :
                  p ∈ (appendAffineEquiv n 1) '' closure
                      (g_aff '' epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
                exact ⟨(y, z), hyz, by simp [p]⟩
              simpa [hpre'] using this
          have hpre_g :
              g_aff.toHomeomorphOfFiniteDimensional ⁻¹'
                  closure (g_aff '' epigraph (S := (Set.univ : Set (Fin n → Real))) f) =
                closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
            simpa [Set.preimage_image_eq, g_aff.injective] using
              (Homeomorph.preimage_closure
                  (h := g_aff.toHomeomorphOfFiniteDimensional)
                  (s := g_aff '' epigraph (S := (Set.univ : Set (Fin n → Real))) f))
          have hmem_g :
              (y, z) ∈
                  closure (g_aff '' epigraph (S := (Set.univ : Set (Fin n → Real))) f) ↔
                ((x : Fin n → Real), μ) ∈
                  closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
            have hg : g_aff.symm (y, z) = ((x : Fin n → Real), μ) := by
              have hg1 : (g_aff.symm (y, z)).1 = (x : Fin n → Real) := by
                change eN.symm y = (x : Fin n → Real)
                simpa [eN, y] using
                  (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).apply_symm_apply
                    (x : Fin n → Real)
              have hg2 : (g_aff.symm (y, z)).2 = μ := by
                change e1.symm z = μ
                let L : Real ≃ₗ[Real] EuclideanSpace Real (Fin 1) := e1L
                have hzL : L μ = z := by
                  ext i
                  fin_cases i
                  simp [L, e1L, e1CL, z]
                have hL : L.symm z = μ := by
                  simpa [hzL] using (L.symm_apply_apply μ)
                simpa [e1, L] using hL
              exact Prod.ext hg1 hg2
            have :
                (y, z) ∈
                    closure (g_aff '' epigraph (S := (Set.univ : Set (Fin n → Real))) f) ↔
                  g_aff.symm (y, z) ∈
                    closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
              constructor
              · intro hyz
                have hyz' :
                    g_aff.symm (y, z) ∈
                      g_aff.toHomeomorphOfFiniteDimensional ⁻¹'
                        closure (g_aff '' epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
                  change
                    g_aff.toHomeomorphOfFiniteDimensional (g_aff.symm (y, z)) ∈
                      closure (g_aff '' epigraph (S := (Set.univ : Set (Fin n → Real))) f)
                  simpa using hyz
                have hyz'' := hyz'
                rw [hpre_g] at hyz''
                exact hyz''
              · intro hyz
                have hyz' := hyz
                rw [← hpre_g] at hyz'
                simpa using hyz'
            simpa [hg] using this
          exact (hp_mem.trans hmem_g).symm
        constructor
        · intro hcl
          have hpC : p ∈ closure C := (hCmem_cl).1 hcl
          have hpC' : p ∈ C := (hp_closure).1 hpC
          exact (hCmem).2 hpC'
        · intro hmem
          have hpC : p ∈ C := (hCmem).1 hmem
          have hpC' : p ∈ closure C := (hp_closure).2 hpC
          exact (hCmem_cl).2 hpC'
      constructor
      · intro hmemC
        have hcl :
            ((x : Fin n → Real), μ) ∈
              closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
          simpa [h_epi] using hmemC
        exact (hmem').1 hcl
      · intro hmemC
        have hcl :
            ((x : Fin n → Real), μ) ∈
              closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f) :=
          (hmem').2 hmemC
        simpa [h_epi] using hcl
    simpa [mem_epigraph_univ_iff] using hmem
  cases hfx' : f (x : Fin n → Real) using EReal.rec with
  | bot =>
      exact (hx_ne_bot (by simp [hfx'])).elim
  | top =>
      exfalso
      simp [hfx'] at hx_lt_top
  | coe r =>
      cases hcx : convexFunctionClosure f (x : Fin n → Real) using EReal.rec with
      | bot =>
          have hforall : ∀ μ : Real, f (x : Fin n → Real) ≤ (μ : EReal) := by
            intro μ
            have hle :
                convexFunctionClosure f (x : Fin n → Real) ≤ (μ : EReal) := by
              simp [hcx]
            exact (hle_iff μ).1 hle
          have hbot : f (x : Fin n → Real) = (⊥ : EReal) := by
            by_contra hne
            rcases exists_real_not_le_of_ne_bot (x := f (x : Fin n → Real)) hne with ⟨α, hα⟩
            exact hα (hforall α)
          simp [hbot] at hfx'
      | top =>
          have h := (hle_iff r).2 (by simp [hfx'])
          have : False := by
            simp [hcx] at h
          exact (False.elim this)
      | coe s =>
          have hle_s :
              convexFunctionClosure f (x : Fin n → Real) ≤ (s : EReal) := by
            simp [hcx]
          have hle_s' := (hle_iff s).1 hle_s
          have hle_rs : (r : Real) ≤ s := by
            simpa [hfx', EReal.coe_le_coe_iff] using hle_s'
          have hle_r :
              convexFunctionClosure f (x : Fin n → Real) ≤ (r : EReal) := by
            have h := (hle_iff r).2 (by simp [hfx'])
            exact h
          have hle_sr :
              s ≤ r := by
            simpa [hcx, EReal.coe_le_coe_iff] using hle_r
          have hsr : (s : Real) = r := le_antisymm hle_sr hle_rs
          simp [hsr]

end Section07
end Chap02
