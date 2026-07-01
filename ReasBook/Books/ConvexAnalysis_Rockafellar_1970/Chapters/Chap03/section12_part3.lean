/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Zhiyan Wang, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section12_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section11_part4

section Chap03
section Section12

/-- Corollary 12.2.1. The conjugacy operation `f ↦ f*` (here `f* = fenchelConjugate n f`)
induces a symmetric one-to-one correspondence in the class of all closed proper convex functions
on `ℝ^n`. -/
theorem fenchelConjugate_symm_bijOn_closedProperConvex (n : Nat) :
    Set.BijOn (fun f : (Fin n → Real) → EReal => fenchelConjugate n f)
        {f :
            (Fin n → Real) → EReal |
          LowerSemicontinuous f ∧ ConvexFunction f ∧
            ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f}
        {f :
            (Fin n → Real) → EReal |
          LowerSemicontinuous f ∧ ConvexFunction f ∧
            ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f} ∧
      ∀ f : (Fin n → Real) → EReal,
        (LowerSemicontinuous f ∧ ConvexFunction f ∧
            ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) →
          fenchelConjugate n (fenchelConjugate n f) = f := by
  classical
  have hbiconj :
      ∀ f : (Fin n → Real) → EReal,
        (LowerSemicontinuous f ∧ ConvexFunction f ∧
            ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) →
          fenchelConjugate n (fenchelConjugate n f) = f := by
    intro f hf
    have h :=
      fenchelConjugate_closedConvex_proper_iff_and_biconjugate (n := n) (f := f) hf.2.1
    have hb : fenchelConjugate n (fenchelConjugate n f) = clConv n f := h.2.2.2
    have hcl : clConv n f = f :=
      clConv_eq_of_closedProperConvex (n := n) (f := f) (hf_closed := hf.1) (hf_proper := hf.2.2)
    simpa [hcl] using hb
  refine ⟨?_, hbiconj⟩
  refine ⟨?_, ?_⟩
  · intro f hf
    have h :=
      fenchelConjugate_closedConvex_proper_iff_and_biconjugate (n := n) (f := f) hf.2.1
    refine ⟨h.1.1, h.1.2, ?_⟩
    exact (h.2.1).2 hf.2.2
  · refine ⟨?_, ?_⟩
    · intro f₁ hf₁ f₂ hf₂ hEq
      have hEq' :=
        congrArg (fun g : (Fin n → Real) → EReal => fenchelConjugate n g) hEq
      simpa [hbiconj f₁ hf₁, hbiconj f₂ hf₂] using hEq'
    · intro g hg
      refine ⟨fenchelConjugate n g, ?_, ?_⟩
      · have h :=
          fenchelConjugate_closedConvex_proper_iff_and_biconjugate (n := n) (f := g) hg.2.1
        exact ⟨h.1.1, h.1.2, (h.2.1).2 hg.2.2⟩
      · simpa using (hbiconj g hg)

/-- Taking the convex-function closure does not change the Fenchel conjugate. -/
lemma fenchelConjugate_eq_of_convexFunctionClosure (n : Nat) (f : (Fin n → Real) → EReal) :
    fenchelConjugate n (convexFunctionClosure f) = fenchelConjugate n f := by
  classical
  -- Compare by real upper bounds using the affine-inequality characterization.
  funext b
  refine
    EReal.eq_of_forall_le_coe_iff (a := fenchelConjugate n (convexFunctionClosure f) b)
      (b := fenchelConjugate n f b) (fun μ => ?_)
  by_cases hnotbot : ∀ x, f x ≠ (⊥ : EReal)
  · have hcl : convexFunctionClosure f = lowerSemicontinuousHull f := by
      simp [convexFunctionClosure, hnotbot]
    have hspec :
        LowerSemicontinuous (lowerSemicontinuousHull f) ∧ lowerSemicontinuousHull f ≤ f ∧
          ∀ h : (Fin n → Real) → EReal,
            LowerSemicontinuous h → h ≤ f → h ≤ lowerSemicontinuousHull f := by
      simpa [lowerSemicontinuousHull] using
        (Classical.choose_spec (exists_lowerSemicontinuousHull (n := n) f))
    constructor
    · intro hμ
      -- `cl f ≤ f`, so an affine inequality against `cl f` transfers to `f`.
      have hAffine :
          ∀ x : Fin n → Real, ((x ⬝ᵥ b - μ : Real) : EReal) ≤ lowerSemicontinuousHull f x := by
        simpa [hcl] using
          (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := convexFunctionClosure f) (b := b)
                (μ := μ)).1 hμ
      have hle : ∀ x : Fin n → Real, ((x ⬝ᵥ b - μ : Real) : EReal) ≤ f x := by
        intro x
        exact le_trans (hAffine x) (hspec.2.1 x)
      exact (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := f) (b := b) (μ := μ)).2 hle
    · intro hμ
      -- Any affine minorant of `f` is lower semicontinuous, hence bounded above by the
      -- lower semicontinuous hull.
      have hle : ∀ x : Fin n → Real, ((x ⬝ᵥ b - μ : Real) : EReal) ≤ f x := by
        exact (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := f) (b := b) (μ := μ)).1 hμ
      have hlsc :
          LowerSemicontinuous (fun x : Fin n → Real => ((x ⬝ᵥ b - μ : Real) : EReal)) := by
        have hcont₁ : Continuous (fun x : Fin n → Real => b ⬝ᵥ x) :=
          continuous_dotProduct_const (x := b)
        have hcont₂ : Continuous (fun x : Fin n → Real => x ⬝ᵥ b) := by
          simpa [dotProduct_comm] using hcont₁
        have hcont₃ : Continuous (fun x : Fin n → Real => (x ⬝ᵥ b : Real) - μ) :=
          hcont₂.sub continuous_const
        have hcont₄ :
            Continuous (fun x : Fin n → Real => ((x ⬝ᵥ b - μ : Real) : EReal)) := by
          simpa using (EReal.continuous_coe_iff (f := fun x : Fin n → Real => (x ⬝ᵥ b : Real) - μ)).2
            hcont₃
        exact hcont₄.lowerSemicontinuous
      have hle_hull :
          ∀ x : Fin n → Real, ((x ⬝ᵥ b - μ : Real) : EReal) ≤ lowerSemicontinuousHull f x := by
        exact (hspec.2.2 _ hlsc hle)
      -- Convert back via the affine-inequality characterization.
      have hle_hull' :
          ∀ x : Fin n → Real, ((x ⬝ᵥ b - μ : Real) : EReal) ≤ convexFunctionClosure f x := by
        simpa [hcl] using hle_hull
      simpa using
        (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := convexFunctionClosure f) (b := b)
              (μ := μ)).2 hle_hull'
  · -- If `f` attains `⊥`, then `f*` is identically `⊤`, and so is `(cl f)*`.
    have hexists : ∃ x, f x = (⊥ : EReal) := by
      push_neg at hnotbot
      exact hnotbot
    have htop_f : fenchelConjugate n f b = ⊤ := by
      unfold fenchelConjugate
      rcases hexists with ⟨x0, hx0⟩
      have hmem :
          (⊤ : EReal) ∈ Set.range (fun x : Fin n → Real => ((x ⬝ᵥ b : Real) : EReal) - f x) :=
        ⟨x0, by simp [hx0]⟩
      exact top_unique (le_sSup hmem)
    have hcl : convexFunctionClosure f = fun _ : (Fin n → Real) => (⊥ : EReal) := by
      exact convexFunctionClosure_eq_bot_of_exists_bot (f := f) hexists
    have htop_cl : fenchelConjugate n (convexFunctionClosure f) b = ⊤ := by
      -- Reduce to the constant `⊥` case by exhibiting `⊤` in the range.
      unfold fenchelConjugate
      have hmem :
          (⊤ : EReal) ∈
            Set.range (fun x : Fin n → Real =>
              ((x ⬝ᵥ b : Real) : EReal) - (convexFunctionClosure f) x) :=
        ⟨0, by simp [hcl]⟩
      exact top_unique (le_sSup hmem)
    simp [htop_f, htop_cl]

/-- The effective domain of `x ↦ if x ∈ ri(dom f) then f x else ⊤` is exactly `ri(dom f)`. -/
lemma effectiveDomain_if_eq_intrinsicInterior (n : Nat) (f : (Fin n → Real) → EReal) :
    let C := effectiveDomain (Set.univ : Set (Fin n → Real)) f
    let A := intrinsicInterior ℝ C
    let g : (Fin n → Real) → EReal := fun x => by
      classical
      exact if x ∈ A then f x else ⊤
    effectiveDomain (Set.univ : Set (Fin n → Real)) g = A := by
  classical
  intro C A g
  ext x
  constructor
  · intro hx
    have hxlt : g x < (⊤ : EReal) := by
      have : x ∈ (Set.univ : Set (Fin n → Real)) ∧ g x < (⊤ : EReal) := by
        simpa [effectiveDomain_eq] using (show x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) g from hx)
      exact this.2
    by_contra hxA
    -- If `x ∉ A`, then `g x = ⊤`, contradicting `g x < ⊤`.
    simp [g, hxA] at hxlt
  · intro hxA
    -- If `x ∈ A`, then `x ∈ dom f`, hence `f x < ⊤` and so `g x < ⊤`.
    have hxC : x ∈ C := intrinsicInterior_subset (𝕜 := ℝ) (s := C) hxA
    have hxlt_f : f x < (⊤ : EReal) := by
      have : x ∈ (Set.univ : Set (Fin n → Real)) ∧ f x < (⊤ : EReal) := by
        simpa [effectiveDomain_eq] using (show x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f from hxC)
      exact this.2
    have hxlt_g : g x < (⊤ : EReal) := by
      simpa [g, hxA] using hxlt_f
    -- Use the characterization `dom g = {x | g x < ⊤}` (on `Set.univ`).
    have : x ∈ (Set.univ : Set (Fin n → Real)) ∧ g x < (⊤ : EReal) := ⟨by simp, hxlt_g⟩
    simpa [effectiveDomain_eq] using this

/-- Extending a convex function by `⊤` outside a convex set preserves convexity. -/
lemma convexFunction_if_eq_top_on_compl (n : Nat) (f : (Fin n → Real) → EReal) (hf : ConvexFunction f)
    (A : Set (Fin n → Real)) (hA : Convex ℝ A) :
    ConvexFunction (fun x : Fin n → Real => by
      classical
      exact if x ∈ A then f x else ⊤) := by
  classical
  let g : (Fin n → Real) → EReal := fun x => if x ∈ A then f x else ⊤
  change ConvexFunction g
  -- Compare epigraphs: outside `A` the inequality `⊤ ≤ μ` is impossible for real `μ`.
  unfold ConvexFunction ConvexFunctionOn at hf ⊢
  have hep :
      epigraph (Set.univ : Set (Fin n → Real)) g = epigraph A f := by
    ext p
    by_cases hp : p.1 ∈ A
    · constructor
      · intro hpE
        refine ⟨hp, ?_⟩
        simpa [epigraph, g, hp] using hpE.2
      · intro hpE
        refine ⟨Set.mem_univ p.1, ?_⟩
        simpa [epigraph, g, hp] using hpE.2
    · constructor
      · intro hpE
        have : (⊤ : EReal) ≤ (p.2 : EReal) := by
          simpa [epigraph, g, hp] using hpE.2
        exact (not_top_le_coe p.2 this).elim
      · intro hpE
        exact (hp hpE.1).elim
  -- `epigraph A f = (A ×ˢ univ) ∩ epigraph univ f` is convex.
  have hep' :
      epigraph A f =
        (Set.prod A (Set.univ : Set Real)) ∩ epigraph (Set.univ : Set (Fin n → Real)) f := by
    ext p
    constructor
    · intro hpE
      refine ⟨⟨hpE.1, Set.mem_univ p.2⟩, ?_⟩
      exact ⟨Set.mem_univ p.1, hpE.2⟩
    · rintro ⟨hpProd, hpE⟩
      exact ⟨hpProd.1, hpE.2⟩
  rw [hep, hep']
  have hprod : Convex ℝ (Set.prod A (Set.univ : Set Real)) :=
    hA.prod (convex_univ : Convex ℝ (Set.univ : Set Real))
  exact hprod.inter hf

/-- For `g(x)=f(x)` on `A` and `g(x)=⊤` outside, `g*` is the supremum over `A`. -/
lemma fenchelConjugate_if_eq_sSup_image (n : Nat) (f : (Fin n → Real) → EReal) (A : Set (Fin n → Real)) :
    ∀ xStar : Fin n → Real,
      fenchelConjugate n (fun x : Fin n → Real => by
        classical
        exact if x ∈ A then f x else ⊤) xStar =
        sSup ((fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal) - f x) '' A) := by
  intro xStar
  classical
  let g : (Fin n → Real) → EReal := fun x => if x ∈ A then f x else ⊤
  change fenchelConjugate n g xStar =
      sSup ((fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal) - f x) '' A)
  unfold fenchelConjugate
  apply le_antisymm
  · refine sSup_le ?_
    rintro y ⟨x, rfl⟩
    by_cases hx : x ∈ A
    · -- Use the corresponding element in the image over `A`.
      have hy : ((x ⬝ᵥ xStar : Real) : EReal) - f x ∈
          (fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal) - f x) '' A :=
        ⟨x, hx, rfl⟩
      simpa [g, hx] using le_sSup hy
    · -- Outside `A` the summand is `⊥`.
      simp [g, hx]
  · refine sSup_le ?_
    rintro y ⟨x, hxA, rfl⟩
    have hy :
        ((x ⬝ᵥ xStar : Real) : EReal) - g x ∈
          Set.range (fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal) - g x) :=
      ⟨x, rfl⟩
    have : ((x ⬝ᵥ xStar : Real) : EReal) - g x = ((x ⬝ᵥ xStar : Real) : EReal) - f x := by
      simp [g, hxA]
    simpa [this] using le_sSup hy

/-- Relative interior is idempotent for convex sets in Euclidean space. -/
lemma euclideanRelativeInterior_idem_of_convex (n : Nat) (C : Set (EuclideanSpace Real (Fin n)))
    (hC : Convex ℝ C) :
    euclideanRelativeInterior n (euclideanRelativeInterior n C) = euclideanRelativeInterior n C := by
  have hriCconv : Convex ℝ (euclideanRelativeInterior n C) :=
    convex_euclideanRelativeInterior n C hC
  have hcl_riC : closure (euclideanRelativeInterior n C) = closure C :=
    (euclidean_closure_relativeInterior_eq_and_relativeInterior_closure_eq n C hC).1
  have hri_closureC : euclideanRelativeInterior n (closure C) = euclideanRelativeInterior n C :=
    (euclidean_closure_relativeInterior_eq_and_relativeInterior_closure_eq n C hC).2
  have hri_closure_riC :
      euclideanRelativeInterior n (closure (euclideanRelativeInterior n C)) =
        euclideanRelativeInterior n (euclideanRelativeInterior n C) :=
    (euclidean_closure_relativeInterior_eq_and_relativeInterior_closure_eq n (euclideanRelativeInterior n C)
          hriCconv).2
  calc
    euclideanRelativeInterior n (euclideanRelativeInterior n C)
        = euclideanRelativeInterior n (closure (euclideanRelativeInterior n C)) := by
            simpa using hri_closure_riC.symm
    _ = euclideanRelativeInterior n (closure C) := by simp [hcl_riC]
    _ = euclideanRelativeInterior n C := hri_closureC

/-- Corollary 12.2.2. For a convex function `f` on `ℝ^n`, one can compute the Fenchel conjugate
`f*(x*) = sup_x (⟪x, x*⟫ - f x)` by restricting to points `x` in `ri (dom f)`. Here
`f* = fenchelConjugate n f`, `dom f = effectiveDomain Set.univ f`, and
`ri = intrinsicInterior ℝ`. -/
theorem fenchelConjugate_eq_sSup_intrinsicInterior_effectiveDomain (n : Nat)
    (f : (Fin n → Real) → EReal) (hf : ConvexFunction f) :
    ∀ xStar : Fin n → Real,
      fenchelConjugate n f xStar =
        sSup
          ((fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal) - f x) ''
            intrinsicInterior ℝ (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) := by
  classical
  intro xStar
  -- Let `A := ri(dom f)` and extend `f` by `⊤` outside `A`.
  let C : Set (Fin n → Real) := effectiveDomain (Set.univ : Set (Fin n → Real)) f
  let A : Set (Fin n → Real) := intrinsicInterior ℝ C
  let g : (Fin n → Real) → EReal := fun x => if x ∈ A then f x else ⊤
  have hdomg : effectiveDomain (Set.univ : Set (Fin n → Real)) g = A := by
    ext x
    constructor
    · intro hx
      have hxlt : g x < (⊤ : EReal) := by
        have : x ∈ (Set.univ : Set (Fin n → Real)) ∧ g x < (⊤ : EReal) := by
          simpa [effectiveDomain_eq] using hx
        exact this.2
      by_contra hxA
      -- If `x ∉ A`, then `g x = ⊤`, contradicting `g x < ⊤`.
      have : g x = (⊤ : EReal) := by simp [g, hxA]
      simp [this] at hxlt
    · intro hxA
      have hxC : x ∈ C := intrinsicInterior_subset (𝕜 := ℝ) (s := C) hxA
      have hxlt_f : f x < (⊤ : EReal) := by
        have : x ∈ (Set.univ : Set (Fin n → Real)) ∧ f x < (⊤ : EReal) := by
          simpa [C, effectiveDomain_eq] using hxC
        exact this.2
      have hxlt_g : g x < (⊤ : EReal) := by
        simpa [g, hxA] using hxlt_f
      have : x ∈ (Set.univ : Set (Fin n → Real)) ∧ g x < (⊤ : EReal) := ⟨by simp, hxlt_g⟩
      simpa [effectiveDomain_eq] using this
  have hCconv : Convex ℝ C :=
    effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real))) (f := f) hf
  have hAconv : Convex ℝ A :=
    convex_intrinsicInterior_of_convex (n := n) (C := C) hCconv
  have hg : ConvexFunction g := by
    simpa [g] using convexFunction_if_eq_top_on_compl (n := n) (f := f) hf (A := A) hAconv
  -- Transport between `EuclideanSpace` and `Fin n → ℝ` using the standard equivalence.
  let e : EuclideanSpace Real (Fin n) ≃L[Real] (Fin n → Real) :=
    EuclideanSpace.equiv (ι := Fin n) (𝕜 := Real)
  let CE : Set (EuclideanSpace Real (Fin n)) := e ⁻¹' C
  let AE : Set (EuclideanSpace Real (Fin n)) := e ⁻¹' A
  have hCEconv : Convex ℝ CE := hCconv.affine_preimage (e.toAffineEquiv.toAffineMap)
  have hriCE : euclideanRelativeInterior n CE = AE := by
    have hIE : intrinsicInterior ℝ CE = euclideanRelativeInterior n CE :=
      intrinsicInterior_eq_euclideanRelativeInterior (n := n) (C := CE)
    have hsymmC : e.symm '' C = CE := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [CE] using hy
      · intro hx
        refine ⟨e x, hx, ?_⟩
        simp
    have hsymmA : e.symm '' A = AE := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [AE] using hy
      · intro hx
        refine ⟨e x, hx, ?_⟩
        simp
    have hpre : intrinsicInterior ℝ CE = AE := by
      have himage :
          intrinsicInterior ℝ (e.symm '' C) = e.symm '' intrinsicInterior ℝ C :=
        ContinuousLinearEquiv.image_intrinsicInterior (e := e.symm) (s := C)
      -- Rewrite `intrinsicInterior C` as `A`.
      simpa [A, hsymmC, hsymmA] using himage
    calc
      euclideanRelativeInterior n CE = intrinsicInterior ℝ CE := by simpa using hIE.symm
      _ = AE := hpre
  have hriAE : euclideanRelativeInterior n AE = AE := by
    -- `AE = ri CE`, hence `ri AE = ri (ri CE) = ri CE = AE`.
    simpa [hriCE] using (euclideanRelativeInterior_idem_of_convex (n := n) (C := CE) hCEconv)
  have hri :
      euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹' C) =
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) g) := by
    have hri' : euclideanRelativeInterior n CE = euclideanRelativeInterior n AE := by
      -- Both sides are `AE`.
      simp [hriCE, hriAE]
    have hpre_f :
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹' C) = CE := by
      ext x
      -- `EuclideanSpace.equiv` is `PiLp.ofLp`, which is also the coercion to functions.
      simp [CE, e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv]
    have hpre_g :
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) g) = AE := by
      ext x
      simp [AE, e, hdomg, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv]
    simpa [hpre_f, hpre_g] using hri'
  have hagree :
      ∀ x ∈
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹' C),
        f (x : Fin n → Real) = g (x : Fin n → Real) := by
    intro x hx
    have hxAE : x ∈ AE := by
      -- `ri CE = AE`.
      have : x ∈ euclideanRelativeInterior n CE := by simpa [CE, e] using hx
      simpa [hriCE] using this
    have hxA : (x : Fin n → Real) ∈ A := by
      simpa [AE, e] using hxAE
    simp [g, hxA]
  have hclosure : convexFunctionClosure f = convexFunctionClosure g := by
    refine
      (convexFunctionClosure_eq_of_agree_on_ri_effectiveDomain (n := n) (f := f) (g := g) hf hg
        (hri := hri) (hagree := hagree))
  have hconj : fenchelConjugate n f = fenchelConjugate n g := by
    calc
      fenchelConjugate n f = fenchelConjugate n (convexFunctionClosure f) := by
        simpa using (fenchelConjugate_eq_of_convexFunctionClosure (n := n) (f := f)).symm
      _ = fenchelConjugate n (convexFunctionClosure g) := by simp [hclosure]
      _ = fenchelConjugate n g := by
        simpa using (fenchelConjugate_eq_of_convexFunctionClosure (n := n) (f := g))
  have hgSup :
      fenchelConjugate n g xStar =
        sSup ((fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal) - f x) '' A) := by
    simpa [g] using (fenchelConjugate_if_eq_sSup_image (n := n) (f := f) (A := A) xStar)
  simp [hconj, hgSup, A, C]

/-- Text 12.2.2: A pair of functions `(f, g) : (ℝ^n → [-∞, ∞]) × (ℝ^n → [-∞, ∞])` satisfies the
generalized Fenchel inequality if `⟪x, y⟫ ≤ f x + g y` for all `x, y ∈ ℝ^n`. -/
def SatisfiesGeneralizedFenchelInequality (n : Nat)
    (p : ((Fin n → Real) → EReal) × ((Fin n → Real) → EReal)) : Prop :=
  ∀ x y : Fin n → Real, ((x ⬝ᵥ y : Real) : EReal) ≤ p.1 x + p.2 y

/-- Text 12.2.2: The set `𝓦` of all pairs `(f, g)` satisfying the generalized Fenchel inequality. -/
abbrev GeneralizedFenchelPairs (n : Nat) :=
  {p : ((Fin n → Real) → EReal) × ((Fin n → Real) → EReal) //
    SatisfiesGeneralizedFenchelInequality n p}

/-- From the generalized Fenchel inequality for `(f, g)`, we get the pointwise bound `f* ≤ g`. -/
lemma satisfiesGeneralizedFenchelInequality_conjugate_le_snd (n : Nat)
    {f g : (Fin n → Real) → EReal} (h : SatisfiesGeneralizedFenchelInequality n (f, g)) :
    ∀ y : Fin n → Real, fenchelConjugate n f y ≤ g y := by
  intro y
  unfold fenchelConjugate
  refine sSup_le ?_
  rintro z ⟨x, rfl⟩
  have h' : ((x ⬝ᵥ y : Real) : EReal) ≤ g y + f x := by
    simpa [add_comm, add_left_comm, add_assoc] using h x y
  exact EReal.sub_le_of_le_add h'

/-- A generalized Fenchel pair cannot take the value `⊥` in either component. -/
lemma satisfiesGeneralizedFenchelInequality_no_bot (n : Nat)
    {f g : (Fin n → Real) → EReal} (h : SatisfiesGeneralizedFenchelInequality n (f, g)) :
    (∀ x : Fin n → Real, f x ≠ (⊥ : EReal)) ∧ (∀ y : Fin n → Real, g y ≠ (⊥ : EReal)) := by
  constructor
  · intro x hx
    have hcontra : ¬ ((0 : Real) : EReal) ≤ (⊥ : EReal) := by simp
    have : ((0 : Real) : EReal) ≤ (⊥ : EReal) := by
      simpa [SatisfiesGeneralizedFenchelInequality, hx] using (h x 0)
    exact (hcontra this).elim
  · intro y hy
    have hcontra : ¬ ((0 : Real) : EReal) ≤ (⊥ : EReal) := by simp
    have : ((0 : Real) : EReal) ≤ (⊥ : EReal) := by
      simpa [SatisfiesGeneralizedFenchelInequality, hy] using (h 0 y)
    exact (hcontra this).elim

/-- A minimal generalized Fenchel pair has some point where the first component is not `⊤`. -/
lemma generalizedFenchelPairs_exists_fst_ne_top_of_isMin (n : Nat) (p : GeneralizedFenchelPairs n)
    (hpmin : IsMin p) : ∃ x : Fin n → Real, p.1.1 x ≠ (⊤ : EReal) := by
  classical
  rcases p with ⟨⟨f, g⟩, hp⟩
  by_contra h
  push_neg at h
  have hf_top : ∀ x : Fin n → Real, f x = (⊤ : EReal) := h
  have hg_ne_bot :
      ∀ y : Fin n → Real, g y ≠ (⊥ : EReal) :=
    (satisfiesGeneralizedFenchelInequality_no_bot (n := n) (f := f) (g := g) hp).2
  by_cases hg_top : ∀ y : Fin n → Real, g y = (⊤ : EReal)
  · let g' : (Fin n → Real) → EReal := fun _ => (0 : EReal)
    have hg'le : g' ≤ g := by
      intro y
      simp [g', hg_top y]
    have hg'ne_bot : ∀ y : Fin n → Real, g' y ≠ (⊥ : EReal) := by
      intro y
      simp [g']
    have hp' : SatisfiesGeneralizedFenchelInequality n (f, g') := by
      intro x y
      have : f x = (⊤ : EReal) := hf_top x
      have htop : (f x + g' y) = (⊤ : EReal) := by
        -- `⊤ + a = ⊤` when `a ≠ ⊥`.
        by_cases hgy : g' y = (⊥ : EReal)
        · exact (hg'ne_bot y hgy).elim
        · simp [this, g']
      simp [htop]
    let p' : GeneralizedFenchelPairs n := ⟨(f, g'), hp'⟩
    have hp'le : p' ≤ (⟨(f, g), hp⟩ : GeneralizedFenchelPairs n) := by
      change (f, g') ≤ (f, g)
      exact ⟨le_rfl, hg'le⟩
    have hle : (⟨(f, g), hp⟩ : GeneralizedFenchelPairs n) ≤ p' := hpmin (b := p') hp'le
    have hg_le : g ≤ g' := by
      have : (f, g) ≤ (f, g') := by simpa [p'] using hle
      exact this.2
    have : (⊤ : EReal) ≤ (0 : EReal) := by
      simpa [hg_top 0, g'] using hg_le 0
    exact (not_top_le_coe 0 this).elim
  · rcases not_forall.1 hg_top with ⟨y0, hy0'⟩
    have hy0 : g y0 ≠ (⊤ : EReal) := by simpa using hy0'
    have hy0_ne_bot : g y0 ≠ (⊥ : EReal) := hg_ne_bot y0
    set r : Real := (g y0).toReal
    have hgr : g y0 = (r : EReal) := by
      simpa [r] using (EReal.coe_toReal (x := g y0) hy0 hy0_ne_bot).symm
    let g' : (Fin n → Real) → EReal := fun y => if y = y0 then ((r - 1 : Real) : EReal) else g y
    have hg'le : g' ≤ g := by
      intro y
      by_cases hy : y = y0
      · subst hy
        have hreal : (r - 1 : Real) ≤ r := by linarith
        have hcoe : ((r - 1 : Real) : EReal) ≤ (r : EReal) :=
          (EReal.coe_le_coe_iff).2 hreal
        simpa [g', hgr] using hcoe
      · simp [g', hy]
    have hg'ne_bot : ∀ y : Fin n → Real, g' y ≠ (⊥ : EReal) := by
      intro y
      by_cases hy : y = y0
      · subst hy
        have : ((r - 1 : Real) : EReal) ≠ (⊥ : EReal) := by
          simpa using (EReal.coe_ne_bot (r - 1))
        simpa [g'] using this
      · simpa [g', hy] using hg_ne_bot y
    have hp' : SatisfiesGeneralizedFenchelInequality n (f, g') := by
      intro x y
      have : f x = (⊤ : EReal) := hf_top x
      have htop : (f x + g' y) = (⊤ : EReal) := by
        by_cases hgy : g' y = (⊥ : EReal)
        · exact (hg'ne_bot y hgy).elim
        · simp [this, hgy]
      simp [htop]
    let p' : GeneralizedFenchelPairs n := ⟨(f, g'), hp'⟩
    have hp'le : p' ≤ (⟨(f, g), hp⟩ : GeneralizedFenchelPairs n) := by
      change (f, g') ≤ (f, g)
      exact ⟨le_rfl, hg'le⟩
    have hle : (⟨(f, g), hp⟩ : GeneralizedFenchelPairs n) ≤ p' := hpmin (b := p') hp'le
    have hg_le : g ≤ g' := by
      have : (f, g) ≤ (f, g') := by simpa [p'] using hle
      exact this.2
    have : (r : EReal) ≤ ((r - 1 : Real) : EReal) := by
      have := hg_le y0
      simpa [g', hgr] using this
    have : r ≤ r - 1 := (EReal.coe_le_coe_iff).1 this
    linarith

/-- A minimal generalized Fenchel pair has some point where the second component is not `⊤`. -/
lemma generalizedFenchelPairs_exists_snd_ne_top_of_isMin (n : Nat) (p : GeneralizedFenchelPairs n)
    (hpmin : IsMin p) : ∃ y : Fin n → Real, p.1.2 y ≠ (⊤ : EReal) := by
  classical
  rcases p with ⟨⟨f, g⟩, hp⟩
  by_contra h
  push_neg at h
  have hg_top : ∀ y : Fin n → Real, g y = (⊤ : EReal) := h
  have hf_ne_bot :
      ∀ x : Fin n → Real, f x ≠ (⊥ : EReal) :=
    (satisfiesGeneralizedFenchelInequality_no_bot (n := n) (f := f) (g := g) hp).1
  by_cases hf_top : ∀ x : Fin n → Real, f x = (⊤ : EReal)
  · let f' : (Fin n → Real) → EReal := fun _ => (0 : EReal)
    have hf'le : f' ≤ f := by
      intro x
      simp [f', hf_top x]
    have hf'ne_bot : ∀ x : Fin n → Real, f' x ≠ (⊥ : EReal) := by
      intro x
      simp [f']
    have hp' : SatisfiesGeneralizedFenchelInequality n (f', g) := by
      intro x y
      have : g y = (⊤ : EReal) := hg_top y
      have htop : (f' x + g y) = (⊤ : EReal) := by
        by_cases hfx : f' x = (⊥ : EReal)
        · exact (hf'ne_bot x hfx).elim
        · simp [f', this]
      simp [htop]
    let p' : GeneralizedFenchelPairs n := ⟨(f', g), hp'⟩
    have hp'le : p' ≤ (⟨(f, g), hp⟩ : GeneralizedFenchelPairs n) := by
      change (f', g) ≤ (f, g)
      exact ⟨hf'le, le_rfl⟩
    have hle : (⟨(f, g), hp⟩ : GeneralizedFenchelPairs n) ≤ p' := hpmin (b := p') hp'le
    have hf_le : f ≤ f' := by
      have : (f, g) ≤ (f', g) := by simpa [p'] using hle
      exact this.1
    have : (⊤ : EReal) ≤ (0 : EReal) := by
      simpa [hf_top 0, f'] using hf_le 0
    exact (not_top_le_coe 0 this).elim
  · rcases not_forall.1 hf_top with ⟨x0, hx0'⟩
    have hx0 : f x0 ≠ (⊤ : EReal) := by simpa using hx0'
    have hx0_ne_bot : f x0 ≠ (⊥ : EReal) := hf_ne_bot x0
    set r : Real := (f x0).toReal
    have hfr : f x0 = (r : EReal) := by
      simpa [r] using (EReal.coe_toReal (x := f x0) hx0 hx0_ne_bot).symm
    let f' : (Fin n → Real) → EReal := fun x => if x = x0 then ((r - 1 : Real) : EReal) else f x
    have hf'le : f' ≤ f := by
      intro x
      by_cases hx : x = x0
      · subst hx
        have hreal : (r - 1 : Real) ≤ r := by linarith
        have hcoe : ((r - 1 : Real) : EReal) ≤ (r : EReal) :=
          (EReal.coe_le_coe_iff).2 hreal
        simpa [f', hfr] using hcoe
      · simp [f', hx]
    have hf'ne_bot : ∀ x : Fin n → Real, f' x ≠ (⊥ : EReal) := by
      intro x
      by_cases hx : x = x0
      · subst hx
        have : ((r - 1 : Real) : EReal) ≠ (⊥ : EReal) := by
          simpa using (EReal.coe_ne_bot (r - 1))
        simpa [f'] using this
      · simpa [f', hx] using hf_ne_bot x
    have hp' : SatisfiesGeneralizedFenchelInequality n (f', g) := by
      intro x y
      have : g y = (⊤ : EReal) := hg_top y
      have htop : (f' x + g y) = (⊤ : EReal) := by
        by_cases hfx : f' x = (⊥ : EReal)
        · exact (hf'ne_bot x hfx).elim
        · simp [this, hfx]
      simp [htop]
    let p' : GeneralizedFenchelPairs n := ⟨(f', g), hp'⟩
    have hp'le : p' ≤ (⟨(f, g), hp⟩ : GeneralizedFenchelPairs n) := by
      change (f', g) ≤ (f, g)
      exact ⟨hf'le, le_rfl⟩
    have hle : (⟨(f, g), hp⟩ : GeneralizedFenchelPairs n) ≤ p' := hpmin (b := p') hp'le
    have hf_le : f ≤ f' := by
      have : (f, g) ≤ (f', g) := by simpa [p'] using hle
      exact this.1
    have : (r : EReal) ≤ ((r - 1 : Real) : EReal) := by
      have := hf_le x0
      simpa [f', hfr] using this
    have : r ≤ r - 1 := (EReal.coe_le_coe_iff).1 this
    linarith

/-- Under the generalized Fenchel inequality, swapping the pair preserves the property. -/
lemma satisfiesGeneralizedFenchelInequality_swap (n : Nat) {f g : (Fin n → Real) → EReal}
    (h : SatisfiesGeneralizedFenchelInequality n (f, g)) :
    SatisfiesGeneralizedFenchelInequality n (g, f) := by
  intro x y
  have := h y x
  simpa [dotProduct_comm, add_comm, add_left_comm, add_assoc] using this

/-- If `f` has no `⊥` values and is not identically `⊤`, then `f*` is never `⊥`. -/
lemma fenchelConjugate_ne_bot_of_exists_ne_top (n : Nat) (f : (Fin n → Real) → EReal)
    (h : ∃ x0 : Fin n → Real, f x0 ≠ (⊤ : EReal)) :
    ∀ y : Fin n → Real, fenchelConjugate n f y ≠ (⊥ : EReal) := by
  classical
  rcases h with ⟨x0, hx0⟩
  intro y
  unfold fenchelConjugate
  -- Exhibit a point in the range which is strictly above `⊥`.
  have hmem :
      ((x0 ⬝ᵥ y : Real) : EReal) - f x0 ∈
        Set.range (fun x : Fin n → Real => ((x ⬝ᵥ y : Real) : EReal) - f x) :=
    ⟨x0, rfl⟩
  have hle_sSup :
      ((x0 ⬝ᵥ y : Real) : EReal) - f x0 ≤
        sSup (Set.range (fun x : Fin n → Real => ((x ⬝ᵥ y : Real) : EReal) - f x)) :=
    le_sSup hmem
  have hterm_ne_bot : ((x0 ⬝ᵥ y : Real) : EReal) - f x0 ≠ (⊥ : EReal) := by
    by_cases hxbot : f x0 = (⊥ : EReal)
    · simp [hxbot]
    · set r : Real := (f x0).toReal
      have hfr : f x0 = (r : EReal) := by
        simpa [r] using (EReal.coe_toReal (x := f x0) hx0 hxbot).symm
      -- Subtracting a real from a real stays real, hence not `⊥`.
      have hreal : (((x0 ⬝ᵥ y) - r : Real) : EReal) ≠ (⊥ : EReal) := by
        simpa using (EReal.coe_ne_bot ((x0 ⬝ᵥ y) - r))
      have hcoe :
          (((x0 ⬝ᵥ y) - r : Real) : EReal) =
            ((x0 ⬝ᵥ y : Real) : EReal) - (r : EReal) := by
        exact (EReal.coe_sub (x0 ⬝ᵥ y) r)
      have : ((x0 ⬝ᵥ y : Real) : EReal) - (r : EReal) ≠ (⊥ : EReal) := by
        intro hbot
        have : (((x0 ⬝ᵥ y) - r : Real) : EReal) = (⊥ : EReal) := by
          simpa [hcoe] using hbot
        exact hreal this
      simpa [hfr] using this
  -- If the supremum were `⊥`, it would force the exhibited term to be `≤ ⊥`, contradiction.
  intro hsup
  have hle_bot : ((x0 ⬝ᵥ y : Real) : EReal) - f x0 ≤ (⊥ : EReal) := by
    simpa [hsup] using hle_sSup
  have hlt : (⊥ : EReal) < ((x0 ⬝ᵥ y : Real) : EReal) - f x0 :=
    bot_lt_iff_ne_bot.2 hterm_ne_bot
  have : (⊥ : EReal) < (⊥ : EReal) := lt_of_lt_of_le hlt hle_bot
  exact (lt_irrefl _ this).elim

/-- Fenchel's inequality: the pair `(f, f*)` satisfies the generalized Fenchel inequality. -/
lemma satisfiesGeneralizedFenchelInequality_self_conjugate (n : Nat) {f : (Fin n → Real) → EReal}
    (hf_bot : ∀ x : Fin n → Real, f x ≠ (⊥ : EReal))
    (hf_top : ∃ x0 : Fin n → Real, f x0 ≠ (⊤ : EReal)) :
    SatisfiesGeneralizedFenchelInequality n (f, fenchelConjugate n f) := by
  intro x y
  have hsub :
      ((x ⬝ᵥ y : Real) : EReal) - f x ≤ fenchelConjugate n f y := by
    unfold fenchelConjugate
    exact le_sSup ⟨x, rfl⟩
  have h1 : f x ≠ (⊥ : EReal) ∨ fenchelConjugate n f y ≠ ⊤ := Or.inl (hf_bot x)
  have h2 : f x ≠ ⊤ ∨ fenchelConjugate n f y ≠ (⊥ : EReal) := by
    exact Or.inr (fenchelConjugate_ne_bot_of_exists_ne_top (n := n) (f := f) hf_top y)
  have hle : ((x ⬝ᵥ y : Real) : EReal) ≤ fenchelConjugate n f y + f x :=
    (EReal.sub_le_iff_le_add h1 h2).1 hsub
  simpa [add_comm, add_left_comm, add_assoc] using hle

/-- Text 12.2.2: For `𝓦` the set of pairs satisfying the generalized Fenchel inequality, ordered by
`(f', g') ≼ (f, g)` meaning `f' ≤ f` and `g' ≤ g` pointwise, a pair is a minimal element of `𝓦`
if and only if `f` and `g` are mutually conjugate, i.e. `g = f^*` and `f = g^*` (here `f^*` is
`fenchelConjugate`). -/
theorem generalizedFenchelPairs_isMin_iff_mutuallyConjugate (n : Nat)
    (p : GeneralizedFenchelPairs n) :
    IsMin p ↔
      p.1.2 = fenchelConjugate n p.1.1 ∧ p.1.1 = fenchelConjugate n p.1.2 := by
  classical
  rcases p with ⟨⟨f, g⟩, hp⟩
  constructor
  · intro hpmin
    have hf_bot : ∀ x : Fin n → Real, f x ≠ (⊥ : EReal) :=
      (satisfiesGeneralizedFenchelInequality_no_bot (n := n) (f := f) (g := g) hp).1
    have hg_bot : ∀ y : Fin n → Real, g y ≠ (⊥ : EReal) :=
      (satisfiesGeneralizedFenchelInequality_no_bot (n := n) (f := f) (g := g) hp).2
    have hf_top : ∃ x0 : Fin n → Real, f x0 ≠ (⊤ : EReal) :=
      generalizedFenchelPairs_exists_fst_ne_top_of_isMin (n := n) (p := ⟨(f, g), hp⟩) hpmin
    have hg_top : ∃ y0 : Fin n → Real, g y0 ≠ (⊤ : EReal) :=
      generalizedFenchelPairs_exists_snd_ne_top_of_isMin (n := n) (p := ⟨(f, g), hp⟩) hpmin
    have hfg : ∀ y : Fin n → Real, fenchelConjugate n f y ≤ g y :=
      satisfiesGeneralizedFenchelInequality_conjugate_le_snd (n := n) (f := f) (g := g) hp
    -- Compare `p` with `(f, f*)`.
    have hp_self : SatisfiesGeneralizedFenchelInequality n (f, fenchelConjugate n f) :=
      satisfiesGeneralizedFenchelInequality_self_conjugate (n := n) (f := f) hf_bot hf_top
    let q : GeneralizedFenchelPairs n := ⟨(f, fenchelConjugate n f), hp_self⟩
    have hqle : q ≤ (⟨(f, g), hp⟩ : GeneralizedFenchelPairs n) := by
      change (f, fenchelConjugate n f) ≤ (f, g)
      exact ⟨le_rfl, hfg⟩
    have hp_le_q : (⟨(f, g), hp⟩ : GeneralizedFenchelPairs n) ≤ q := hpmin (b := q) hqle
    have hg_le : g ≤ fenchelConjugate n f := by
      have : (f, g) ≤ (f, fenchelConjugate n f) := by simpa [q] using hp_le_q
      exact this.2
    have hg_eq : g = fenchelConjugate n f := by
      funext y
      exact le_antisymm (hg_le y) (hfg y)
    -- Compare `p` with `(g*, g)`.
    have hswap : SatisfiesGeneralizedFenchelInequality n (g, f) :=
      satisfiesGeneralizedFenchelInequality_swap (n := n) (f := f) (g := g) hp
    have hgf : ∀ x : Fin n → Real, fenchelConjugate n g x ≤ f x :=
      satisfiesGeneralizedFenchelInequality_conjugate_le_snd (n := n) (f := g) (g := f) hswap
    have hp_self_g : SatisfiesGeneralizedFenchelInequality n (g, fenchelConjugate n g) :=
      satisfiesGeneralizedFenchelInequality_self_conjugate (n := n) (f := g) hg_bot hg_top
    have hp_self_g_swap : SatisfiesGeneralizedFenchelInequality n (fenchelConjugate n g, g) :=
      satisfiesGeneralizedFenchelInequality_swap (n := n) (f := g) (g := fenchelConjugate n g) hp_self_g
    let q' : GeneralizedFenchelPairs n := ⟨(fenchelConjugate n g, g), hp_self_g_swap⟩
    have hq'le : q' ≤ (⟨(f, g), hp⟩ : GeneralizedFenchelPairs n) := by
      change (fenchelConjugate n g, g) ≤ (f, g)
      exact ⟨hgf, le_rfl⟩
    have hp_le_q' : (⟨(f, g), hp⟩ : GeneralizedFenchelPairs n) ≤ q' := hpmin (b := q') hq'le
    have hf_le : f ≤ fenchelConjugate n g := by
      have : (f, g) ≤ (fenchelConjugate n g, g) := by simpa [q'] using hp_le_q'
      exact this.1
    have hf_eq : f = fenchelConjugate n g := by
      funext x
      exact le_antisymm (hf_le x) (hgf x)
    exact ⟨hg_eq, hf_eq⟩
  · rintro ⟨hg, hf⟩
    -- Sufficiency: mutual conjugacy implies minimality.
    intro q hqle
    classical
    have hgfun : g = fenchelConjugate n f := by simpa using hg
    have hffun : f = fenchelConjugate n g := by simpa using hf
    rcases q with ⟨⟨f', g'⟩, hq⟩
    have hle : (f', g') ≤ (f, g) := by simpa using hqle
    have hf'le : f' ≤ f := hle.1
    have hg'le : g' ≤ g := hle.2
    have hq_conj : ∀ y : Fin n → Real, fenchelConjugate n f' y ≤ g' y :=
      satisfiesGeneralizedFenchelInequality_conjugate_le_snd (n := n) (f := f') (g := g') hq
    have hq_swap : SatisfiesGeneralizedFenchelInequality n (g', f') :=
      satisfiesGeneralizedFenchelInequality_swap (n := n) (f := f') (g := g') hq
    have hq_conj' : ∀ x : Fin n → Real, fenchelConjugate n g' x ≤ f' x :=
      satisfiesGeneralizedFenchelInequality_conjugate_le_snd (n := n) (f := g') (g := f') hq_swap
    have hanti := fenchelConjugate_antitone (n := n)
    have h_f : fenchelConjugate n f ≤ fenchelConjugate n f' := hanti hf'le
    have h_g : fenchelConjugate n g ≤ fenchelConjugate n g' := hanti hg'le
    have hg_le : g ≤ g' := by
      intro y
      calc
        g y = fenchelConjugate n f y := by simp [hgfun]
        _ ≤ fenchelConjugate n f' y := h_f y
        _ ≤ g' y := hq_conj y
    have hf_le : f ≤ f' := by
      intro x
      calc
        f x = fenchelConjugate n g x := by simp [hffun]
        _ ≤ fenchelConjugate n g' x := h_g x
        _ ≤ f' x := hq_conj' x
    -- Package as `p ≤ q` in the product order.
    change (f, g) ≤ (f', g')
    exact ⟨hf_le, hg_le⟩

/-- Text 12.2.3 (Fenchel's inequality): For any proper convex function `f` on `ℝ^n` and its
conjugate `f*`, the inequality `⟪x, x*⟫ ≤ f x + f*(x*)` holds for every `x ∈ ℝ^n` and every
`x* ∈ ℝ^n`. Here the conjugate `f*` is represented by `fenchelConjugate n f`. -/
theorem fenchel_inequality (n : Nat) (f : (Fin n → Real) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    ∀ x xStar : Fin n → Real, ((x ⬝ᵥ xStar : Real) : EReal) ≤ f x + fenchelConjugate n f xStar := by
  have hf_bot : ∀ x : Fin n → Real, f x ≠ (⊥ : EReal) := by
    intro x
    exact hf.2.2 x (by simp)
  obtain ⟨x0, _r0, hx0⟩ := properConvexFunctionOn_exists_finite_point (n := n) (f := f) hf
  have hf_top : ∃ x0 : Fin n → Real, f x0 ≠ (⊤ : EReal) := by
    refine ⟨x0, ?_⟩
    simp [hx0]
  have hgen : SatisfiesGeneralizedFenchelInequality n (f, fenchelConjugate n f) :=
    satisfiesGeneralizedFenchelInequality_self_conjugate (n := n) (f := f) hf_bot hf_top
  intro x xStar
  exact hgen x xStar

/-- The Fenchel conjugate of the indicator of a set is the supremum of the dot product over that set. -/
lemma fenchelConjugate_indicatorFunction_eq_sSup_dotProduct_image (n : Nat)
    (L : Submodule ℝ (Fin n → Real)) :
    ∀ xStar : Fin n → Real,
      fenchelConjugate n (indicatorFunction (L : Set (Fin n → Real))) xStar =
        sSup ((fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal)) '' (L : Set (Fin n → Real))) := by
  intro xStar
  classical
  simpa [indicatorFunction] using
    (fenchelConjugate_if_eq_sSup_image (n := n) (f := fun _ : Fin n → Real => (0 : EReal))
      (A := (L : Set (Fin n → Real))) xStar)

/-- Scaling the left argument scales the dot product. -/
lemma dotProduct_smul_left_real {n : Nat} (a : Real) (y xStar : Fin n → Real) :
    (a • y) ⬝ᵥ xStar = a * (y ⬝ᵥ xStar) := by
  simp [dotProduct_comm, dotProduct_smul, smul_eq_mul]

/-- If `xStar` is orthogonal to every `x ∈ L`, then the supremum of `⟪x,xStar⟫` over `L` is `0`. -/
lemma sSup_dotProduct_image_eq_zero_of_forall_mem_eq_zero {n : Nat}
    (L : Submodule ℝ (Fin n → Real)) (xStar : Fin n → Real)
    (h : ∀ x : Fin n → Real, x ∈ L → x ⬝ᵥ xStar = 0) :
    sSup ((fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal)) '' (L : Set (Fin n → Real))) = 0 := by
  apply le_antisymm
  · refine sSup_le ?_
    rintro y ⟨x, hxL, rfl⟩
    have hx0 : x ⬝ᵥ xStar = 0 := h x hxL
    simp [hx0]
  · have hmem :
        (0 : EReal) ∈
          (fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal)) '' (L : Set (Fin n → Real)) := by
      refine ⟨0, L.zero_mem, ?_⟩
      simp
    exact le_sSup hmem

/-- If some `y ∈ L` has nonzero dot product with `xStar`, then the supremum over `L` is `+∞`. -/
lemma sSup_dotProduct_image_eq_top_of_exists_mem_ne_zero {n : Nat}
    (L : Submodule ℝ (Fin n → Real)) (xStar : Fin n → Real)
    (h : ∃ y : Fin n → Real, y ∈ L ∧ y ⬝ᵥ xStar ≠ 0) :
    sSup ((fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal)) '' (L : Set (Fin n → Real))) = ⊤ := by
  classical
  rcases h with ⟨y, hyL, hyne0⟩
  refine (EReal.eq_top_iff_forall_lt _).2 ?_
  intro μ
  let a : Real := (μ + 1) / (y ⬝ᵥ xStar)
  have haL : a • y ∈ (L : Set (Fin n → Real)) := L.smul_mem a hyL
  have hdot : (a • y) ⬝ᵥ xStar = μ + 1 := by
    calc
      (a • y) ⬝ᵥ xStar = a * (y ⬝ᵥ xStar) := dotProduct_smul_left_real (a := a) (y := y) (xStar := xStar)
      _ = ((μ + 1) / (y ⬝ᵥ xStar)) * (y ⬝ᵥ xStar) := by simp [a]
      _ = μ + 1 := by
        field_simp [hyne0]
  have hmem :
      ((μ + 1 : Real) : EReal) ∈
        (fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal)) '' (L : Set (Fin n → Real)) := by
    refine ⟨a • y, haL, ?_⟩
    simp [hdot]
  have hle : ((μ + 1 : Real) : EReal) ≤
      sSup ((fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal)) '' (L : Set (Fin n → Real))) :=
    le_sSup hmem
  have hlt : (μ : EReal) < ((μ + 1 : Real) : EReal) :=
    (EReal.coe_lt_coe_iff).2 (by linarith)
  exact lt_of_lt_of_le hlt hle

/-- Text 12.2.3 (indicator function of a subspace): Let `f` be the indicator function of a
subspace `L` of `ℝ^n`, i.e. `f(x) = δ(x | L)`. Then the conjugate function `f*` is the indicator
function of the orthogonal complement `L^{⊥}` (the set of vectors `x*` such that `⟪x, x*⟫ = 0`
for all `x ∈ L`), denoted `δ(· | L^{⊥})`. -/

theorem fenchelConjugate_indicatorFunction_submodule (n : Nat) (L : Submodule ℝ (Fin n → Real)) :
    fenchelConjugate n (indicatorFunction (L : Set (Fin n → Real))) =
      indicatorFunction {xStar : Fin n → Real | ∀ x : Fin n → Real, x ∈ L → x ⬝ᵥ xStar = 0} := by
  classical
  funext xStar
  have hSup :
      fenchelConjugate n (indicatorFunction (L : Set (Fin n → Real))) xStar =
        sSup ((fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal)) '' (L : Set (Fin n → Real))) :=
    fenchelConjugate_indicatorFunction_eq_sSup_dotProduct_image (n := n) (L := L) xStar
  by_cases hx :
      xStar ∈ {xStar : Fin n → Real | ∀ x : Fin n → Real, x ∈ L → x ⬝ᵥ xStar = 0}
  · have hx' : ∀ x : Fin n → Real, x ∈ L → x ⬝ᵥ xStar = 0 := by
      simpa [Set.mem_setOf_eq] using hx
    have hSup0 :
        sSup ((fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal)) '' (L : Set (Fin n → Real))) = 0 :=
      sSup_dotProduct_image_eq_zero_of_forall_mem_eq_zero (L := L) (xStar := xStar) hx'
    simp [hSup, hSup0, indicatorFunction, hx]
  · have hx' : ∃ y : Fin n → Real, y ∈ L ∧ y ⬝ᵥ xStar ≠ 0 := by
      have : ¬ ∀ x : Fin n → Real, x ∈ L → x ⬝ᵥ xStar = 0 := by
        simpa [Set.mem_setOf_eq] using hx
      push_neg at this
      exact this
    have hSupTop :
        sSup ((fun x : Fin n → Real => ((x ⬝ᵥ xStar : Real) : EReal)) '' (L : Set (Fin n → Real))) = ⊤ :=
      sSup_dotProduct_image_eq_top_of_exists_mem_ne_zero (L := L) (xStar := xStar) hx'
    simp [hSup, hSupTop, indicatorFunction, hx]

end Section12
end Chap03
