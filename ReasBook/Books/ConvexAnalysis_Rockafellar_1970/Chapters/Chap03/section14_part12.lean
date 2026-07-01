/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yuhao Jiang, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section14_part11
section Chap03
section Section14

open scoped Pointwise

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Finite-dimensional formula: `dim(Wᵃⁿⁿ) = dim(E) - dim(W)` for dual annihilators. -/
lemma section14_finrank_dualAnnihilator_eq_sub [FiniteDimensional ℝ E] (W : Submodule ℝ E) :
    Module.finrank ℝ (W.dualAnnihilator) = Module.finrank ℝ E - Module.finrank ℝ W := by
  classical
  have hsum : Module.finrank ℝ W + Module.finrank ℝ (W.dualAnnihilator) = Module.finrank ℝ E := by
    simpa using (Subspace.finrank_add_finrank_dualAnnihilator_eq (K := ℝ) (V := E) W)
  calc
    Module.finrank ℝ (W.dualAnnihilator) =
        (Module.finrank ℝ W + Module.finrank ℝ (W.dualAnnihilator)) - Module.finrank ℝ W := by
          simp
    _ = Module.finrank ℝ E - Module.finrank ℝ W := by
          simp [hsum]

/-- Orthogonality relation: the span of `polar C` is the dual annihilator of the lineality subspace
of `C` (spanned by `(-rec C) ∩ rec C`). -/
lemma section14_span_polar_eq_dualAnnihilator_span_lineality
    [FiniteDimensional ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] {C : Set E} (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hC0 : (0 : E) ∈ C) :
    Submodule.span ℝ (polar (E := E) C) =
        (Submodule.span ℝ ((-Set.recessionCone C) ∩ Set.recessionCone C)).dualAnnihilator := by
  classical
  have hbipolar : {x : E | ∀ φ ∈ polar (E := E) C, φ x ≤ 1} = C :=
    section14_bipolar_eq_of_closed_convex (E := E) hCclosed hCconv hC0
  have hco :
      (Submodule.span ℝ (polar (E := E) C)).dualCoannihilator =
        Submodule.span ℝ ((-Set.recessionCone C) ∩ Set.recessionCone C) :=
    section14_dualCoannihilator_span_polar_eq_span_negRec_inter_rec_of_bipolar (E := E) (C := C)
      (Cpolar := polar (E := E) C) hbipolar hC0
  have hco' := congrArg Submodule.dualAnnihilator hco
  have hW :
      ((Submodule.span ℝ (polar (E := E) C)).dualCoannihilator).dualAnnihilator =
        Submodule.span ℝ (polar (E := E) C) := by
    simpa using
      (Subspace.dualCoannihilator_dualAnnihilator_eq (W := (Submodule.span ℝ (polar (E := E) C))))
  simpa [hW] using hco'

/-- Orthogonality relation (dual direction): the span of the lineality subspace of `polar C`
is the dual annihilator of `span C`. -/
lemma section14_span_lineality_polar_eq_dualAnnihilator_span {C : Set E} :
    Submodule.span ℝ
          ((-Set.recessionCone (polar (E := E) C)) ∩ Set.recessionCone (polar (E := E) C)) =
        (Submodule.span ℝ C).dualAnnihilator := by
  classical
  simpa using
    (section14_dualAnnihilator_span_primal_eq_span_lineality_Cpolar_of_hpolar (E := E) (C := C)
        (Cpolar := polar (E := E) C) (hpolar := rfl)
        (hCpolar0 := (section14_convex_and_zeroMem_polar (E := E) (C := C)).2)).symm

/-- Corollary 14.6.1. Let `C` be a closed convex set in `ℝ^n` containing the origin. Then
`dimension C^∘ = n - lineality C`, `lineality C^∘ = n - dimension C`, and `rank C^∘ = rank C`.

In this file, we model `C^∘` as `polar C : Set (Module.Dual ℝ E)`. We interpret the book's
`dimension S` as `Module.finrank ℝ (Submodule.span ℝ S)` and the book's `lineality S` as
`Module.finrank ℝ (Submodule.span ℝ ((-Set.recessionCone S) ∩ Set.recessionCone S))`, so that
`rank S = dimension S - lineality S`. -/
theorem finrank_span_polar_eq_finrank_sub_finrank_span_lineality_and_dual_and_rank
    [FiniteDimensional ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] {C : Set E} (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hC0 : (0 : E) ∈ C) :
    (Module.finrank ℝ (Submodule.span ℝ (polar (E := E) C)) =
        Module.finrank ℝ E -
          Module.finrank ℝ (Submodule.span ℝ ((-Set.recessionCone C) ∩ Set.recessionCone C))) ∧
      (Module.finrank ℝ
            (Submodule.span ℝ
              ((-Set.recessionCone (polar (E := E) C)) ∩ Set.recessionCone (polar (E := E) C))) =
          Module.finrank ℝ E - Module.finrank ℝ (Submodule.span ℝ C)) ∧
      (Module.finrank ℝ (Submodule.span ℝ (polar (E := E) C)) -
            Module.finrank ℝ
              (Submodule.span ℝ
                ((-Set.recessionCone (polar (E := E) C)) ∩
                  Set.recessionCone (polar (E := E) C))) =
          Module.finrank ℝ (Submodule.span ℝ C) -
          Module.finrank ℝ
              (Submodule.span ℝ ((-Set.recessionCone C) ∩ Set.recessionCone C))) := by
  classical
  have hspan_polar :
      Submodule.span ℝ (polar (E := E) C) =
        (Submodule.span ℝ ((-Set.recessionCone C) ∩ Set.recessionCone C)).dualAnnihilator :=
    section14_span_polar_eq_dualAnnihilator_span_lineality (E := E) hCclosed hCconv hC0
  have hspan_lineality_polar :
      Submodule.span ℝ
            ((-Set.recessionCone (polar (E := E) C)) ∩ Set.recessionCone (polar (E := E) C)) =
          (Submodule.span ℝ C).dualAnnihilator :=
    section14_span_lineality_polar_eq_dualAnnihilator_span (E := E) (C := C)
  have h1 :
      Module.finrank ℝ (Submodule.span ℝ (polar (E := E) C)) =
        Module.finrank ℝ E -
          Module.finrank ℝ (Submodule.span ℝ ((-Set.recessionCone C) ∩ Set.recessionCone C)) := by
    calc
      Module.finrank ℝ (Submodule.span ℝ (polar (E := E) C)) =
          Module.finrank ℝ
            (Submodule.dualAnnihilator
              (Submodule.span ℝ ((-Set.recessionCone C) ∩ Set.recessionCone C))) := by
              simpa using
                congrArg
                  (fun S : Submodule ℝ (Module.Dual ℝ E) =>
                    Module.finrank ℝ S)
                  hspan_polar
      _ =
          Module.finrank ℝ E -
            Module.finrank ℝ (Submodule.span ℝ ((-Set.recessionCone C) ∩ Set.recessionCone C)) := by
              simpa using
                (section14_finrank_dualAnnihilator_eq_sub (E := E)
                  (W := Submodule.span ℝ ((-Set.recessionCone C) ∩ Set.recessionCone C)))
  have h2 :
      Module.finrank ℝ
            (Submodule.span ℝ
              ((-Set.recessionCone (polar (E := E) C)) ∩ Set.recessionCone (polar (E := E) C))) =
          Module.finrank ℝ E - Module.finrank ℝ (Submodule.span ℝ C) := by
    calc
      Module.finrank ℝ
            (Submodule.span ℝ
              ((-Set.recessionCone (polar (E := E) C)) ∩ Set.recessionCone (polar (E := E) C))) =
          Module.finrank ℝ ((Submodule.span ℝ C).dualAnnihilator) := by
            simpa using
              congrArg
                (fun S : Submodule ℝ (Module.Dual ℝ E) =>
                  Module.finrank ℝ S)
                hspan_lineality_polar
      _ = Module.finrank ℝ E - Module.finrank ℝ (Submodule.span ℝ C) := by
            simpa using
              (section14_finrank_dualAnnihilator_eq_sub (E := E) (W := Submodule.span ℝ C))
  have hdn : Module.finrank ℝ (Submodule.span ℝ C) ≤ Module.finrank ℝ E := by
    simpa using (Submodule.finrank_le (R := ℝ) (M := E) (s := Submodule.span ℝ C))
  refine ⟨h1, h2, ?_⟩
  -- `rank(polar C) = rank(C)` follows by rewriting with the two dimension identities.
  -- `tsub_tsub_tsub_cancel_left` is the Nat subtraction identity `(n - l) - (n - d) = d - l`.
  simpa [h1, h2] using
    (tsub_tsub_tsub_cancel_left (a := Module.finrank ℝ E)
      (b := Module.finrank ℝ (Submodule.span ℝ C))
      (c :=
        Module.finrank ℝ (Submodule.span ℝ ((-Set.recessionCone C) ∩ Set.recessionCone C))) hdn)

/-- If `f` is nonnegative and vanishes at `0`, then its Fenchel conjugate (for evaluation) is also
nonnegative and vanishes at `0`. -/
lemma section14_fenchelConjugate_nonneg_of_nonneg_and_zero
    {f : E → EReal} (hf_nonneg : ∀ x, (0 : EReal) ≤ f x) (hf0 : f 0 = 0) :
    (∀ xStar : Module.Dual ℝ E,
        (0 : EReal) ≤
          fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f xStar) ∧
      fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f 0 = 0 := by
  classical
  let p := LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)
  have hnonneg : ∀ xStar : Module.Dual ℝ E, (0 : EReal) ≤ fenchelConjugateBilin p f xStar := by
    intro xStar
    unfold fenchelConjugateBilin
    -- Witness the supremum with `x = 0`.
    have hmem : (0 : EReal) ∈ Set.range (fun x => (p x xStar : EReal) - f x) := by
      refine ⟨0, ?_⟩
      simp [p, hf0]
    simpa using (le_sSup hmem)
  have hzero : fenchelConjugateBilin p f 0 = 0 := by
    unfold fenchelConjugateBilin
    apply le_antisymm
    · refine sSup_le ?_
      rintro _ ⟨x, rfl⟩
      -- `0 - f x ≤ 0` follows from `0 ≤ f x` via the `sub_le_of_le_add'` lemma for `EReal`.
      have : (p x (0 : Module.Dual ℝ E) : EReal) ≤ f x + (0 : EReal) := by
        simpa [p, add_comm, add_left_comm, add_assoc] using hf_nonneg x
      have : (p x (0 : Module.Dual ℝ E) : EReal) - f x ≤ (0 : EReal) :=
        EReal.sub_le_of_le_add' this
      simpa [p] using this
    · -- Witness the supremum with `x = 0`.
      have hmem : (0 : EReal) ∈ Set.range (fun x => (p x (0 : Module.Dual ℝ E) : EReal) - f x) := by
        refine ⟨0, ?_⟩
        simp [p, hf0]
      simpa using (le_sSup hmem)
  refine ⟨?_, ?_⟩
  · simpa [p] using hnonneg
  · simpa [p] using hzero

/-- Fenchel–Young inequality for the evaluation pairing: `⟪x★, x⟫ ≤ f x + f★ x★`. -/
lemma section14_eval_le_add_fenchelConjugate
    {f : E → EReal} (x : E) (xStar : Module.Dual ℝ E) (hfbot : f x ≠ ⊥) (hftop : f x ≠ ⊤) :
    ((xStar x : ℝ) : EReal) ≤
      f x +
        fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f xStar := by
  classical
  let p := LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)
  have hle :
      (p x xStar : EReal) - f x ≤ fenchelConjugateBilin p f xStar := by
    unfold fenchelConjugateBilin
    exact le_sSup ⟨x, rfl⟩
  -- Rewrite `a - b ≤ c` as `a ≤ c + b` using the `EReal` lemma (requires mild side conditions).
  have :
      (p x xStar : EReal) ≤ fenchelConjugateBilin p f xStar + f x :=
    (EReal.sub_le_iff_le_add (a := (p x xStar : EReal)) (b := f x) (c := fenchelConjugateBilin p f xStar)
          (.inl hfbot) (.inl hftop)).1 hle
  simpa [p, add_comm, add_left_comm, add_assoc] using this

/-- The `α⁻¹`-scaled `α`-sublevel set of the conjugate lies in `2 • polar` of the primal
`α`-sublevel set. -/
lemma section14_inv_smul_sublevel_fenchelConjugate_subset_two_smul_polar_sublevel
    {f : E → EReal} (hf_nonneg : ∀ x, (0 : EReal) ≤ f x) {α : ℝ} (hα : 0 < α) :
    (α⁻¹ : ℝ) •
          {xStar : Module.Dual ℝ E |
              fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f xStar ≤
                (α : EReal)} ⊆
        (2 : ℝ) • polar (E := E) {x : E | f x ≤ (α : EReal)} := by
  classical
  let p := LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)
  intro y hy
  rcases hy with ⟨xStar, hxStar, rfl⟩
  -- Reduce membership in `2 • polar` to a uniform bound on the sublevel set.
  refine (section14_mem_smul_polar_iff_forall_le (E := E) (C := {x : E | f x ≤ (α : EReal)})
      (r := (2 : ℝ)) (by norm_num) (φ := (α⁻¹ : ℝ) • xStar)).2 ?_
  intro x hx
  have hfy : f x ≤ (α : EReal) := hx
  have hfbot : f x ≠ ⊥ := by
    intro hbot
    have : ¬ ((0 : EReal) ≤ (⊥ : EReal)) := by simp
    exact this (by simpa [hbot] using hf_nonneg x)
  have hftop : f x ≠ ⊤ := by
    intro htop
    have hfy' := hfy
    simp [htop] at hfy'
  have hyoung :
      ((xStar x : ℝ) : EReal) ≤ f x + fenchelConjugateBilin p f xStar :=
    by
      -- Use Fenchel–Young on the finite point `x` (since `f x ≤ α < ⊤`).
      simpa [add_comm, add_left_comm, add_assoc] using
        (section14_eval_le_add_fenchelConjugate (E := E) (f := f) x xStar hfbot hftop)
  have hsum :
      f x + fenchelConjugateBilin p f xStar ≤ (α : EReal) + (α : EReal) :=
    add_le_add hfy (by simpa [p] using hxStar)
  have hleE :
      ((xStar x : ℝ) : EReal) ≤ (α : EReal) + (α : EReal) :=
    le_trans hyoung hsum
  have hleR : xStar x ≤ 2 * α := by
    have : ((xStar x : ℝ) : EReal) ≤ ((2 * α : ℝ) : EReal) := by
      simpa [two_mul] using hleE
    exact (EReal.coe_le_coe_iff).1 this
  have hmul :
      (α⁻¹ : ℝ) * xStar x ≤ (α⁻¹ : ℝ) * (2 * α) :=
    mul_le_mul_of_nonneg_left hleR (le_of_lt (inv_pos.2 hα))
  -- Simplify `α⁻¹ * (2 * α) = 2`.
  have hα0 : (α : ℝ) ≠ 0 := ne_of_gt hα
  have : (α⁻¹ : ℝ) * xStar x ≤ (2 : ℝ) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (le_trans hmul (by
      have : (α⁻¹ : ℝ) * (2 * α) = (2 : ℝ) := by
        field_simp [hα0]
      simp [this]))
  simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using this

/-- The polar of the primal `α`-sublevel set is contained in the `α⁻¹`-scaled `α`-sublevel set of
the conjugate, for a convex function vanishing at `0`. -/
lemma section14_polar_sublevel_subset_inv_smul_sublevel_fenchelConjugate
    {f : E → EReal} (hf_nonneg : ∀ x, (0 : EReal) ≤ f x) (hf_conv : ConvexERealFunction (F := E) f)
    (hf0 : f 0 = 0) {α : ℝ} (hα : 0 < α) :
    polar (E := E) {x : E | f x ≤ (α : EReal)} ⊆
      (α⁻¹ : ℝ) •
        {xStar : Module.Dual ℝ E |
            fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f xStar ≤
              (α : EReal)} := by
  classical
  let p := LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)
  set C : Set E := {x : E | f x ≤ (α : EReal)}
  intro φ hφ
  have hφC : ∀ x ∈ C, φ x ≤ 1 := (mem_polar_iff (E := E) (C := C) (φ := φ)).1 (by simpa [C] using hφ)
  -- It suffices to show `fenchelConjugateBilin p f (α • φ) ≤ α`.
  have hconj :
      fenchelConjugateBilin p f (α • φ) ≤ (α : EReal) := by
    -- Use the pointwise inequality characterization of `fenchelConjugateBilin ≤ α`.
    refine (section14_fenchelConjugate_le_iff_forall (E := E) (p := p) (f := f)
      (xStar := (α • φ)) (μStar := (α : EReal))).2 ?_
    intro x
    -- Prove `p x (α•φ) - f x ≤ α` by showing `p x (α•φ) ≤ f x + α`.
    by_cases hxC : x ∈ C
    · have hφx : φ x ≤ 1 := hφC x hxC
      have hmulR : α * φ x ≤ α := by nlinarith [hφx]
      have hmulE : ((α * φ x : ℝ) : EReal) ≤ (α : EReal) := EReal.coe_le_coe hmulR
      have : (α : EReal) ≤ f x + (α : EReal) := le_add_of_nonneg_left (hf_nonneg x)
      have hle : ((α * φ x : ℝ) : EReal) ≤ f x + (α : EReal) := le_trans hmulE this
      have hsub : (p x (α • φ) : EReal) - f x ≤ (α : EReal) := by
        refine EReal.sub_le_of_le_add' ?_
        simpa [p, smul_eq_mul, add_comm, add_left_comm, add_assoc] using hle
      simpa [p] using hsub
    · -- If `x ∉ C`, use a scaling argument from convexity (or triviality if `f x = ⊤`).
      have hxC' : ¬ f x ≤ (α : EReal) := by
        intro hxle
        exact hxC (by simpa [C] using hxle)
      cases hfx : f x using EReal.rec with
      | bot =>
          exfalso
          have : (0 : EReal) ≤ (⊥ : EReal) := by simpa [hfx] using hf_nonneg x
          simp at this
      | top =>
          -- `a - ⊤ = ⊥`, hence the inequality is trivial.
          simp
      | coe r =>
          have hr : α < r := by
            have : ¬ ((r : ℝ) ≤ α) := by
              intro hrle
              apply hxC'
              simpa [hfx] using (EReal.coe_le_coe hrle)
            exact lt_of_not_ge this
          have hrpos : 0 < r := lt_trans hα hr
          let t : ℝ := α / r
          have ht_mul : t * r = α := by
            have hr0 : (r : ℝ) ≠ 0 := ne_of_gt hrpos
            simp [t, div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hr0]
          have ht0 : 0 ≤ t := by
            have : 0 ≤ α / r := div_nonneg (le_of_lt hα) (le_of_lt hrpos)
            simpa [t] using this
          have ht1 : t ≤ 1 := by
            have : t < 1 := by
              have : α / r < 1 := (div_lt_one hrpos).2 hr
              simpa [t] using this
            exact le_of_lt this
          have ha : 0 ≤ (1 - t) := sub_nonneg.2 ht1
          have hab : (1 - t) + t = 1 := by ring
          have hftx : f (t • x) ≤ (α : EReal) := by
            have hconv :
                f ((1 - t) • (0 : E) + t • x) ≤
                  ((1 - t : ℝ) : EReal) * f (0 : E) + ((t : ℝ) : EReal) * f x :=
              hf_conv (x := (0 : E)) (y := x) (a := (1 - t)) (b := t) ha ht0 hab
            have hconv' : f (t • x) ≤ ((t : ℝ) : EReal) * f x := by
              simpa [hf0, add_comm, add_left_comm, add_assoc] using hconv
            have hconv'' : f (t • x) ≤ ((t : ℝ) : EReal) * (r : EReal) := by
              simpa [hfx] using hconv'
            have ht_mulE : ((t : ℝ) : EReal) * (r : EReal) = (α : EReal) := by
              calc
                ((t : ℝ) : EReal) * (r : EReal) = ((t * r : ℝ) : EReal) := by
                  simp
                _ = (α : EReal) := by simp [ht_mul]
            simpa [ht_mulE] using hconv''
          have htC : t • x ∈ C := by
            simpa [C] using hftx
          have hφtx : φ (t • x) ≤ 1 := hφC (t • x) htC
          have hφx : t * φ x ≤ 1 := by
            simpa [t, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hφtx
          have hmul' : r * (t * φ x) ≤ r := by
            have := mul_le_mul_of_nonneg_left hφx (le_of_lt hrpos)
            simpa [mul_assoc, mul_one] using this
          have hrt : r * t = α := by
            simpa [mul_comm] using ht_mul
          have hαφ : α * φ x ≤ r := by
            have hmul'' : (r * t) * φ x ≤ r := by
              simpa [mul_assoc] using hmul'
            simpa [hrt] using hmul''
          have hle : ((α * φ x : ℝ) : EReal) ≤ (r : EReal) + (α : EReal) := by
            have hcoe : ((α * φ x : ℝ) : EReal) ≤ (r : EReal) := EReal.coe_le_coe hαφ
            have h0α : (0 : EReal) ≤ (α : EReal) := by
              simpa using (EReal.coe_le_coe (show (0 : ℝ) ≤ α from le_of_lt hα))
            have : (r : EReal) ≤ (r : EReal) + (α : EReal) := le_add_of_nonneg_right h0α
            exact le_trans hcoe this
          have hsub' : ((α * φ x : ℝ) : EReal) - (r : EReal) ≤ (α : EReal) :=
            EReal.sub_le_of_le_add' hle
          simpa [p, hfx, smul_eq_mul, add_comm, add_left_comm, add_assoc] using hsub'
  -- Conclude the set inclusion by choosing `α • φ` as the witness.
  refine ⟨α • φ, ?_, ?_⟩
  · exact hconj
  · have hα0 : (α : ℝ) ≠ 0 := ne_of_gt hα
    simp [smul_smul, inv_mul_cancel₀ hα0]

/-- Theorem 14.7. Let `f` be a non-negative closed convex function which vanishes at the origin.
Then the Fenchel–Legendre conjugate `f*` (with respect to the evaluation pairing) is also
non-negative and vanishes at the origin. Moreover, for `0 < α < ∞` one has

`{x | f x ≤ α}^∘ = α⁻¹ • {x★ | f* x★ ≤ α} ⊆ 2 • {x | f x ≤ α}^∘`,

where `^∘` denotes the polar of a set (modeled here as `polar`). -/
theorem polar_sublevel_eq_inv_smul_sublevel_fenchelConjugate_and_subset_two_smul
    [TopologicalSpace E] {f : E → EReal} (hf_nonneg : ∀ x, (0 : EReal) ≤ f x)
    (hf_conv : ConvexERealFunction (F := E) f)
    (hf0 : f 0 = 0) {α : ℝ} (hα : 0 < α) :
    let p := LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)
    let fstar := fenchelConjugateBilin p f
    (∀ xStar : Module.Dual ℝ E, (0 : EReal) ≤ fstar xStar) ∧
      fstar 0 = 0 ∧
        polar (E := E) {x : E | f x ≤ (α : EReal)} ⊆
            (α⁻¹ : ℝ) • {xStar : Module.Dual ℝ E | fstar xStar ≤ (α : EReal)} ∧
          (α⁻¹ : ℝ) • {xStar : Module.Dual ℝ E | fstar xStar ≤ (α : EReal)} ⊆
            (2 : ℝ) • polar (E := E) {x : E | f x ≤ (α : EReal)} := by
  classical
  dsimp
  have hnonneg0 :=
    section14_fenchelConjugate_nonneg_of_nonneg_and_zero (E := E) (f := f) hf_nonneg hf0
  refine ⟨hnonneg0.1, hnonneg0.2, ?_, ?_⟩
  · simpa using
      (section14_polar_sublevel_subset_inv_smul_sublevel_fenchelConjugate (E := E) (f := f)
        hf_nonneg hf_conv hf0 hα)
  · simpa using
      (section14_inv_smul_sublevel_fenchelConjugate_subset_two_smul_polar_sublevel (E := E)
        (f := f) hf_nonneg (α := α) hα)

end Section14
end Chap03
