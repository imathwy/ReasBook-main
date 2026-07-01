/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yifan Bai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part2

open scoped Pointwise

section Chap01
section Section05

/-- Text 5.4.1.6: For any functions `f_1` and `f_2` from `R^n` to `[-infty, +infty]`
(not necessarily convex nor proper), `(f_1 □ f_2)(x)` can be defined directly in
terms of addition of epigraphs:
`(f_1 □ f_2)(x) = inf { μ | (x, μ) ∈ (epi f_1 + epi f_2) }`. -/
theorem infimalConvolution_eq_sInf_epigraph_add {n : Nat}
    (f1 f2 : (Fin n → Real) → EReal) :
    ∀ x : Fin n → Real,
      infimalConvolution f1 f2 x =
        sInf { z : EReal |
          ∃ x1 x2 : Fin n → Real, x1 + x2 = x ∧ z = f1 x1 + f2 x2 } := by
  intro x
  rfl

/-- Text 5.4.2: Let `f : R^n → R ∪ {+infty}` be convex and `lam ∈ [0, +infty)`.
Define the right scalar multiple `f lam` to be the convex function obtained from
Theorem 5.3 by taking `F = lam (epi f) ⊆ R^{n+1}`. -/
noncomputable def rightScalarMultiple {n : Nat} (f : (Fin n → Real) → EReal) (lam : Real) :
    (Fin n → Real) → EReal :=
  fun x =>
    sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ |
      (x, μ) ∈
        Set.image (fun p : (Fin n → Real) × Real => lam • p)
          (epigraph (Set.univ : Set (Fin n → Real)) f) })

/-- Membership in the scaled epigraph fiber for positive scaling. -/
lemma mem_image_smul_epigraph_iff {n : Nat} {f : (Fin n → Real) → EReal} {lam : Real}
    (hlam : 0 < lam) {x : Fin n → Real} {μ : Real} :
    (x, μ) ∈
        Set.image (fun p : (Fin n → Real) × Real => lam • p)
          (epigraph (Set.univ : Set (Fin n → Real)) f) ↔
      f (lam⁻¹ • x) ≤ ((μ / lam : Real) : EReal) := by
  constructor
  · intro h
    rcases h with ⟨⟨y, ν⟩, hp, hxy⟩
    have hy : f y ≤ (ν : EReal) := (mem_epigraph_univ_iff).1 hp
    have hx : x = lam • y := by
      have hx' := congrArg Prod.fst hxy
      simpa using hx'.symm
    have hμ : μ = lam * ν := by
      have hμ' := congrArg Prod.snd hxy
      have hμ'' : lam * ν = μ := by
        simpa [smul_eq_mul] using hμ'
      exact hμ''.symm
    simpa [hx, hμ, smul_smul, inv_mul_cancel, hlam.ne', mul_div_cancel_left₀] using hy
  · intro h
    refine ⟨(lam⁻¹ • x, μ / lam), (mem_epigraph_univ_iff).2 h, ?_⟩
    ext
    · simp [smul_smul, hlam.ne']
    · have hne : lam ≠ 0 := ne_of_gt hlam
      simp [smul_eq_mul]
      field_simp [hne]

/-- The infimum of all real coercions in `EReal` is `⊥`. -/
lemma sInf_image_real_univ :
    sInf ((fun μ : ℝ => (μ : EReal)) '' (Set.univ : Set ℝ)) = (⊥ : EReal) := by
  apply ereal_eq_bot_of_le_all_coe
  intro μ
  refine sInf_le ?_
  exact ⟨μ, by simp, rfl⟩

/-- The infimum over a scaled epigraph fiber equals the scaled value of `f`. -/
lemma sInf_fiber_smul_eq {n : Nat} {f : (Fin n → Real) → EReal} {lam : Real}
    (hlam : 0 < lam) (x : Fin n → Real) :
    sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ |
      (x, μ) ∈
        Set.image (fun p : (Fin n → Real) × Real => lam • p)
          (epigraph (Set.univ : Set (Fin n → Real)) f) }) =
      (lam : EReal) * f (lam⁻¹ • x) := by
  classical
  set y : Fin n → Real := lam⁻¹ • x
  set a : EReal := f y
  have hset :
      { μ : ℝ |
        (x, μ) ∈
          Set.image (fun p : (Fin n → Real) × Real => lam • p)
            (epigraph (Set.univ : Set (Fin n → Real)) f) } =
        { μ : ℝ | a ≤ ((μ / lam : Real) : EReal) } := by
    ext μ
    simpa [y, a] using
      (mem_image_smul_epigraph_iff (f := f) (lam := lam) (x := x) (μ := μ) hlam)
  cases ha : a using EReal.rec with
  | bot =>
      have hset' : { μ : ℝ | a ≤ ((μ / lam : Real) : EReal) } = (Set.univ : Set ℝ) := by
        ext μ; simp [ha]
      calc
        sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ |
            (x, μ) ∈
              Set.image (fun p : (Fin n → Real) × Real => lam • p)
                (epigraph (Set.univ : Set (Fin n → Real)) f) }) =
            sInf ((fun μ : ℝ => (μ : EReal)) '' (Set.univ : Set ℝ)) := by
              rw [hset, hset']
        _ = (⊥ : EReal) := sInf_image_real_univ
        _ = (lam : EReal) * ⊥ := by
              simp [EReal.coe_mul_bot_of_pos hlam]
  | coe r =>
      have hset' :
          { μ : ℝ | a ≤ ((μ / lam : Real) : EReal) } = { μ : ℝ | lam * r ≤ μ } := by
        ext μ
        constructor
        · intro h
          have h' : r ≤ μ / lam := by
            have h'': (r : EReal) ≤ ((μ / lam : Real) : EReal) := by
              simpa [ha] using h
            exact (EReal.coe_le_coe_iff).1 h''
          have hmul : r * lam ≤ (μ / lam) * lam :=
            (mul_le_mul_of_nonneg_right h' (le_of_lt hlam))
          have hne : lam ≠ 0 := ne_of_gt hlam
          have h'' : r * lam ≤ μ := by
            simpa [div_eq_mul_inv, mul_assoc, inv_mul_cancel, hne] using hmul
          simpa [mul_comm] using h''
        · intro h
          have h' : r * lam ≤ μ := by simpa [mul_comm] using h
          have hne : lam ≠ 0 := ne_of_gt hlam
          have hmul : r * lam * lam⁻¹ ≤ μ * lam⁻¹ :=
            (mul_le_mul_of_nonneg_right h' (le_of_lt (inv_pos.2 hlam)))
          have h'' : r ≤ μ / lam := by
            simpa [div_eq_mul_inv, mul_assoc, inv_mul_cancel, hne] using hmul
          have hE : (r : EReal) ≤ ((μ / lam : Real) : EReal) :=
            (EReal.coe_le_coe_iff).2 h''
          simpa [ha] using hE
      set S' : Set EReal :=
        (fun μ : ℝ => (μ : EReal)) '' { μ : ℝ | lam * r ≤ μ }
      have hmem : ((lam * r : Real) : EReal) ∈ S' := by
        refine ⟨lam * r, ?_, rfl⟩
        simp
      have hle : (lam * r : EReal) ≤ sInf S' := by
        refine le_sInf ?_
        intro z hz
        rcases hz with ⟨μ, hμ, rfl⟩
        exact (EReal.coe_le_coe_iff).2 hμ
      have hge : sInf S' ≤ (lam * r : EReal) := sInf_le hmem
      have hSinf : sInf S' = (lam * r : EReal) := le_antisymm hge hle
      calc
        sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ |
            (x, μ) ∈
              Set.image (fun p : (Fin n → Real) × Real => lam • p)
                (epigraph (Set.univ : Set (Fin n → Real)) f) }) =
            sInf S' := by
              rw [hset, hset']
        _ = (lam * r : EReal) := hSinf
        _ = (lam : EReal) * (r : EReal) := by
              simp
  | top =>
      have hset' : { μ : ℝ | a ≤ ((μ / lam : Real) : EReal) } = (∅ : Set ℝ) := by
        ext μ; simp [ha]
      calc
        sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ |
            (x, μ) ∈
              Set.image (fun p : (Fin n → Real) × Real => lam • p)
                (epigraph (Set.univ : Set (Fin n → Real)) f) }) =
            sInf (∅ : Set EReal) := by
              rw [hset, hset']
              simp
        _ = (⊤ : EReal) := by simp
        _ = (lam : EReal) * ⊤ := by
              simp [EReal.coe_mul_top_of_pos hlam]

/-- The zero scaling of a nonempty epigraph is the singleton `{(0,0)}`. -/
lemma image_zero_smul_epigraph_eq_singleton {n : Nat} {f : (Fin n → Real) → EReal}
    (hne : Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) f)) :
    Set.image (fun p : (Fin n → Real) × Real => (0 : Real) • p)
      (epigraph (Set.univ : Set (Fin n → Real)) f) =
      {(0 : (Fin n → Real) × Real)} := by
  ext p
  constructor
  · intro hp
    rcases hp with ⟨q, hq, rfl⟩
    simp
  · intro hp
    rcases hne with ⟨q, hq⟩
    simp [Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨q, hq, ?_⟩
    simp

/-- Evaluate the zero scalar multiple when the epigraph is nonempty. -/
lemma rightScalarMultiple_zero_eval {n : Nat} {f : (Fin n → Real) → EReal}
    (hne : Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) f)) :
    ∀ x : Fin n → Real,
      rightScalarMultiple f 0 x = (if x = 0 then (0 : EReal) else ⊤) := by
  classical
  intro x
  have himage :
      Set.image (fun p : (Fin n → Real) × Real => (0 : Real) • p)
          (epigraph (Set.univ : Set (Fin n → Real)) f) =
        {(0 : (Fin n → Real) × Real)} :=
    image_zero_smul_epigraph_eq_singleton (f := f) hne
  by_cases hx : x = 0
  · subst hx
    have hset :
        { μ : ℝ | ((0 : Fin n → Real), μ) ∈ ({(0 : (Fin n → Real) × Real)} : Set _) } =
          ({0} : Set ℝ) := by
      ext μ; simp
    rw [rightScalarMultiple, himage, hset]
    simp
  · have hset :
        { μ : ℝ | (x, μ) ∈ ({(0 : (Fin n → Real) × Real)} : Set _) } = (∅ : Set ℝ) := by
        ext μ; simp [hx]
    rw [rightScalarMultiple, himage, hset]
    simp [hx]

/-- Text 5.4.3 (i): Let `f` be convex on `ℝ^n`. If `λ > 0`, then for all `x`,
`(f λ)(x) = λ f (λ^{-1} x)`. -/
theorem rightScalarMultiple_pos {n : Nat} {f : (Fin n → Real) → EReal} {lam : Real}
    (_hf : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f) (hlam : 0 < lam) :
    ∀ x : Fin n → Real,
      rightScalarMultiple f lam x = ((lam : Real) : EReal) * f (lam⁻¹ • x) := by
  intro x
  simpa [rightScalarMultiple] using
    (sInf_fiber_smul_eq (f := f) (lam := lam) (x := x) hlam)

/-- Text 5.4.3 (ii): Let `f` be convex on `ℝ^n`. If `λ = 0` and `f` is not identically
`+∞`, then for all `x`, `(f 0)(x) = δ(x | 0)`. (Trivially, if `f ≡ +∞` then `f 0 = f`.) -/
theorem rightScalarMultiple_zero_eq_indicator {n : Nat} {f : (Fin n → Real) → EReal}
    (_hf : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f)
    (hfinite : ∃ x, f x ≠ (⊤ : EReal)) :
    rightScalarMultiple f 0 = indicatorFunction ({0} : Set (Fin n → Real)) := by
  funext x
  rcases hfinite with ⟨x0, hx0⟩
  have hx0' : x0 ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
    have hx0lt : f x0 < (⊤ : EReal) := (lt_top_iff_ne_top).2 hx0
    have hx0mem : x0 ∈ {x | x ∈ (Set.univ : Set (Fin n → Real)) ∧ f x < (⊤ : EReal)} :=
      ⟨by simp, hx0lt⟩
    simpa [effectiveDomain_eq] using hx0mem
  have hne_eff :
      Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → Real)) f) := ⟨x0, hx0'⟩
  have hne_epi :
      Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) f) :=
    (nonempty_epigraph_iff_nonempty_effectiveDomain (S := Set.univ) (f := f)).2 hne_eff
  have hval := rightScalarMultiple_zero_eval (f := f) hne_epi x
  simpa [indicatorFunction_singleton_simp] using hval

/-- Text 5.4.4: A function `f : ℝ^n → ℝ ∪ {+∞}` is positively homogeneous if
`f (α x) = α f x` for all `x` and all `α > 0`. -/
lemma positivelyHomogeneous_iff {n : Nat} {f : (Fin n → Real) → EReal} :
    PositivelyHomogeneous f ↔
      ∀ x : Fin n → Real, ∀ α : Real, 0 < α → f (α • x) = (α : EReal) * f x := by
  rfl

/-- Simplify `lam⁻¹ • (lam • x)` when `lam ≠ 0`. -/
lemma smul_inv_smul_simplify {n : Nat} {lam : Real} {x : Fin n → Real} (hne : lam ≠ 0) :
    lam⁻¹ • (lam • x) = x := by
  simp [smul_smul, inv_mul_cancel₀ hne]

/-- If `f` is positively homogeneous, all positive right scalar multiples equal `f`. -/
lemma rightScalarMultiple_eq_self_of_posHom {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f)
    (hpos : PositivelyHomogeneous f) :
    ∀ lam : Real, 0 < lam → rightScalarMultiple f lam = f := by
  intro lam hlam
  funext x
  have hne : lam ≠ 0 := ne_of_gt hlam
  have hpos' : f x = (lam : EReal) * f (lam⁻¹ • x) := by
    simpa [smul_smul, mul_inv_cancel₀ hne] using
      (hpos (lam⁻¹ • x) lam hlam)
  calc
    rightScalarMultiple f lam x =
        (lam : EReal) * f (lam⁻¹ • x) := rightScalarMultiple_pos (f := f) (lam := lam) hf hlam x
    _ = f x := by
        simpa using hpos'.symm

/-- If every positive right scalar multiple equals `f`, then `f` is positively homogeneous. -/
lemma posHom_of_rightScalarMultiple_eq_self {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f)
    (hscale : ∀ lam : Real, 0 < lam → rightScalarMultiple f lam = f) :
    PositivelyHomogeneous f := by
  intro x lam hlam
  have hne : lam ≠ 0 := ne_of_gt hlam
  have hEq := congrArg (fun g => g (lam • x)) (hscale lam hlam)
  have hright := rightScalarMultiple_pos (f := f) (lam := lam) hf hlam (lam • x)
  calc
    f (lam • x) = rightScalarMultiple f lam (lam • x) := by
      simpa using hEq.symm
    _ = (lam : EReal) * f (lam⁻¹ • (lam • x)) := hright
    _ = (lam : EReal) * f x := by
      simp [smul_inv_smul_simplify (x := x) hne]

/-- Text 5.4.5 (Characterization via right scalar multiplication): A convex function `f`
is positively homogeneous if and only if `f λ = f` for every `λ > 0`, where `f λ`
denotes the right scalar multiple. -/
theorem positivelyHomogeneous_iff_rightScalarMultiple_eq {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hf : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f) :
    PositivelyHomogeneous f ↔
      ∀ lam : Real, 0 < lam → rightScalarMultiple f lam = f := by
  constructor
  · intro hpos
    exact rightScalarMultiple_eq_self_of_posHom (hf := hf) hpos
  · intro hscale
    exact posHom_of_rightScalarMultiple_eq_self (hf := hf) hscale

/-- Text 5.4.6 (Cone generated by an epigraph): Let `h : ℝ^n → ℝ ∪ {+∞}` be convex.
The convex cone generated by `epi h` is the smallest convex cone `F ⊆ ℝ^{n+1}`
containing `epi h`. Equivalently,
`F = cone (epi h) := conv ({0} ∪ ⋃_{λ > 0} λ • (epi h))`. -/
def convexConeGeneratedEpigraph {n : Nat} (h : (Fin n → Real) → EReal) :
    Set ((Fin n → Real) × Real) :=
  Set.insert (0 : (Fin n → Real) × Real)
    ((ConvexCone.hull ℝ (epigraph (Set.univ : Set (Fin n → Real)) h)) :
      Set ((Fin n → Real) × Real))

/-- Text 5.4.7 (Positively homogeneous convex function generated by `h`): Let
`h : ℝ^n → ℝ ∪ {+∞}` be convex and let `F = cone (epi h) ⊆ ℝ^{n+1}`. Define
`f x = inf { μ | (x, μ) ∈ F }` (as in Theorem 5.3). The function `f` is called the
positively homogeneous convex function generated by `h`. -/
noncomputable def positivelyHomogeneousConvexFunctionGenerated {n : Nat}
    (h : (Fin n → Real) → EReal) : (Fin n → Real) → EReal :=
  fun x =>
    sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ | (x, μ) ∈ convexConeGeneratedEpigraph h })

/-- The generated epigraph is closed under positive scaling. -/
lemma smul_mem_convexConeGeneratedEpigraph {n : Nat} {h : (Fin n → Real) → EReal}
    {t : Real} (ht : 0 < t) {p : (Fin n → Real) × Real} :
    p ∈ convexConeGeneratedEpigraph h → t • p ∈ convexConeGeneratedEpigraph h := by
  classical
  intro hp
  have hp' :
      p = 0 ∨ p ∈
        (ConvexCone.hull ℝ (epigraph (Set.univ : Set (Fin n → Real)) h)) := by
    simpa [convexConeGeneratedEpigraph] using hp
  rcases hp' with rfl | hp'
  · change t • (0 : (Fin n → Real) × Real) ∈
        Set.insert 0 (ConvexCone.hull ℝ (epigraph (Set.univ : Set (Fin n → Real)) h))
    refine (Set.mem_insert_iff).2 ?_
    left
    simp
  · have hmem :
        t • p ∈
          (ConvexCone.hull ℝ (epigraph (Set.univ : Set (Fin n → Real)) h)) :=
      ConvexCone.smul_mem
        (C := ConvexCone.hull ℝ (epigraph (Set.univ : Set (Fin n → Real)) h)) ht hp'
    change t • p ∈
      Set.insert 0 (ConvexCone.hull ℝ (epigraph (Set.univ : Set (Fin n → Real)) h))
    refine (Set.mem_insert_iff).2 (Or.inr hmem)

/-- The generated epigraph is closed under addition. -/
lemma add_mem_convexConeGeneratedEpigraph {n : Nat} {h : (Fin n → Real) → EReal}
    {p q : (Fin n → Real) × Real} :
    p ∈ convexConeGeneratedEpigraph h →
    q ∈ convexConeGeneratedEpigraph h →
    p + q ∈ convexConeGeneratedEpigraph h := by
  classical
  intro hp hq
  have hp' :
      p = 0 ∨ p ∈
        (ConvexCone.hull ℝ (epigraph (Set.univ : Set (Fin n → Real)) h)) := by
    simpa [convexConeGeneratedEpigraph] using hp
  have hq' :
      q = 0 ∨ q ∈
        (ConvexCone.hull ℝ (epigraph (Set.univ : Set (Fin n → Real)) h)) := by
    simpa [convexConeGeneratedEpigraph] using hq
  rcases hp' with rfl | hp'
  · simpa [convexConeGeneratedEpigraph] using hq
  rcases hq' with rfl | hq'
  · have hp'' :
        p ∈ Set.insert 0 (ConvexCone.hull ℝ (epigraph (Set.univ : Set (Fin n → Real)) h)) :=
      (Set.mem_insert_iff).2 (Or.inr hp')
    simpa [convexConeGeneratedEpigraph] using hp''
  have hsum :
      p + q ∈ (ConvexCone.hull ℝ (epigraph (Set.univ : Set (Fin n → Real)) h)) :=
    ConvexCone.add_mem (C := ConvexCone.hull ℝ (epigraph (Set.univ : Set (Fin n → Real)) h)) hp'
      hq'
  change p + q ∈
    Set.insert 0 (ConvexCone.hull ℝ (epigraph (Set.univ : Set (Fin n → Real)) h))
  exact (Set.mem_insert_iff).2 (Or.inr hsum)

/-- The generated epigraph forms a convex cone. -/
def convexCone_generatedEpigraph {n : Nat} (h : (Fin n → Real) → EReal) :
    ConvexCone ℝ ((Fin n → Real) × Real) :=
  { carrier := convexConeGeneratedEpigraph h
    smul_mem' := by
      intro t ht p hp
      exact smul_mem_convexConeGeneratedEpigraph (h := h) ht hp
    add_mem' := by
      intro p hp q hq
      exact add_mem_convexConeGeneratedEpigraph (h := h) hp hq }

/-- Multiplying by a positive real preserves order in `EReal`. -/
lemma ereal_mul_le_mul_of_pos_left_general {t : Real} (ht : 0 < t) {x y : EReal} (h : x ≤ y) :
    (t : EReal) * x ≤ (t : EReal) * y := by
  cases hx : x using EReal.rec with
  | bot =>
      cases hy : y using EReal.rec with
      | bot =>
          simp [EReal.coe_mul_bot_of_pos ht]
      | coe r =>
          simp [EReal.coe_mul_bot_of_pos ht]
      | top =>
          simp [EReal.coe_mul_bot_of_pos ht, EReal.coe_mul_top_of_pos ht]
  | coe r =>
      cases hy : y using EReal.rec with
      | bot =>
          simp [hx, hy] at h
      | coe s =>
          simp [hx, hy] at h
          have hle : r ≤ s := h
          have hmul : t * r ≤ t * s := mul_le_mul_of_nonneg_left hle (le_of_lt ht)
          have hmul' : ((t * r : Real) : EReal) ≤ ((t * s : Real) : EReal) :=
            (EReal.coe_le_coe_iff).2 hmul
          simpa [EReal.coe_mul] using hmul'
      | top =>
          simp [EReal.coe_mul_top_of_pos ht]
  | top =>
      cases hy : y using EReal.rec with
      | bot =>
          simp [hx, hy] at h
      | coe s =>
          simp [hx, hy] at h
      | top =>
          simp [EReal.coe_mul_top_of_pos ht]

/-- Positive scaling by `t` and `t⁻¹` cancels on `EReal`. -/
lemma ereal_mul_inv_smul {t : Real} (ht : 0 < t) (x : EReal) :
    (t : EReal) * ((t⁻¹ : EReal) * x) = x := by
  cases x using EReal.rec with
  | bot =>
      rw [← EReal.coe_inv t]
      simp [EReal.coe_mul_bot_of_pos ht,
        EReal.coe_mul_bot_of_pos (x := t⁻¹) (inv_pos.mpr ht)]
  | coe r =>
      have ht0 : t ≠ 0 := ne_of_gt ht
      rw [← EReal.coe_inv t]
      have hreal : t * (t⁻¹ * r) = r := by
        simpa using (mul_inv_cancel_left₀ (a := t) (b := r) ht0)
      simp [← EReal.coe_mul, hreal]
  | top =>
      rw [← EReal.coe_inv t]
      simp [EReal.coe_mul_top_of_pos ht,
        EReal.coe_mul_top_of_pos (x := t⁻¹) (inv_pos.mpr ht)]

/-- Scaling a real set scales the infimum of its `EReal` image. -/
lemma sInf_image_real_smul {S : Set ℝ} {t : Real} (ht : 0 < t) :
    sInf ((fun μ : ℝ => (μ : EReal)) '' (t • S)) =
      (t : EReal) * sInf ((fun μ : ℝ => (μ : EReal)) '' S) := by
  classical
  set A : Set EReal := (fun μ : ℝ => (μ : EReal)) '' S
  set B : Set EReal := (fun μ : ℝ => (μ : EReal)) '' (t • S)
  have hB : B = (fun z : EReal => (t : EReal) * z) '' A := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨μ, hμ, rfl⟩
      rcases hμ with ⟨μ0, hμ0, rfl⟩
      refine ⟨(μ0 : EReal), ?_, ?_⟩
      · exact ⟨μ0, hμ0, rfl⟩
      · simp [smul_eq_mul, EReal.coe_mul]
    · intro hz
      rcases hz with ⟨z0, hz0, rfl⟩
      rcases hz0 with ⟨μ0, hμ0, rfl⟩
      refine ⟨t * μ0, ?_, ?_⟩
      · exact ⟨μ0, hμ0, by simp [smul_eq_mul]⟩
      · simp [EReal.coe_mul]
  have hle : (t : EReal) * sInf A ≤ sInf B := by
    refine le_sInf ?_
    intro z hz
    rcases (by simpa [hB] using hz) with ⟨z0, hz0, rfl⟩
    rcases hz0 with ⟨μ, hμ, rfl⟩
    have hleA : sInf A ≤ (μ : EReal) := sInf_le ⟨μ, hμ, rfl⟩
    simpa [EReal.coe_mul] using (ereal_mul_le_mul_of_pos_left (t := t) ht hleA)
  have hle' : sInf B ≤ (t : EReal) * sInf A := by
    have htinv : 0 < t⁻¹ := inv_pos.mpr ht
    have hleinv : (t⁻¹ : EReal) * sInf B ≤ sInf A := by
      refine le_sInf ?_
      intro z hz
      rcases hz with ⟨μ, hμS, rfl⟩
      have hmemB : ((t * μ : Real) : EReal) ∈ B := by
        refine ⟨t * μ, ?_, rfl⟩
        exact ⟨μ, hμS, by simp [smul_eq_mul]⟩
      have hleB : sInf B ≤ ((t * μ : Real) : EReal) := sInf_le hmemB
      have hmul :
          (t⁻¹ : EReal) * sInf B ≤ ((t⁻¹ * (t * μ) : Real) : EReal) :=
        ereal_mul_le_mul_of_pos_left (t := t⁻¹) htinv hleB
      have hmul' : t⁻¹ * (t * μ) = μ := by
        field_simp [ht.ne']
      simpa [hmul'] using hmul
    have hmul := ereal_mul_le_mul_of_pos_left_general (t := t) ht hleinv
    simpa [ereal_mul_inv_smul (t := t) ht (x := sInf B)] using hmul
  exact le_antisymm hle' hle

/-- The inf-section of a set closed under positive scaling is positively homogeneous. -/
lemma posHom_of_inf_section_of_cone {n : Nat} {F : Set ((Fin n → Real) × Real)}
    (hcone : ∀ t : Real, 0 < t →
      Set.image (fun p : (Fin n → Real) × Real => t • p) F ⊆ F) :
    PositivelyHomogeneous (fun x =>
      sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ | (x, μ) ∈ F })) := by
  intro x t ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  set S : Set ℝ := { μ : ℝ | (x, μ) ∈ F }
  set St : Set ℝ := { μ : ℝ | (t • x, μ) ∈ F }
  have hset : St = t • S := by
    ext μ
    constructor
    · intro hμ
      have hsubset := hcone t⁻¹ (inv_pos.mpr ht)
      have hmem' : (t⁻¹) • (t • x, μ) ∈ F :=
        hsubset ⟨(t • x, μ), hμ, rfl⟩
      have hmem : (x, t⁻¹ • μ) ∈ F := by
        simpa [smul_smul, inv_mul_cancel₀ ht0] using hmem'
      have hmemS : t⁻¹ • μ ∈ S := by
        simpa [S] using hmem
      exact (Set.mem_smul_set_iff_inv_smul_mem₀ (ha := ht0) S μ).2 hmemS
    · intro hμ
      have hmemS : t⁻¹ • μ ∈ S :=
        (Set.mem_smul_set_iff_inv_smul_mem₀ (ha := ht0) S μ).1 hμ
      have hmemF : (x, t⁻¹ • μ) ∈ F := by
        simpa [S] using hmemS
      have hsubset := hcone t ht
      have hmem' : t • (x, t⁻¹ • μ) ∈ F :=
        hsubset ⟨(x, t⁻¹ • μ), hmemF, rfl⟩
      have hmem'' : (t • x, μ) ∈ F := by
        simpa [smul_smul, smul_eq_mul, mul_inv_cancel_left₀ ht0] using hmem'
      simpa [St] using hmem''
  have hinf :
      sInf ((fun μ : ℝ => (μ : EReal)) '' St) =
        (t : EReal) * sInf ((fun μ : ℝ => (μ : EReal)) '' S) := by
    rw [hset]
    exact (sInf_image_real_smul (S := S) (t := t) ht)
  simpa [S, St] using hinf

/-- The epigraph of a convex positively homogeneous function is closed under addition. -/
lemma add_mem_epigraph_of_posHom_convex {n : Nat} {f : (Fin n → Real) → EReal}
    (hpos : PositivelyHomogeneous f)
    (hconv : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f)
    {p q : (Fin n → Real) × Real}
    (hp : p ∈ epigraph (Set.univ : Set (Fin n → Real)) f)
    (hq : q ∈ epigraph (Set.univ : Set (Fin n → Real)) f) :
    p + q ∈ epigraph (Set.univ : Set (Fin n → Real)) f := by
  rcases p with ⟨x, μ⟩
  rcases q with ⟨y, ν⟩
  have hx2 : (2 : Real) • (x, μ) ∈ epigraph (Set.univ : Set (Fin n → Real)) f := by
    have hsubset := epigraph_cone_of_posHom (f := f) hpos (2 : Real) (by norm_num)
    exact hsubset ⟨(x, μ), hp, rfl⟩
  have hy2 : (2 : Real) • (y, ν) ∈ epigraph (Set.univ : Set (Fin n → Real)) f := by
    have hsubset := epigraph_cone_of_posHom (f := f) hpos (2 : Real) (by norm_num)
    exact hsubset ⟨(y, ν), hq, rfl⟩
  have hconv_epi : Convex ℝ (epigraph (Set.univ : Set (Fin n → Real)) f) := by
    simpa [ConvexFunctionOn] using hconv
  have hsum :
      (1 / 2 : Real) • ((2 : Real) • (x, μ)) +
          (1 / 2 : Real) • ((2 : Real) • (y, ν)) ∈
        epigraph (Set.univ : Set (Fin n → Real)) f := by
    exact hconv_epi hx2 hy2 (by norm_num) (by norm_num) (by ring)
  have hscale : (1 / 2 : Real) * 2 = 1 := by norm_num
  have hsum' : (x + y, μ + ν) ∈ epigraph (Set.univ : Set (Fin n → Real)) f := by
    simpa [smul_smul, smul_eq_mul, hscale] using hsum
  simpa using hsum'

/-- The epigraph of a convex positively homogeneous function is a convex cone. -/
def convexCone_epigraph_of_posHom_convex {n : Nat} {f : (Fin n → Real) → EReal}
    (hpos : PositivelyHomogeneous f)
    (hconv : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f) :
    ConvexCone ℝ ((Fin n → Real) × Real) :=
  { carrier := epigraph (Set.univ : Set (Fin n → Real)) f
    smul_mem' := by
      intro t ht p hp
      have hsubset := epigraph_cone_of_posHom (f := f) hpos t ht
      exact hsubset ⟨p, hp, rfl⟩
    add_mem' := by
      intro p hp q hq
      exact add_mem_epigraph_of_posHom_convex (f := f) hpos hconv hp hq }

/-- If `epigraph h ⊆ F`, then the inf-section of `F` is dominated by `h`. -/
lemma le_of_epigraph_subset_inf_section {n : Nat} {h : (Fin n → Real) → EReal}
    {F : Set ((Fin n → Real) × Real)}
    (hF : epigraph (Set.univ : Set (Fin n → Real)) h ⊆ F) :
    (fun x =>
      sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ | (x, μ) ∈ F })) ≤ h := by
  intro x
  cases hx : h x using EReal.rec with
  | bot =>
      have hfiber : { μ : ℝ | (x, μ) ∈ F } = (Set.univ : Set ℝ) := by
        ext μ
        constructor
        · intro _; trivial
        · intro _
          have hxmem : (x, μ) ∈ epigraph (Set.univ : Set (Fin n → Real)) h := by
            have : h x ≤ (μ : EReal) := by simp [hx]
            exact And.intro (by trivial) this
          exact hF hxmem
      have hle :
          sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ | (x, μ) ∈ F }) =
            (⊥ : EReal) := by
        rw [hfiber, sInf_image_real_univ]
      simp [hle]
  | coe r =>
      have hmem : (r : EReal) ∈
          (fun μ : ℝ => (μ : EReal)) '' { μ : ℝ | (x, μ) ∈ F } := by
        refine ⟨r, ?_, rfl⟩
        have hxmem : (x, r) ∈ epigraph (Set.univ : Set (Fin n → Real)) h := by
          exact (mem_epigraph_univ_iff (f := h)).2 (by simp [hx])
        exact hF hxmem
      have hle :
          sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ | (x, μ) ∈ F }) ≤ (r : EReal) :=
        sInf_le hmem
      exact hle
  | top =>
      have hle : (fun x =>
          sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ | (x, μ) ∈ F })) x ≤ (⊤ : EReal) :=
        le_top
      exact hle

/-- Minimality of the generated cone inside any epigraph majorant. -/
lemma cone_minimality_epigraph_u {n : Nat} {h u : (Fin n → Real) → EReal}
    (hu_pos : PositivelyHomogeneous u)
    (hu_conv : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) u)
    (hu0 : u 0 ≤ 0) (hu_le : u ≤ h) :
    convexConeGeneratedEpigraph h ⊆ epigraph (Set.univ : Set (Fin n → Real)) u := by
  let C : ConvexCone ℝ ((Fin n → Real) × Real) :=
    convexCone_epigraph_of_posHom_convex (f := u) hu_pos hu_conv
  have hsubset : epigraph (Set.univ : Set (Fin n → Real)) h ⊆ (C : Set _) := by
    intro p hp
    have hp' : u p.1 ≤ (p.2 : EReal) := by
      have hhp : h p.1 ≤ (p.2 : EReal) := (mem_epigraph_univ_iff (f := h)).1 hp
      exact (le_trans (hu_le _) hhp)
    have hp'' : p ∈ epigraph (Set.univ : Set (Fin n → Real)) u :=
      (mem_epigraph_univ_iff (f := u)).2 hp'
    change p ∈ epigraph (Set.univ : Set (Fin n → Real)) u
    exact hp''
  have hhull :
      (ConvexCone.hull ℝ (epigraph (Set.univ : Set (Fin n → Real)) h) :
          Set ((Fin n → Real) × Real)) ⊆
        (C : Set ((Fin n → Real) × Real)) :=
    by
      simpa [SetLike.coe_subset_coe] using (ConvexCone.hull_min (C := C) hsubset)
  intro p hp
  have hp' :
      p = 0 ∨ p ∈
        (ConvexCone.hull ℝ (epigraph (Set.univ : Set (Fin n → Real)) h)) := by
    simpa [convexConeGeneratedEpigraph] using hp
  rcases hp' with rfl | hp'
  · exact (mem_epigraph_univ_iff (f := u)).2 (by simpa using hu0)
  · exact hhull hp'

/-- Text 5.4.8 (Maximality of the positively homogeneous hull): Let `h` be convex on `ℝ^n`,
and let `f` be the positively homogeneous convex function generated by `h`. Then:
(i) `epi f` is a convex cone in `ℝ^{n+1}` containing the origin.
(ii) `f` is convex and positively homogeneous, and satisfies `f(0) ≤ 0` and `f ≤ h`.
(iii) (Greatest such minorant) If `u` is any positively homogeneous convex function with
`u(0) ≤ 0` and `u ≤ h`, then `u ≤ f`. -/
theorem maximality_posHomogeneousHull {n : Nat} {h : (Fin n → Real) → EReal}
    (_hh : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) h) :
    let f := positivelyHomogeneousConvexFunctionGenerated h;
    (∃ C : ConvexCone ℝ ((Fin n → Real) × Real),
      (C : Set ((Fin n → Real) × Real)) =
        epigraph (S := (Set.univ : Set (Fin n → Real))) f ∧
      (0 : (Fin n → Real) × Real) ∈
        epigraph (S := (Set.univ : Set (Fin n → Real))) f)
    ∧
    (ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f ∧
      PositivelyHomogeneous f ∧
      f 0 ≤ 0 ∧
      f ≤ h)
    ∧
    (∀ u : (Fin n → Real) → EReal,
      PositivelyHomogeneous u →
      ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) u →
      u 0 ≤ 0 →
      u ≤ h →
      u ≤ f) := by
  classical
  set f := positivelyHomogeneousConvexFunctionGenerated h
  have hcone :
      ∀ t : Real, 0 < t →
        Set.image (fun p : (Fin n → Real) × Real => t • p)
          (convexConeGeneratedEpigraph h) ⊆ convexConeGeneratedEpigraph h := by
    intro t ht p hp
    rcases hp with ⟨q, hq, rfl⟩
    exact smul_mem_convexConeGeneratedEpigraph (h := h) ht hq
  have hpos : PositivelyHomogeneous f := by
    simpa [f, positivelyHomogeneousConvexFunctionGenerated] using
      (posHom_of_inf_section_of_cone (F := convexConeGeneratedEpigraph h) hcone)
  have hf0 : f 0 ≤ 0 := by
    have hmem0 : (0 : EReal) ∈
        (fun μ : ℝ => (μ : EReal)) '' { μ : ℝ |
          (0, μ) ∈ convexConeGeneratedEpigraph h } := by
      refine ⟨0, ?_, rfl⟩
      have : (0 : (Fin n → Real) × Real) ∈ convexConeGeneratedEpigraph h := by
        change (0 : (Fin n → Real) × Real) ∈
          Set.insert 0 (ConvexCone.hull ℝ (epigraph (Set.univ : Set (Fin n → Real)) h))
        exact (Set.mem_insert_iff).2 (Or.inl rfl)
      simpa using this
    have hle :
        sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ |
          (0, μ) ∈ convexConeGeneratedEpigraph h }) ≤ (0 : EReal) :=
      sInf_le hmem0
    simpa [f, positivelyHomogeneousConvexFunctionGenerated] using hle
  have hconv : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f := by
    have hFconv : Convex ℝ (convexConeGeneratedEpigraph h) := by
      simpa using (ConvexCone.convex (C := convexCone_generatedEpigraph h))
    simpa [f, positivelyHomogeneousConvexFunctionGenerated] using
      (convexOn_inf_section_of_convex (F := convexConeGeneratedEpigraph h) hFconv)
  have hle : f ≤ h := by
    have hsubset : epigraph (Set.univ : Set (Fin n → Real)) h ⊆
        convexConeGeneratedEpigraph h := by
      intro p hp
      have hp' :
          p ∈ (ConvexCone.hull ℝ (epigraph (Set.univ : Set (Fin n → Real)) h)) :=
        ConvexCone.subset_hull hp
      have : p = 0 ∨
          p ∈ (ConvexCone.hull ℝ (epigraph (Set.univ : Set (Fin n → Real)) h)) := Or.inr hp'
      simpa [convexConeGeneratedEpigraph] using this
    simpa [f, positivelyHomogeneousConvexFunctionGenerated] using
      (le_of_epigraph_subset_inf_section (h := h) (F := convexConeGeneratedEpigraph h) hsubset)
  have hmem0 :
      (0 : (Fin n → Real) × Real) ∈ epigraph (Set.univ : Set (Fin n → Real)) f := by
    exact (mem_epigraph_univ_iff (f := f)).2 (by simpa using hf0)
  refine And.intro ?_ ?_
  · refine ⟨
      convexCone_epigraph_of_posHom_convex (f := f) hpos hconv, rfl, hmem0⟩
  · refine And.intro ?_ ?_
    · exact ⟨hconv, hpos, hf0, hle⟩
    · intro u hu_pos hu_conv hu0 hu_le
      have hsubset :
          convexConeGeneratedEpigraph h ⊆ epigraph (Set.univ : Set (Fin n → Real)) u :=
        cone_minimality_epigraph_u (h := h) (u := u) hu_pos hu_conv hu0 hu_le
      intro x
      have hle' :
          u x ≤ sInf ((fun μ : ℝ => (μ : EReal)) '' { μ : ℝ |
            (x, μ) ∈ convexConeGeneratedEpigraph h }) := by
        refine le_sInf ?_
        intro z hz
        rcases hz with ⟨μ, hμ, rfl⟩
        have hxmem : (x, μ) ∈ epigraph (Set.univ : Set (Fin n → Real)) u :=
          hsubset hμ
        exact (mem_epigraph_univ_iff (f := u)).1 hxmem
      simpa [f, positivelyHomogeneousConvexFunctionGenerated] using hle'

/-- Membership in the generated cone is either zero or a positive scaling of the epigraph,
for convex `h`. -/
lemma mem_convexConeGeneratedEpigraph_iff {n : Nat} {h : (Fin n → Real) → EReal}
    (hh : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) h)
    {p : (Fin n → Real) × Real} :
    p ∈ convexConeGeneratedEpigraph h ↔
      p = 0 ∨ ∃ lam : Real, 0 < lam ∧
        p ∈ Set.image (fun q : (Fin n → Real) × Real => lam • q)
          (epigraph (Set.univ : Set (Fin n → Real)) h) := by
  constructor
  · intro hp
    have hp' : p = 0 ∨
        p ∈ (ConvexCone.hull ℝ (epigraph (Set.univ : Set (Fin n → Real)) h)) := by
      simpa [convexConeGeneratedEpigraph] using hp
    rcases hp' with rfl | hp'
    · exact Or.inl rfl
    · have hconv : Convex ℝ (epigraph (Set.univ : Set (Fin n → Real)) h) := by
        simpa [ConvexFunctionOn] using hh
      rcases (ConvexCone.mem_hull_of_convex
        (s := epigraph (Set.univ : Set (Fin n → Real)) h) hconv).1 hp' with
        ⟨lam, hlam, hmem⟩
      exact Or.inr ⟨lam, hlam, hmem⟩
  · intro hp
    rcases hp with rfl | ⟨lam, hlam, hmem⟩
    · exact (Set.mem_insert_iff).2 (Or.inl rfl)
    · have hconv : Convex ℝ (epigraph (Set.univ : Set (Fin n → Real)) h) := by
        simpa [ConvexFunctionOn] using hh
      have hmem' :
          p ∈ (ConvexCone.hull ℝ (epigraph (Set.univ : Set (Fin n → Real)) h)) := by
        exact (ConvexCone.mem_hull_of_convex
          (s := epigraph (Set.univ : Set (Fin n → Real)) h) hconv).2
          ⟨lam, hlam, hmem⟩
      exact (Set.mem_insert_iff).2 (Or.inr hmem')

/-- The `λ ≥ 0` right-scalar-multiple values are obtained by inserting the `λ = 0` value. -/
lemma rightScalarMultiple_set_eq_insert {n : Nat} {h : (Fin n → Real) → EReal}
    (x : Fin n → Real) :
    { z : EReal | ∃ lam : Real, 0 ≤ lam ∧ z = rightScalarMultiple h lam x } =
      Set.insert (rightScalarMultiple h 0 x)
        { z : EReal | ∃ lam : Real, 0 < lam ∧ z = rightScalarMultiple h lam x } := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨lam, hlam, rfl⟩
    by_cases h0 : lam = 0
    · subst h0
      exact (Set.mem_insert_iff).2 (Or.inl rfl)
    · have hlam' : 0 < lam := lt_of_le_of_ne hlam (Ne.symm h0)
      exact (Set.mem_insert_iff).2 (Or.inr ⟨lam, hlam', rfl⟩)
  · intro hz
    rcases (Set.mem_insert_iff).1 hz with hz | hz
    · refine ⟨0, le_rfl, ?_⟩
      simp [hz]
    · rcases hz with ⟨lam, hlam, rfl⟩
      exact ⟨lam, le_of_lt hlam, rfl⟩

/-- If `h 0 < ⊤`, then the infimum of positive right scalar multiples at `0` is `≤ 0`. -/
lemma sInf_rightScalarMultiple_pos_le_zero {n : Nat} {h : (Fin n → Real) → EReal}
    (hh : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) h)
    (h0 : h 0 < (⊤ : EReal)) :
    sInf { z : EReal | ∃ lam : Real, 0 < lam ∧ z = rightScalarMultiple h lam 0 } ≤ (0 : EReal) := by
  classical
  set S : Set EReal := { z : EReal | ∃ lam : Real, 0 < lam ∧ z = rightScalarMultiple h lam 0 }
  cases hval : h 0 using EReal.rec with
  | bot =>
      have hmem : (⊥ : EReal) ∈ S := by
        refine ⟨1, by norm_num, ?_⟩
        have hpos : 0 < (1 : Real) := by norm_num
        have hmul := rightScalarMultiple_pos (f := h) (lam := 1) hh hpos (0)
        simpa [hval] using hmul.symm
      have hle : sInf S ≤ (⊥ : EReal) := sInf_le hmem
      exact le_trans hle bot_le
  | top =>
      simp [hval] at h0
  | coe r =>
      by_cases hr : r ≤ 0
      · have hmem : ((r : Real) : EReal) ∈ S := by
          refine ⟨1, by norm_num, ?_⟩
          have hpos : 0 < (1 : Real) := by norm_num
          have hmul := rightScalarMultiple_pos (f := h) (lam := 1) hh hpos (0)
          simpa [hval] using hmul.symm
        have hle : sInf S ≤ ((r : Real) : EReal) := sInf_le hmem
        have hle' : ((r : Real) : EReal) ≤ (0 : EReal) :=
          (EReal.coe_le_coe_iff).2 hr
        exact le_trans hle hle'
      · have hrpos : 0 < r := lt_of_not_ge hr
        refine (sInf_le_iff).2 ?_
        intro b hb
        have hb' : ∀ z ∈ S, b ≤ z := by
          simpa [lowerBounds] using hb
        cases hbval : b using EReal.rec with
        | bot =>
            simp
        | top =>
            have hmem : ((r : Real) : EReal) ∈ S := by
              refine ⟨1, by norm_num, ?_⟩
              have hpos : 0 < (1 : Real) := by norm_num
              have hmul := rightScalarMultiple_pos (f := h) (lam := 1) hh hpos (0)
              simpa [hval] using hmul.symm
            have hle : (⊤ : EReal) ≤ ((r : Real) : EReal) := by
              simpa [hbval] using hb' _ hmem
            have htop : ((r : Real) : EReal) = (⊤ : EReal) := (top_le_iff).1 hle
            simp at htop
        | coe s =>
            by_cases hs : s ≤ 0
            · exact (EReal.coe_le_coe_iff).2 hs
            · have hspos : 0 < s := lt_of_not_ge hs
              set lam : Real := s / (2 * r)
              have hlam : 0 < lam := by
                have hden : 0 < (2 * r) := by nlinarith [hrpos]
                exact div_pos hspos hden
              have hmul : rightScalarMultiple h lam 0 = ((lam * r : Real) : EReal) := by
                have hmul' := rightScalarMultiple_pos (f := h) (lam := lam) hh hlam (0)
                simpa [hval, EReal.coe_mul, mul_comm, mul_left_comm, mul_assoc] using hmul'
              have hmem : ((lam * r : Real) : EReal) ∈ S := by
                refine ⟨lam, hlam, ?_⟩
                simp [hmul]
              have hle : b ≤ ((lam * r : Real) : EReal) := hb' _ hmem
              have hle' : (s : Real) ≤ lam * r := by
                have hle'' : (s : EReal) ≤ ((lam * r : Real) : EReal) := by
                  simpa [hbval] using hle
                exact (EReal.coe_le_coe_iff).1 hle''
              have hrne : r ≠ 0 := ne_of_gt hrpos
              have hcalc : lam * r = s / 2 := by
                dsimp [lam]
                field_simp [hrne, mul_comm, mul_left_comm, mul_assoc]
              have : s ≤ s / 2 := by simpa [hcalc] using hle'
              have : False := by nlinarith [hspos, this]
              exact this.elim


end Section05
end Chap01
