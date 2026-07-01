/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xuran Sun, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section04_part4

open Matrix
open scoped BigOperators
open scoped Topology

section Chap01
section Section04
open scoped BigOperators

/-- Extend convexity to the closure under continuity. -/
lemma convexOn_closure_of_continuousOn {n : Nat} {C : Set (Fin n → Real)}
    {f : (Fin n → Real) → Real} (hconv : ConvexOn ℝ C f)
    (hcont : ContinuousOn f (closure C)) :
    ConvexOn ℝ (closure C) f := by
  classical
  refine ⟨(Convex.closure hconv.1), ?_⟩
  intro x hx y hy a b ha hb hab
  let s : Set ((Fin n → Real) × (Fin n → Real)) := C ×ˢ C
  let F : ((Fin n → Real) × (Fin n → Real)) → Real :=
    fun p => f (a • p.1 + b • p.2)
  let G : ((Fin n → Real) × (Fin n → Real)) → Real :=
    fun p => a • f p.1 + b • f p.2
  have hineq : ∀ p ∈ s, F p ≤ G p := by
    intro p hp
    rcases hp with ⟨hxC, hyC⟩
    exact hconv.2 hxC hyC ha hb hab
  have hfst : Set.MapsTo Prod.fst (closure s) (closure C) := by
    intro p hp
    have hp' : p ∈ closure C ×ˢ closure C := by
      simpa [s, closure_prod_eq] using hp
    exact hp'.1
  have hsnd : Set.MapsTo Prod.snd (closure s) (closure C) := by
    intro p hp
    have hp' : p ∈ closure C ×ˢ closure C := by
      simpa [s, closure_prod_eq] using hp
    exact hp'.2
  have hcomb_map :
      Set.MapsTo (fun p : (Fin n → Real) × (Fin n → Real) => a • p.1 + b • p.2)
        (closure s) (closure C) := by
    intro p hp
    have hp' : p ∈ closure C ×ˢ closure C := by
      simpa [s, closure_prod_eq] using hp
    exact (Convex.closure hconv.1) hp'.1 hp'.2 ha hb hab
  have hcont_combo :
      ContinuousOn (fun p : (Fin n → Real) × (Fin n → Real) => a • p.1 + b • p.2)
        (closure s) := by
    have hcont_fst :
        ContinuousOn (fun p : (Fin n → Real) × (Fin n → Real) => p.1)
          (closure s) := continuous_fst.continuousOn
    have hcont_snd :
        ContinuousOn (fun p : (Fin n → Real) × (Fin n → Real) => p.2)
          (closure s) := continuous_snd.continuousOn
    have hcont_a :
        ContinuousOn (fun _ : (Fin n → Real) × (Fin n → Real) => a) (closure s) :=
      continuousOn_const
    have hcont_b :
        ContinuousOn (fun _ : (Fin n → Real) × (Fin n → Real) => b) (closure s) :=
      continuousOn_const
    have hcont_a_smul :
        ContinuousOn (fun p : (Fin n → Real) × (Fin n → Real) => a • p.1) (closure s) :=
      hcont_a.smul hcont_fst
    have hcont_b_smul :
        ContinuousOn (fun p : (Fin n → Real) × (Fin n → Real) => b • p.2) (closure s) :=
      hcont_b.smul hcont_snd
    simpa using hcont_a_smul.add hcont_b_smul
  have hcont_F : ContinuousOn F (closure s) :=
    hcont.comp hcont_combo hcomb_map
  have hcont_fst : ContinuousOn (fun p : (Fin n → Real) × (Fin n → Real) => f p.1) (closure s) :=
    hcont.comp continuous_fst.continuousOn hfst
  have hcont_snd : ContinuousOn (fun p : (Fin n → Real) × (Fin n → Real) => f p.2) (closure s) :=
    hcont.comp continuous_snd.continuousOn hsnd
  have hcont_G : ContinuousOn G (closure s) := by
    have hcont_a :
        ContinuousOn (fun _ : (Fin n → Real) × (Fin n → Real) => a) (closure s) :=
      continuousOn_const
    have hcont_b :
        ContinuousOn (fun _ : (Fin n → Real) × (Fin n → Real) => b) (closure s) :=
      continuousOn_const
    have hcont_a_smul :
        ContinuousOn (fun p : (Fin n → Real) × (Fin n → Real) => a • f p.1) (closure s) :=
      hcont_a.smul hcont_fst
    have hcont_b_smul :
        ContinuousOn (fun p : (Fin n → Real) × (Fin n → Real) => b • f p.2) (closure s) :=
      hcont_b.smul hcont_snd
    simpa using hcont_a_smul.add hcont_b_smul
  have hxy : (x, y) ∈ closure s := by
    have hxy' : (x, y) ∈ closure C ×ˢ closure C := by
      exact ⟨hx, hy⟩
    simpa [s, closure_prod_eq] using hxy'
  have hle : F (x, y) ≤ G (x, y) :=
    le_on_closure (s := s) hineq hcont_F hcont_G hxy
  simpa [F, G] using hle

/-- Convexity of the negative geometric mean on the nonnegative orthant. -/
lemma convexOn_negGeomMean_nonneg {n : Nat} (hn : n ≠ 0) :
    ConvexOn ℝ {x | ∀ i, 0 ≤ x i}
      (fun x : Fin n → Real =>
        -(Real.rpow (Finset.univ.prod (fun i => x i)) (1 / (n : Real)))) := by
  classical
  let g : (Fin n → Real) → Real :=
    fun x => -(Real.rpow (Finset.univ.prod (fun i => x i)) (1 / (n : Real)))
  have hconv_pos : ConvexOn ℝ {x | ∀ i, 0 < x i} g :=
    convexOn_negGeomMean_pos (n := n) hn
  have hcont :
      ContinuousOn g (closure {x : Fin n → Real | ∀ i, 0 < x i}) := by
    simpa [closure_posOrthant_eq_nonneg, g] using
      (continuousOn_negGeomMean_nonneg (n := n))
  have hconv_closure :
      ConvexOn ℝ (closure {x : Fin n → Real | ∀ i, 0 < x i}) g :=
    convexOn_closure_of_continuousOn (C := {x | ∀ i, 0 < x i}) (f := g) hconv_pos hcont
  simpa [closure_posOrthant_eq_nonneg, g] using hconv_closure

/-- The effective domain of the negative geometric mean is the nonnegative orthant. -/
lemma effectiveDomain_negativeGeometricMean {n : Nat} :
    effectiveDomain Set.univ (fun x : Fin n → Real =>
      if (∀ i, 0 ≤ x i) then
        (-(Real.rpow (Finset.univ.prod (fun i => x i)) (1 / (n : Real))) : EReal)
      else (⊤ : EReal)) = {x | ∀ i, 0 ≤ x i} := by
  classical
  let f : (Fin n → Real) → EReal := fun x =>
    if (∀ i, 0 ≤ x i) then
      (-(Real.rpow (Finset.univ.prod (fun i => x i)) (1 / (n : Real))) : EReal)
    else (⊤ : EReal)
  have hdom : effectiveDomain Set.univ f = {x | ∀ i, 0 ≤ x i} := by
    ext x; constructor
    · intro hx
      have hx' : x ∈ {x | x ∈ Set.univ ∧ f x < (⊤ : EReal)} := by
        simpa [effectiveDomain_eq] using hx
      have hxlt : f x < (⊤ : EReal) := hx'.2
      by_cases h : ∀ i, 0 ≤ x i
      · exact h
      · have : ¬ f x < (⊤ : EReal) := by simp [f, h]
        exact (this hxlt).elim
    · intro hx
      have hx_nonneg : ∀ i, 0 ≤ x i := by
        simpa using hx
      have hx' : f x < (⊤ : EReal) := by
        simpa [f, hx_nonneg] using
          (EReal.coe_lt_top
            (-(Real.rpow (Finset.univ.prod (fun i => x i)) (1 / (n : Real)))))
      have hx'' : x ∈ Set.univ ∧ f x < (⊤ : EReal) := by
        exact ⟨by simp, hx'⟩
      simpa [effectiveDomain_eq] using hx''
  simpa [f] using hdom

lemma convexFunction_negativeGeometricMean {n : Nat} :
    (let f : (Fin n → Real) → EReal :=
      fun x =>
        if (∀ i, 0 ≤ x i) then
          (-(Real.rpow (Finset.univ.prod (fun i => x i)) (1 / (n : Real))) : EReal)
        else (⊤ : EReal);
      ConvexFunction f) := by
  classical
  let f : (Fin n → Real) → EReal := fun x =>
    if (∀ i, 0 ≤ x i) then
      (-(Real.rpow (Finset.univ.prod (fun i => x i)) (1 / (n : Real))) : EReal)
    else (⊤ : EReal)
  have hdom : effectiveDomain Set.univ f = {x | ∀ i, 0 ≤ x i} := by
    simpa [f] using (effectiveDomain_negativeGeometricMean (n := n))
  have hconv_nonneg : ConvexFunctionOn {x | ∀ i, 0 ≤ x i} f := by
    -- TODO: prove convexity of the negative geometric mean on the nonnegative orthant.
    classical
    let g : (Fin n → Real) → Real := fun x =>
      -(Real.rpow (Finset.univ.prod (fun i => x i)) (1 / (n : Real)))
    have hg : ConvexOn ℝ {x | ∀ i, 0 ≤ x i} g := by
      classical
      by_cases hzero : n = 0
      · subst hzero
        have hset :
            ({x : Fin 0 → Real | ∀ i, 0 ≤ x i} : Set (Fin 0 → Real)) = Set.univ := by
          ext x; constructor
          · intro _; trivial
          · intro _ i; exact (Fin.elim0 i)
        have hC : Convex ℝ ({x : Fin 0 → Real | ∀ i, 0 ≤ x i}) := by
          simpa [hset] using (convex_univ : Convex ℝ (Set.univ : Set (Fin 0 → Real)))
        have hgconst : g = fun _ : Fin 0 → Real => (-1 : Real) := by
          funext x
          simp [g]
        simpa [hgconst] using (convexOn_const (-1 : Real) hC)
      · -- Main case `n ≠ 0`: use Hessian computation and Cauchy-Schwarz.
        exact convexOn_negGeomMean_nonneg (n := n) hzero
    have hconv_g :
        ConvexFunctionOn {x | ∀ i, 0 ≤ x i} (fun x => (g x : EReal)) :=
      convexFunctionOn_of_convexOn_real (S := {x | ∀ i, 0 ≤ x i}) hg
    have hepigraph :
        epigraph {x | ∀ i, 0 ≤ x i} f =
          epigraph {x | ∀ i, 0 ≤ x i} (fun x => (g x : EReal)) := by
      ext p; constructor <;> intro hp
      · rcases hp with ⟨hpC, hle⟩
        have hpC' : ∀ i, 0 ≤ p.1 i := by simpa using hpC
        have hf : f p.1 = (g p.1 : EReal) := by simp [f, g, hpC']
        refine ⟨hpC, ?_⟩
        simpa [hf] using hle
      · rcases hp with ⟨hpC, hle⟩
        have hpC' : ∀ i, 0 ≤ p.1 i := by simpa using hpC
        have hf : f p.1 = (g p.1 : EReal) := by simp [f, g, hpC']
        refine ⟨hpC, ?_⟩
        simpa [hf] using hle
    have hconv_epi :
        Convex ℝ (epigraph {x | ∀ i, 0 ≤ x i} (fun x => (g x : EReal))) := by
      simpa [ConvexFunctionOn] using hconv_g
    have hconv_epi' : Convex ℝ (epigraph {x | ∀ i, 0 ≤ x i} f) := by
      simpa [hepigraph] using hconv_epi
    simpa [ConvexFunctionOn] using hconv_epi'
  have hconv_dom : ConvexFunctionOn (effectiveDomain Set.univ f) f := by
    simpa [hdom] using hconv_nonneg
  have hconv_univ : ConvexFunctionOn Set.univ f :=
    (convexFunctionOn_iff_convexFunctionOn_effectiveDomain (S := Set.univ) (f := f)).2 hconv_dom
  simpa [ConvexFunction, f] using hconv_univ

/-- Remark 4.5.3: One of the most important convex functions on `ℝ^n` is the Euclidean norm
`|x| = ⟪x, x⟫^{1/2} = (xi_1^2 + ... + xi_n^2)^{1/2}`. -/
lemma convexOn_univ_euclidean_norm {n : Nat} :
    ConvexOn ℝ (Set.univ) (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) := by
  simpa using (convexOn_univ_norm (E := EuclideanSpace ℝ (Fin n)))

/-- Remark 4.5.3: This Euclidean norm is the absolute value when `n = 1`. -/
lemma euclidean_norm_eq_abs (x : ℝ) : ‖x‖ = |x| := by
  simp

/-- Strict real sublevel sets of a convex function are convex. -/
lemma convex_sublevel_lt_real_of_convexFunction {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ConvexFunction f) (r : Real) :
    Convex ℝ {x | f x < (r : EReal)} := by
  classical
  have hf' : ConvexFunctionOn (Set.univ) f := by
    simpa [ConvexFunction] using hf
  have hstrict := (convexFunctionOn_univ_iff_strict_inequality (f := f)).1 hf'
  intro x hx y hy a b ha hb hab
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith [hab, hb0]
    simpa [hb0, ha1] using hx
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith [hab, ha0]
    simpa [ha0, hb1] using hy
  have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb_lt1 : b < 1 := by linarith [hab, ha_pos]
  have ha_eq : a = 1 - b := by linarith [hab]
  have hlt :
      f ((1 - b) • x + b • y) <
        ((1 - b : Real) : EReal) * (r : EReal) + ((b : Real) : EReal) * (r : EReal) :=
    hstrict x y r r b hx hy hb_pos hb_lt1
  have hcalc_real : (1 - b) * r + b * r = r := by ring
  have hcalc :
      ((1 - b : Real) : EReal) * (r : EReal) + ((b : Real) : EReal) * (r : EReal)
        = (r : EReal) := by
    simp [← EReal.coe_add, ← EReal.coe_mul, hcalc_real, -EReal.coe_sub]
  have hcomb : a • x + b • y = (1 - b) • x + b • y := by
    simp [ha_eq]
  have hlt' :
      f (a • x + b • y) <
        ((1 - b : Real) : EReal) * (r : EReal) + ((b : Real) : EReal) * (r : EReal) := by
    simpa [hcomb] using hlt
  exact (lt_of_lt_of_eq hlt' hcalc)

/-- The strict sublevel at `⊤` is the effective domain, hence convex. -/
lemma convex_sublevel_lt_top_of_convexFunction {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ConvexFunction f) :
    Convex ℝ {x | f x < (⊤ : EReal)} := by
  have hf' : ConvexFunctionOn (Set.univ) f := by
    simpa [ConvexFunction] using hf
  have hconv : Convex ℝ (effectiveDomain Set.univ f) :=
    effectiveDomain_convex (S := Set.univ) (f := f) hf'
  simpa [effectiveDomain_eq] using hconv

/-- A non-strict sublevel is the intersection of strict real sublevels above it. -/
lemma sublevel_le_eq_iInter_lt_real {n : Nat} {f : (Fin n → Real) → EReal} (α : EReal) :
    {x | f x ≤ α} =
      ⋂ (β : {β : Real // (α : EReal) < β}), {x | f x < (β : EReal)} := by
  ext x; constructor
  · intro hx
    refine Set.mem_iInter.2 ?_
    intro β
    exact lt_of_le_of_lt hx β.property
  · intro hx
    have hx' :
        ∀ β : {β : Real // (α : EReal) < β}, f x < (β : EReal) := by
      intro β
      have hxβ : x ∈ {x | f x < (β : EReal)} := (Set.mem_iInter.1 hx) β
      simpa using hxβ
    by_contra hnot
    have hlt : α < f x := lt_of_not_ge hnot
    obtain ⟨β, hαβ, hβfx⟩ := EReal.exists_between_coe_real hlt
    have hfx : f x < (β : EReal) := hx' ⟨β, hαβ⟩
    exact (lt_asymm hβfx hfx)

/-- Theorem 4.6: For any convex function `f` and any `α ∈ [-∞, +∞]`, the level sets
`{x | f x < α}` and `{x | f x ≤ α}` are convex. -/
theorem convexFunction_level_sets_convex {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ConvexFunction f) (α : EReal) :
    Convex ℝ {x | f x < α} ∧ Convex ℝ {x | f x ≤ α} := by
  classical
  have hstrict : Convex ℝ {x | f x < α} := by
    cases α using EReal.rec with
    | bot =>
        have hset : {x | f x < (⊥ : EReal)} = (∅ : Set (Fin n → Real)) := by
          ext x; simp
        simpa [hset] using (convex_empty : Convex ℝ (∅ : Set (Fin n → Real)))
    | coe r =>
        simpa using (convex_sublevel_lt_real_of_convexFunction (f := f) hf r)
    | top =>
        simpa using (convex_sublevel_lt_top_of_convexFunction (f := f) hf)
  have hle : Convex ℝ {x | f x ≤ α} := by
    have hconv :
        ∀ β : {β : Real // (α : EReal) < β}, Convex ℝ {x | f x < (β : EReal)} := by
      intro β
      simpa using (convex_sublevel_lt_real_of_convexFunction (f := f) hf (β : Real))
    simpa [sublevel_le_eq_iInter_lt_real (f := f) (α := α)] using (convex_iInter hconv)
  exact ⟨hstrict, hle⟩

/-- Remark 4.6.1: Taking `f` to be a quadratic convex function in Theorem 4.6, the set
`{x | (1/2) ⟪x, Q x⟫ + ⟪x, a⟫ + α ≤ 0}` is convex when `Q` is positive semidefinite
(Theorem 4.5). Sets of this form include solid ellipsoids and paraboloids, in
particular the ball `{x | ⟪x, x⟫ ≤ 1}`. -/
lemma convex_quadratic_inequality_set {n : Nat}
    {Q : Matrix (Fin n) (Fin n) ℝ} {a : Fin n → ℝ} {α : ℝ}
    (hQ : Matrix.PosSemidef Q) :
    Convex ℝ {x : Fin n → ℝ |
      ((1 / 2 : ℝ) * dotProduct x (Q.mulVec x) + dotProduct x a + α) ≤ 0} := by
  classical
  let g : (Fin n → ℝ) → ℝ := fun x =>
    (1 / 2 : ℝ) * dotProduct x (Q.mulVec x) + dotProduct x a + α
  have hconv : ConvexOn ℝ Set.univ g :=
    posSemidef_implies_convexity_quadratic (Q := Q) (a := a) (α := α) hQ
  have hconvE : ConvexFunction (fun x => (g x : EReal)) := by
    have hconvEon :
        ConvexFunctionOn Set.univ (fun x => (g x : EReal)) :=
      convexFunctionOn_of_convexOn_real (S := Set.univ) (g := g) hconv
    simpa [ConvexFunction] using hconvEon
  have hset :
      Convex ℝ {x : Fin n → ℝ | (g x : EReal) ≤ (0 : EReal)} :=
    (convexFunction_level_sets_convex (f := fun x => (g x : EReal))
      (α := (0 : EReal)) hconvE).2
  have hset' :
      Convex ℝ {x : Fin n → ℝ | g x ≤ 0} := by
    simpa [EReal.coe_le_coe_iff] using hset
  simpa [g] using hset'

/-- Corollary 4.6.1: Let `f_i` be a convex function on `ℝ^n` and `α_i` be a real number for each
`i ∈ I`. Then `C = {x | f_i(x) ≤ α_i, ∀ i ∈ I}` is a convex set. -/
lemma convex_iInter_sublevel_sets {n : Nat} {I : Type*}
    (f : I → (Fin n → Real) → EReal) (α : I → Real) (hf : ∀ i, ConvexFunction (f i)) :
    Convex ℝ {x | ∀ i, f i x ≤ (α i : EReal)} := by
  have hconv : ∀ i, Convex ℝ {x | f i x ≤ (α i : EReal)} := by
    intro i
    exact (convexFunction_level_sets_convex (f := f i) (α := (α i : EReal)) (hf i)).2
  simpa [Set.setOf_forall] using (convex_iInter hconv)

/-- Remark 4.6.2: Theorem 4.6 and Corollary 4.6.1 are significant for systems of nonlinear
inequalities. Convexity also enters other aspects of inequality theory, since various
classical inequalities can be regarded as special cases of Theorem 4.3. -/
lemma convexity_inequality_analysis {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ConvexFunction f) (hnotbot : ∀ x, f x ≠ ⊥) (β : EReal) {I : Type*}
    (g : I → (Fin n → Real) → EReal) (α : I → Real) (hg : ∀ i, ConvexFunction (g i)) :
    (Convex ℝ {x | f x < β} ∧ Convex ℝ {x | f x ≤ β}) ∧
      Convex ℝ {x | ∀ i, g i x ≤ (α i : EReal)} ∧
      (∀ m : Nat, ∀ w : Fin m → Real, ∀ x : Fin m → (Fin n → Real),
        (∀ i, 0 ≤ w i) → (Finset.univ.sum (fun i => w i) = 1) →
          f (Finset.univ.sum (fun i => w i • x i)) ≤
            Finset.univ.sum (fun i => ((w i : Real) : EReal) * f (x i))) := by
  refine ⟨convexFunction_level_sets_convex (f := f) hf β, ?_⟩
  refine ⟨convex_iInter_sublevel_sets (f := g) (α := α) hg, ?_⟩
  have hf' : ConvexFunctionOn Set.univ f := by
    simpa [ConvexFunction] using hf
  simpa using (jensen_inequality_of_convexFunctionOn_univ (f := f) hf' hnotbot)

/-- Definition 4.6: A convex function `f` is proper if its epigraph is nonempty and
contains no vertical lines (equivalently, `f x ≠ ⊥` for all `x ∈ S`). -/
def ProperConvexFunctionOn {n : Nat} (S : Set (Fin n -> Real))
    (f : (Fin n -> Real) -> EReal) : Prop :=
  ConvexFunctionOn S f ∧ Set.Nonempty (epigraph S f) ∧
    ∀ x ∈ S, f x ≠ (⊥ : EReal)

/-- The epigraph is nonempty iff the effective domain is nonempty. -/
lemma nonempty_epigraph_iff_nonempty_effectiveDomain {n : Nat}
    (S : Set (Fin n -> Real)) (f : (Fin n -> Real) -> EReal) :
    Set.Nonempty (epigraph S f) ↔ Set.Nonempty (effectiveDomain S f) := by
  constructor
  · intro h
    rcases h with ⟨p, hp⟩
    exact ⟨p.1, ⟨p.2, by simpa using hp⟩⟩
  · intro h
    rcases h with ⟨x, hx⟩
    rcases hx with ⟨μ, hμ⟩
    exact ⟨(x, μ), hμ⟩

/-- Points in the effective domain have value different from `⊤`. -/
lemma mem_effectiveDomain_imp_ne_top {n : Nat} {S : Set (Fin n -> Real)}
    {f : (Fin n -> Real) -> EReal} {x : Fin n -> Real} :
    x ∈ effectiveDomain S f → f x ≠ (⊤ : EReal) := by
  intro hx htop
  rcases hx with ⟨μ, hμ⟩
  exact (not_top_le_coe μ) (by simpa [htop] using hμ.2)

/-- Points in `S` outside the effective domain cannot take value `⊥`. -/
lemma not_mem_effectiveDomain_imp_ne_bot {n : Nat} {S : Set (Fin n -> Real)}
    {f : (Fin n -> Real) -> EReal} {x : Fin n -> Real} (hxS : x ∈ S)
    (hx : x ∉ effectiveDomain S f) : f x ≠ (⊥ : EReal) := by
  intro hbot
  apply hx
  refine ⟨0, ?_⟩
  refine And.intro hxS ?_
  rw [hbot]
  exact bot_le

/-- Remark 4.6.1: `f` is proper iff the convex set `C = dom f` is nonempty and the
restriction of `f` to `C` is finite; equivalently, a proper convex function on `ℝ^n`
comes from a finite convex function on a nonempty convex set `C` and is extended by
`f x = +∞` outside `C`. -/
lemma properConvexFunctionOn_iff_effectiveDomain_nonempty_finite {n : Nat}
    (S : Set (Fin n -> Real)) (f : (Fin n -> Real) -> EReal) :
    ProperConvexFunctionOn S f ↔
      (ConvexFunctionOn S f ∧ Set.Nonempty (effectiveDomain S f) ∧
        ∀ x ∈ effectiveDomain S f, f x ≠ (⊥ : EReal) ∧ f x ≠ (⊤ : EReal)) := by
  constructor
  · intro hproper
    rcases hproper with ⟨hconv, hne_epi, hbot⟩
    refine ⟨hconv, ?_, ?_⟩
    · exact
        (nonempty_epigraph_iff_nonempty_effectiveDomain (S := S) (f := f)).1 hne_epi
    · intro x hx
      have hxS : x ∈ S := (effectiveDomain_subset (S := S) (f := f)) hx
      have hbotx : f x ≠ (⊥ : EReal) := hbot x hxS
      have htopx : f x ≠ (⊤ : EReal) := mem_effectiveDomain_imp_ne_top (S := S) (f := f) hx
      exact ⟨hbotx, htopx⟩
  · intro h
    rcases h with ⟨hconv, hne_dom, hfinite⟩
    refine ⟨hconv, ?_, ?_⟩
    · rcases hne_dom with ⟨x, hx⟩
      rcases hx with ⟨μ, hμ⟩
      exact ⟨(x, μ), hμ⟩
    · intro x hxS
      by_cases hx_dom : x ∈ effectiveDomain S f
      · exact (hfinite x hx_dom).1
      · exact not_mem_effectiveDomain_imp_ne_bot (S := S) (f := f) hxS hx_dom

/-- Definition 4.7: A convex function which is not proper is improper. -/
def ImproperConvexFunctionOn {n : Nat} (S : Set (Fin n -> Real))
    (f : (Fin n -> Real) -> EReal) : Prop :=
  ConvexFunctionOn S f ∧ ¬ ProperConvexFunctionOn S f

/-- Example 4.7.2: An improper convex function on `ℝ` that is not identically
`+∞` or `-∞` is given by `f x = -∞` if `|x| < 1`, `f x = 0` if `|x| = 1`,
and `f x = +∞` if `|x| > 1`. -/
lemma improperConvexExample :
    (let f : (Fin 1 → Real) → EReal :=
      fun x =>
        if |x 0| < 1 then (⊥ : EReal)
        else if |x 0| = 1 then ((0 : Real) : EReal)
        else (⊤ : EReal);
    ImproperConvexFunctionOn (Set.univ) f ∧
      ¬ (∀ x, f x = (⊤ : EReal)) ∧
      ¬ (∀ x, f x = (⊥ : EReal))) := by
  classical
  let f : (Fin 1 → Real) → EReal :=
    fun x =>
      if |x 0| < 1 then (⊥ : EReal)
      else if |x 0| = 1 then ((0 : Real) : EReal)
      else (⊤ : EReal)
  have hconv : ConvexFunctionOn (Set.univ) f := by
    unfold ConvexFunctionOn
    intro p hp q hq a b ha hb hab
    set x : Real := p.1 0
    set y : Real := q.1 0
    have hp' : f p.1 ≤ (p.2 : EReal) := by
      have hp' := hp
      simp [epigraph] at hp'
      exact hp'.2
    have hq' : f q.1 ≤ (q.2 : EReal) := by
      have hq' := hq
      simp [epigraph] at hq'
      exact hq'.2
    have hx_le : |x| ≤ 1 := by
      by_contra hx_gt
      have hx_gt' : 1 < |x| := lt_of_not_ge hx_gt
      have hlt : ¬ |x| < 1 := not_lt_of_ge (le_of_lt hx_gt')
      have hEq : |x| ≠ 1 := ne_of_gt hx_gt'
      have hf_top : f p.1 = (⊤ : EReal) := by
        simp [f, x, hlt, hEq]
      have hle := hp'
      rw [hf_top] at hle
      exact (not_top_le_coe p.2) hle
    have hy_le : |y| ≤ 1 := by
      by_contra hy_gt
      have hy_gt' : 1 < |y| := lt_of_not_ge hy_gt
      have hlt : ¬ |y| < 1 := not_lt_of_ge (le_of_lt hy_gt')
      have hEq : |y| ≠ 1 := ne_of_gt hy_gt'
      have hf_top : f q.1 = (⊤ : EReal) := by
        simp [f, y, hlt, hEq]
      have hle := hq'
      rw [hf_top] at hle
      exact (not_top_le_coe q.2) hle
    have hp2_nonneg : |x| = 1 → 0 ≤ p.2 := by
      intro hx_eq
      have hf0 : f p.1 = (0 : EReal) := by
        simp [f, x, hx_eq]
      have hle : (0 : EReal) ≤ (p.2 : EReal) := by
        simpa [hf0] using hp'
      have hle' : ((0 : Real) : EReal) ≤ (p.2 : EReal) := by
        simpa using hle
      exact (EReal.coe_le_coe_iff).1 hle'
    have hq2_nonneg : |y| = 1 → 0 ≤ q.2 := by
      intro hy_eq
      have hf0 : f q.1 = (0 : EReal) := by
        simp [f, y, hy_eq]
      have hle : (0 : EReal) ≤ (q.2 : EReal) := by
        simpa [hf0] using hq'
      have hle' : ((0 : Real) : EReal) ≤ (q.2 : EReal) := by
        simpa using hle
      exact (EReal.coe_le_coe_iff).1 hle'
    have hcomb : (a • p.1 + b • q.1) 0 = a * x + b * y := by
      simp [x, y, smul_eq_mul]
    have hcomb2 : (a • p + b • q).2 = a * p.2 + b * q.2 := by
      simp [smul_eq_mul]
    have habs_le : |a * x + b * y| ≤ 1 := by
      have htri : |a * x + b * y| ≤ |a * x| + |b * y| := by
        simpa using abs_add_le (a * x) (b * y)
      have hax : |a * x| ≤ a * 1 := by
        have hax' : a * |x| ≤ a * 1 := mul_le_mul_of_nonneg_left hx_le ha
        simpa [abs_mul, abs_of_nonneg ha] using hax'
      have hby : |b * y| ≤ b * 1 := by
        have hby' : b * |y| ≤ b * 1 := mul_le_mul_of_nonneg_left hy_le hb
        simpa [abs_mul, abs_of_nonneg hb] using hby'
      have hsum : |a * x| + |b * y| ≤ a * 1 + b * 1 := add_le_add hax hby
      have hsum' : |a * x| + |b * y| ≤ 1 := by
        simpa [hab, mul_one] using hsum
      exact le_trans htri hsum'
    have hle :
        f (a • p.1 + b • q.1) ≤ ((a • p + b • q).2 : EReal) := by
      by_cases hlt : |a * x + b * y| < 1
      · have hlt' : |a * p.1 0 + b * q.1 0| < 1 := by
          simpa [x, y] using hlt
        have hf : f (a • p.1 + b • q.1) = (⊥ : EReal) := by
          simp [f, hlt']
        simp [hf]
      · have hEq : |a * x + b * y| = 1 := by
          have hge : 1 ≤ |a * x + b * y| := le_of_not_gt hlt
          exact le_antisymm habs_le hge
        have hlt' : ¬ |a * p.1 0 + b * q.1 0| < 1 := by
          simpa [x, y] using hlt
        have hEq' : |a * p.1 0 + b * q.1 0| = 1 := by
          simpa [x, y] using hEq
        have hnonneg : 0 ≤ a * p.2 + b * q.2 := by
          by_cases ha0 : a = 0
          · have hb1 : b = 1 := by linarith [hab, ha0]
            have hy_eq : |y| = 1 := by
              simpa [ha0, hb1] using hEq
            have hq_nonneg : 0 ≤ q.2 := hq2_nonneg hy_eq
            simpa [ha0, hb1] using hq_nonneg
          · by_cases hb0 : b = 0
            · have ha1 : a = 1 := by linarith [hab, hb0]
              have hx_eq : |x| = 1 := by
                simpa [ha1, hb0] using hEq
              have hp_nonneg : 0 ≤ p.2 := hp2_nonneg hx_eq
              simpa [ha1, hb0] using hp_nonneg
            · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
              have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
              have htri' : 1 ≤ a * |x| + b * |y| := by
                have htri'' : |a * x + b * y| ≤ a * |x| + b * |y| := by
                  simpa [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using
                    (abs_add_le (a * x) (b * y))
                simpa [hEq] using htri''
              have hx_ge : ¬ |x| < 1 := by
                intro hx_lt
                have hax_lt : a * |x| < a * 1 := mul_lt_mul_of_pos_left hx_lt ha_pos
                have hby_le : b * |y| ≤ b * 1 := mul_le_mul_of_nonneg_left hy_le hb
                have hsum_lt : a * |x| + b * |y| < a * 1 + b * 1 :=
                  add_lt_add_of_lt_of_le hax_lt hby_le
                have hsum_lt' : a * |x| + b * |y| < 1 := by
                  simpa [hab, mul_one] using hsum_lt
                exact (not_lt_of_ge htri') hsum_lt'
              have hy_ge : ¬ |y| < 1 := by
                intro hy_lt
                have hby_lt : b * |y| < b * 1 := mul_lt_mul_of_pos_left hy_lt hb_pos
                have hax_le : a * |x| ≤ a * 1 := mul_le_mul_of_nonneg_left hx_le ha
                have hsum_lt : a * |x| + b * |y| < a * 1 + b * 1 :=
                  add_lt_add_of_le_of_lt hax_le hby_lt
                have hsum_lt' : a * |x| + b * |y| < 1 := by
                  simpa [hab, mul_one] using hsum_lt
                exact (not_lt_of_ge htri') hsum_lt'
              have hx_eq : |x| = 1 := le_antisymm hx_le (le_of_not_gt hx_ge)
              have hy_eq : |y| = 1 := le_antisymm hy_le (le_of_not_gt hy_ge)
              have hp_nonneg : 0 ≤ p.2 := hp2_nonneg hx_eq
              have hq_nonneg : 0 ≤ q.2 := hq2_nonneg hy_eq
              exact add_nonneg (mul_nonneg ha hp_nonneg) (mul_nonneg hb hq_nonneg)
        have hf : f (a • p.1 + b • q.1) = (0 : EReal) := by
          simp [f, hEq']
        have hle0 : (0 : EReal) ≤ ((a • p + b • q).2 : EReal) := by
          have hle' :
              ((0 : Real) : EReal) ≤ ((a * p.2 + b * q.2 : Real) : EReal) :=
            (EReal.coe_le_coe_iff).2 hnonneg
          simpa [hcomb2] using hle'
        simpa [hf] using hle0
    exact (by
      have hmem : Set.univ (a • p.1 + b • q.1) ∧
          f (a • p.1 + b • q.1) ≤ ((a • p + b • q).2 : EReal) := by
        exact ⟨by trivial, hle⟩
      simpa [epigraph] using hmem)
  have hnotproper : ¬ ProperConvexFunctionOn (Set.univ) f := by
    intro hproper
    have hbot : f (fun _ => (0 : Real)) = (⊥ : EReal) := by
      simp [f]
    exact (hproper.2.2 (fun _ => (0 : Real)) (by simp)) hbot
  have hnot_top : ¬ ∀ x, f x = (⊤ : EReal) := by
    intro h
    have h0 := h (fun _ => (0 : Real))
    simp [f] at h0
  have hnot_bot : ¬ ∀ x, f x = (⊥ : EReal) := by
    intro h
    have h2 := h (fun _ => (2 : Real))
    simp [f] at h2
  refine ⟨⟨hconv, hnotproper⟩, hnot_top, hnot_bot⟩

/-- Definition 4.8: A function `f` on `ℝ^n` is positively homogeneous (of degree 1)
if for every `x` and every `λ` with `0 < λ`, one has `f (λ • x) = λ * f x`. -/
def PositivelyHomogeneous {n : Nat} (f : (Fin n → Real) → EReal) : Prop :=
  ∀ x : Fin n → Real, ∀ t : Real, 0 < t → f (t • x) = (t : EReal) * f x

/-- A convex positively homogeneous function is subadditive. -/
lemma subadditive_of_convex_posHom {n : Nat} {f : (Fin n → Real) → EReal}
    (hpos : PositivelyHomogeneous f) (hconv : ConvexFunction f) (hnotbot : ∀ x, f x ≠ ⊥) :
    ∀ x y : Fin n → Real, f (x + y) ≤ f x + f y := by
  have hconv' : ConvexFunctionOn (Set.univ) f := by
    simpa [ConvexFunction] using hconv
  have hseg :=
    (convexFunctionOn_iff_segment_inequality (C := Set.univ) (f := f)
      (hC := convex_univ)
      (hnotbot := by
        intro x hx
        simpa using hnotbot x)).1 hconv'
  intro x y
  have h := hseg ((2 : Real) • x) (by simp) ((2 : Real) • y) (by simp)
    ((2 : Real)⁻¹) (by norm_num) (by norm_num)
  have hhalf : (1 - (2 : Real)⁻¹) = (2 : Real)⁻¹ := by
    norm_num
  have hcomb :
      (1 - (2 : Real)⁻¹) • ((2 : Real) • x) + (2 : Real)⁻¹ • ((2 : Real) • y) = x + y := by
    calc
      (1 - (2 : Real)⁻¹) • ((2 : Real) • x) + (2 : Real)⁻¹ • ((2 : Real) • y)
          = ((2 : Real)⁻¹ * 2) • x + ((2 : Real)⁻¹ * 2) • y := by
              simp [smul_smul, hhalf]
      _ = x + y := by
              simp
  have h' :
      f (x + y) ≤ ((2 : Real)⁻¹ : EReal) * f ((2 : Real) • x) +
        ((2 : Real)⁻¹ : EReal) * f ((2 : Real) • y) := by
    have h' := h
    rw [hcomb] at h'
    rw [hhalf] at h'
    simpa using h'
  have hx : f ((2 : Real) • x) = (2 : EReal) * f x := hpos x (2 : Real) (by norm_num)
  have hy : f ((2 : Real) • y) = (2 : EReal) * f y := hpos y (2 : Real) (by norm_num)
  have hscale : ((2 : Real)⁻¹ : EReal) * (2 : EReal) = (1 : EReal) := by
    calc
      ((2 : Real)⁻¹ : EReal) * (2 : EReal)
          = (((2 : Real)⁻¹ * 2 : Real) : EReal) := by
              simpa using (EReal.coe_mul ((2 : Real)⁻¹) 2).symm
      _ = (1 : EReal) := by norm_num
  have hmul : ∀ z : EReal, ((2 : Real)⁻¹ : EReal) * ((2 : EReal) * z) = z := by
    intro z
    calc
      ((2 : Real)⁻¹ : EReal) * ((2 : EReal) * z)
          = (((2 : Real)⁻¹ : EReal) * (2 : EReal)) * z := by
              simpa using (mul_assoc ((2 : Real)⁻¹ : EReal) (2 : EReal) z).symm
      _ = (1 : EReal) * z := by simp [hscale]
      _ = z := by simp
  calc
    f (x + y) ≤ ((2 : Real)⁻¹ : EReal) * f ((2 : Real) • x) +
        ((2 : Real)⁻¹ : EReal) * f ((2 : Real) • y) := h'
    _ = ((2 : Real)⁻¹ : EReal) * ((2 : EReal) * f x) +
        ((2 : Real)⁻¹ : EReal) * ((2 : EReal) * f y) := by
          rw [hx, hy]
    _ = f x + f y := by
          simp [hmul]

/-- Subadditivity and positive homogeneity yield the segment inequality. -/
lemma segment_inequality_of_subadditive_posHom {n : Nat} {f : (Fin n → Real) → EReal}
    (hpos : PositivelyHomogeneous f)
    (hsub : ∀ x y : Fin n → Real, f (x + y) ≤ f x + f y) :
    ∀ x y : Fin n → Real, ∀ t : Real, 0 < t → t < 1 →
      f ((1 - t) • x + t • y) ≤
        ((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y := by
  intro x y t ht0 ht1
  have ht1' : 0 < 1 - t := by linarith
  have h := hsub ((1 - t) • x) (t • y)
  calc
    f ((1 - t) • x + t • y) ≤ f ((1 - t) • x) + f (t • y) := h
    _ = ((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y := by
          simp [hpos x (1 - t) ht1', hpos y t ht0]

/-- Subadditivity and positive homogeneity imply convexity. -/
lemma convex_of_subadditive_posHom {n : Nat} {f : (Fin n → Real) → EReal}
    (hpos : PositivelyHomogeneous f)
    (hsub : ∀ x y : Fin n → Real, f (x + y) ≤ f x + f y)
    (hnotbot : ∀ x, f x ≠ ⊥) :
    ConvexFunction f := by
  have hseg := segment_inequality_of_subadditive_posHom (hpos := hpos) hsub
  have hconv : ConvexFunctionOn (Set.univ) f := by
    refine (convexFunctionOn_iff_segment_inequality (C := Set.univ) (f := f)
      (hC := convex_univ)
      (hnotbot := by
        intro x hx
        simpa using hnotbot x)).2 ?_
    intro x hx y hy t ht0 ht1
    simpa using hseg x y t ht0 ht1
  simpa [ConvexFunction] using hconv

/-- Theorem 4.7: A positively homogeneous function `f` from `R^n` to `(-∞, +∞]` is
convex iff `f (x + y) ≤ f x + f y` for every `x` and `y` in `R^n`. -/
theorem convexFunction_iff_subadditive_of_posHom {n : Nat} {f : (Fin n → Real) → EReal}
    (hpos : PositivelyHomogeneous f) (hnotbot : ∀ x, f x ≠ ⊥) :
    ConvexFunction f ↔ ∀ x y : Fin n → Real, f (x + y) ≤ f x + f y := by
  constructor
  · intro hconv
    exact subadditive_of_convex_posHom (hpos := hpos) hconv hnotbot
  · intro hsub
    exact convex_of_subadditive_posHom (hpos := hpos) hsub hnotbot

/-- Corollary 4.7.1: If `f` is a positively homogeneous proper convex function, then
`f (lambda_1 x_1 + ... + lambda_m x_m) ≤ lambda_1 f x_1 + ... + lambda_m f x_m`
whenever `lambda_1 > 0, ..., lambda_m > 0`. -/
lemma convexFunction_jensen_inequality_of_posHom_proper {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hpos : PositivelyHomogeneous f)
    (hproper : ProperConvexFunctionOn (Set.univ) f) :
    ∀ m : Nat, m ≠ 0 → ∀ w : Fin m → Real, ∀ x : Fin m → (Fin n → Real),
      (∀ i, 0 < w i) →
        f (Finset.univ.sum (fun i => w i • x i)) ≤
          Finset.univ.sum (fun i => ((w i : Real) : EReal) * f (x i)) := by
  classical
  intro m hm w x hwpos
  let s : Real := Finset.univ.sum w
  have hs_pos : 0 < s := by
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
    let i0 : Fin m := ⟨0, hm_pos⟩
    have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin m)), 0 ≤ w i := by
      intro i hi
      exact le_of_lt (hwpos i)
    have hpos : ∃ i ∈ (Finset.univ : Finset (Fin m)), 0 < w i := by
      exact ⟨i0, by simp, hwpos i0⟩
    have hsum : 0 < Finset.univ.sum w := Finset.sum_pos' hnonneg hpos
    simpa [s] using hsum
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  let w' : Fin m → Real := fun i => w i / s
  have hw'_nonneg : ∀ i, 0 ≤ w' i := by
    intro i
    exact div_nonneg (le_of_lt (hwpos i)) (le_of_lt hs_pos)
  have hsum_w' : Finset.univ.sum w' = 1 := by
    have hsum_w' :
        (Finset.univ.sum w') = (Finset.univ.sum w) / s := by
      simpa [w'] using
        (Finset.sum_div (s := Finset.univ) (f := w) (a := s)).symm
    calc
      Finset.univ.sum w' = (Finset.univ.sum w) / s := hsum_w'
      _ = s / s := by simp [s]
      _ = (1 : Real) := by simp [hs_ne]
  have hconv : ConvexFunctionOn (Set.univ) f := hproper.1
  have hjensen :=
    jensen_inequality_of_convexFunctionOn_univ (f := f) hconv
      (by
        intro y
        exact hproper.2.2 y (by simp))
      m w' x hw'_nonneg hsum_w'
  have hcoeff : ∀ i, w i = s * w' i := by
    intro i
    have : w i = s * (w i / s) := by
      field_simp [hs_ne]
    simpa [w'] using this
  have hsum_w :
      Finset.univ.sum (fun i => w i • x i) =
        s • Finset.univ.sum (fun i => w' i • x i) := by
    calc
      Finset.univ.sum (fun i => w i • x i) =
          Finset.univ.sum (fun i => (s * w' i) • x i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [hcoeff i]
      _ = Finset.univ.sum (fun i => s • (w' i • x i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [smul_smul]
      _ = s • Finset.univ.sum (fun i => w' i • x i) := by
            simpa using
              (Finset.smul_sum (s := Finset.univ)
                (f := fun i => w' i • x i) (r := s)).symm
  have hs_nonneg : (0 : EReal) ≤ (s : EReal) :=
    EReal.coe_nonneg.mpr (le_of_lt hs_pos)
  have hmul :
      (s : EReal) * f (Finset.univ.sum (fun i => w' i • x i)) ≤
        (s : EReal) *
          (Finset.univ.sum (fun i => ((w' i : Real) : EReal) * f (x i))) := by
    exact mul_le_mul_of_nonneg_left hjensen hs_nonneg
  have hsum_scale :
      (s : EReal) *
          (Finset.univ.sum (fun i => ((w' i : Real) : EReal) * f (x i))) =
        Finset.univ.sum (fun i => ((w i : Real) : EReal) * f (x i)) := by
    have hmul_sum :=
      EReal.mul_sum_of_nonneg_of_ne_top (s := Finset.univ) (a := (s : EReal)) hs_nonneg
        (EReal.coe_ne_top s) (f := fun i => ((w' i : Real) : EReal) * f (x i))
    calc
      (s : EReal) *
          (Finset.univ.sum (fun i => ((w' i : Real) : EReal) * f (x i))) =
          Finset.univ.sum (fun i =>
            (s : EReal) * (((w' i : Real) : EReal) * f (x i))) := by
              simpa using hmul_sum
      _ = Finset.univ.sum (fun i => ((w i : Real) : EReal) * f (x i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hw : s * w' i = w i := (hcoeff i).symm
            calc
              (s : EReal) * (((w' i : Real) : EReal) * f (x i)) =
                  ((s : EReal) * ((w' i : Real) : EReal)) * f (x i) := by
                    simp [mul_assoc]
              _ = ((s * w' i : Real) : EReal) * f (x i) := by
                    simp [EReal.coe_mul]
              _ = ((w i : Real) : EReal) * f (x i) := by
                    simp [hw]
  calc
    f (Finset.univ.sum (fun i => w i • x i)) =
        f (s • Finset.univ.sum (fun i => w' i • x i)) := by
          simp [hsum_w]
    _ = (s : EReal) * f (Finset.univ.sum (fun i => w' i • x i)) := by
          simpa using
            (hpos (Finset.univ.sum (fun i => w' i • x i)) s hs_pos)
    _ ≤ (s : EReal) *
          (Finset.univ.sum (fun i => ((w' i : Real) : EReal) * f (x i))) := hmul
    _ = Finset.univ.sum (fun i => ((w i : Real) : EReal) * f (x i)) := hsum_scale

/-- For a positively homogeneous proper convex function, `f 0` is nonnegative. -/
lemma posHom_zero_nonneg {n : Nat} {f : (Fin n → Real) → EReal}
    (hpos : PositivelyHomogeneous f)
    (hproper : ProperConvexFunctionOn (Set.univ) f) :
    (0 : EReal) ≤ f 0 := by
  have hnotbot : f 0 ≠ (⊥ : EReal) := hproper.2.2 0 (by simp)
  cases h0 : f 0 using EReal.rec with
  | bot =>
      exfalso
      exact hnotbot (by simp [h0])
  | top =>
      simp
  | coe r =>
      have hpos0 := hpos (0 : Fin n → Real) (2 : Real) (by norm_num)
      have hpos0' : (r : EReal) = ((2 : Real) : EReal) * (r : EReal) := by
        simpa [h0] using hpos0
      have hpos0'' : (r : EReal) = ((2 * r : Real) : EReal) := by
        calc
          (r : EReal) = ((2 : Real) : EReal) * (r : EReal) := hpos0'
          _ = ((2 * r : Real) : EReal) := by
            exact (EReal.coe_mul (2 : Real) r).symm
      have hreal : r = 2 * r := (EReal.coe_eq_coe_iff).1 hpos0''
      have hr : r = 0 := by linarith
      simp [hr]

/-- Proper convexity plus positive homogeneity yield subadditivity. -/
lemma subadditive_of_posHom_proper {n : Nat} {f : (Fin n → Real) → EReal}
    (hpos : PositivelyHomogeneous f)
    (hproper : ProperConvexFunctionOn (Set.univ) f) :
    ∀ x y : Fin n → Real, f (x + y) ≤ f x + f y := by
  have hconv : ConvexFunction f := by
    have hconv_on : ConvexFunctionOn (Set.univ) f := hproper.1
    simpa [ConvexFunction] using hconv_on
  exact subadditive_of_convex_posHom (hpos := hpos) hconv
    (by intro x; exact hproper.2.2 x (by simp))

/-- A nonnegative sum gives a lower bound on the second term. -/
lemma ereal_neg_le_of_add_nonneg {a b : EReal}
    (ha : a ≠ (⊥ : EReal)) (hb : b ≠ (⊥ : EReal))
    (h : (0 : EReal) ≤ a + b) : -a ≤ b := by
  cases ha' : a using EReal.rec with
  | bot =>
      exact (ha (by simp [ha'])).elim
  | top =>
      simp [EReal.neg_top]
  | coe r =>
      cases hb' : b using EReal.rec with
      | bot =>
          exact (hb (by simp [hb'])).elim
      | top =>
          simp
      | coe s =>
          have h' :
              (0 : EReal) ≤ ((r : Real) : EReal) + ((s : Real) : EReal) := by
            simpa [ha', hb'] using h
          have h'' :
              (0 : EReal) ≤ ((r + s : Real) : EReal) := by
            simpa [EReal.coe_add] using h'
          have hreal : (0 : Real) ≤ r + s := (EReal.coe_le_coe_iff).1 h''
          have hreal' : (-r : Real) ≤ s := by linarith
          have hE : ((-r : Real) : EReal) ≤ ((s : Real) : EReal) :=
            (EReal.coe_le_coe_iff).2 hreal'
          have hE' : -((r : Real) : EReal) ≤ ((s : Real) : EReal) := by
            simpa [EReal.coe_neg] using hE
          simpa [ha', hb'] using hE'

/-- Corollary 4.7.2: If `f` is a positively homogeneous proper convex function, then
`f (-x) ≥ -f x` for every `x`. -/
lemma convexFunction_neg_ge_neg_of_posHom_proper {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hpos : PositivelyHomogeneous f)
    (hproper : ProperConvexFunctionOn (Set.univ) f) :
    ∀ x : Fin n → Real, f (-x) ≥ -f x := by
  intro x
  have hsub := subadditive_of_posHom_proper (hpos := hpos) (hproper := hproper)
  have h0le : (0 : EReal) ≤ f 0 :=
    posHom_zero_nonneg (hpos := hpos) (hproper := hproper)
  have hxbot : f x ≠ (⊥ : EReal) := hproper.2.2 x (by simp)
  have hxbott : f (-x) ≠ (⊥ : EReal) := hproper.2.2 (-x) (by simp)
  have hsum : (0 : EReal) ≤ f x + f (-x) := by
    have h0 : f 0 ≤ f x + f (-x) := by
      have h := hsub x (-x)
      simpa using h
    exact le_trans h0le h0
  have hneg : -f x ≤ f (-x) :=
    ereal_neg_le_of_add_nonneg (ha := hxbot) (hb := hxbott) hsum
  exact hneg

/-- Oddness at a point rules out the value `⊤`. -/
lemma ne_top_of_neg_eq_neg {n : Nat} {f : (Fin n → Real) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ) f) {x : Fin n → Real}
    (hneg : f (-x) = -f x) : f x ≠ (⊤ : EReal) := by
  intro hx
  have hbot : f (-x) = (⊥ : EReal) := by simpa [hx] using hneg
  exact hproper.2.2 (-x) (by simp) hbot

/-- Under oddness at `x`, `f x` can be rewritten as a real. -/
lemma coe_toReal_of_neg_eq_neg {n : Nat} {f : (Fin n → Real) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ) f) {x : Fin n → Real}
    (hneg : f (-x) = -f x) : ((f x).toReal : EReal) = f x := by
  have hxbot : f x ≠ (⊥ : EReal) := hproper.2.2 x (by simp)
  have hxtop : f x ≠ (⊤ : EReal) := ne_top_of_neg_eq_neg (hproper := hproper) hneg
  simpa using (EReal.coe_toReal (x := f x) (hx := hxtop) (h'x := hxbot))

/-- Oddness at a vector extends positive homogeneity to all real scalars. -/
lemma posHom_all_real_of_neg_vec {n : Nat} {f : (Fin n → Real) → EReal}
    (hpos : PositivelyHomogeneous f)
    (hproper : ProperConvexFunctionOn (Set.univ) f) {v : Fin n → Real}
    (hnegv : f (-v) = -f v) :
    ∀ t : Real, f (t • v) = (t : EReal) * f v := by
  have hsub := subadditive_of_posHom_proper (hpos := hpos) (hproper := hproper)
  have hv_coe : ((f v).toReal : EReal) = f v :=
    coe_toReal_of_neg_eq_neg (hproper := hproper) hnegv
  have h0le : (0 : EReal) ≤ f 0 :=
    posHom_zero_nonneg (hpos := hpos) (hproper := hproper)
  have h0le' : f 0 ≤ (0 : EReal) := by
    have h' : f 0 ≤ f v + f (-v) := by
      have h := hsub v (-v)
      simpa using h
    have hsum : f v + f (-v) = (0 : EReal) := by
      have hv_coe' : f v = ((f v).toReal : EReal) := by
        simpa using hv_coe.symm
      have hv_neg_coe' : -f v = -((f v).toReal : EReal) := by
        simpa using congrArg Neg.neg hv_coe'
      calc
        f v + f (-v) = f v + -f v := by
          simp [hnegv]
        _ = ((f v).toReal : EReal) + -f v := by
          simpa using congrArg (fun z : EReal => z + -f v) hv_coe'
        _ = ((f v).toReal : EReal) + -((f v).toReal : EReal) := by
          simpa using congrArg (fun z : EReal => ((f v).toReal : EReal) + z) hv_neg_coe'
        _ = ((f v).toReal : EReal) + ((-(f v).toReal : Real) : EReal) := by
          simp [EReal.coe_neg]
        _ = (((f v).toReal + -(f v).toReal : Real) : EReal) := by
          simpa using (EReal.coe_add (f v).toReal (-(f v).toReal)).symm
        _ = (0 : EReal) := by simp
    simpa [hsum] using h'
  have h0 : f 0 = (0 : EReal) := le_antisymm h0le' h0le
  intro t
  by_cases ht : t = 0
  · subst ht
    simp [h0]
  · by_cases htpos : 0 < t
    · simpa using hpos v t htpos
    · have htneg : t < 0 := lt_of_le_of_ne (le_of_not_gt htpos) ht
      have htpos' : 0 < -t := by linarith
      have hpos' := hpos (-v) (-t) htpos'
      calc
        f (t • v) = f ((-t) • (-v)) := by
          simp
        _ = (-t : EReal) * f (-v) := hpos'
        _ = (-t : EReal) * (-f v) := by simp [hnegv]
        _ = ((-t) * (-(f v).toReal) : Real) := by
              simp [hv_coe, EReal.coe_mul]
        _ = ((t * (f v).toReal : Real) : EReal) := by
              have : (-t) * (-(f v).toReal) = t * (f v).toReal := by ring
              simp [this]
        _ = (t : EReal) * f v := by
              simp [hv_coe, EReal.coe_mul]

/-- Oddness on a submodule yields additivity there. -/
lemma additive_on_L_of_neg {n : Nat} {f : (Fin n → Real) → EReal}
    (hpos : PositivelyHomogeneous f)
    (hproper : ProperConvexFunctionOn (Set.univ) f)
    {L : Submodule Real (Fin n → Real)}
    (hneg : ∀ x : L, f (-(x : (Fin n → Real))) = -f (x : (Fin n → Real))) :
    ∀ x y : L, f ((x + y : L) : (Fin n → Real)) =
      f (x : (Fin n → Real)) + f (y : (Fin n → Real)) := by
  intro x y
  have hsub := subadditive_of_posHom_proper (hpos := hpos) (hproper := hproper)
  have hxy_le :
      f ((x + y : L) : (Fin n → Real)) ≤
        f (x : (Fin n → Real)) + f (y : (Fin n → Real)) := by
    simpa using (hsub (x : (Fin n → Real)) (y : (Fin n → Real)))
  have hsubneg := hsub (-(x : (Fin n → Real))) (-(y : (Fin n → Real)))
  have hsubneg' :
      f (-( (x + y : L) : (Fin n → Real))) ≤
        f (-(x : (Fin n → Real))) + f (-(y : (Fin n → Real))) := by
    have hsumneg :
        (-(x : (Fin n → Real)) + -(y : (Fin n → Real))) =
          -((x + y : L) : (Fin n → Real)) := by
      simpa using (neg_add (x : (Fin n → Real)) (y : (Fin n → Real))).symm
    simpa [hsumneg] using hsubneg
  have hnegxy := hneg (x + y)
  have hnegx := hneg x
  have hnegy := hneg y
  have hineq :
      -f ((x + y : L) : (Fin n → Real)) ≤
        -f (x : (Fin n → Real)) + -f (y : (Fin n → Real)) := by
    have hsubneg'' := hsubneg'
    rw [hnegx, hnegy] at hsubneg''
    rw [hnegxy] at hsubneg''
    exact hsubneg''
  have hx_coe :
      ((f (x : (Fin n → Real))).toReal : EReal) = f (x : (Fin n → Real)) :=
    coe_toReal_of_neg_eq_neg (hproper := hproper) (hneg := hnegx)
  have hy_coe :
      ((f (y : (Fin n → Real))).toReal : EReal) = f (y : (Fin n → Real)) :=
    coe_toReal_of_neg_eq_neg (hproper := hproper) (hneg := hnegy)
  have hxy_coe :
      ((f ((x + y : L) : (Fin n → Real))).toReal : EReal) =
        f ((x + y : L) : (Fin n → Real)) :=
    coe_toReal_of_neg_eq_neg (hproper := hproper) (hneg := hnegxy)
  have hineq_real :
      -(f ((x + y : L) : (Fin n → Real))).toReal ≤
        -(f (x : (Fin n → Real))).toReal + -(f (y : (Fin n → Real))).toReal := by
    have hineq' :
        -((f ((x + y : L) : (Fin n → Real))).toReal : EReal) ≤
          -((f (x : (Fin n → Real))).toReal : EReal) +
            -((f (y : (Fin n → Real))).toReal : EReal) := by
      have hineq' := hineq
      rw [←hxy_coe, ←hx_coe, ←hy_coe] at hineq'
      exact hineq'
    have hineq'' :
        ((-(f ((x + y : L) : (Fin n → Real))).toReal : Real) : EReal) ≤
          (((-(f (x : (Fin n → Real))).toReal + -(f (y : (Fin n → Real))).toReal) :
              Real) : EReal) := by
      simpa [EReal.coe_neg, EReal.coe_add] using hineq'
    exact (EReal.coe_le_coe_iff).1 hineq''
  have hineq_real' :
      (f (x : (Fin n → Real))).toReal + (f (y : (Fin n → Real))).toReal ≤
        (f ((x + y : L) : (Fin n → Real))).toReal := by
    linarith
  have hineq_E :
      f (x : (Fin n → Real)) + f (y : (Fin n → Real)) ≤
        f ((x + y : L) : (Fin n → Real)) := by
    have hcoe :
        (((f (x : (Fin n → Real))).toReal +
            (f (y : (Fin n → Real))).toReal : Real) : EReal) ≤
          ((f ((x + y : L) : (Fin n → Real))).toReal : EReal) :=
      (EReal.coe_le_coe_iff).2 hineq_real'
    have hcoe' := hcoe
    rw [EReal.coe_add, hx_coe, hy_coe, hxy_coe] at hcoe'
    exact hcoe'
  exact le_antisymm hxy_le hineq_E

/-- Oddness on a submodule yields a linear map representing `f` there. -/
lemma linear_map_of_neg_on_L {n : Nat} {f : (Fin n → Real) → EReal}
    (hpos : PositivelyHomogeneous f)
    (hproper : ProperConvexFunctionOn (Set.univ) f)
    {L : Submodule Real (Fin n → Real)}
    (hneg : ∀ x : L, f (-(x : (Fin n → Real))) = -f (x : (Fin n → Real))) :
    ∃ g : L →ₗ[Real] Real, ∀ x : L,
      f (x : (Fin n → Real)) = (g x : EReal) := by
  classical
  have hadd := additive_on_L_of_neg (hpos := hpos) (hproper := hproper) hneg
  have hsmul :
      ∀ t : Real, ∀ x : L,
        f ((t • x : L) : (Fin n → Real)) =
          (t : EReal) * f (x : (Fin n → Real)) := by
    intro t x
    exact posHom_all_real_of_neg_vec (hpos := hpos) (hproper := hproper) (hneg x) t
  let g : L → Real := fun x => (f (x : (Fin n → Real))).toReal
  have hfin :
      ∀ x : L, f (x : (Fin n → Real)) ≠ (⊥ : EReal) ∧
        f (x : (Fin n → Real)) ≠ (⊤ : EReal) := by
    intro x
    refine ⟨hproper.2.2 (x : (Fin n → Real)) (by simp), ?_⟩
    exact ne_top_of_neg_eq_neg (hproper := hproper) (hneg := hneg x)
  have hcoe : ∀ x : L, (g x : EReal) = f (x : (Fin n → Real)) := by
    intro x
    have hx := hfin x
    simpa [g] using (EReal.coe_toReal (x := f (x : (Fin n → Real)))
      (hx := hx.2) (h'x := hx.1))
  refine ⟨
    { toFun := g
      map_add' := ?_
      map_smul' := ?_ }, ?_⟩
  · intro x y
    have hE :
        (g (x + y) : EReal) = (g x : EReal) + (g y : EReal) := by
      calc
        (g (x + y) : EReal) =
            f ((x + y : L) : (Fin n → Real)) := by
              simp [hcoe]
        _ = f (x : (Fin n → Real)) + f (y : (Fin n → Real)) := hadd x y
        _ = (g x : EReal) + (g y : EReal) := by
              simp [hcoe]
    have hE' :
        (g (x + y) : EReal) = ((g x + g y : Real) : EReal) := by
      simpa [EReal.coe_add] using hE
    exact (EReal.coe_eq_coe_iff).1 hE'
  · intro t x
    have hE :
        (g (t • x) : EReal) = (t : EReal) * (g x : EReal) := by
      calc
        (g (t • x) : EReal) =
            f ((t • x : L) : (Fin n → Real)) := by
              simp [hcoe]
        _ = (t : EReal) * f (x : (Fin n → Real)) := hsmul t x
        _ = (t : EReal) * (g x : EReal) := by simp [hcoe]
    have hE' :
        (g (t • x) : EReal) = ((t * g x : Real) : EReal) := by
      simpa [EReal.coe_mul] using hE
    have hE'' : g (t • x) = t * g x := (EReal.coe_eq_coe_iff).1 hE'
    simpa [smul_eq_mul] using hE''
  · intro x
    simp [hcoe]

/-- Subadditivity extends to finite sums for positively homogeneous proper convex functions. -/
lemma subadditive_finset_of_posHom_proper {n : Nat} {f : (Fin n → Real) → EReal}
    (hpos : PositivelyHomogeneous f)
    (hproper : ProperConvexFunctionOn (Set.univ) f)
    (hzero : f 0 = (0 : EReal))
    {ι : Type*} (s : Finset ι) (g : ι → Fin n → Real) :
    f (s.sum g) ≤ s.sum (fun i => f (g i)) := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · simp [hzero]
  · intro a s ha hs
    have hsub := subadditive_of_posHom_proper (hpos := hpos) (hproper := hproper)
    have h' : f (g a + s.sum g) ≤ f (g a) + f (s.sum g) := hsub (g a) (s.sum g)
    have h'' : f (g a) + f (s.sum g) ≤ f (g a) + s.sum (fun i => f (g i)) :=
      add_le_add le_rfl hs
    have h''' : f (g a + s.sum g) ≤ f (g a) + s.sum (fun i => f (g i)) :=
      le_trans h' h''
    simpa [Finset.sum_insert, ha, add_comm, add_left_comm, add_assoc] using h'''

/-- A finite sum of real-coe values in `EReal` is the coe of the real sum. -/
lemma ereal_sum_coe {ι : Type*} (s : Finset ι) (r : ι → Real) :
    s.sum (fun i => ((r i : Real) : EReal)) = ((s.sum r : Real) : EReal) := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · simp
  · intro a s ha hs
    simp [ha, hs, EReal.coe_add]

/-- Oddness on a basis implies oddness on all of the submodule. -/
lemma neg_on_L_of_basis_neg {n : Nat} {f : (Fin n → Real) → EReal}
    (hpos : PositivelyHomogeneous f)
    (hproper : ProperConvexFunctionOn (Set.univ) f)
    {L : Submodule Real (Fin n → Real)} {ι : Type*} [Fintype ι] [Nonempty ι]
    (b : Module.Basis ι Real L)
    (hnegb : ∀ i, f (-(b i : (Fin n → Real))) = -f (b i : (Fin n → Real))) :
    ∀ x : L, f (-(x : (Fin n → Real))) = -f (x : (Fin n → Real)) := by
  classical
  have i0 : ι := Classical.choice (inferInstance : Nonempty ι)
  have hzero : f 0 = (0 : EReal) := by
    have hposall :=
      posHom_all_real_of_neg_vec (hpos := hpos) (hproper := hproper)
        (v := (b i0 : (Fin n → Real))) (hnegv := hnegb i0)
    have h0 := hposall 0
    simpa using h0
  intro x
  let c : ι → Real := fun i => b.repr x i
  let r : ι → Real := fun i => (f (b i : (Fin n → Real))).toReal
  have hbi_coe : ∀ i, f (b i : (Fin n → Real)) = ((r i : Real) : EReal) := by
    intro i
    simpa [r] using
      (coe_toReal_of_neg_eq_neg (hproper := hproper) (hneg := hnegb i)).symm
  have hterm :
      ∀ i t, f (t • (b i : (Fin n → Real))) = ((t * r i : Real) : EReal) := by
    intro i t
    have hposall :=
      posHom_all_real_of_neg_vec (hpos := hpos) (hproper := hproper) (hnegv := hnegb i)
    calc
      f (t • (b i : (Fin n → Real))) =
          (t : EReal) * f (b i : (Fin n → Real)) := hposall t
      _ = (t : EReal) * ((r i : Real) : EReal) := by simp [hbi_coe]
      _ = ((t * r i : Real) : EReal) := by simp [EReal.coe_mul]
  have hx_repr_L : (x : L) = ∑ i, c i • b i := by
    symm
    simp [c, b.sum_repr]
  have hx_repr :
      (x : (Fin n → Real)) =
        Finset.univ.sum (fun i => c i • (b i : (Fin n → Real))) := by
    simpa using congrArg (fun y : L => (y : (Fin n → Real))) hx_repr_L
  have hneg_repr_L : (-x : L) = ∑ i, (-c i) • b i := by
    calc
      (-x : L) = -(∑ i, c i • b i) := by
        simp [hx_repr_L]
      _ = ∑ i, -(c i • b i) := by
        classical
        simp [Finset.sum_neg_distrib]
      _ = ∑ i, (-c i) • b i := by
        classical
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact (neg_smul (c i) (b i)).symm
  have hneg_repr :
      (-(x : (Fin n → Real))) =
        Finset.univ.sum (fun i => (-c i) • (b i : (Fin n → Real))) := by
    simpa using congrArg (fun y : L => (y : (Fin n → Real))) hneg_repr_L
  have hsubsum :=
    subadditive_finset_of_posHom_proper (ι := ι) (hpos := hpos) (hproper := hproper)
      (hzero := hzero)
  have hx_le :
      f (x : (Fin n → Real)) ≤
        Finset.univ.sum (fun i => f (c i • (b i : (Fin n → Real)))) := by
    have h := hsubsum (s := (Finset.univ : Finset ι))
      (g := fun i => c i • (b i : (Fin n → Real)))
    simpa [hx_repr] using h
  have hneg_le :
      f (-(x : (Fin n → Real))) ≤
        Finset.univ.sum (fun i => f ((-c i) • (b i : (Fin n → Real)))) := by
    have h := hsubsum (s := (Finset.univ : Finset ι))
      (g := fun i => (-c i) • (b i : (Fin n → Real)))
    rw [←hneg_repr] at h
    exact h
  have hsum_coe :
      Finset.univ.sum (fun i => f (c i • (b i : (Fin n → Real)))) =
        ((Finset.univ.sum (fun i => c i * r i) : Real) : EReal) := by
    calc
      Finset.univ.sum (fun i => f (c i • (b i : (Fin n → Real)))) =
          Finset.univ.sum (fun i => ((c i * r i : Real) : EReal)) := by
            simp [hterm]
      _ =
          ((Finset.univ.sum (fun i => c i * r i) : Real) : EReal) := by
            simpa using
              (ereal_sum_coe (s := (Finset.univ : Finset ι)) (r := fun i => c i * r i))
  have hsumneg_coe :
      Finset.univ.sum (fun i => f ((-c i) • (b i : (Fin n → Real)))) =
        ((Finset.univ.sum (fun i => (-c i) * r i) : Real) : EReal) := by
    calc
      Finset.univ.sum (fun i => f ((-c i) • (b i : (Fin n → Real)))) =
          Finset.univ.sum (fun i => (((-c i) * r i : Real) : EReal)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa using (hterm i (-c i))
      _ =
          ((Finset.univ.sum (fun i => (-c i) * r i) : Real) : EReal) := by
            simpa using
              (ereal_sum_coe (s := (Finset.univ : Finset ι)) (r := fun i => (-c i) * r i))
  have hneg_le' :
      f (-(x : (Fin n → Real))) ≤
        ((Finset.univ.sum (fun i => (-c i) * r i) : Real) : EReal) := by
    have hneg_le' := hneg_le
    rw [hsumneg_coe] at hneg_le'
    exact hneg_le'
  have hxbot : f (-(x : (Fin n → Real))) ≠ (⊥ : EReal) :=
    hproper.2.2 (-(x : (Fin n → Real))) (by simp)
  have hxtop : f (-(x : (Fin n → Real))) ≠ (⊤ : EReal) := by
    intro htop
    have htop_le :
        (⊤ : EReal) ≤ ((Finset.univ.sum (fun i => (-c i) * r i) : Real) : EReal) := by
      rw [←htop]
      exact hneg_le'
    exact (not_top_le_coe _ htop_le)
  have hneg_coe :
      (((f (-(x : (Fin n → Real)))).toReal : EReal)) =
        f (-(x : (Fin n → Real))) := by
    simpa using (EReal.coe_toReal (x := f (-(x : (Fin n → Real))))
      (hx := hxtop) (h'x := hxbot))
  have hneg_le_real :
      ((f (-(x : (Fin n → Real)))).toReal) ≤
        Finset.univ.sum (fun i => (-c i) * r i) := by
    have hneg_le_coe :
        (((f (-(x : (Fin n → Real)))).toReal : EReal)) ≤
          ((Finset.univ.sum (fun i => (-c i) * r i) : Real) : EReal) := by
      have hneg_le_coe := hneg_le'
      rw [hneg_coe.symm] at hneg_le_coe
      exact hneg_le_coe
    exact (EReal.coe_le_coe_iff).1 hneg_le_coe
  have hsumneg_real :
      Finset.univ.sum (fun i => (-c i) * r i) =
        - (Finset.univ.sum (fun i => c i * r i)) := by
    calc
      Finset.univ.sum (fun i => (-c i) * r i) =
          Finset.univ.sum (fun i => -(c i * r i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = - (Finset.univ.sum (fun i => c i * r i)) := by
            simp [Finset.sum_neg_distrib]
  have hsum_le_real :
      (Finset.univ.sum (fun i => c i * r i)) ≤
        - ((f (-(x : (Fin n → Real)))).toReal) := by
    have hneg_le_real' :
        ((f (-(x : (Fin n → Real)))).toReal) ≤
          - (Finset.univ.sum (fun i => c i * r i)) := by
      simpa [hsumneg_real] using hneg_le_real
    linarith
  have hsum_le_negfx :
      Finset.univ.sum (fun i => f (c i • (b i : (Fin n → Real)))) ≤
        -f (-(x : (Fin n → Real))) := by
    have hcoe :
        ((Finset.univ.sum (fun i => c i * r i) : Real) : EReal) ≤
          ((-((f (-(x : (Fin n → Real)))).toReal) : Real) : EReal) :=
      (EReal.coe_le_coe_iff).2 hsum_le_real
    simpa [hsum_coe.symm, hneg_coe, EReal.coe_neg] using hcoe
  have hx_le_neg :
      f (x : (Fin n → Real)) ≤ -f (-(x : (Fin n → Real))) :=
    le_trans hx_le hsum_le_negfx
  have hneg_ge :
      -f (-(x : (Fin n → Real))) ≤ f (x : (Fin n → Real)) := by
    have h := convexFunction_neg_ge_neg_of_posHom_proper (hpos := hpos) (hproper := hproper)
      (x := -(x : (Fin n → Real)))
    simpa using h
  have hfx :
      f (x : (Fin n → Real)) = -f (-(x : (Fin n → Real))) :=
    le_antisymm hx_le_neg hneg_ge
  have hfx' : f (-(x : (Fin n → Real))) = -f (x : (Fin n → Real)) := by
    have hfx_neg := congrArg Neg.neg hfx
    simpa [neg_neg] using hfx_neg.symm
  exact hfx'

/-- Theorem 4.8: A positively homogeneous proper convex function `f` is linear on a
subspace `L` iff `f (-x) = -f x` for every `x ∈ L`. This is true if merely
`f (-b_i) = -f b_i` for all vectors in some basis `b_1, ..., b_m` for `L`. -/
theorem positivelyHomogeneous_properConvex_linear_on_submodule_iff_neg {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hpos : PositivelyHomogeneous f)
    (hproper : ProperConvexFunctionOn (Set.univ) f)
    (L : Submodule Real (Fin n → Real)) :
    ((∃ g : L →ₗ[Real] Real, ∀ x : L, f (x : (Fin n → Real)) = (g x : EReal)) ↔
        (∀ x : L, f (-(x : (Fin n → Real))) = -f (x : (Fin n → Real))))
      ∧
    ((∃ (ι : Type*) (_ : Fintype ι) (_ : Nonempty ι) (b : Module.Basis ι Real L),
          (∀ i, f (-(b i : (Fin n → Real))) = -f (b i : (Fin n → Real)))) →
        (∃ g : L →ₗ[Real] Real, ∀ x : L, f (x : (Fin n → Real)) = (g x : EReal))) := by
  constructor
  · constructor
    · intro hlin x
      rcases hlin with ⟨g, hg⟩
      have hx : f (x : (Fin n → Real)) = (g x : EReal) := hg x
      have hnx : f (-(x : (Fin n → Real))) = (g (-x) : EReal) := hg (-x)
      have hneg : g (-x) = -g x := g.map_neg x
      calc
        f (-(x : (Fin n → Real))) = (g (-x) : EReal) := hnx
        _ = ((-g x : Real) : EReal) := by
              exact congrArg (fun r : Real => (r : EReal)) hneg
        _ = - (g x : EReal) := by simp [EReal.coe_neg]
        _ = -f (x : (Fin n → Real)) := by simp [hx]
    · intro hneg
      exact linear_map_of_neg_on_L (hpos := hpos) (hproper := hproper) hneg
  · intro hb
    rcases hb with ⟨ι, hfin, hnonempty, b, hnegb⟩
    classical
    haveI : Nonempty ι := hnonempty
    have hnegL :
        ∀ x : L, f (-(x : (Fin n → Real))) = -f (x : (Fin n → Real)) :=
      neg_on_L_of_basis_neg (hpos := hpos) (hproper := hproper) (b := b) hnegb
    exact linear_map_of_neg_on_L (hpos := hpos) (hproper := hproper) hnegL

/-- Membership in the epigraph over `Set.univ` is just the inequality. -/
lemma mem_epigraph_univ_iff {n : Nat} {f : (Fin n → Real) → EReal}
    {x : Fin n → Real} {μ : Real} :
    ((x, μ) ∈ epigraph (Set.univ) f) ↔ f x ≤ (μ : EReal) := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨by trivial, h⟩

/-- An extended real bounded above by every real is `⊥`. -/
lemma ereal_eq_bot_of_le_all_coe {x : EReal}
    (h : ∀ μ : Real, x ≤ (μ : EReal)) : x = (⊥ : EReal) := by
  cases hx : x using EReal.rec with
  | bot =>
      rfl
  | coe r =>
      have h' : r ≤ r - 1 := by
        have : (r : EReal) ≤ ((r - 1 : Real) : EReal) := by
          simpa [hx] using h (r - 1)
        exact (EReal.coe_le_coe_iff).1 (by simpa [hx] using this)
      linarith
  | top =>
      have htop : (⊤ : EReal) ≤ (0 : EReal) := by
        simpa [hx] using h 0
      exact (not_top_le_coe 0 htop).elim

/-- Multiplying by a positive real preserves order against a real upper bound. -/
lemma ereal_mul_le_mul_of_pos_left {t : Real} (ht : 0 < t)
    {x : EReal} {μ : Real} (hx : x ≤ (μ : EReal)) :
    (t : EReal) * x ≤ ((t * μ : Real) : EReal) := by
  cases hx' : x using EReal.rec with
  | bot =>
      have hmul : (t : EReal) * (⊥ : EReal) = (⊥ : EReal) :=
        EReal.coe_mul_bot_of_pos (x := t) ht
      simp [hmul]
  | coe r =>
      have hxr : r ≤ μ := by
        have : (r : EReal) ≤ (μ : EReal) := by simpa [hx'] using hx
        exact (EReal.coe_le_coe_iff).1 this
      have hmul : (t * r : Real) ≤ t * μ := by
        have ht' : 0 ≤ t := le_of_lt ht
        exact mul_le_mul_of_nonneg_left hxr ht'
      have hmul' : ((t * r : Real) : EReal) ≤ ((t * μ : Real) : EReal) :=
        (EReal.coe_le_coe_iff).2 hmul
      simpa [hx', EReal.mul] using hmul'
  | top =>
      have htop : (⊤ : EReal) ≤ (μ : EReal) := by
        simp [hx', -top_le_iff] at hx
        exact hx
      exact (not_top_le_coe μ htop).elim

/-- Positive homogeneity implies the epigraph is closed under positive scaling. -/
lemma epigraph_cone_of_posHom {n : Nat} {f : (Fin n → Real) → EReal}
    (hpos : PositivelyHomogeneous f) :
    ∀ t : Real, 0 < t →
      Set.image (fun p : (Fin n → Real) × Real => t • p) (epigraph (Set.univ) f) ⊆
        epigraph (Set.univ) f := by
  intro t ht p hp
  rcases hp with ⟨⟨x, μ⟩, hmem, rfl⟩
  have hμ : f x ≤ (μ : EReal) := (mem_epigraph_univ_iff).1 hmem
  have hmul : (t : EReal) * f x ≤ ((t * μ : Real) : EReal) :=
    ereal_mul_le_mul_of_pos_left (t := t) ht hμ
  have hle : f (t • x) ≤ ((t * μ : Real) : EReal) := by
    simpa [hpos x t ht] using hmul
  have hmem' : (t • x, t * μ) ∈ epigraph (Set.univ) f :=
    (mem_epigraph_univ_iff).2 hle
  simpa [smul_eq_mul] using hmem'

/-- The cone property of the epigraph implies positive homogeneity. -/
lemma posHom_of_epigraph_cone {n : Nat} {f : (Fin n → Real) → EReal}
    (hcone : ∀ t : Real, 0 < t →
      Set.image (fun p : (Fin n → Real) × Real => t • p) (epigraph (Set.univ) f) ⊆
        epigraph (Set.univ) f) :
    PositivelyHomogeneous f := by
  intro x t ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  cases hx : f x using EReal.rec with
  | bot =>
      have hle_all : ∀ μ : Real, f (t • x) ≤ (μ : EReal) := by
        intro μ
        have hxmem : (x, μ / t) ∈ epigraph (Set.univ) f := by
          have : f x ≤ ((μ / t : Real) : EReal) := by
            simp [hx]
          exact (mem_epigraph_univ_iff).2 this
        have hmem : (t • (x, μ / t)) ∈ epigraph (Set.univ) f := by
          have hsubset := hcone t ht
          exact hsubset ⟨(x, μ / t), hxmem, rfl⟩
        have hle' : f (t • x) ≤ ((t * (μ / t) : Real) : EReal) := by
          simpa [mem_epigraph_univ_iff, smul_eq_mul] using hmem
        have hmul : t * (μ / t) = μ := by
          field_simp [ht0]
        simpa [hmul] using hle'
      have hbot : f (t • x) = (⊥ : EReal) := ereal_eq_bot_of_le_all_coe hle_all
      have hmul : (t : EReal) * (⊥ : EReal) = (⊥ : EReal) :=
        EReal.coe_mul_bot_of_pos (x := t) ht
      simp [hbot, hmul]
  | coe r =>
      have hxmem : (x, r) ∈ epigraph (Set.univ) f := by
        have : f x ≤ ((r : Real) : EReal) := by simp [hx]
        exact (mem_epigraph_univ_iff).2 this
      have hmem : (t • (x, r)) ∈ epigraph (Set.univ) f := by
        have hsubset := hcone t ht
        exact hsubset ⟨(x, r), hxmem, rfl⟩
      have hle1 : f (t • x) ≤ ((t * r : Real) : EReal) := by
        simpa [mem_epigraph_univ_iff, smul_eq_mul] using hmem
      cases htx : f (t • x) using EReal.rec with
      | bot =>
          have htinv : 0 < (1 / t : Real) := (one_div_pos).2 ht
          have hsubset := hcone (1 / t) htinv
          have hmem' : (t • x, t * (r - 1)) ∈ epigraph (Set.univ) f := by
            have : f (t • x) ≤ ((t * (r - 1) : Real) : EReal) := by
              simp [htx]
            exact (mem_epigraph_univ_iff).2 this
          have hmem'' :
              ((1 / t) • (t • x, t * (r - 1))) ∈ epigraph (Set.univ) f := by
            exact hsubset ⟨(t • x, t * (r - 1)), hmem', rfl⟩
          have hle'' :
              f ((1 / t) • (t • x)) ≤ ((1 / t) * (t * (r - 1)) : EReal) := by
            simpa [mem_epigraph_univ_iff, smul_eq_mul] using hmem''
          have hscale1 : (1 / t : Real) * t = 1 := by
            field_simp [ht0]
          have hscale2 : (t⁻¹ : Real) * (t * (r - 1)) = r - 1 := by
            field_simp [ht0]
          have hscale2' :
              (↑t)⁻¹ * (↑t * (↑r - 1)) = ((r - 1 : Real) : EReal) := by
            calc
              (↑t)⁻¹ * (↑t * (↑r - 1))
                  = (↑t)⁻¹ * (↑t * ((r - 1 : Real) : EReal)) := by
                      rw [← EReal.coe_one, ← EReal.coe_sub]
              _ = (↑t)⁻¹ * ((t * (r - 1) : Real) : EReal) := by
                    rw [← EReal.coe_mul]
              _ = ((t⁻¹ * (t * (r - 1)) : Real) : EReal) := by
                    simp [← EReal.coe_inv, ← EReal.coe_mul]
              _ = ((r - 1 : Real) : EReal) := by
                    simp [hscale2]
          have hle' : f x ≤ ((r - 1 : Real) : EReal) := by
            have hle''1 : f x ≤ 1 / (↑t : EReal) * (↑t * (↑r - 1)) := by
              simpa [smul_smul, hscale1, -one_div] using hle''
            simpa [one_div, hscale2'] using hle''1
          have hrr : r ≤ r - 1 := (EReal.coe_le_coe_iff).1 (by simpa [hx] using hle')
          linarith
      | coe s =>
          have htinv : 0 < (1 / t : Real) := (one_div_pos).2 ht
          have hsubset := hcone (1 / t) htinv
          have hmem' : (t • x, s) ∈ epigraph (Set.univ) f := by
            have : f (t • x) ≤ ((s : Real) : EReal) := by simp [htx]
            exact (mem_epigraph_univ_iff).2 this
          have hmem'' : ((1 / t) • (t • x, s)) ∈ epigraph (Set.univ) f := by
            exact hsubset ⟨(t • x, s), hmem', rfl⟩
          have hle'' : f ((1 / t) • (t • x)) ≤ ((1 / t) * s : EReal) := by
            simpa [mem_epigraph_univ_iff, smul_eq_mul] using hmem''
          have hle' : f x ≤ (((t⁻¹) * s : Real) : EReal) := by
            simpa [one_div, smul_smul, inv_mul_cancel₀ (a := t) ht0] using hle''
          have hrs : r ≤ (t⁻¹) * s := by
            simp [hx] at hle'
            exact (EReal.coe_le_coe_iff).1 hle'
          have hmul : t * r ≤ s := by
            have ht' : 0 ≤ t := le_of_lt ht
            have : t * r ≤ t * (t⁻¹ * s) := mul_le_mul_of_nonneg_left hrs ht'
            have hscale2 : t * (t⁻¹ * s) = s := by
              simpa using (mul_inv_cancel_left₀ (a := t) (b := s) ht0)
            simpa [hscale2] using this
          have hle2 : ((t * r : Real) : EReal) ≤ (s : EReal) :=
            (EReal.coe_le_coe_iff).2 hmul
          have hle1' : (s : EReal) ≤ ((t * r : Real) : EReal) := by
            simpa [htx] using hle1
          have h_eq : (s : EReal) = ((t * r : Real) : EReal) := le_antisymm hle1' hle2
          simpa [hx, htx, EReal.mul] using h_eq
      | top =>
          have htop : (⊤ : EReal) ≤ ((t * r : Real) : EReal) := by simpa [htx] using hle1
          exact (not_top_le_coe (t * r) htop).elim
  | top =>
      cases htx : f (t • x) using EReal.rec with
      | bot =>
          have htinv : 0 < (1 / t : Real) := (one_div_pos).2 ht
          have hsubset := hcone (1 / t) htinv
          have hmem' : (t • x, 0) ∈ epigraph (Set.univ) f := by
            have : f (t • x) ≤ ((0 : Real) : EReal) := by
              simp [htx]
            exact (mem_epigraph_univ_iff).2 this
          have hmem'' : ((1 / t) • (t • x, 0)) ∈ epigraph (Set.univ) f := by
            exact hsubset ⟨(t • x, 0), hmem', rfl⟩
          have hle'' : f ((1 / t) • (t • x)) ≤ ((1 / t) * 0 : EReal) := by
            simpa [mem_epigraph_univ_iff, smul_eq_mul] using hmem''
          have hle' : f x ≤ ((0 : Real) : EReal) := by
            simpa [one_div, smul_smul, inv_mul_cancel₀ (a := t) ht0] using hle''
          have htop : (⊤ : EReal) ≤ ((0 : Real) : EReal) := by
            simp [hx, -top_le_iff] at hle'
            exact hle'
          exact (not_top_le_coe 0 htop).elim
      | coe s =>
          have htinv : 0 < (1 / t : Real) := (one_div_pos).2 ht
          have hsubset := hcone (1 / t) htinv
          have hmem' : (t • x, s) ∈ epigraph (Set.univ) f := by
            have : f (t • x) ≤ ((s : Real) : EReal) := by simp [htx]
            exact (mem_epigraph_univ_iff).2 this
          have hmem'' : ((1 / t) • (t • x, s)) ∈ epigraph (Set.univ) f := by
            exact hsubset ⟨(t • x, s), hmem', rfl⟩
          have hle'' : f ((1 / t) • (t • x)) ≤ ((1 / t) * s : EReal) := by
            simpa [mem_epigraph_univ_iff, smul_eq_mul] using hmem''
          have hle' : f x ≤ (((t⁻¹) * s : Real) : EReal) := by
            simpa [one_div, smul_smul, inv_mul_cancel₀ (a := t) ht0] using hle''
          have htop : (⊤ : EReal) ≤ (((t⁻¹) * s : Real) : EReal) := by
            simp [hx, -top_le_iff] at hle'
            exact hle'
          exact (not_top_le_coe ((t⁻¹) * s) htop).elim
      | top =>
          simp [EReal.coe_mul_top_of_pos ht]

/-- Remark 4.8.1: Obviously, positive homogeneity is equivalent to the epigraph being a
cone in `ℝ^{n+1}`. -/
lemma positivelyHomogeneous_iff_epigraph_cone {n : Nat} (f : (Fin n → Real) → EReal) :
    PositivelyHomogeneous f ↔
      (∀ t : Real, 0 < t →
        Set.image (fun p : (Fin n → Real) × Real => t • p) (epigraph (Set.univ) f) ⊆
          epigraph (Set.univ) f) := by
  constructor
  · intro hpos
    exact epigraph_cone_of_posHom (f := f) hpos
  · intro hcone
    exact posHom_of_epigraph_cone (f := f) hcone

/-- The absolute value is positively homogeneous as an `EReal`-valued function. -/
lemma posHom_abs_ereal :
    PositivelyHomogeneous (fun x : Fin 1 → Real => ((|x 0| : Real) : EReal)) := by
  intro x t ht
  have ht0 : 0 ≤ t := le_of_lt ht
  calc
    ((|((t • x) 0)| : Real) : EReal) = ((|t * x 0| : Real) : EReal) := by
      simp [Pi.smul_apply, smul_eq_mul]
    _ = ((|t| * |x 0| : Real) : EReal) := by
      simp [abs_mul]
    _ = ((t * |x 0| : Real) : EReal) := by
      simp [abs_of_nonneg ht0]
    _ = (t : EReal) * ((|x 0| : Real) : EReal) := by
      simp [EReal.coe_mul]

/-- The absolute value is subadditive when coerced to `EReal`. -/
lemma subadditive_abs_ereal :
    ∀ x y : Fin 1 → Real,
      ((|x 0 + y 0| : Real) : EReal) ≤
        ((|x 0| : Real) : EReal) + ((|y 0| : Real) : EReal) := by
  intro x y
  have hreal : |x 0 + y 0| ≤ |x 0| + |y 0| := by
    simpa using abs_add_le (x 0) (y 0)
  have hcoe :
      ((|x 0 + y 0| : Real) : EReal) ≤ ((|x 0| + |y 0| : Real) : EReal) :=
    (EReal.coe_le_coe_iff).2 hreal
  simpa [EReal.coe_add] using hcoe

/-- The absolute value is not linear as an `EReal`-valued function. -/
lemma abs_not_linear_ereal :
    ¬ ∃ a : Real, ∀ x : Fin 1 → Real,
      ((|x 0| : Real) : EReal) = ((a * x 0 : Real) : EReal) := by
  rintro ⟨a, ha⟩
  have h1E : ((|1| : Real) : EReal) = ((a * 1 : Real) : EReal) := by
    simpa using ha (fun _ => (1 : Real))
  have h1' : (|1| : Real) = a * 1 := (EReal.coe_eq_coe_iff).1 h1E
  have h1 : (1 : Real) = a := by
    simpa using h1'
  have hnegE : ((|(-1 : Real)| : Real) : EReal) = ((a * (-1) : Real) : EReal) := by
    simpa using ha (fun _ => (-1 : Real))
  have hneg' : (|(-1 : Real)| : Real) = a * (-1) := (EReal.coe_eq_coe_iff).1 hnegE
  have hneg : (1 : Real) = -a := by
    simpa using hneg'
  have hcontra : (1 : Real) = -1 := by
    simpa [h1] using hneg
  linarith

/-- Example 4.8.2: An example of a positively homogeneous convex function which is not
simply a linear function is `f(x) = |x|`. -/
lemma positivelyHomogeneous_convex_abs_not_linear :
    (let f : (Fin 1 → Real) → EReal := fun x => ((|x 0| : Real) : EReal);
    PositivelyHomogeneous f ∧ ConvexFunction f ∧
      ¬ (∃ a : Real, ∀ x : Fin 1 → Real, f x = ((a * x 0 : Real) : EReal))) := by
  have hpos :
      PositivelyHomogeneous (fun x : Fin 1 → Real => ((|x 0| : Real) : EReal)) :=
    posHom_abs_ereal
  have hconv :
      ConvexFunction (fun x : Fin 1 → Real => ((|x 0| : Real) : EReal)) := by
    refine (convexFunction_iff_subadditive_of_posHom
      (f := fun x : Fin 1 → Real => ((|x 0| : Real) : EReal)) hpos
      (by
        intro x
        simp)).2 ?_
    intro x y
    simpa using subadditive_abs_ereal x y
  have hnot :
      ¬ ∃ a : Real, ∀ x : Fin 1 → Real,
        ((|x 0| : Real) : EReal) = ((a * x 0 : Real) : EReal) :=
    abs_not_linear_ereal
  dsimp
  exact ⟨hpos, hconv, hnot⟩

end Section04
end Chap01
