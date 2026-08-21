/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Shu Miao, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section08_part6

noncomputable section
open scoped RealInnerProductSpace
open scoped Pointwise Topology
open Metric

section Chap02
section Section08

/-- Corollary 8.6.2. A convex function `f` is constant on any affine set `M` where it is
finite and bounded above. -/
theorem convexFunction_const_on_affine_of_finite_boundedAbove {n : Nat}
    {f : (Fin n → Real) → EReal} (hf : ConvexFunction f)
    (M : AffineSubspace Real (Fin n → Real))
    (hfinite :
      ∀ x ∈ (M : Set (Fin n → Real)), f x ≠ (⊥ : EReal) ∧ f x ≠ (⊤ : EReal))
    (hbounded : ∃ α : Real, ∀ x ∈ (M : Set (Fin n → Real)), f x ≤ (α : EReal)) :
    ∃ c : EReal, ∀ x ∈ (M : Set (Fin n → Real)), f x = c := by
  classical
  by_cases hMempty : (M : Set (Fin n → Real)) = ∅
  · refine ⟨0, ?_⟩
    intro x hx
    simp [hMempty] at hx
  · have hMne : (M : Set (Fin n → Real)).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hMempty
    rcases hMne with ⟨x0, hx0⟩
    refine ⟨f x0, ?_⟩
    intro x hx
    have hline :=
      line_const_of_bddAbove_on_affine (f := f) (hf := hf) (M := M) hfinite hbounded hx0 hx
    have hEq := hline 1 0
    simpa using hEq

/-- Definiton 8.7.0. Let `f` be a proper convex function on `ℝ^n` and let `f0^+` be its
recession function. The constancy space of `f` is the set `{ y ∈ ℝ^n | (f0^+)(y) ≤ 0 and
(f0^+)(-y) ≤ 0 }`. -/
def Function.constancySpace {n : Nat} (f0_plus : EuclideanSpace Real (Fin n) → EReal) :
    Set (EuclideanSpace Real (Fin n)) :=
  { y | f0_plus y ≤ 0 ∧ f0_plus (-y) ≤ 0 }

/-- If all rays are antitone, then any sublevel set recedes in direction `y`. -/
lemma recessionCone_sublevel_of_antitone {n : Nat} {f : EuclideanSpace Real (Fin n) → EReal}
    {r : Real} {y : EuclideanSpace Real (Fin n)} :
    (∀ x : EuclideanSpace Real (Fin n), Antitone (fun t : ℝ => f (x + t • y))) →
      y ∈ Set.recessionCone {x : EuclideanSpace Real (Fin n) | f x ≤ (r : EReal)} := by
  intro h x hx t ht
  have hanti := h x
  have hle : f (x + t • y) ≤ f (x + 0 • y) := by
    simpa using (hanti (a := 0) (b := t) ht)
  have hle' : f (x + t • y) ≤ f x := by
    simpa using hle
  exact le_trans hle' hx

/-- If the recession cone is given by `f0_plus y ≤ 0`, its lineality space is the constancy
space of `f0_plus`. -/
lemma lineality_eq_constancySpace_of_recessionCone_eq {n : Nat}
    {S : Set (EuclideanSpace Real (Fin n))}
    {f0_plus : EuclideanSpace Real (Fin n) → EReal}
    (hEq : Set.recessionCone S = {y : EuclideanSpace Real (Fin n) | f0_plus y ≤ 0}) :
    (-Set.recessionCone S) ∩ Set.recessionCone S = Function.constancySpace f0_plus := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨hyneg, hy⟩
    have hy' : f0_plus y ≤ 0 := by
      have : y ∈ {y : EuclideanSpace Real (Fin n) | f0_plus y ≤ 0} := by
        simpa [hEq] using hy
      simpa using this
    have hyneg' : f0_plus (-y) ≤ 0 := by
      have : -y ∈ Set.recessionCone S := by
        simpa using hyneg
      have : -y ∈ {y : EuclideanSpace Real (Fin n) | f0_plus y ≤ 0} := by
        simpa [hEq] using this
      simpa using this
    exact ⟨hy', hyneg'⟩
  · intro hy
    rcases hy with ⟨hy, hyneg⟩
    have hy' : y ∈ Set.recessionCone S := by
      simpa [hEq] using hy
    have hyneg' : -y ∈ Set.recessionCone S := by
      simpa [hEq] using hyneg
    have hyneg'' : y ∈ -Set.recessionCone S := by
      simpa using hyneg'
    exact ⟨hyneg'', hy'⟩

/-- If `x` is in a sublevel set and `y` in its recession cone, the ray liminf is finite. -/
lemma liminf_lt_top_of_recessionCone_sublevel {n : Nat}
    {f : EuclideanSpace Real (Fin n) → Real} {r : Real}
    {x y : EuclideanSpace Real (Fin n)}
    (hx : (f x : EReal) ≤ (r : EReal))
    (hy :
      y ∈ Set.recessionCone {x : EuclideanSpace Real (Fin n) | (f x : EReal) ≤ (r : EReal)}) :
    Filter.liminf (fun t : ℝ => (f (x + t • y) : EReal)) Filter.atTop < (⊤ : EReal) := by
  have hE : ∀ᶠ t : ℝ in Filter.atTop, (f (x + t • y) : EReal) ≤ (r : EReal) := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨0, ?_⟩
    intro t ht
    have hmem :
        x + t • y ∈
          {x : EuclideanSpace Real (Fin n) | (f x : EReal) ≤ (r : EReal)} :=
      hy hx ht
    simpa using hmem
  have hfreq :
      ∃ᶠ t in Filter.atTop, (f (x + t • y) : EReal) ≤ (r : EReal) :=
    hE.frequently
  have hlim_le :
      Filter.liminf (fun t : ℝ => (f (x + t • y) : EReal)) Filter.atTop ≤ (r : EReal) :=
    Filter.liminf_le_of_frequently_le hfreq
  have hlt : (r : EReal) < (⊤ : EReal) := (lt_top_iff_ne_top).2 (EReal.coe_ne_top r)
  exact lt_of_le_of_lt hlim_le hlt

/-- Membership in a sublevel recession cone forces all rays to be antitone. -/
lemma antitone_all_of_mem_recessionCone_sublevel {n : Nat}
    {f : EuclideanSpace Real (Fin n) → Real} {f0_plus : EuclideanSpace Real (Fin n) → EReal}
    (hfclosed :
      ClosedConvexFunction
        (fun x => (f ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x) : EReal)))
    (hfproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
        (fun x => (f ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x) : EReal)))
    (hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm y) =
          sSup { r : EReal | ∃ x ∈ (Set.univ : Set (Fin n → Real)),
            r =
              ((f ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x + y)) -
                  f ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x) : Real) :
                EReal) })
    {r : Real}
    (hnonempty :
      ({x : EuclideanSpace Real (Fin n) | (f x : EReal) ≤ (r : EReal)} : Set _).Nonempty)
    {y : EuclideanSpace Real (Fin n)}
    (hy :
      y ∈ Set.recessionCone {x : EuclideanSpace Real (Fin n) | (f x : EReal) ≤ (r : EReal)}) :
    ∀ x : EuclideanSpace Real (Fin n), Antitone (fun t : ℝ => f (x + t • y)) := by
  classical
  let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
  let g : (Fin n → Real) → Real := fun x => f (e.symm x)
  let g0_plus : (Fin n → Real) → EReal := fun y => f0_plus (e.symm y)
  have htheorem :=
    recessionFunction_ray_antitone_iff (f := g) (f0_plus := g0_plus) (hf := hfproper)
      (hf0_plus := hf0_plus) (y := e y)
  rcases hnonempty with ⟨x0, hx0⟩
  have hlim_lt' :
      Filter.liminf (fun t : ℝ => (f (x0 + t • y) : EReal)) Filter.atTop < (⊤ : EReal) :=
    liminf_lt_top_of_recessionCone_sublevel (f := f) (r := r) (x := x0) (y := y) hx0 hy
  have hfun :
      (fun t : ℝ => (g (e x0 + t • e y) : EReal)) =
        fun t : ℝ => (f (x0 + t • y) : EReal) := by
    funext t
    simp [g]
  have hlim_lt :
      Filter.liminf (fun t : ℝ => (g (e x0 + t • e y) : EReal)) Filter.atTop < (⊤ : EReal) := by
    simpa [hfun] using hlim_lt'
  have hanti0 : Antitone (fun t : ℝ => g (e x0 + t • e y)) :=
    (htheorem.1) (e x0) hlim_lt
  have hx0_dom :
      e x0 ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => (g x : EReal)) := by
    have hx0_dom' :
        e x0 ∈ {x | x ∈ (Set.univ : Set (Fin n → Real)) ∧ (g x : EReal) < (⊤ : EReal)} := by
      refine ⟨by simp, ?_⟩
      exact (lt_top_iff_ne_top).2 (EReal.coe_ne_top (g (e x0)))
    simp [effectiveDomain_eq]
  have hclosed' : ClosedConvexFunction (fun x => (g x : EReal)) := by
    simpa [g] using hfclosed
  have hanti_all' :
      ∀ x : Fin n → Real, Antitone (fun t : ℝ => g (x + t • e y)) :=
    (htheorem.2.2) hclosed' ⟨e x0, hx0_dom, hanti0⟩
  intro x
  have hanti' := hanti_all' (e x)
  simpa [g] using hanti'

/-- Nonempty sublevel sets share recession cone `{y | f0_plus y ≤ 0}`. -/
lemma recessionCone_sublevel_eq_f0plus_le_zero {n : Nat}
    {f : EuclideanSpace Real (Fin n) → Real} {f0_plus : EuclideanSpace Real (Fin n) → EReal}
    (hfclosed :
      ClosedConvexFunction
        (fun x => (f ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x) : EReal)))
    (hfproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
        (fun x => (f ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x) : EReal)))
    (hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm y) =
          sSup { r : EReal | ∃ x ∈ (Set.univ : Set (Fin n → Real)),
            r =
              ((f ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x + y)) -
                  f ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x) : Real) :
                EReal) })
    {r : Real}
    (hnonempty :
      ({x : EuclideanSpace Real (Fin n) | (f x : EReal) ≤ (r : EReal)} : Set _).Nonempty) :
    Set.recessionCone {x : EuclideanSpace Real (Fin n) | (f x : EReal) ≤ (r : EReal)} =
      {y : EuclideanSpace Real (Fin n) | f0_plus y ≤ 0} := by
  classical
  let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
  let g : (Fin n → Real) → Real := fun x => f (e.symm x)
  let g0_plus : (Fin n → Real) → EReal := fun y => f0_plus (e.symm y)
  ext y
  constructor
  · intro hy
    have hanti :
        ∀ x : EuclideanSpace Real (Fin n), Antitone (fun t : ℝ => f (x + t • y)) :=
      antitone_all_of_mem_recessionCone_sublevel (f := f) (f0_plus := f0_plus) hfclosed
        hfproper hf0_plus hnonempty hy
    have htheorem :=
      recessionFunction_ray_antitone_iff (f := g) (f0_plus := g0_plus) (hf := hfproper)
        (hf0_plus := hf0_plus) (y := e y)
    have hanti' : ∀ x : Fin n → Real, Antitone (fun t : ℝ => g (x + t • e y)) := by
      intro x
      have hanti_x := hanti (e.symm x)
      simpa [g, e, map_add, map_smul] using hanti_x
    have hle : g0_plus (e y) ≤ 0 := (htheorem.2.1).1 hanti'
    simpa [g0_plus, e] using hle
  · intro hy
    have htheorem :=
      recessionFunction_ray_antitone_iff (f := g) (f0_plus := g0_plus) (hf := hfproper)
        (hf0_plus := hf0_plus) (y := e y)
    have hle : g0_plus (e y) ≤ 0 := by
      simpa [g0_plus, e] using hy
    have hanti' : ∀ x : Fin n → Real, Antitone (fun t : ℝ => g (x + t • e y)) :=
      (htheorem.2.1).2 hle
    have hanti :
        ∀ x : EuclideanSpace Real (Fin n), Antitone (fun t : ℝ => f (x + t • y)) := by
      intro x
      have hanti_x := hanti' (e x)
      simpa [g, e, map_add, map_smul] using hanti_x
    have hantiE :
        ∀ x : EuclideanSpace Real (Fin n),
          Antitone (fun t : ℝ => (f (x + t • y) : EReal)) := by
      intro x s t hst
      exact (EReal.coe_le_coe_iff).2 (hanti x hst)
    exact
      recessionCone_sublevel_of_antitone (f := fun x => (f x : EReal)) (r := r) (y := y)
        hantiE

/-- Theorem 8.7. Let `f` be a closed proper convex function. Then all non-empty level sets
`{x | f(x) ≤ λ}` have the same recession cone and the same lineality space, namely
`{y | (f0^+)(y) ≤ 0}` and the constancy space of `f`, respectively. -/
theorem levelSet_recessionCone_and_lineality_eq_constancySpace {n : Nat}
    {f : EuclideanSpace Real (Fin n) → Real}
    {f0_plus : EuclideanSpace Real (Fin n) → EReal}
    (hfclosed :
      ClosedConvexFunction
        (fun x => (f ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x) : EReal)))
    (hfproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
        (fun x => (f ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x) : EReal)))
    (hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm y) =
          sSup { r : EReal | ∃ x ∈ (Set.univ : Set (Fin n → Real)),
            r =
              ((f ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x + y)) -
                  f ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x) : Real) :
                EReal) }) :
    ∀ {r : Real},
      ({x : EuclideanSpace Real (Fin n) | (f x : EReal) ≤ (r : EReal)} : Set _).Nonempty →
        Set.recessionCone {x : EuclideanSpace Real (Fin n) | (f x : EReal) ≤ (r : EReal)} =
          {y : EuclideanSpace Real (Fin n) | f0_plus y ≤ 0} ∧
        (-Set.recessionCone {x : EuclideanSpace Real (Fin n) | (f x : EReal) ≤ (r : EReal)}) ∩
            Set.recessionCone {x : EuclideanSpace Real (Fin n) | (f x : EReal) ≤ (r : EReal)} =
          Function.constancySpace f0_plus := by
  intro r hnonempty
  have hrc :
      Set.recessionCone {x : EuclideanSpace Real (Fin n) | (f x : EReal) ≤ (r : EReal)} =
        {y : EuclideanSpace Real (Fin n) | f0_plus y ≤ 0} :=
    recessionCone_sublevel_eq_f0plus_le_zero (f := f) (f0_plus := f0_plus) hfclosed hfproper
      hf0_plus hnonempty
  refine ⟨hrc, ?_⟩
  exact
    lineality_eq_constancySpace_of_recessionCone_eq (S := {x : EuclideanSpace Real (Fin n) |
      (f x : EReal) ≤ (r : EReal)}) (f0_plus := f0_plus) hrc

/-- Sublevel sets of a closed convex function are closed and convex. -/
lemma sublevel_isClosed_convex_of_closedConvex {n : Nat}
    {f : EuclideanSpace Real (Fin n) → Real}
    (hfclosed :
      ClosedConvexFunction
        (fun x => (f ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x) : EReal)))
    (r : Real) :
    IsClosed ({x : EuclideanSpace Real (Fin n) | (f x : EReal) ≤ (r : EReal)}) ∧
      Convex Real ({x : EuclideanSpace Real (Fin n) | (f x : EReal) ≤ (r : EReal)}) := by
  classical
  let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
  let g : (Fin n → Real) → EReal := fun x => (f (e.symm x) : EReal)
  have hclosed_sub : IsClosed {x : Fin n → Real | g x ≤ (r : EReal)} :=
    (lowerSemicontinuous_iff_closed_sublevel (f := g)).1 hfclosed.2 r
  have hconv_sub : Convex Real {x : Fin n → Real | g x ≤ (r : EReal)} :=
    (convexFunction_level_sets_convex (f := g) hfclosed.1 (α := (r : EReal))).2
  let A : EuclideanSpace Real (Fin n) →ₗ[Real] (Fin n → Real) := e.toLinearMap
  have hclosed_pre :
      IsClosed (e ⁻¹' {x : Fin n → Real | g x ≤ (r : EReal)}) :=
    hclosed_sub.preimage e.continuous
  have hconv_pre :
      Convex Real (A ⁻¹' {x : Fin n → Real | g x ≤ (r : EReal)}) :=
    hconv_sub.linear_preimage A
  refine ⟨?_, ?_⟩
  · have hclosed_pre' :
        IsClosed {x : EuclideanSpace Real (Fin n) | g (e x) ≤ (r : EReal)} := by
      simpa using hclosed_pre
    simpa [g] using hclosed_pre'
  · have hconv_pre' :
        Convex Real {x : EuclideanSpace Real (Fin n) | g (A x) ≤ (r : EReal)} := by
      simpa using hconv_pre
    simpa [A, g] using hconv_pre'

/-- Corollary 8.7.1. Let `f` be a closed proper convex function. If the level set
`{x | f(x) ≤ λ}` is non-empty and bounded for one `λ`, it is bounded for every `λ`. -/
theorem levelSet_bounded_of_bounded_one {n : Nat}
    {f : EuclideanSpace Real (Fin n) → Real}
    (hfclosed :
      ClosedConvexFunction
        (fun x => (f ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x) : EReal)))
    (hfproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
        (fun x => (f ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x) : EReal)))
    {r0 : Real}
    (hlevel :
      ({x : EuclideanSpace Real (Fin n) | f x ≤ (r0 : EReal)} : Set _).Nonempty)
    (hbounded :
      Bornology.IsBounded
        ({x : EuclideanSpace Real (Fin n) | f x ≤ (r0 : EReal)} : Set _)) :
    ∀ r : Real,
      Bornology.IsBounded ({x : EuclideanSpace Real (Fin n) | f x ≤ (r : EReal)} : Set _) := by
  classical
  let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
  let f0_plus : EuclideanSpace Real (Fin n) → EReal := fun y =>
    sSup { r : EReal | ∃ x ∈ (Set.univ : Set (Fin n → Real)),
      r =
        ((f ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x + e y)) -
            f ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x) : Real) : EReal) }
  have hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm y) =
          sSup { r : EReal | ∃ x ∈ (Set.univ : Set (Fin n → Real)),
            r =
              ((f ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm (x + y)) -
                  f ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x) : Real) :
                EReal) } := by
    intro y
    have hy : e (WithLp.toLp 2 y) = y := by
      change e (e.symm y) = y
      exact e.apply_symm_apply y
    simp [f0_plus, hy]
  intro r
  by_cases hS :
      ({x : EuclideanSpace Real (Fin n) | f x ≤ (r : EReal)} : Set _) = ∅
  · rw [hS]
    exact Bornology.isBounded_empty
  · have hnonempty :
        ({x : EuclideanSpace Real (Fin n) | f x ≤ (r : EReal)} : Set _).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hS
    have hclosed_convex_r0 :
        IsClosed ({x : EuclideanSpace Real (Fin n) | (f x : EReal) ≤ (r0 : EReal)}) ∧
          Convex Real ({x : EuclideanSpace Real (Fin n) | (f x : EReal) ≤ (r0 : EReal)}) :=
      sublevel_isClosed_convex_of_closedConvex (f := f) hfclosed r0
    have hrec0 :
        Set.recessionCone
            {x : EuclideanSpace Real (Fin n) | (f x : EReal) ≤ (r0 : EReal)} =
          {0} := by
      exact
        (bounded_iff_recessionCone_eq_singleton_zero
          (C := {x : EuclideanSpace Real (Fin n) | (f x : EReal) ≤ (r0 : EReal)}) hlevel
          hclosed_convex_r0.1 hclosed_convex_r0.2).1 hbounded
    have hrc0 :
        Set.recessionCone
            {x : EuclideanSpace Real (Fin n) | (f x : EReal) ≤ (r0 : EReal)} =
          {y : EuclideanSpace Real (Fin n) | f0_plus y ≤ 0} :=
      recessionCone_sublevel_eq_f0plus_le_zero (f := f) (f0_plus := f0_plus) hfclosed hfproper
        hf0_plus hlevel
    have hcone_eq : {y : EuclideanSpace Real (Fin n) | f0_plus y ≤ 0} = {0} := by
      exact hrc0.symm.trans hrec0
    have hrc :
        Set.recessionCone
            {x : EuclideanSpace Real (Fin n) | (f x : EReal) ≤ (r : EReal)} =
          {y : EuclideanSpace Real (Fin n) | f0_plus y ≤ 0} :=
      recessionCone_sublevel_eq_f0plus_le_zero (f := f) (f0_plus := f0_plus) hfclosed hfproper
        hf0_plus hnonempty
    have hrec :
        Set.recessionCone
            {x : EuclideanSpace Real (Fin n) | (f x : EReal) ≤ (r : EReal)} =
          {0} := by
      simpa [hcone_eq] using hrc
    have hclosed_convex_r :
        IsClosed ({x : EuclideanSpace Real (Fin n) | (f x : EReal) ≤ (r : EReal)}) ∧
          Convex Real ({x : EuclideanSpace Real (Fin n) | (f x : EReal) ≤ (r : EReal)}) :=
      sublevel_isClosed_convex_of_closedConvex (f := f) hfclosed r
    exact
      (bounded_iff_recessionCone_eq_singleton_zero
        (C := {x : EuclideanSpace Real (Fin n) | (f x : EReal) ≤ (r : EReal)}) hnonempty
        hclosed_convex_r.1 hclosed_convex_r.2).2 hrec

/-- Two-sided ray inequalities force affine behavior along the direction. -/
lemma ray_eq_of_ineq_pair {n : Nat} {f : (Fin n → Real) → Real} {y : Fin n → Real} {v : Real}
    (hpos : ∀ x : Fin n → Real, ∀ t : Real, 0 ≤ t → f (x + t • y) ≤ f x + t * v)
    (hneg : ∀ x : Fin n → Real, ∀ t : Real, 0 ≤ t → f (x + t • (-y)) ≤ f x + t * (-v)) :
    ∀ x : Fin n → Real, ∀ t : Real, f (x + t • y) = f x + t * v := by
  intro x t
  by_cases ht : 0 ≤ t
  · have hle : f (x + t • y) ≤ f x + t * v := hpos x t ht
    have hge : f x + t * v ≤ f (x + t • y) := by
      have hneg' := hneg (x + t • y) t ht
      simpa [smul_neg, add_comm, add_left_comm, add_assoc] using hneg'
    exact le_antisymm hle hge
  · have htneg : t < 0 := lt_of_not_ge ht
    set s : Real := -t
    have hs : 0 ≤ s := by linarith
    have hle : f (x + s • (-y)) ≤ f x + s * (-v) := hneg x s hs
    have hge : f x + s * (-v) ≤ f (x + s • (-y)) := by
      have hpos' := hpos (x + s • (-y)) s hs
      simpa [smul_neg, add_comm, add_left_comm, add_assoc] using hpos'
    have hEq : f (x + s • (-y)) = f x + s * (-v) := le_antisymm hle hge
    simpa [s, smul_neg, neg_smul, neg_neg, mul_neg, neg_mul] using hEq

/-- Negation commutes with the embedded epigraph map. -/
lemma embedded_epigraph_neg {n : Nat} :
    let eN : (Fin n → Real) ≃ᵃ[Real] EuclideanSpace Real (Fin n) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm.toLinearEquiv.toAffineEquiv
    let e1 : Real ≃ᵃ[Real] EuclideanSpace Real (Fin 1) :=
      ((ContinuousLinearEquiv.funUnique (ι := Fin 1) (R := Real) (M := Real)).symm.toLinearEquiv.trans
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm.toLinearEquiv).toAffineEquiv
    let g : (Fin n → Real) × Real ≃ᵃ[Real]
        (EuclideanSpace Real (Fin n) × EuclideanSpace Real (Fin 1)) :=
      AffineEquiv.prodCongr eN e1
    ∀ y : Fin n → Real, ∀ v : Real,
      (appendAffineEquiv n 1) (g (-y, -v)) = - (appendAffineEquiv n 1) (g (y, v)) := by
  classical
  intro eN e1 g y v
  have hlin_append :
      ∀ u, appendAffineEquiv n 1 u = (appendAffineEquiv n 1).linear u := by
    intro u
    have h := congrArg (fun f => f u) (appendAffineEquiv_eq_linear_toAffineEquiv n 1)
    simpa using h
  have hlin_g : ∀ u, g u = g.linear u := by
    intro u
    have hmap := g.map_vadd (0 : (Fin n → Real) × Real) u
    have h0 : g (0 : (Fin n → Real) × Real) = 0 := by
      simp [g, eN, e1]
    simpa [h0, vadd_eq_add] using hmap
  have hneg_lin : g.linear (-y, -v) = - g.linear (y, v) := by
    simpa using (map_neg g.linear (y, v))
  calc
    appendAffineEquiv n 1 (g (-y, -v)) =
        (appendAffineEquiv n 1).linear (g.linear (-y, -v)) := by
      simp [hlin_append, hlin_g]
    _ = (appendAffineEquiv n 1).linear (- g.linear (y, v)) := by
      simp [hneg_lin]
    _ = - (appendAffineEquiv n 1).linear (g.linear (y, v)) := by
      simp
    _ = - (appendAffineEquiv n 1) (g (y, v)) := by
      simp [hlin_append, hlin_g]

/-- Membership in the embedded epigraph recession cone is equivalent to ray inequalities. -/
lemma mem_recessionCone_embedded_epigraph_iff_ray_ineq {n : Nat}
    {f : (Fin n → Real) → Real} {y : Fin n → Real} {v : Real} :
    (let eN : (Fin n → Real) ≃ᵃ[Real] EuclideanSpace Real (Fin n) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm.toLinearEquiv.toAffineEquiv
    let e1 : Real ≃ᵃ[Real] EuclideanSpace Real (Fin 1) :=
      ((ContinuousLinearEquiv.funUnique (ι := Fin 1) (R := Real) (M := Real)).symm.toLinearEquiv.trans
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm.toLinearEquiv).toAffineEquiv
    let g : (Fin n → Real) × Real ≃ᵃ[Real]
        (EuclideanSpace Real (Fin n) × EuclideanSpace Real (Fin 1)) :=
      AffineEquiv.prodCongr eN e1
    let epi : Set (EuclideanSpace Real (Fin (n + 1))) :=
      (appendAffineEquiv n 1) ''
        (g '' epigraph (S := (Set.univ : Set (Fin n → Real)))
          (fun x => (f x : EReal)))
    let yv : EuclideanSpace Real (Fin (n + 1)) :=
      (appendAffineEquiv n 1) (g (y, v))
    yv ∈ Set.recessionCone epi) ↔
      ∀ x : Fin n → Real, ∀ t : Real, 0 ≤ t → f (x + t • y) ≤ f x + t * v := by
  classical
  let eN : (Fin n → Real) ≃ᵃ[Real] EuclideanSpace Real (Fin n) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm.toLinearEquiv.toAffineEquiv
  let e1 : Real ≃ᵃ[Real] EuclideanSpace Real (Fin 1) :=
    ((ContinuousLinearEquiv.funUnique (ι := Fin 1) (R := Real) (M := Real)).symm.toLinearEquiv.trans
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm.toLinearEquiv).toAffineEquiv
  let g : (Fin n → Real) × Real ≃ᵃ[Real]
      (EuclideanSpace Real (Fin n) × EuclideanSpace Real (Fin 1)) :=
    AffineEquiv.prodCongr eN e1
  let embed : (Fin n → Real) × Real → EuclideanSpace Real (Fin (n + 1)) :=
    fun p => appendAffineEquiv n 1 (g p)
  let dir : (Fin n → Real) × Real → EuclideanSpace Real (Fin (n + 1)) :=
    fun q => (appendAffineEquiv n 1).linear (g.linear q)
  let epi : Set (EuclideanSpace Real (Fin (n + 1))) :=
    (appendAffineEquiv n 1) ''
      (g '' epigraph (S := (Set.univ : Set (Fin n → Real))) (fun x => (f x : EReal)))
  let yv : EuclideanSpace Real (Fin (n + 1)) :=
    (appendAffineEquiv n 1) (g (y, v))
  have hlin_append :
      ∀ u, appendAffineEquiv n 1 u = (appendAffineEquiv n 1).linear u := by
    intro u
    have h := congrArg (fun f => f u) (appendAffineEquiv_eq_linear_toAffineEquiv n 1)
    simpa using h
  have hlin_g : ∀ u, g u = g.linear u := by
    intro u
    have hmap := g.map_vadd (0 : (Fin n → Real) × Real) u
    have h0 : g (0 : (Fin n → Real) × Real) = 0 := by
      simp [g, eN, e1]
    simpa [h0, vadd_eq_add] using hmap
  have hyv_eq : yv = dir (y, v) := by
    simp [yv, dir, hlin_append, hlin_g]
  have hdir_eq :
      ∀ p q : (Fin n → Real) × Real, ∀ t : Real,
        embed (p + t • q) = embed p + t • dir q := by
    intro p q t
    simpa [embed, dir, g, eN, e1] using
      (embedded_epigraph_add_smul (n := n) (p := p) (q := q) (t := t))
  have h :
      (yv ∈ Set.recessionCone epi) ↔
        ∀ x : Fin n → Real, ∀ t : Real, 0 ≤ t → f (x + t • y) ≤ f x + t * v := by
    constructor
    · intro hyv x t ht
      have hx_mem : embed (x, f x) ∈ epi := by
        refine ⟨g (x, f x), ?_, rfl⟩
        refine ⟨(x, f x), ?_, rfl⟩
        exact (mem_epigraph_univ_iff).2 (by simp)
      have hmem := hyv hx_mem (t := t) ht
      have hmem' : embed (x + t • y, f x + t * v) ∈ epi := by
        have hmem'' : embed (x, f x) + t • dir (y, v) ∈ epi := by
          simpa [hyv_eq] using hmem
        have hdir := hdir_eq (p := (x, f x)) (q := (y, v)) (t := t)
        have hdir' :
            embed (x, f x) + t • dir (y, v) = embed (x + t • y, f x + t * v) := by
          simpa using hdir.symm
        simpa [hdir'] using hmem''
      have hmem_epi :
          (x + t • y, f x + t * v) ∈
            epigraph (Set.univ : Set (Fin n → Real)) (fun x => (f x : EReal)) := by
        rcases hmem' with ⟨p, hp, hp_eq⟩
        have hp_eq' : p = g (x + t • y, f x + t * v) := by
          apply (appendAffineEquiv n 1).injective
          simpa [embed] using hp_eq
        have hp' :
            g (x + t • y, f x + t * v) ∈
              g '' epigraph (Set.univ : Set (Fin n → Real)) (fun x => (f x : EReal)) := by
          simpa [hp_eq'] using hp
        rcases hp' with ⟨q, hq, hq_eq⟩
        have hq_eq' : q = (x + t • y, f x + t * v) := by
          exact g.injective hq_eq
        simpa [hq_eq'] using hq
      have hle_ereal :
          (f (x + t • y) : EReal) ≤ ((f x + t * v : Real) : EReal) :=
        (mem_epigraph_univ_iff).1 hmem_epi
      have hle_real : f (x + t • y) ≤ f x + t * v :=
        (EReal.coe_le_coe_iff).1 (by simpa using hle_ereal)
      exact hle_real
    · intro hineq z hz t ht
      rcases hz with ⟨p, hp, rfl⟩
      rcases hp with ⟨q, hq, rfl⟩
      rcases q with ⟨x, μ⟩
      have hx_le :
          f x ≤ μ := by
        have hx_le_ereal : (f x : EReal) ≤ (μ : EReal) :=
          (mem_epigraph_univ_iff).1 hq
        exact (EReal.coe_le_coe_iff).1 (by simpa using hx_le_ereal)
      have hineq' : f (x + t • y) ≤ f x + t * v := hineq x t ht
      have hle : f (x + t • y) ≤ μ + t * v := by
        linarith
      have hmem_epi :
          (x + t • y, μ + t * v) ∈
            epigraph (Set.univ : Set (Fin n → Real)) (fun x => (f x : EReal)) := by
        exact (mem_epigraph_univ_iff).2 ((EReal.coe_le_coe_iff).2 hle)
      have hmem : embed (x + t • y, μ + t * v) ∈ epi := by
        refine ⟨g (x + t • y, μ + t * v), ?_, rfl⟩
        exact ⟨(x + t • y, μ + t * v), hmem_epi, rfl⟩
      have hdir := hdir_eq (p := (x, μ)) (q := (y, v)) (t := t)
      have hdir' :
          embed (x, μ) + t • dir (y, v) = embed (x + t • y, μ + t * v) := by
        simpa using hdir.symm
      have hmem' : embed (x, μ) + t • dir (y, v) ∈ epi := by
        simpa [hdir'] using hmem
      simpa [hyv_eq] using hmem'
  simpa [eN, e1, g, embed, dir, epi, yv] using h

/-- An affine ray determines the recession function value. -/
lemma f0plus_eq_slope_of_affine_ray {n : Nat}
    {f : (Fin n → Real) → Real} {f0_plus : (Fin n → Real) → Real}
    (hf0_plus :
      ∀ y : Fin n → Real,
        (f0_plus y : EReal) =
          sSup { r : EReal | ∃ x ∈ (Set.univ : Set (Fin n → Real)),
            r = ((f (x + y) - f x : Real) : EReal) })
    (hclosed : ClosedConvexFunction (fun x => (f x : EReal))) :
    ∀ {x : Fin n → Real}
      (_hx :
        x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => (f x : EReal)))
      {y : Fin n → Real} {a b : Real},
      (∀ t : Real, f (x + t • y) = a * t + b) →
      f0_plus y = a ∧ f0_plus (-y) = -a := by
  classical
  intro x hx y a b h_affine
  have hx0 : f x = b := by
    have h0 := h_affine 0
    simpa using h0
  have hmain :
      ∀ {y : Fin n → Real} {a : Real},
        (∀ t : Real, f (x + t • y) = a * t + b) → f0_plus y = a := by
    intro y a h_affine'
    have hbound : ∀ t > 0, ((f (x + t • y) - f x) / t : Real) ≤ a := by
      intro t ht
      have hfx : f (x + t • y) = a * t + b := h_affine' t
      have hdiff' : f (x + t • y) - f x = a * t := by
        linarith [hfx, hx0]
      have hdiff : f (x + t • y) - f x = t * a := by
        simpa [mul_comm] using hdiff'
      have ht' : t ≠ 0 := ne_of_gt ht
      have hquot : ((f (x + t • y) - f x) / t : Real) = a := by
        calc
          ((f (x + t • y) - f x) / t : Real) = (t * a) / t := by
            simp [hdiff]
          _ = a := by
            field_simp [ht']
      exact le_of_eq hquot
    have hbound_all :
        ∀ x' : Fin n → Real, ∀ t : Real, 0 < t →
          ((f (x' + t • y) - f x') / t : Real) ≤ a :=
      ray_bound_extend_closed (f := f) (x0 := x) (y := y) (v := a) hclosed hbound
    have hbound_one : ∀ x' : Fin n → Real, f (x' + y) - f x' ≤ a := by
      intro x'
      have h := hbound_all x' 1 (by exact zero_lt_one)
      simpa using h
    have hle_ereal : (f0_plus y : EReal) ≤ (a : EReal) := by
      have hsup_le :
          sSup { r : EReal | ∃ x' ∈ (Set.univ : Set (Fin n → Real)),
            r = ((f (x' + y) - f x' : Real) : EReal) } ≤ (a : EReal) := by
        refine sSup_le ?_
        intro r hr
        rcases hr with ⟨x', hx', rfl⟩
        have hdiff := hbound_one x'
        exact (EReal.coe_le_coe_iff).2 hdiff
      simpa [hf0_plus y] using hsup_le
    have hdiff1 : f (x + y) - f x = a := by
      have hfx1 : f (x + (1 : Real) • y) = a * 1 + b := h_affine' 1
      have hfx1' : f (x + y) = a + b := by
        simpa using hfx1
      linarith [hfx1', hx0]
    have hge_ereal : (a : EReal) ≤ (f0_plus y : EReal) := by
      have hmem :
          ((f (x + y) - f x : Real) : EReal) ∈
            { r : EReal | ∃ x' ∈ (Set.univ : Set (Fin n → Real)),
              r = ((f (x' + y) - f x' : Real) : EReal) } := by
        exact ⟨x, by simp, rfl⟩
      have hle := le_sSup hmem
      simpa [hf0_plus y, hdiff1] using hle
    have hle : f0_plus y ≤ a := (EReal.coe_le_coe_iff).1 (by simpa using hle_ereal)
    have hge : a ≤ f0_plus y := (EReal.coe_le_coe_iff).1 (by simpa using hge_ereal)
    exact le_antisymm hle hge
  have hy : f0_plus y = a := hmain (y := y) (a := a) h_affine
  have h_affine_neg : ∀ t : Real, f (x + t • (-y)) = (-a) * t + b := by
    intro t
    have h := h_affine (-t)
    simpa [smul_neg, neg_smul, mul_neg, neg_mul, add_comm, add_left_comm, add_assoc] using h
  have hyneg : f0_plus (-y) = -a := hmain (y := -y) (a := -a) h_affine_neg
  exact ⟨hy, hyneg⟩

/-- Theorem 8.8. For a proper convex function `f`, the following conditions on a vector `y`
and a real number `v` are equivalent: (a) `f (x + λ • y) = f x + λ v` for all `x` and
`λ ∈ ℝ`; (b) `(y, v)` belongs to the lineality space of `epi f`; (c)
`-(f0^+)(-y) = (f0^+)(y) = v`. When `f` is closed, `y` satisfies these conditions with
`v = (f0^+)(y)` if there is some `x ∈ dom f` such that `λ ↦ f (x + λ • y)` is affine. -/
theorem properConvexFunction_lineality_equiv {n : Nat}
    {f : (Fin n → Real) → Real} {f0_plus : (Fin n → Real) → Real}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fun x => (f x : EReal)))
    (hf0_plus :
      ∀ y : Fin n → Real,
        (f0_plus y : EReal) =
          sSup { r : EReal | ∃ x ∈ (Set.univ : Set (Fin n → Real)),
            r = ((f (x + y) - f x : Real) : EReal) }) :
    (∀ y : Fin n → Real, ∀ v : Real,
        ((∀ x : Fin n → Real, ∀ t : Real, f (x + t • y) = f x + t * v) ↔
            (let epi : Set (EuclideanSpace Real (Fin (n + 1))) :=
              (appendAffineEquiv n 1) ''
                ((fun p : (Fin n → Real) × Real =>
                    ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
                      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                        (fun _ : Fin 1 => p.2))) ''
                  epigraph (S := (Set.univ : Set (Fin n → Real)))
                    (fun x => (f x : EReal)));
              let yv : EuclideanSpace Real (Fin (n + 1)) :=
                (appendAffineEquiv n 1)
                  ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm y,
                    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                      (fun _ : Fin 1 => v));
              yv ∈ (-Set.recessionCone epi) ∩ Set.recessionCone epi)) ∧
          ((let epi : Set (EuclideanSpace Real (Fin (n + 1))) :=
              (appendAffineEquiv n 1) ''
                ((fun p : (Fin n → Real) × Real =>
                    ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
                      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                        (fun _ : Fin 1 => p.2))) ''
                  epigraph (S := (Set.univ : Set (Fin n → Real)))
                    (fun x => (f x : EReal)));
              let yv : EuclideanSpace Real (Fin (n + 1)) :=
                (appendAffineEquiv n 1)
                  ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm y,
                    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                      (fun _ : Fin 1 => v));
              yv ∈ (-Set.recessionCone epi) ∩ Set.recessionCone epi) ↔
            (-(f0_plus (-y)) = f0_plus y ∧ f0_plus y = v))) ∧
      (∀ y : Fin n → Real,
        ClosedConvexFunction (fun x => (f x : EReal)) →
          (∃ x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) (fun x => (f x : EReal)),
              ∃ a b : Real, ∀ t : Real, f (x + t • y) = a * t + b) →
          (∀ x : Fin n → Real, ∀ t : Real, f (x + t • y) = f x + t * f0_plus y) ∧
            (let epi : Set (EuclideanSpace Real (Fin (n + 1))) :=
              (appendAffineEquiv n 1) ''
                ((fun p : (Fin n → Real) × Real =>
                    ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
                      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                        (fun _ : Fin 1 => p.2))) ''
                  epigraph (S := (Set.univ : Set (Fin n → Real)))
                    (fun x => (f x : EReal)));
              let yv : EuclideanSpace Real (Fin (n + 1)) :=
                (appendAffineEquiv n 1)
                  ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm y,
                    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                      (fun _ : Fin 1 => f0_plus y));
              yv ∈ (-Set.recessionCone epi) ∩ Set.recessionCone epi) ∧
            (-(f0_plus (-y)) = f0_plus y)) := by
  classical
  let f0E : (Fin n → Real) → EReal := fun y => (f0_plus y : EReal)
  have hf0E :
      ∀ y : Fin n → Real,
        f0E y =
          sSup { r : EReal | ∃ x ∈ (Set.univ : Set (Fin n → Real)),
            r = ((f (x + y) - f x : Real) : EReal) } := by
    intro y
    simpa [f0E] using hf0_plus y
  have hpos : PositivelyHomogeneous f0E :=
    (recessionFunction_properties (C := Set.univ) (f := f) (f0_plus := f0E) hf rfl hf0E).1
  have hmaj :
      ∀ x y : Fin n → Real, (f (x + y) : EReal) ≤ (f x : EReal) + f0E y :=
    recessionFunction_additive_majorant (f := f) (f0_plus := f0E) hf0E
  let eN : (Fin n → Real) ≃ᵃ[Real] EuclideanSpace Real (Fin n) :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm.toLinearEquiv.toAffineEquiv
  let e1 : Real ≃ᵃ[Real] EuclideanSpace Real (Fin 1) :=
    ((ContinuousLinearEquiv.funUnique (ι := Fin 1) (R := Real) (M := Real)).symm.toLinearEquiv.trans
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm.toLinearEquiv).toAffineEquiv
  let g : (Fin n → Real) × Real ≃ᵃ[Real]
      (EuclideanSpace Real (Fin n) × EuclideanSpace Real (Fin 1)) :=
    AffineEquiv.prodCongr eN e1
  let epi : Set (EuclideanSpace Real (Fin (n + 1))) :=
    (appendAffineEquiv n 1) ''
      (g '' epigraph (S := (Set.univ : Set (Fin n → Real))) (fun x => (f x : EReal)))
  let yv : (Fin n → Real) → Real → EuclideanSpace Real (Fin (n + 1)) :=
    fun y v => (appendAffineEquiv n 1) (g (y, v))
  have hmem_iff :
      ∀ y v,
        yv y v ∈ Set.recessionCone epi ↔
          ∀ x : Fin n → Real, ∀ t : Real, 0 ≤ t → f (x + t • y) ≤ f x + t * v := by
    intro y v
    simpa [epi, yv, g, eN, e1] using
      (mem_recessionCone_embedded_epigraph_iff_ray_ineq (f := f) (y := y) (v := v))
  have hneg_yv : ∀ y v, yv (-y) (-v) = - yv y v := by
    intro y v
    simpa [yv, g, eN, e1] using (embedded_epigraph_neg (n := n) (y := y) (v := v))
  have hineq_of_f0 :
      ∀ {y : Fin n → Real} {v : Real},
        f0_plus y = v →
          ∀ x : Fin n → Real, ∀ t : Real, 0 ≤ t → f (x + t • y) ≤ f x + t * v := by
    intro y v hyv x t ht
    by_cases ht0 : t = 0
    · subst ht0
      simp
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hmaj' : (f (x + t • y) : EReal) ≤ (f x : EReal) + f0E (t • y) := hmaj x (t • y)
      have hpos' : f0E (t • y) = (t : EReal) * f0E y := by
        simpa [f0E] using hpos y t htpos
      have hpos'' : f0E (t • y) = ((t * v : Real) : EReal) := by
        simpa [f0E, hyv, EReal.coe_mul] using hpos'
      have hmaj'' : (f (x + t • y) : EReal) ≤ (f x : EReal) + ((t * v : Real) : EReal) := by
        simpa [hpos''] using hmaj'
      have hmaj''' : (f (x + t • y) : EReal) ≤ ((f x + t * v : Real) : EReal) := by
        simpa [EReal.coe_add] using hmaj''
      exact (EReal.coe_le_coe_iff).1 (by simpa using hmaj''')
  have hconst_to_f0 :
      ∀ {y : Fin n → Real} {v : Real},
        (∀ x : Fin n → Real, f (x + y) - f x = v) → f0_plus y = v := by
    intro y v hconst
    have hle_ereal : (f0_plus y : EReal) ≤ (v : EReal) := by
      have hsup_le :
          sSup { r : EReal | ∃ x ∈ (Set.univ : Set (Fin n → Real)),
            r = ((f (x + y) - f x : Real) : EReal) } ≤ (v : EReal) := by
        refine sSup_le ?_
        intro r hr
        rcases hr with ⟨x, hx, rfl⟩
        have hdiff : f (x + y) - f x = v := hconst x
        exact (EReal.coe_le_coe_iff).2 (by linarith [hdiff])
      simpa [hf0_plus y] using hsup_le
    have hge_ereal : (v : EReal) ≤ (f0_plus y : EReal) := by
      have hmem :
          ((f (0 + y) - f 0 : Real) : EReal) ∈
            { r : EReal | ∃ x ∈ (Set.univ : Set (Fin n → Real)),
              r = ((f (x + y) - f x : Real) : EReal) } := by
        exact ⟨0, by simp, rfl⟩
      have hle := le_sSup hmem
      have hdiff : f y - f 0 = v := by
        simpa using hconst 0
      simpa [hf0_plus y, hdiff] using hle
    have hle : f0_plus y ≤ v := (EReal.coe_le_coe_iff).1 (by simpa using hle_ereal)
    have hge : v ≤ f0_plus y := (EReal.coe_le_coe_iff).1 (by simpa using hge_ereal)
    exact le_antisymm hle hge
  have hmain :
      ∀ y v,
        ((∀ x : Fin n → Real, ∀ t : Real, f (x + t • y) = f x + t * v) ↔
            (yv y v ∈ (-Set.recessionCone epi) ∩ Set.recessionCone epi)) ∧
          ((yv y v ∈ (-Set.recessionCone epi) ∩ Set.recessionCone epi) ↔
            (-(f0_plus (-y)) = f0_plus y ∧ f0_plus y = v)) := by
    intro y v
    have hAB :
        (∀ x : Fin n → Real, ∀ t : Real, f (x + t • y) = f x + t * v) ↔
          yv y v ∈ (-Set.recessionCone epi) ∩ Set.recessionCone epi := by
      constructor
      · intro h
        have hineq :
            ∀ x : Fin n → Real, ∀ t : Real, 0 ≤ t →
              f (x + t • y) ≤ f x + t * v := by
          intro x t ht
          exact le_of_eq (h x t)
        have hypos : yv y v ∈ Set.recessionCone epi := (hmem_iff y v).2 hineq
        have hineq_neg :
            ∀ x : Fin n → Real, ∀ t : Real, 0 ≤ t →
              f (x + t • (-y)) ≤ f x + t * (-v) := by
          intro x t ht
          have h' := h x (-t)
          have h'' : f (x + t • (-y)) = f x + t * (-v) := by
            simpa [smul_neg, neg_smul, mul_neg, neg_mul, add_comm, add_left_comm, add_assoc] using h'
          exact le_of_eq h''
        have hyneg' : yv (-y) (-v) ∈ Set.recessionCone epi :=
          (hmem_iff (-y) (-v)).2 hineq_neg
        have hyneg : - yv y v ∈ Set.recessionCone epi := by
          simpa [hneg_yv y v] using hyneg'
        have hyneg_mem : yv y v ∈ -Set.recessionCone epi := by
          simpa [Set.mem_neg] using hyneg
        exact ⟨hyneg_mem, hypos⟩
      · intro h
        rcases h with ⟨hyneg_mem, hypos⟩
        have hpos_ineq :
            ∀ x : Fin n → Real, ∀ t : Real, 0 ≤ t →
              f (x + t • y) ≤ f x + t * v :=
          (hmem_iff y v).1 hypos
        have hyneg : - yv y v ∈ Set.recessionCone epi := by
          simpa [Set.mem_neg] using hyneg_mem
        have hyneg' : yv (-y) (-v) ∈ Set.recessionCone epi := by
          simpa [hneg_yv y v] using hyneg
        have hneg_ineq :
            ∀ x : Fin n → Real, ∀ t : Real, 0 ≤ t →
              f (x + t • (-y)) ≤ f x + t * (-v) :=
          (hmem_iff (-y) (-v)).1 hyneg'
        exact ray_eq_of_ineq_pair (f := f) (y := y) (v := v) hpos_ineq hneg_ineq
    have hAC :
        (∀ x : Fin n → Real, ∀ t : Real, f (x + t • y) = f x + t * v) →
          (-(f0_plus (-y)) = f0_plus y ∧ f0_plus y = v) := by
      intro h
      have hconst : ∀ x : Fin n → Real, f (x + y) - f x = v := by
        intro x
        have h1 := h x 1
        have h1' : f (x + y) = f x + v := by
          simpa using h1
        calc
          f (x + y) - f x = (f x + v) - f x := by
            simp [h1']
          _ = v := by
            ring
      have hy : f0_plus y = v := hconst_to_f0 hconst
      have hconst_neg : ∀ x : Fin n → Real, f (x + (-y)) - f x = -v := by
        intro x
        have h1 := h x (-1)
        have h1' : f (x + (-y)) = f x + (-v) := by
          simpa [smul_neg, neg_smul, mul_neg, neg_mul, add_comm, add_left_comm, add_assoc] using h1
        calc
          f (x + (-y)) - f x = (f x + (-v)) - f x := by
            simp [h1']
          _ = -v := by
            ring
      have hyneg : f0_plus (-y) = -v := hconst_to_f0 hconst_neg
      refine ⟨?_, hy⟩
      simp [hyneg, hy]
    have hBC :
        (yv y v ∈ (-Set.recessionCone epi) ∩ Set.recessionCone epi) →
          (-(f0_plus (-y)) = f0_plus y ∧ f0_plus y = v) :=
      fun hb => hAC (hAB.mpr hb)
    have hCB :
        (-(f0_plus (-y)) = f0_plus y ∧ f0_plus y = v) →
          (yv y v ∈ (-Set.recessionCone epi) ∩ Set.recessionCone epi) := by
      intro hc
      have hfy : f0_plus y = v := hc.2
      have hfneg' : f0_plus (-y) = - f0_plus y := by
        have := congrArg Neg.neg hc.1
        simpa using this
      have hfneg : f0_plus (-y) = -v := by
        simpa [hfy] using hfneg'
      have hineq := hineq_of_f0 (y := y) (v := v) hfy
      have hineq_neg := hineq_of_f0 (y := -y) (v := -v) hfneg
      have hypos : yv y v ∈ Set.recessionCone epi := (hmem_iff y v).2 hineq
      have hyneg' : yv (-y) (-v) ∈ Set.recessionCone epi := (hmem_iff (-y) (-v)).2 hineq_neg
      have hyneg : - yv y v ∈ Set.recessionCone epi := by
        simpa [hneg_yv y v] using hyneg'
      have hyneg_mem : yv y v ∈ -Set.recessionCone epi := by
        simpa [Set.mem_neg] using hyneg
      exact ⟨hyneg_mem, hypos⟩
    exact ⟨hAB, ⟨hBC, hCB⟩⟩
  refine ⟨?_, ?_⟩
  · simpa [epi, yv, g, eN, e1] using hmain
  · intro y hclosed h_affine
    rcases h_affine with ⟨x, hx, a, b, h_affine⟩
    have hfb :
        f0_plus y = a ∧ f0_plus (-y) = -a :=
      f0plus_eq_slope_of_affine_ray (f := f) (f0_plus := f0_plus) hf0_plus hclosed
        (x := x) hx (y := y) (a := a) (b := b) h_affine
    have hy : f0_plus y = a := hfb.1
    have hyneg : f0_plus (-y) = -a := hfb.2
    have hc : (-(f0_plus (-y)) = f0_plus y ∧ f0_plus y = f0_plus y) := by
      refine ⟨?_, rfl⟩
      simp [hyneg, hy]
    have hmain_y := hmain y (f0_plus y)
    have hb : yv y (f0_plus y) ∈ (-Set.recessionCone epi) ∩ Set.recessionCone epi :=
      (hmain_y.2).mpr hc
    have ha : ∀ x : Fin n → Real, ∀ t : Real, f (x + t • y) = f x + t * f0_plus y :=
      (hmain_y.1).mpr hb
    refine ⟨ha, ?_, ?_⟩
    · simpa [epi, yv, g, eN, e1] using hb
    · simp [hyneg, hy]

/-- Definition 8.9.0. Let `f` be a proper convex function on `ℝ^n` with recession function
`f0^+`. The set of vectors `y` such that `(f0^+)(-y) = -(f0^+)(y)` is called the lineality
space of the proper convex function `f`. -/
def Function.linealitySpace {n : Nat} (f0_plus : EuclideanSpace Real (Fin n) → EReal) :
    Set (EuclideanSpace Real (Fin n)) :=
  { y | f0_plus (-y) = -(f0_plus y) }

end Section08
end Chap02
