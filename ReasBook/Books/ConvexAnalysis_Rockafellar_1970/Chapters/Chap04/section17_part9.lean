/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yunfei Zhang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section04_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section12_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section13_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section13_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section13_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap04.section17_part8

open scoped BigOperators Pointwise
open Topology

section Chap04
section Section17

/-- The restricted supremum `supremumInnerSub` matches the Fenchel conjugate of the `+∞`
extension. -/
lemma supremumInnerSub_eq_fenchelConjugate_fExt {n : Nat} {S : Set (Fin n → Real)}
    {f : (Fin n → Real) → Real} :
    (let fExt : (Fin n → Real) → EReal := fun x => (f x : EReal) + indicatorFunction S x
    ∀ z,
      supremumInnerSub (S := S) (f := fun x : S => (f x.1 : EReal)) z =
        fenchelConjugate n fExt z) := by
  classical
  intro fExt z
  unfold supremumInnerSub fenchelConjugate
  apply le_antisymm
  · refine sSup_le ?_
    rintro y ⟨x, rfl⟩
    have hx : x.1 ∈ S := x.2
    refine le_sSup ?_
    refine ⟨x.1, ?_⟩
    simp [fExt, indicatorFunction, hx, dotProduct, mul_comm]
  · refine sSup_le ?_
    rintro y ⟨x, rfl⟩
    by_cases hx : x ∈ S
    · refine le_sSup ?_
      refine ⟨⟨x, hx⟩, ?_⟩
      simp [fExt, indicatorFunction, hx, dotProduct, mul_comm]
    ·
      have hx' : fExt x = (⊤ : EReal) := by
        simp [fExt, indicatorFunction, hx]
      have hbot :
          ((x ⬝ᵥ z : Real) : EReal) - fExt x = (⊥ : EReal) := by
        simp [hx', EReal.sub_top]
      simp [hbot]

/-- Under the compactness hypotheses, `supremumInnerSub` is finite everywhere. -/
lemma supremumInnerSub_ne_top_and_ne_bot_of_continuousOn_closed_bounded
    {n : Nat} {S : Set (Fin n → Real)} (hS_ne : S.Nonempty) (hS_closed : IsClosed S)
    (hS_bdd : Bornology.IsBounded S) {f : (Fin n → Real) → Real} (hf : ContinuousOn f S) :
    ∀ z,
      (supremumInnerSub (S := S) (f := fun x : S => (f x.1 : EReal)) z ≠ (⊤ : EReal)) ∧
        (supremumInnerSub (S := S) (f := fun x : S => (f x.1 : EReal)) z ≠ (⊥ : EReal)) := by
  classical
  intro z
  let h : (Fin n → Real) → EReal :=
    fun z => supremumInnerSub (S := S) (f := fun x : S => (f x.1 : EReal)) z
  have hS_compact : IsCompact S := cor1721_isCompact_S (S := S) hS_closed hS_bdd
  rcases cor1721_exists_lowerBound_on_S (S := S) hS_compact hS_ne hf with ⟨m, hm⟩
  have hcont :
      ContinuousOn (fun x : Fin n → Real => z ⬝ᵥ x) S :=
    (continuous_dotProduct_const (x := z)).continuousOn
  rcases hS_compact.exists_isMaxOn hS_ne hcont with ⟨xmax, hxmaxS, hxmax⟩
  have hxmax' : ∀ x ∈ S, z ⬝ᵥ x ≤ z ⬝ᵥ xmax := by
    simpa [IsMaxOn, IsMaxFilter] using hxmax
  set M : Real := z ⬝ᵥ xmax
  have hle_M : ∀ x ∈ S, (∑ i, z i * x i : Real) ≤ M := by
    intro x hxS
    have hle := hxmax' x hxS
    simpa [M, dotProduct] using hle
  have hle_top : h z ≤ ((M - m : Real) : EReal) := by
    unfold h supremumInnerSub
    refine sSup_le ?_
    rintro y ⟨x, rfl⟩
    have hxS : x.1 ∈ S := x.2
    have hdot : (∑ i, z i * x.1 i : Real) ≤ M := hle_M _ hxS
    have hfm : m ≤ f x.1 := hm _ hxS
    have hreal : (∑ i, z i * x.1 i : Real) - f x.1 ≤ M - m := by
      linarith [hdot, hfm]
    have hreal' :
        ((∑ i, z i * x.1 i - f x.1 : Real) : EReal) ≤ ((M - m : Real) : EReal) :=
      (EReal.coe_le_coe_iff).2 hreal
    simpa [EReal.coe_sub] using hreal'
  have h_not_top : h z ≠ (⊤ : EReal) := by
    intro htop
    have hle' : (⊤ : EReal) ≤ ((M - m : Real) : EReal) := by
      simpa [htop] using hle_top
    have hnot : ((M - m : Real) : EReal) ≠ (⊤ : EReal) := by
      exact EReal.coe_ne_top _
    have hEq : ((M - m : Real) : EReal) = (⊤ : EReal) := (top_le_iff).1 hle'
    exact hnot hEq
  rcases hS_ne with ⟨x0, hx0S⟩
  have hterm_not_bot :
      ((∑ i, z i * x0 i : Real) : EReal) - (f x0 : EReal) ≠ (⊥ : EReal) := by
    have hterm' :
        ((∑ i, z i * x0 i - f x0 : Real) : EReal) ≠ (⊥ : EReal) := by
      exact EReal.coe_ne_bot _
    simpa [EReal.coe_sub] using hterm'
  have hle_term :
      ((∑ i, z i * x0 i : Real) : EReal) - (f x0 : EReal) ≤ h z := by
    unfold h supremumInnerSub
    exact le_sSup ⟨⟨x0, hx0S⟩, rfl⟩
  have h_not_bot : h z ≠ (⊥ : EReal) := by
    intro hbot
    have hle_bot :
        ((∑ i, z i * x0 i : Real) : EReal) - (f x0 : EReal) ≤ (⊥ : EReal) := by
      simpa [hbot] using hle_term
    have hterm_eq : ((∑ i, z i * x0 i : Real) : EReal) - (f x0 : EReal) = (⊥ : EReal) :=
      (le_bot_iff).1 hle_bot
    exact hterm_not_bot hterm_eq
  exact ⟨h_not_top, h_not_bot⟩

/-- `clConv` is monotone with respect to pointwise order. -/
lemma clConv_mono {n : Nat} {f₁ f₂ : (Fin n → Real) → EReal} (h : f₁ ≤ f₂) :
    clConv n f₁ ≤ clConv n f₂ := by
  classical
  intro x
  unfold clConv
  refine sSup_le ?_
  rintro y ⟨hAff, hhAff, rfl⟩
  have hhAff' : ∀ y, (hAff y : EReal) ≤ f₂ y := by
    intro y
    exact le_trans (hhAff y) (h y)
  exact affine_le_clConv (n := n) (f := f₂) hAff hhAff' x

/-- For compact `S` and continuous `f`, the biconjugate envelope coincides with the convex
hull function of the `+∞` extension. -/
lemma clConv_fExt_eq_convexHullFunction_fExt_of_closedConvexHull
    {n : Nat} {S : Set (Fin n → Real)} (hS_ne : S.Nonempty) (hS_closed : IsClosed S)
    (hS_bdd : Bornology.IsBounded S) {f : (Fin n → Real) → Real} (hf : ContinuousOn f S) :
    (let fExt : (Fin n → Real) → EReal := fun x => (f x : EReal) + indicatorFunction S x
    clConv n fExt = convexHullFunction fExt) := by
  classical
  intro fExt
  have hclosed_proper :
      ClosedConvexFunction (convexHullFunction fExt) ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (convexHullFunction fExt) := by
    simpa [fExt] using
      (closedConvex_and_properConvexFunctionOn_convexHullFunction_of_continuousOn_closed_bounded
        (S := S) hS_ne hS_closed hS_bdd (f := f) hf)
  have hcl_eq :
      clConv n (convexHullFunction fExt) = convexHullFunction fExt := by
    have hls : LowerSemicontinuous (convexHullFunction fExt) := hclosed_proper.1.2
    have hproper := hclosed_proper.2
    simpa using
      (clConv_eq_of_closedProperConvex (n := n) (f := convexHullFunction fExt) hls hproper)
  have hle_fExt : convexHullFunction fExt ≤ fExt :=
    (convexHullFunction_greatest_convex_minorant (g := fExt)).2.1
  have hcl_mono :
      clConv n (convexHullFunction fExt) ≤ clConv n fExt :=
    clConv_mono (n := n) (f₁ := convexHullFunction fExt) (f₂ := fExt) hle_fExt
  have hle1 : convexHullFunction fExt ≤ clConv n fExt := by
    simpa [hcl_eq] using hcl_mono
  have hconv_cl : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) (clConv n fExt) := by
    have hconv : ConvexFunction (clConv n fExt) := by
      have hcc := (fenchelConjugate_closedConvex (n := n) (f := fenchelConjugate n fExt))
      have hconv' : ConvexFunction (fenchelConjugate n (fenchelConjugate n fExt)) := hcc.2
      simpa [fenchelConjugate_biconjugate_eq_clConv (n := n) (f := fExt)] using hconv'
    simpa [ConvexFunction] using hconv
  have hcl_le : clConv n fExt ≤ fExt := clConv_le (n := n) (f := fExt)
  have hle2 :
      clConv n fExt ≤ convexHullFunction fExt :=
    (convexHullFunction_greatest_convex_minorant (g := fExt)).2.2
      (h := clConv n fExt) hconv_cl hcl_le
  exact le_antisymm hle2 hle1

/-- Proposition 17.2.3 (Finiteness of `h` and identification of its conjugate), LaTeX label
`prop:h_conj`.

Assume the hypotheses of Corollary 17.2.1: `S` is a nonempty closed bounded subset of `ℝⁿ`, `f` is
continuous on `S`, and we extend `f` by `f(x) = +∞` outside `S`.

Then the function `h` from Definition 17.2.2 is finite everywhere (hence continuous everywhere).
Moreover, using Theorem 12.2, the conjugate `h^*` equals `conv f` (here: `convexHullFunction`
applied to the extension). -/
theorem supremumInnerSub_finite_and_fenchelConjugate_eq_convexHullFunction_of_continuousOn_closed_bounded
    {n : Nat} {S : Set (Fin n → Real)} (hS_ne : S.Nonempty) (hS_closed : IsClosed S)
    (hS_bdd : Bornology.IsBounded S) {f : (Fin n → Real) → Real} (hf : ContinuousOn f S) :
    (let fExt : (Fin n → Real) → EReal := fun x => (f x : EReal) + indicatorFunction S x
    let h : (Fin n → Real) → EReal :=
      fun z => supremumInnerSub (S := S) (f := fun x : S => (f x.1 : EReal)) z
    (∀ z, h z ≠ (⊤ : EReal) ∧ h z ≠ (⊥ : EReal)) ∧
      fenchelConjugate n h = convexHullFunction fExt) := by
  classical
  intro fExt h
  have hfinite :
      ∀ z, h z ≠ (⊤ : EReal) ∧ h z ≠ (⊥ : EReal) := by
    simpa [h] using
      (supremumInnerSub_ne_top_and_ne_bot_of_continuousOn_closed_bounded
        (S := S) hS_ne hS_closed hS_bdd (f := f) hf)
  have hconj' : ∀ z, h z = fenchelConjugate n fExt z := by
    simpa [h, fExt] using
      (supremumInnerSub_eq_fenchelConjugate_fExt (S := S) (f := f))
  have hEq : h = fenchelConjugate n fExt := by
    funext z
    exact hconj' z
  have hcl : clConv n fExt = convexHullFunction fExt := by
    simpa [fExt] using
      (clConv_fExt_eq_convexHullFunction_fExt_of_closedConvexHull
        (S := S) hS_ne hS_closed hS_bdd (f := f) hf)
  have hconj : fenchelConjugate n h = convexHullFunction fExt := by
    calc
      fenchelConjugate n h = fenchelConjugate n (fenchelConjugate n fExt) := by
        simp [hEq]
      _ = clConv n fExt := by
        simpa using (fenchelConjugate_biconjugate_eq_clConv (n := n) (f := fExt))
      _ = convexHullFunction fExt := hcl
  exact ⟨hfinite, hconj⟩

/-- Definition 17.2.4 (Half-space representation), LaTeX label `def:halfspace`.

A closed half-space `H ⊆ ℝⁿ` can be represented by a pair `(x^*, μ^*) ∈ ℝ^{n+1}` with `x^* ≠ 0`,
as

`H = {x ∈ ℝⁿ | ⟪x, x^*⟫ ≤ μ^*}`.

In `Fin n → ℝ`, the inner product `⟪x, x^*⟫` is `x ⬝ᵥ x^*`. -/
structure HalfspaceRep (n : Nat) where
  xStar : Fin n → Real
  muStar : Real
  hxStar : xStar ≠ 0

/-- The closed half-space represented by `r`. -/
def HalfspaceRep.set {n : Nat} (r : HalfspaceRep n) : Set (Fin n → Real) :=
  {x : Fin n → Real | x ⬝ᵥ r.xStar ≤ r.muStar}

/-- Definition 17.2.5 (Intersection of half-spaces), LaTeX label `def:C`.

Let `S* ⊆ ℝ^{n+1}` be nonempty. Define the closed convex set

`C = {x ∈ ℝⁿ | ∀ (x*, μ*) ∈ S*, ⟪x, x*⟫ ≤ μ*}`.

In this formalization, we model `ℝⁿ` as `Fin n → ℝ` and `ℝ^{n+1}` as
`(Fin n → ℝ) × ℝ`. The inner product `⟪x, x*⟫` is `x ⬝ᵥ x*`. -/
def intersectionOfHalfspaces {n : Nat} (Sstar : Set ((Fin n → Real) × Real)) : Set (Fin n → Real) :=
  {x : Fin n → Real | ∀ p ∈ Sstar, x ⬝ᵥ p.1 ≤ p.2}

/-- Definition 17.2.5 (Intersection of half-spaces), LaTeX label `def:C`:
the set `intersectionOfHalfspaces S*` is convex. -/
theorem convex_intersectionOfHalfspaces {n : Nat} (Sstar : Set ((Fin n → Real) × Real)) :
    Convex ℝ (intersectionOfHalfspaces (n := n) Sstar) := by
  classical
  intro x hx y hy a b ha hb hab
  simp [intersectionOfHalfspaces] at hx hy ⊢
  intro v μ hmem
  have hx' : x ⬝ᵥ v ≤ μ := hx v μ hmem
  have hy' : y ⬝ᵥ v ≤ μ := hy v μ hmem
  have hle1 : a * (x ⬝ᵥ v) ≤ a * μ :=
    mul_le_mul_of_nonneg_left hx' ha
  have hle2 : b * (y ⬝ᵥ v) ≤ b * μ :=
    mul_le_mul_of_nonneg_left hy' hb
  have hsum :
      a * (x ⬝ᵥ v) + b * (y ⬝ᵥ v) ≤ a * μ + b * μ :=
    add_le_add hle1 hle2
  have hmu : a * μ + b * μ = μ := by
    calc
      a * μ + b * μ = (a + b) * μ := by ring
      _ = μ := by simp [hab]
  have hfinal : a * x ⬝ᵥ v + b * y ⬝ᵥ v ≤ μ := by
    calc
      a * x ⬝ᵥ v + b * y ⬝ᵥ v ≤ a * μ + b * μ := hsum
      _ = μ := hmu
  exact hfinal

/-- Definition 17.2.5 (Intersection of half-spaces), LaTeX label `def:C`:
the set `intersectionOfHalfspaces S*` is closed. -/
theorem isClosed_intersectionOfHalfspaces {n : Nat} (Sstar : Set ((Fin n → Real) × Real)) :
    IsClosed (intersectionOfHalfspaces (n := n) Sstar) := by
  classical
  have hclosed_halfspace :
      ∀ p : (Fin n → Real) × Real,
        IsClosed {x : Fin n → Real | x ⬝ᵥ p.1 ≤ p.2} := by
    intro p
    have hcont : Continuous fun x : Fin n → Real => x ⬝ᵥ p.1 := by
      simpa [dotProduct_comm] using (continuous_dotProduct_const (x := p.1))
    simpa using (isClosed_le hcont continuous_const)
  have hclosed_iInter :
      IsClosed (⋂ p ∈ Sstar, {x : Fin n → Real | x ⬝ᵥ p.1 ≤ p.2}) := by
    refine isClosed_iInter ?_
    intro p
    refine isClosed_iInter ?_
    intro hp
    exact hclosed_halfspace p
  have hset :
      intersectionOfHalfspaces (n := n) Sstar =
        ⋂ p ∈ Sstar, {x : Fin n → Real | x ⬝ᵥ p.1 ≤ p.2} := by
    ext x; constructor <;> intro hx
    · simpa [intersectionOfHalfspaces, Set.mem_iInter] using hx
    · simpa [intersectionOfHalfspaces, Set.mem_iInter] using hx
  simpa [hset] using hclosed_iInter

/-- Containment in a half-space is equivalent to a pointwise dot-product bound. -/
lemma halfspaceRep_set_superset_iff_forall_dot_le {n : Nat} (C : Set (Fin n → Real))
    (r : HalfspaceRep n) :
    r.set ⊇ C ↔ ∀ x ∈ C, x ⬝ᵥ r.xStar ≤ r.muStar := by
  constructor
  · intro h x hx
    have hx' : x ∈ r.set := h hx
    simpa [HalfspaceRep.set] using hx'
  · intro h x hx
    have hx' : x ⬝ᵥ r.xStar ≤ r.muStar := h x hx
    change x ∈ r.set
    simpa [HalfspaceRep.set] using hx'

/-- Swap the dot-product order to match the `⬝ᵥ` notation. -/
lemma dotProduct_comm_bridge_for_supportFunction {n : Nat} (xStar x : Fin n → Real) :
    dotProduct xStar x = (x ⬝ᵥ xStar : Real) := by
  simp [dotProduct_comm]

/-- A support-function bound is equivalent to a pointwise dot-product bound. -/
lemma supportFunction_le_iff_forall_dot_le {n : Nat} (C : Set (Fin n → Real))
    (r : HalfspaceRep n) (hC : C.Nonempty)
    (hbd : BddAbove {t : ℝ | ∃ y ∈ C, t = dotProduct r.xStar y}) :
    supportFunction C r.xStar ≤ r.muStar ↔
      ∀ x ∈ C, dotProduct r.xStar x ≤ r.muStar := by
  classical
  let s : Set ℝ := {t : ℝ | ∃ y ∈ C, t = dotProduct r.xStar y}
  have hbd' : BddAbove s := by
    simpa [s] using hbd
  have hne : s.Nonempty := by
    rcases hC with ⟨y, hy⟩
    exact ⟨dotProduct r.xStar y, ⟨y, hy, rfl⟩⟩
  constructor
  · intro hsup
    have hsup' : ∀ t ∈ s, t ≤ r.muStar := by
      have : sSup s ≤ r.muStar := by
        simpa [supportFunction, s] using hsup
      exact (csSup_le_iff (s := s) (a := r.muStar) hbd' hne).1 this
    intro x hx
    exact hsup' _ ⟨x, hx, rfl⟩
  · intro hforall
    have hsup' : ∀ t ∈ s, t ≤ r.muStar := by
      intro t ht
      rcases ht with ⟨x, hx, rfl⟩
      exact hforall x hx
    have : sSup s ≤ r.muStar :=
      (csSup_le_iff (s := s) (a := r.muStar) hbd' hne).2 hsup'
    simpa [supportFunction, s] using this

/-- Lemma 17.2.6 (Containment characterized by the support function), LaTeX label
`lem:containment_support`.

Let `C ⊆ ℝⁿ` and let `(x^*, μ^*) ∈ ℝ^{n+1}` with `x^* ≠ 0`. Set
`H = {x ∈ ℝⁿ | ⟪x, x^*⟫ ≤ μ^*}`. Then `H ⊇ C` if and only if
`μ^* ≥ sup_{x ∈ C} ⟪x, x^*⟫ =: supp(x^*, C)`.

In this formalization, `H` is `r.set` for `r : HalfspaceRep n`, and the support function is
`supportFunction C r.xStar` (up to symmetry of the dot product). -/
lemma halfspaceRep_set_superset_iff_supportFunction_le {n : Nat} (C : Set (Fin n → Real))
    (r : HalfspaceRep n) (hC : C.Nonempty)
    (hbd : BddAbove {t : ℝ | ∃ y ∈ C, t = dotProduct r.xStar y}) :
    r.set ⊇ C ↔ supportFunction C r.xStar ≤ r.muStar := by
  constructor
  · intro hsuperset
    have hforall : ∀ x ∈ C, x ⬝ᵥ r.xStar ≤ r.muStar :=
      (halfspaceRep_set_superset_iff_forall_dot_le (C := C) (r := r)).1 hsuperset
    have hforall' : ∀ x ∈ C, dotProduct r.xStar x ≤ r.muStar := by
      intro x hx
      have hx' := hforall x hx
      simpa [dotProduct_comm_bridge_for_supportFunction] using hx'
    exact
      (supportFunction_le_iff_forall_dot_le (C := C) (r := r) hC hbd).2 hforall'
  · intro hsup
    have hforall' : ∀ x ∈ C, dotProduct r.xStar x ≤ r.muStar :=
      (supportFunction_le_iff_forall_dot_le (C := C) (r := r) hC hbd).1 hsup
    have hforall : ∀ x ∈ C, x ⬝ᵥ r.xStar ≤ r.muStar := by
      intro x hx
      have hx' := hforall' x hx
      simpa [dotProduct_comm_bridge_for_supportFunction] using hx'
    exact (halfspaceRep_set_superset_iff_forall_dot_le (C := C) (r := r)).2 hforall

/-- Definition 17.2.7 (The cone `K` and the function `f` generated by `S*`), LaTeX label
`def:Kf`.

Let `S* ⊆ ℝ^{n+1}` be nonempty and consider the “vertical” vector `(0, 1) ∈ ℝ^{n+1}`. Set
`D := S* ∪ {(0, 1)}` and let `K ⊆ ℝ^{n+1}` be the convex cone generated by `D`. Define
`f : ℝⁿ → ℝ ∪ {+∞}` by

`f(x*) = inf { μ* ∈ ℝ | (x*, μ*) ∈ K }`.

In this formalization, we model `ℝⁿ` as `Fin n → ℝ` and `ℝ^{n+1}` as `(Fin n → ℝ) × ℝ`, and we
take the codomain `ℝ ∪ {+∞}` to be `WithTop ℝ`. -/
def verticalVector (n : Nat) : (Fin n → Real) × Real :=
  (0, 1)

/-- The set `D := S* ∪ {(0, 1)}` obtained by adjoining the vertical vector to `S*`. -/
def adjoinVertical {n : Nat} (Sstar : Set ((Fin n → Real) × Real)) : Set ((Fin n → Real) × Real) :=
  Sstar ∪ {verticalVector n}

/-- The convex cone `K` generated by `D = S* ∪ {(0, 1)}` (as a subset of `ℝ^{n+1}`). -/
def coneK {n : Nat} (Sstar : Set ((Fin n → Real) × Real)) : Set ((Fin n → Real) × Real) :=
  Set.insert (0 : (Fin n → Real) × Real)
    ((ConvexCone.hull Real (adjoinVertical (n := n) Sstar) : Set ((Fin n → Real) × Real)))

/-- The function `f(x*) = inf {μ* | (x*, μ*) ∈ K}` with values in `ℝ ∪ {+∞}`. -/
noncomputable def infMuInCone {n : Nat} (Sstar : Set ((Fin n → Real) × Real)) (xStar : Fin n → Real) :
    WithTop Real :=
  sInf ((fun μ : Real => (μ : WithTop Real)) '' {μ : Real | (xStar, μ) ∈ coneK (n := n) Sstar})

/-- The `infMuInCone`-based embedding into `EReal` never hits `⊥`. -/
lemma infMuInCone_embed_ne_bot {n : Nat} (Sstar : Set ((Fin n → Real) × Real)) :
    ∀ xStar : Fin n → Real,
      (match infMuInCone (n := n) Sstar xStar with
        | (μ : Real) => (μ : EReal)
        | ⊤ => (⊤ : EReal)) ≠ (⊥ : EReal) := by
  intro xStar
  cases h : infMuInCone (n := n) Sstar xStar <;> simp

/-- The epigraph of the closure of `infMuInCone` equals the closure of its epigraph. -/
lemma epigraph_convexFunctionClosure_eq_closure_epigraph_of_infMuInCone {n : Nat}
    (Sstar : Set ((Fin n → Real) × Real)) :
    (let f : (Fin n → Real) → EReal :=
      fun xStar =>
        match infMuInCone (n := n) Sstar xStar with
        | (μ : Real) => (μ : EReal)
        | ⊤ => (⊤ : EReal)
    epigraph (S := (Set.univ : Set (Fin n → Real))) (convexFunctionClosure f) =
      closure (epigraph (S := (Set.univ : Set (Fin n → Real))) f)) := by
  classical
  let f : (Fin n → Real) → EReal :=
    fun xStar =>
      match infMuInCone (n := n) Sstar xStar with
      | (μ : Real) => (μ : EReal)
      | ⊤ => (⊤ : EReal)
  have hbot : ∀ xStar, f xStar ≠ (⊥ : EReal) := by
    intro xStar
    simpa [f] using (infMuInCone_embed_ne_bot (n := n) Sstar xStar)
  simpa [f] using (epigraph_convexFunctionClosure_eq_closure_epigraph (f := f) hbot).1

/-- The cone `coneK` is contained in the epigraph of the support function of `C`. -/
lemma coneK_subset_epigraph_supportFunctionEReal {n : Nat}
    (Sstar : Set ((Fin n → Real) × Real))
    (hC_ne : intersectionOfHalfspaces (n := n) Sstar ≠ (∅ : Set (Fin n → Real))) :
    (let C : Set (Fin n → Real) := intersectionOfHalfspaces (n := n) Sstar
    coneK (n := n) Sstar ⊆
      epigraph (S := (Set.univ : Set (Fin n → Real))) (supportFunctionEReal C)) := by
  classical
  intro C
  have hCne : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hC_ne
  have hCconv : Convex ℝ C := convex_intersectionOfHalfspaces (n := n) Sstar
  have hpos :
      PositivelyHomogeneous (supportFunctionEReal C) :=
    (section13_supportFunctionEReal_closedProperConvex_posHom (n := n) (C := C) hCne hCconv).2.2
  have hsub :
      ∀ xStar₁ xStar₂ : Fin n → Real,
        supportFunctionEReal C (xStar₁ + xStar₂) ≤
          supportFunctionEReal C xStar₁ + supportFunctionEReal C xStar₂ :=
    section13_supportFunctionEReal_subadditive (n := n) (C := C) hCne hCconv
  let K : ConvexCone ℝ ((Fin n → Real) × Real) :=
    { carrier := epigraph (S := (Set.univ : Set (Fin n → Real))) (supportFunctionEReal C)
      smul_mem' := by
        intro c hc x hx
        rcases x with ⟨x, μ⟩
        have hle : supportFunctionEReal C x ≤ (μ : EReal) :=
          (mem_epigraph_univ_iff (f := supportFunctionEReal C)).1 hx
        have hmul : (c : EReal) * supportFunctionEReal C x ≤ ((c * μ : Real) : EReal) :=
          ereal_mul_le_mul_of_pos_left (t := c) hc hle
        have hle' : supportFunctionEReal C (c • x) ≤ ((c * μ : Real) : EReal) := by
          have hpos' := hpos x c hc
          simpa [hpos'] using hmul
        have hmem :
            (c • x, c * μ) ∈
              epigraph (S := (Set.univ : Set (Fin n → Real))) (supportFunctionEReal C) :=
          (mem_epigraph_univ_iff (f := supportFunctionEReal C)).2 hle'
        simpa [smul_eq_mul] using hmem
      add_mem' := by
        intro x hx y hy
        rcases x with ⟨x, μ⟩
        rcases y with ⟨y, ν⟩
        have hxle : supportFunctionEReal C x ≤ (μ : EReal) :=
          (mem_epigraph_univ_iff (f := supportFunctionEReal C)).1 hx
        have hyle : supportFunctionEReal C y ≤ (ν : EReal) :=
          (mem_epigraph_univ_iff (f := supportFunctionEReal C)).1 hy
        have hle :
            supportFunctionEReal C (x + y) ≤ ((μ + ν : Real) : EReal) := by
          calc
            supportFunctionEReal C (x + y) ≤
                supportFunctionEReal C x + supportFunctionEReal C y := hsub x y
            _ ≤ (μ : EReal) + (ν : EReal) := add_le_add hxle hyle
            _ = ((μ + ν : Real) : EReal) := by simp
        have hmem :
            (x + y, μ + ν) ∈
              epigraph (S := (Set.univ : Set (Fin n → Real))) (supportFunctionEReal C) :=
          (mem_epigraph_univ_iff (f := supportFunctionEReal C)).2 (by simpa using hle)
        simpa using hmem }
  have hadj :
      adjoinVertical (n := n) Sstar ⊆ (K : Set ((Fin n → Real) × Real)) := by
    intro p hp
    rcases hp with hp | hp
    · rcases p with ⟨y, μ⟩
      have hCdef : ∀ x ∈ C, x ⬝ᵥ y ≤ μ := by
        intro x hx
        have hx' : ∀ q ∈ Sstar, x ⬝ᵥ q.1 ≤ q.2 := by
          simpa [C, intersectionOfHalfspaces] using hx
        exact hx' ⟨y, μ⟩ hp
      have hdot : ∀ x ∈ C, dotProduct x y ≤ μ := by
        intro x hx
        have hxle : x ⬝ᵥ y ≤ μ := hCdef x hx
        have hxle' : dotProduct y x ≤ μ := by
          simpa [dotProduct_comm_bridge_for_supportFunction] using hxle
        simpa [dotProduct_comm] using hxle'
      have hle : supportFunctionEReal C y ≤ (μ : EReal) :=
        (section13_supportFunctionEReal_le_coe_iff (C := C) (y := y) (μ := μ)).2 hdot
      exact (mem_epigraph_univ_iff (f := supportFunctionEReal C)).2 (by simpa using hle)
    · rcases hp with rfl
      have hle : supportFunctionEReal C (0 : Fin n → Real) ≤ (1 : EReal) :=
        (section13_supportFunctionEReal_le_coe_iff (C := C) (y := 0) (μ := 1)).2
          (by intro x hx; simp)
      exact (mem_epigraph_univ_iff (f := supportFunctionEReal C)).2 (by simpa using hle)
  have hhull :
      (ConvexCone.hull Real (adjoinVertical (n := n) Sstar) : Set ((Fin n → Real) × Real)) ⊆
        (K : Set ((Fin n → Real) × Real)) :=
    (ConvexCone.hull_min (C := K) hadj)
  intro p hp
  have hp' :
      p = 0 ∨
        p ∈ (ConvexCone.hull Real (adjoinVertical (n := n) Sstar) :
          Set ((Fin n → Real) × Real)) := by
    simpa [coneK, K] using hp
  cases hp' with
  | inl h0 =>
      have hle0 : supportFunctionEReal C (0 : Fin n → Real) ≤ (0 : EReal) :=
        (section13_supportFunctionEReal_le_coe_iff (C := C) (y := 0) (μ := 0)).2
          (by intro x hx; simp)
      have hmem0 :
          (0 : (Fin n → Real) × Real) ∈
            epigraph (S := (Set.univ : Set (Fin n → Real))) (supportFunctionEReal C) :=
        by
          have hle0' := hle0
          simp at hle0'
          exact (mem_epigraph_univ_iff (f := supportFunctionEReal C)).2 hle0'
      simpa [h0, K] using hmem0
  | inr hmem =>
      simpa [K] using (hhull hmem)

/-- Approximate the infimum in `infMuInCone` by a point in `coneK`. -/
lemma exists_mu_mem_coneK_lt_of_infMuInCone_lt {n : Nat} (Sstar : Set ((Fin n → Real) × Real))
    (hC_ne : intersectionOfHalfspaces (n := n) Sstar ≠ (∅ : Set (Fin n → Real)))
    {xStar : Fin n → Real} {a : Real}
    (h : infMuInCone (n := n) Sstar xStar < (a : WithTop Real)) :
    ∃ μ : Real, μ < a ∧ (xStar, μ) ∈ coneK (n := n) Sstar := by
  classical
  let C : Set (Fin n → Real) := intersectionOfHalfspaces (n := n) Sstar
  have hCne : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hC_ne
  have hCconv : Convex ℝ C := convex_intersectionOfHalfspaces (n := n) Sstar
  set S : Set Real := { μ : Real | (xStar, μ) ∈ coneK (n := n) Sstar }
  set T : Set (WithTop Real) := (fun μ : Real => (μ : WithTop Real)) '' S
  have hT_nonempty : T.Nonempty := by
    by_cases hT : T = ∅
    · exfalso
      have htop : infMuInCone (n := n) Sstar xStar = (⊤ : WithTop Real) := by
        simp [infMuInCone, S, T, hT]
      have h' : False := by
        have h'' := h
        simp [htop] at h''
      exact h'
    · exact Set.nonempty_iff_ne_empty.2 hT
  rcases hT_nonempty with ⟨t, htT⟩
  rcases htT with ⟨μ0, hμ0S, rfl⟩
  have hS_nonempty : S.Nonempty := ⟨μ0, hμ0S⟩
  have hsubset :
      coneK (n := n) Sstar ⊆
        epigraph (S := (Set.univ : Set (Fin n → Real))) (supportFunctionEReal C) := by
    simpa [C] using (coneK_subset_epigraph_supportFunctionEReal (n := n) Sstar hC_ne)
  have hle0 : supportFunctionEReal C xStar ≤ (μ0 : EReal) := by
    have hmem0 :
        (xStar, μ0) ∈
          epigraph (S := (Set.univ : Set (Fin n → Real))) (supportFunctionEReal C) :=
      hsubset hμ0S
    exact (mem_epigraph_univ_iff (f := supportFunctionEReal C)).1 hmem0
  have hnotbot :
      supportFunctionEReal C xStar ≠ (⊥ : EReal) :=
    section13_supportFunctionEReal_ne_bot (n := n) (C := C) hCne hCconv xStar
  have hnot_top : supportFunctionEReal C xStar ≠ (⊤ : EReal) := by
    intro htop
    have hle : (⊤ : EReal) ≤ (μ0 : EReal) := by
      have hle' := hle0
      simp [htop] at hle'
    have hμ0 : (μ0 : EReal) = ⊤ := (top_le_iff).1 hle
    exact (EReal.coe_ne_top _ hμ0).elim
  cases hsf : supportFunctionEReal C xStar with
  | bot =>
      exact (hnotbot hsf).elim
  | top =>
      exact (hnot_top hsf).elim
  | coe a0 =>
      have hS_bdd : BddBelow S := by
        refine ⟨a0, ?_⟩
        intro μ hμS
        have hmem :
            (xStar, μ) ∈
              epigraph (S := (Set.univ : Set (Fin n → Real))) (supportFunctionEReal C) :=
          hsubset hμS
        have hle : supportFunctionEReal C xStar ≤ (μ : EReal) :=
          (mem_epigraph_univ_iff (f := supportFunctionEReal C)).1 hmem
        have hle' : (a0 : EReal) ≤ (μ : EReal) := by simpa [hsf] using hle
        exact (EReal.coe_le_coe_iff).1 hle'
      have hco :
          (↑(sInf S) : WithTop Real) =
            sInf ((fun μ : Real => (μ : WithTop Real)) '' S) :=
        WithTop.coe_sInf' (s := S) hS_nonempty hS_bdd
      have hlt' : (↑(sInf S) : WithTop Real) < (a : WithTop Real) := by
        have h' :
            sInf ((fun μ : Real => (μ : WithTop Real)) '' S) < (a : WithTop Real) := by
          simpa [infMuInCone, S, T] using h
        simpa [hco] using h'
      have hlt_real : sInf S < a := (WithTop.coe_lt_coe.mp hlt')
      rcases (csInf_lt_iff hS_bdd hS_nonempty).1 hlt_real with ⟨μ, hμS, hμlt⟩
      exact ⟨μ, hμlt, by simpa [S] using hμS⟩

/-- Adding a nonnegative multiple of the vertical vector keeps points in `coneK`. -/
lemma mem_coneK_add_vertical {n : Nat} (Sstar : Set ((Fin n → Real) × Real))
    {xStar : Fin n → Real} {μ t : Real} (hp : (xStar, μ) ∈ coneK (n := n) Sstar) (ht : 0 ≤ t) :
    (xStar, μ + t) ∈ coneK (n := n) Sstar := by
  classical
  by_cases ht0 : t = 0
  · subst ht0
    simpa using hp
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  let K : ConvexCone ℝ ((Fin n → Real) × Real) :=
    ConvexCone.hull Real (adjoinVertical (n := n) Sstar)
  have hvertical : verticalVector n ∈ (K : Set ((Fin n → Real) × Real)) := by
    have : verticalVector n ∈ adjoinVertical (n := n) Sstar := by
      simp [adjoinVertical]
    exact (ConvexCone.subset_hull (R := Real) (s := adjoinVertical (n := n) Sstar)) this
  have hsmul : t • verticalVector n ∈ (K : Set ((Fin n → Real) × Real)) :=
    K.smul_mem htpos hvertical
  have hp' : (xStar, μ) = 0 ∨ (xStar, μ) ∈ (K : Set ((Fin n → Real) × Real)) := by
    have hp' :
        (xStar, μ) ∈
          Set.insert (0 : (Fin n → Real) × Real) (K : Set ((Fin n → Real) × Real)) := by
      simpa [coneK, K] using hp
    exact (Set.mem_insert_iff).1 hp'
  rcases hp' with hzero | hpK
  · cases hzero
    have hvec : ((0 : Fin n → Real), t) = t • verticalVector n := by
      ext i <;> simp [verticalVector]
    have hmem : ((0 : Fin n → Real), t) ∈ (K : Set ((Fin n → Real) × Real)) := by
      simpa [hvec] using hsmul
    have : ((0 : Fin n → Real), t) ∈
        Set.insert (0 : (Fin n → Real) × Real) (K : Set ((Fin n → Real) × Real)) :=
      (Set.mem_insert_iff).2 (Or.inr hmem)
    simpa [coneK, K] using this
  ·
    have hadd : (xStar, μ) + t • verticalVector n ∈ (K : Set ((Fin n → Real) × Real)) :=
      K.add_mem hpK hsmul
    have hsum : (xStar, μ) + t • verticalVector n = (xStar, μ + t) := by
      ext i <;> simp [verticalVector]
    have hmem : (xStar, μ + t) ∈ (K : Set ((Fin n → Real) × Real)) := by
      simpa [hsum] using hadd
    have : (xStar, μ + t) ∈
        Set.insert (0 : (Fin n → Real) × Real) (K : Set ((Fin n → Real) × Real)) :=
      (Set.mem_insert_iff).2 (Or.inr hmem)
    simpa [coneK, K] using this

/-- Positive scaling preserves membership in `coneK`. -/
lemma smul_mem_coneK {n : Nat} (Sstar : Set ((Fin n → Real) × Real))
    {t : Real} (ht : 0 < t) {p : (Fin n → Real) × Real} (hp : p ∈ coneK (n := n) Sstar) :
    t • p ∈ coneK (n := n) Sstar := by
  classical
  let K : ConvexCone ℝ ((Fin n → Real) × Real) :=
    ConvexCone.hull Real (adjoinVertical (n := n) Sstar)
  have hp' : p = 0 ∨ p ∈ (K : Set ((Fin n → Real) × Real)) := by
    have hp' :
        p ∈ Set.insert (0 : (Fin n → Real) × Real) (K : Set ((Fin n → Real) × Real)) := by
      simpa [coneK, K] using hp
    exact (Set.mem_insert_iff).1 hp'
  rcases hp' with rfl | hpK
  ·
    have : (0 : (Fin n → Real) × Real) ∈
        Set.insert (0 : (Fin n → Real) × Real) (K : Set ((Fin n → Real) × Real)) :=
      (Set.mem_insert_iff).2 (Or.inl rfl)
    simpa [coneK, K] using this
  ·
    have hsmul : t • p ∈ (K : Set ((Fin n → Real) × Real)) := K.smul_mem ht hpK
    have : t • p ∈
        Set.insert (0 : (Fin n → Real) × Real) (K : Set ((Fin n → Real) × Real)) :=
      (Set.mem_insert_iff).2 (Or.inr hsmul)
    simpa [coneK, K] using this

/-- The cone `coneK` is convex. -/
lemma convex_coneK {n : Nat} (Sstar : Set ((Fin n → Real) × Real)) :
    Convex ℝ (coneK (n := n) Sstar) := by
  classical
  let K : ConvexCone ℝ ((Fin n → Real) × Real) :=
    ConvexCone.hull Real (adjoinVertical (n := n) Sstar)
  have hconvK : Convex ℝ (K : Set ((Fin n → Real) × Real)) := K.convex
  intro x hx y hy a b ha hb hab
  have hx' : x = 0 ∨ x ∈ (K : Set ((Fin n → Real) × Real)) := by
    have hx' :
        x ∈ Set.insert (0 : (Fin n → Real) × Real) (K : Set ((Fin n → Real) × Real)) := by
      simpa [coneK, K] using hx
    exact (Set.mem_insert_iff).1 hx'
  have hy' : y = 0 ∨ y ∈ (K : Set ((Fin n → Real) × Real)) := by
    have hy' :
        y ∈ Set.insert (0 : (Fin n → Real) × Real) (K : Set ((Fin n → Real) × Real)) := by
      simpa [coneK, K] using hy
    exact (Set.mem_insert_iff).1 hy'
  rcases hx' with rfl | hxK
  · rcases hy' with rfl | hyK
    · simpa [coneK, K]
    · by_cases hb0 : b = 0
      · subst hb0
        simpa [coneK, K]
      ·
        have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
        have hmem : b • y ∈ (K : Set ((Fin n → Real) × Real)) := K.smul_mem hbpos hyK
        have : b • y ∈
            Set.insert (0 : (Fin n → Real) × Real) (K : Set ((Fin n → Real) × Real)) :=
          (Set.mem_insert_iff).2 (Or.inr hmem)
        simpa [coneK, K] using this
  · rcases hy' with rfl | hyK
    · by_cases ha0 : a = 0
      · subst ha0
        simpa [coneK, K]
      ·
        have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hmem : a • x ∈ (K : Set ((Fin n → Real) × Real)) := K.smul_mem hapos hxK
        have : a • x ∈
            Set.insert (0 : (Fin n → Real) × Real) (K : Set ((Fin n → Real) × Real)) :=
          (Set.mem_insert_iff).2 (Or.inr hmem)
        simpa [coneK, K] using this
    ·
      have hmem : a • x + b • y ∈ (K : Set ((Fin n → Real) × Real)) :=
        hconvK hxK hyK ha hb hab
      have : a • x + b • y ∈
          Set.insert (0 : (Fin n → Real) × Real) (K : Set ((Fin n → Real) × Real)) :=
        (Set.mem_insert_iff).2 (Or.inr hmem)
      simpa [coneK, K] using this

/-- Points in the epigraph of the `infMuInCone` embedding lie in the closure of `coneK`. -/
lemma mem_epigraph_infMuInCone_imp_mem_closure_coneK {n : Nat}
    (Sstar : Set ((Fin n → Real) × Real))
    (hC_ne : intersectionOfHalfspaces (n := n) Sstar ≠ (∅ : Set (Fin n → Real))) :
    (let f : (Fin n → Real) → EReal :=
      fun xStar =>
        match infMuInCone (n := n) Sstar xStar with
        | (μ : Real) => (μ : EReal)
        | ⊤ => (⊤ : EReal)
    epigraph (S := (Set.univ : Set (Fin n → Real))) f ⊆
      closure (coneK (n := n) Sstar)) := by
  classical
  dsimp
  intro p hp
  rcases p with ⟨x, μ⟩
  let f : (Fin n → Real) → EReal :=
    fun xStar =>
      match infMuInCone (n := n) Sstar xStar with
      | (μ : Real) => (μ : EReal)
      | ⊤ => (⊤ : EReal)
  have hleE : f x ≤ (μ : EReal) := by
    exact (mem_epigraph_univ_iff (f := f) (x := x) (μ := μ)).1 (by simpa using hp)
  have hle_withTop : infMuInCone (n := n) Sstar x ≤ (μ : WithTop Real) := by
    cases h : infMuInCone (n := n) Sstar x with
    | top =>
        have hleTop : (⊤ : EReal) ≤ (μ : EReal) := by
          have hleTop' := hleE
          simp [f, h] at hleTop'
        have hmu : (μ : EReal) = (⊤ : EReal) := (top_le_iff).1 hleTop
        have hmu_ne : (μ : EReal) ≠ (⊤ : EReal) := EReal.coe_ne_top _
        exact (hmu_ne hmu).elim
    | coe m =>
        have hle' : (m : EReal) ≤ (μ : EReal) := by
          simpa [f, h] using hleE
        have hle_real : m ≤ μ := (EReal.coe_le_coe_iff).1 hle'
        simpa [h] using (WithTop.coe_le_coe.mpr hle_real)
  refine Metric.mem_closure_iff.2 ?_
  intro ε hε
  have hmu_lt :
      (μ : WithTop Real) < ((μ + ε / 2 : Real) : WithTop Real) := by
    exact WithTop.coe_lt_coe.mpr (by linarith)
  have hlt : infMuInCone (n := n) Sstar x < ((μ + ε / 2 : Real) : WithTop Real) :=
    lt_of_le_of_lt hle_withTop hmu_lt
  rcases exists_mu_mem_coneK_lt_of_infMuInCone_lt (n := n) Sstar hC_ne hlt with
    ⟨μ0, hμ0lt, hμ0mem⟩
  set t : Real := μ + ε / 2 - μ0
  have ht_nonneg : 0 ≤ t := by
    have hμ0le : μ0 ≤ μ + ε / 2 := le_of_lt hμ0lt
    dsimp [t]
    linarith
  have hmem_shift :
      (x, μ + ε / 2) ∈ coneK (n := n) Sstar := by
    have hmem := mem_coneK_add_vertical (n := n) (Sstar := Sstar) (xStar := x)
      (μ := μ0) (t := t) hμ0mem ht_nonneg
    have hsum : μ0 + t = μ + ε / 2 := by
      dsimp [t]
      linarith
    simpa [hsum] using hmem
  refine ⟨(x, μ + ε / 2), hmem_shift, ?_⟩
  have hdist : dist (x, μ + ε / 2) (x, μ) = |ε / 2| := by
    calc
      dist (x, μ + ε / 2) (x, μ) = dist (μ + ε / 2) μ := by
        simp
      _ = |(μ + ε / 2) - μ| := Real.dist_eq _ _
      _ = |ε / 2| := by simp [add_sub_cancel_left]
  have hpos : 0 < ε / 2 := by linarith
  have hdist' : dist (x, μ + ε / 2) (x, μ) = (ε / 2 : Real) := by
    calc
      dist (x, μ + ε / 2) (x, μ) = |ε / 2| := hdist
      _ = (ε / 2 : Real) := abs_of_pos hpos
  have hlt : (ε / 2 : Real) < ε := by linarith
  have hdist'' : dist (x, μ) (x, μ + ε / 2) = (ε / 2 : Real) := by
    simpa [dist_comm] using hdist'
  calc
    dist (x, μ) (x, μ + ε / 2) = (ε / 2 : Real) := hdist''
    _ < ε := hlt
/-- Points of `coneK` lie in the epigraph of the `infMuInCone` embedding. -/
lemma coneK_subset_epigraph_infMuInCone {n : Nat} (Sstar : Set ((Fin n → Real) × Real))
    (hC_ne : intersectionOfHalfspaces (n := n) Sstar ≠ (∅ : Set (Fin n → Real))) :
    (let f : (Fin n → Real) → EReal :=
      fun xStar =>
        match infMuInCone (n := n) Sstar xStar with
        | (μ : Real) => (μ : EReal)
        | ⊤ => (⊤ : EReal)
    coneK (n := n) Sstar ⊆
      epigraph (S := (Set.univ : Set (Fin n → Real))) f) := by
  classical
  dsimp
  intro p hp
  rcases p with ⟨x, μ⟩
  let C : Set (Fin n → Real) := intersectionOfHalfspaces (n := n) Sstar
  have hCne : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hC_ne
  have hCconv : Convex ℝ C := convex_intersectionOfHalfspaces (n := n) Sstar
  have hmem :
      (μ : WithTop Real) ∈
        (fun μ : Real => (μ : WithTop Real)) '' {μ : Real | (x, μ) ∈ coneK (n := n) Sstar} := by
    exact ⟨μ, hp, rfl⟩
  have hsubset :
      coneK (n := n) Sstar ⊆
        epigraph (S := (Set.univ : Set (Fin n → Real))) (supportFunctionEReal C) := by
    simpa [C] using (coneK_subset_epigraph_supportFunctionEReal (n := n) Sstar hC_ne)
  have hnotbot :
      supportFunctionEReal C x ≠ (⊥ : EReal) :=
    section13_supportFunctionEReal_ne_bot (n := n) (C := C) hCne hCconv x
  have hnot_top : supportFunctionEReal C x ≠ (⊤ : EReal) := by
    have hle0 :
        supportFunctionEReal C x ≤ (μ : EReal) := by
      have hmem0 :
          (x, μ) ∈
          epigraph (S := (Set.univ : Set (Fin n → Real))) (supportFunctionEReal C) :=
        hsubset hp
      exact (mem_epigraph_univ_iff (f := supportFunctionEReal C)).1 hmem0
    intro htop
    have hle : (⊤ : EReal) ≤ (μ : EReal) := by
      have hle' := hle0
      simp [htop] at hle'
    have hμ : (μ : EReal) = ⊤ := (top_le_iff).1 hle
    exact (EReal.coe_ne_top _ hμ).elim
  cases hsf : supportFunctionEReal C x with
  | bot =>
      exact (hnotbot hsf).elim
  | top =>
      exact (hnot_top hsf).elim
  | coe a0 =>
      have hbd :
          BddBelow
              ((fun μ : Real => (μ : WithTop Real)) ''
                {μ : Real | (x, μ) ∈ coneK (n := n) Sstar}) := by
        refine ⟨(a0 : WithTop Real), ?_⟩
        intro t ht
        rcases ht with ⟨μ', hμ', rfl⟩
        have hle0 :
            supportFunctionEReal C x ≤ (μ' : EReal) := by
          have hmem0 :
              (x, μ') ∈
                epigraph (S := (Set.univ : Set (Fin n → Real))) (supportFunctionEReal C) :=
            hsubset hμ'
          exact (mem_epigraph_univ_iff (f := supportFunctionEReal C)).1 hmem0
        have hle' : (a0 : EReal) ≤ (μ' : EReal) := by
          simpa [hsf] using hle0
        have hle_real : a0 ≤ μ' := (EReal.coe_le_coe_iff).1 hle'
        exact (WithTop.coe_le_coe.mpr hle_real)
      have hle : infMuInCone (n := n) Sstar x ≤ (μ : WithTop Real) := by
        simpa [infMuInCone] using
          (csInf_le hbd hmem)
      have hleE :
          (match infMuInCone (n := n) Sstar x with
            | (μ : Real) => (μ : EReal)
            | ⊤ => (⊤ : EReal)) ≤ (μ : EReal) := by
        cases h : infMuInCone (n := n) Sstar x with
        | top =>
            have htop : (⊤ : WithTop Real) ≤ (μ : WithTop Real) := by
              have htop' := hle
              simp [h] at htop'
            have hmu : (μ : WithTop Real) = (⊤ : WithTop Real) := (top_le_iff).1 htop
            have hmu_ne : (μ : WithTop Real) ≠ (⊤ : WithTop Real) := WithTop.coe_ne_top
            exact (hmu_ne hmu).elim
        | coe m =>
            have hle' : (m : WithTop Real) ≤ (μ : WithTop Real) := by
              simpa [h] using hle
            have hle_real : m ≤ μ := by
              simpa using (WithTop.coe_le_coe.mp hle')
            have hleE' : (m : EReal) ≤ (μ : EReal) := (EReal.coe_le_coe_iff).2 hle_real
            simpa [h] using hleE'
      exact (mem_epigraph_univ_iff
          (f := fun xStar =>
            match infMuInCone (n := n) Sstar xStar with
            | (μ : Real) => (μ : EReal)
            | ⊤ => (⊤ : EReal))
          (x := x) (μ := μ)).2 hleE

/-- The closure of `coneK` lies in the epigraph of the support function of `C`. -/
lemma closure_coneK_subset_epigraph_supportFunctionEReal {n : Nat}
    (Sstar : Set ((Fin n → Real) × Real))
    (hC_ne : intersectionOfHalfspaces (n := n) Sstar ≠ (∅ : Set (Fin n → Real))) :
    (let C : Set (Fin n → Real) := intersectionOfHalfspaces (n := n) Sstar
    closure (coneK (n := n) Sstar) ⊆
      epigraph (S := (Set.univ : Set (Fin n → Real))) (supportFunctionEReal C)) := by
  classical
  intro C
  have hsubset :
      coneK (n := n) Sstar ⊆
        epigraph (S := (Set.univ : Set (Fin n → Real))) (supportFunctionEReal C) := by
    simpa [C] using
      (coneK_subset_epigraph_supportFunctionEReal (n := n) Sstar hC_ne)
  have hCne : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hC_ne
  have hCconv : Convex ℝ C := convex_intersectionOfHalfspaces (n := n) Sstar
  have hclosed : ClosedConvexFunction (supportFunctionEReal C) :=
    (section13_supportFunctionEReal_closedProperConvex_posHom (n := n) (C := C) hCne hCconv).1
  have hclosed_epi :
      IsClosed (epigraph (S := (Set.univ : Set (Fin n → Real))) (supportFunctionEReal C)) := by
    exact isClosed_epigraph_univ_of_lowerSemicontinuous (hf := hclosed.2)
  exact closure_minimal hsubset hclosed_epi

end Section17
end Chap04
