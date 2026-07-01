/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Shu Miao, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section04_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section08_part2

noncomputable section
open scoped RealInnerProductSpace
open scoped Pointwise Topology
open Metric

section Chap02
section Section08

/-- If every `x ∈ C` satisfies `x + y ∈ C`, then the translation of `C` by `y` stays in `C`. -/
lemma image_add_subset_of_add_mem {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    {y : EuclideanSpace Real (Fin n)} (h : ∀ x ∈ C, x + y ∈ C) :
    Set.image (fun x => x + y) C ⊆ C := by
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  exact h x hx

/-- If every `x ∈ C` satisfies `x - y ∈ C`, then `C` is contained in its translation by `y`. -/
lemma subset_image_add_of_sub_mem {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    {y : EuclideanSpace Real (Fin n)} (h : ∀ x ∈ C, x + (-y) ∈ C) :
    C ⊆ Set.image (fun x => x + y) C := by
  intro x hx
  refine ⟨x + (-y), h x hx, ?_⟩
  simp [add_assoc]

/-- If `C` is invariant under translation by `y`, then `C` is closed under adding `y` and `-y`. -/
lemma add_mem_of_image_eq {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    {y : EuclideanSpace Real (Fin n)}
    (hEq : Set.image (fun x => x + y) C = C) :
    (∀ x ∈ C, x + y ∈ C) ∧ (∀ x ∈ C, x + (-y) ∈ C) := by
  constructor
  · intro x hx
    have hx' : x + y ∈ Set.image (fun x => x + y) C := ⟨x, hx, rfl⟩
    simpa [hEq] using hx'
  · intro x hx
    have hx' : x ∈ Set.image (fun x => x + y) C := by
      simpa [hEq] using hx
    rcases hx' with ⟨x0, hx0, hx0eq⟩
    have : x + (-y) = x0 := by
      calc
        x + (-y) = (x0 + y) + (-y) := by simp [hx0eq.symm]
        _ = x0 := by simp [add_assoc]
    simpa [this] using hx0

/-- Theorem 8.4.5. For any non-empty convex set `C`, the lineality space
`lin(C) = (-0^+ C) ∩ 0^+ C` equals `{ y ∈ ℝ^n | C + y = C }`. -/
theorem linealitySpace_eq_translation {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hCne : C.Nonempty) (hCconv : Convex Real C) :
    (-Set.recessionCone C) ∩ Set.recessionCone C =
      { y : EuclideanSpace Real (Fin n) | Set.image (fun x => x + y) C = C } := by
  rcases hCne with ⟨x0, hx0⟩
  ext y
  constructor
  · intro hy
    rcases hy with ⟨hyneg, hypos⟩
    have hypos' : ∀ x ∈ C, x + y ∈ C := by
      simpa [recessionCone_eq_add_mem (C := C) hCconv] using hypos
    have hyneg' : ∀ x ∈ C, x + (-y) ∈ C := by
      have hyneg_mem : -y ∈ Set.recessionCone C := by
        simpa using hyneg
      simpa [recessionCone_eq_add_mem (C := C) hCconv] using hyneg_mem
    apply Set.Subset.antisymm
    · exact image_add_subset_of_add_mem (C := C) (y := y) hypos'
    · exact subset_image_add_of_sub_mem (C := C) (y := y) hyneg'
  · intro hy
    have hy' :
        (∀ x ∈ C, x + y ∈ C) ∧ (∀ x ∈ C, x + (-y) ∈ C) :=
      add_mem_of_image_eq (C := C) (y := y) hy
    rcases hy' with ⟨hypos, hyneg⟩
    have hypos_mem : y ∈ Set.recessionCone C := by
      simpa [recessionCone_eq_add_mem (C := C) hCconv] using hypos
    have hyneg_mem : -y ∈ Set.recessionCone C := by
      simpa [recessionCone_eq_add_mem (C := C) hCconv] using hyneg
    have hyneg_mem' : y ∈ -Set.recessionCone C := by
      simpa using hyneg_mem
    exact ⟨hyneg_mem', hypos_mem⟩

/-- Definiton 8.4.6. Let `C` be a non-empty convex set with lineality space
`L = lin(C)`. The rank of `C` is defined by `rank(C) = dim(C) - dim(L)`. -/
noncomputable def Set.rank {n : Nat} (C : Set (EuclideanSpace Real (Fin n))) : Nat :=
  Module.finrank Real (affineSpan Real C).direction -
    Module.finrank Real (Submodule.span Real ((-Set.recessionCone C) ∩ Set.recessionCone C))

/-- Proper convexity implies the domain is nonempty. -/
lemma properConvexFunctionOn_nonempty {n : Nat} {C : Set (Fin n → Real)}
    {f : (Fin n → Real) → EReal} (hf : ProperConvexFunctionOn C f) : C.Nonempty := by
  rcases hf.2.1 with ⟨p, hp⟩
  exact ⟨p.1, hp.1⟩

/-- The difference-quotient set used in the recession formula is nonempty. -/
lemma diffQuotient_set_nonempty {n : Nat} {C : Set (Fin n → Real)}
    {f : (Fin n → Real) → Real}
    (hf : ProperConvexFunctionOn C (fun x => (f x : EReal))) :
    ∀ y : Fin n → Real,
      ( { r : EReal | ∃ x ∈ C, r = ((f (x + y) - f x : Real) : EReal) } ).Nonempty := by
  intro y
  rcases properConvexFunctionOn_nonempty (f := fun x => (f x : EReal)) hf with ⟨x, hx⟩
  exact ⟨((f (x + y) - f x : Real) : EReal), x, hx, rfl⟩

/-- The recession formula forces `f0_plus 0 = 0`. -/
lemma recessionFunction_zero {n : Nat} {C : Set (Fin n → Real)}
    {f : (Fin n → Real) → Real} {f0_plus : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn C (fun x => (f x : EReal)))
    (hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus y =
          sSup { r : EReal | ∃ x ∈ C, r = ((f (x + y) - f x : Real) : EReal) }) :
    f0_plus (0 : Fin n → Real) = (0 : EReal) := by
  rcases properConvexFunctionOn_nonempty (f := fun x => (f x : EReal)) hf with ⟨x, hx⟩
  have hset :
      { r : EReal | ∃ x' ∈ C, r = ((f (x' + (0 : Fin n → Real)) - f x' : Real) : EReal) } =
        { (0 : EReal) } := by
    ext r
    constructor
    · intro hr
      rcases hr with ⟨x', hx', rfl⟩
      simp
    · intro hr
      rcases hr with rfl
      refine ⟨x, hx, ?_⟩
      simp
  calc
    f0_plus (0 : Fin n → Real)
        = sSup { r : EReal |
            ∃ x' ∈ C, r = ((f (x' + (0 : Fin n → Real)) - f x' : Real) : EReal) } := hf0_plus _
    _ = sSup ({(0 : EReal)} : Set EReal) := by
        rw [hset]
    _ = (0 : EReal) := by simp

/-- The recession formula prevents `f0_plus` from taking the value `⊥`. -/
lemma recessionFunction_ne_bot {n : Nat} {C : Set (Fin n → Real)}
    {f : (Fin n → Real) → Real} {f0_plus : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn C (fun x => (f x : EReal)))
    (hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus y =
          sSup { r : EReal | ∃ x ∈ C, r = ((f (x + y) - f x : Real) : EReal) }) :
    ∀ y : Fin n → Real, f0_plus y ≠ (⊥ : EReal) := by
  intro y hbot
  rcases diffQuotient_set_nonempty (C := C) (f := f) hf y with ⟨r, hr⟩
  rcases hr with ⟨x, hx, rfl⟩
  have hrle :
      ((f (x + y) - f x : Real) : EReal) ≤
        sSup { r : EReal | ∃ x ∈ C, r = ((f (x + y) - f x : Real) : EReal) } :=
    le_sSup ⟨x, hx, rfl⟩
  have hsup_bot :
      sSup { r : EReal | ∃ x ∈ C, r = ((f (x + y) - f x : Real) : EReal) } =
        (⊥ : EReal) := by
    simpa [hf0_plus y] using hbot
  have hrle' :
      ((f (x + y) - f x : Real) : EReal) ≤ (⊥ : EReal) := by
    calc
      ((f (x + y) - f x : Real) : EReal) ≤
          sSup { r : EReal | ∃ x ∈ C, r = ((f (x + y) - f x : Real) : EReal) } := hrle
      _ = (⊥ : EReal) := hsup_bot
  have hbot' :
      ((f (x + y) - f x : Real) : EReal) = (⊥ : EReal) :=
    (le_bot_iff).1 hrle'
  have hne : ((f (x + y) - f x : Real) : EReal) ≠ (⊥ : EReal) := by
    simpa using (EReal.coe_ne_bot (f (x + y) - f x))
  exact hne hbot'

/-- The recession formula gives a pointwise inequality characterization. -/
lemma recessionFunction_le_iff {n : Nat} {C : Set (Fin n → Real)}
    {f : (Fin n → Real) → Real} {f0_plus : (Fin n → Real) → EReal}
    (hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus y =
          sSup { r : EReal | ∃ x ∈ C, r = ((f (x + y) - f x : Real) : EReal) }) :
    ∀ y : Fin n → Real, ∀ v : Real,
      f0_plus y ≤ (v : EReal) ↔
        ∀ x ∈ C, ((f (x + y) - f x : Real) : EReal) ≤ (v : EReal) := by
  intro y v
  constructor
  · intro hle x hx
    have hle' :
        ((f (x + y) - f x : Real) : EReal) ≤
          sSup { r : EReal | ∃ x ∈ C, r = ((f (x + y) - f x : Real) : EReal) } :=
      le_sSup ⟨x, hx, rfl⟩
    have hle'' :
        sSup { r : EReal | ∃ x ∈ C, r = ((f (x + y) - f x : Real) : EReal) } ≤
          (v : EReal) := by
      simpa [hf0_plus y] using hle
    exact le_trans hle' hle''
  · intro h
    have hsup :
        sSup { r : EReal | ∃ x ∈ C, r = ((f (x + y) - f x : Real) : EReal) } ≤
          (v : EReal) := by
      refine sSup_le ?_
      intro r hr
      rcases hr with ⟨x, hx, rfl⟩
      exact h x hx
    simpa [hf0_plus y] using hsup

/-- The epigraph of the recession function is nonempty, witnessed at the origin. -/
lemma recessionFunction_epigraph_nonempty {n : Nat} {C : Set (Fin n → Real)}
    {f : (Fin n → Real) → Real} {f0_plus : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn C (fun x => (f x : EReal)))
    (hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus y =
          sSup { r : EReal | ∃ x ∈ C, r = ((f (x + y) - f x : Real) : EReal) }) :
    Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) f0_plus) := by
  refine ⟨((0 : Fin n → Real), (0 : Real)), ?_⟩
  have hzero :
      f0_plus (0 : Fin n → Real) = (0 : EReal) :=
    recessionFunction_zero (C := C) (f := f) (f0_plus := f0_plus) hf hf0_plus
  have hle : f0_plus (0 : Fin n → Real) ≤ (0 : EReal) := by
    simp [hzero]
  exact (mem_epigraph_univ_iff).2 hle

/-- Proper convexity on the whole space gives real-valued convexity on `Set.univ`. -/
lemma convexOn_real_of_convexFunctionOn_ereal_univ {n : Nat} {C : Set (Fin n → Real)}
    {f : (Fin n → Real) → Real} (hC : C = Set.univ)
    (hf : ProperConvexFunctionOn C (fun x => (f x : EReal))) :
    ConvexOn ℝ (Set.univ : Set (Fin n → Real)) f := by
  classical
  have hconvE : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fun x => (f x : EReal)) := by
    simpa [hC] using hf.1
  have hnotbot :
      ∀ x ∈ (Set.univ : Set (Fin n → Real)), (fun x => (f x : EReal)) x ≠ (⊥ : EReal) := by
    intro x hx
    have hx' : x ∈ C := by simp [hC]
    exact hf.2.2 x hx'
  have hseg :
      ∀ x ∈ (Set.univ : Set (Fin n → Real)), ∀ y ∈ (Set.univ : Set (Fin n → Real)),
        ∀ t : Real, 0 < t → t < 1 →
          (f ((1 - t) • x + t • y) : EReal) ≤
            ((1 - t : Real) : EReal) * f x + ((t : Real) : EReal) * f y := by
    have hconv_seg :=
      (convexFunctionOn_iff_segment_inequality
        (C := (Set.univ : Set (Fin n → Real)))
        (f := fun x => (f x : EReal))
        (hC := convex_univ) (hnotbot := hnotbot)).1 hconvE
    intro x hx y hy t ht0 ht1
    simpa using (hconv_seg x hx y hy t ht0 ht1)
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  by_cases hb0 : b = 0
  · subst hb0
    have ha' : a = 1 := by linarith
    subst ha'
    simp
  by_cases hb1 : b = 1
  · subst hb1
    have ha' : a = 0 := by linarith
    subst ha'
    simp
  have hb0' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hb1' : b < 1 := by
    have hb_le : b ≤ 1 := by linarith
    exact lt_of_le_of_ne hb_le hb1
  have hseg' := hseg x (by simp) y (by simp) b hb0' hb1'
  have hseg'' :
      (f ((1 - b) • x + b • y) : EReal) ≤
        ((1 - b) * f x + b * f y : Real) := by
    have hrhs :
        ((1 - b : Real) : EReal) * f x + ((b : Real) : EReal) * f y =
          ((1 - b) * f x + b * f y : Real) := by
      simp [EReal.coe_mul, EReal.coe_add, add_comm]
    simpa [hrhs] using hseg'
  have hreal :
      f ((1 - b) • x + b • y) ≤ (1 - b) * f x + b * f y :=
    (EReal.coe_le_coe_iff).1 hseg''
  have ha' : a = 1 - b := by linarith
  subst ha'
  simpa using hreal

/-- A convex real function with bounded unit increments along `y` has bounded increments at all
positive scales. -/
lemma recessionFunction_ray_bound_real {n : Nat} {C : Set (Fin n → Real)}
    {f : (Fin n → Real) → Real} (hC : C = Set.univ)
    (hf : ProperConvexFunctionOn C (fun x => (f x : EReal))) :
    ∀ {y : Fin n → Real} {v : Real},
      (∀ x, f (x + y) - f x ≤ v) →
      ∀ t > 0, ∀ x, f (x + t • y) - f x ≤ t * v := by
  classical
  intro y v hstep t ht x
  have hstep_nat : ∀ n : Nat, ∀ x, f (x + (n : Real) • y) - f x ≤ (n : Real) * v := by
    intro n
    induction n with
    | zero =>
        intro x
        simp
    | succ n hn =>
        intro x
        have hstep' : f (x + (n : Real) • y + y) - f (x + (n : Real) • y) ≤ v := by
          simpa [add_assoc] using hstep (x + (n : Real) • y)
        have hxy : x + (n : Real) • y + y = x + ((n + 1 : Nat) : Real) • y := by
          ext i
          simp [Nat.cast_add, Nat.cast_one, add_assoc, add_mul]
        have hsum :
            f (x + ((n + 1 : Nat) : Real) • y) - f x =
              (f (x + (n : Real) • y) - f x) +
                (f (x + ((n + 1 : Nat) : Real) • y) - f (x + (n : Real) • y)) := by
          ring
        calc
          f (x + ((n + 1 : Nat) : Real) • y) - f x
              = (f (x + (n : Real) • y) - f x) +
                  (f (x + ((n + 1 : Nat) : Real) • y) - f (x + (n : Real) • y)) := hsum
          _ ≤ (n : Real) * v + v := by
            have hn' := hn x
            have hstep'' :
                f (x + ((n + 1 : Nat) : Real) • y) - f (x + (n : Real) • y) ≤ v := by
              simpa [hxy] using hstep'
            exact add_le_add hn' hstep''
          _ = ((n : Real) + 1) * v := by ring
          _ = ((n + 1 : Nat) : Real) * v := by
            simp [Nat.cast_add, Nat.cast_one]
  obtain ⟨m, hm⟩ := exists_nat_ge t
  have hm0 : 0 < (m : Real) := lt_of_lt_of_le ht hm
  have hs0 : 0 ≤ t / (m : Real) := by
    have hm0' : 0 ≤ (m : Real) := le_of_lt hm0
    exact div_nonneg (le_of_lt ht) hm0'
  have hs1 : t / (m : Real) ≤ 1 := by
    have hm0' : 0 < (m : Real) := hm0
    have : t ≤ (1 : Real) * (m : Real) := by simpa [one_mul] using hm
    exact (div_le_iff₀ hm0').2 this
  have hconv :
      ConvexOn ℝ (Set.univ : Set (Fin n → Real)) f :=
    convexOn_real_of_convexFunctionOn_ereal_univ (C := C) (f := f) hC hf
  set s : Real := t / (m : Real) with hs
  have hs0' : 0 ≤ s := by simpa [hs] using hs0
  have hs1' : s ≤ 1 := by simpa [hs] using hs1
  have hconvineq :
      f ((1 - s) • x + s • (x + (m : Real) • y)) ≤
        (1 - s) * f x + s * f (x + (m : Real) • y) := by
    have hconv' :=
      hconv.2 (x := x) (y := x + (m : Real) • y) (by simp) (by simp)
    exact hconv' (a := 1 - s) (b := s) (by linarith [hs1']) hs0' (by ring)
  have hm0' : (m : Real) ≠ 0 := ne_of_gt hm0
  have hsn : s * (m : Real) = t := by
    calc
      s * (m : Real) = (t / (m : Real)) * (m : Real) := by simp [hs]
      _ = t := by field_simp [hm0']
  have hlin : (1 - s) • x + (s • x + s • (m : Real) • y) = x + t • y := by
    ext i
    simp [hsn, smul_smul, add_comm, add_assoc, sub_eq_add_neg]
    ring
  have hineq :
      f (x + t • y) ≤ (1 - s) * f x + s * f (x + (m : Real) • y) := by
    simpa [hlin] using hconvineq
  have hineq' :
      f (x + t • y) ≤ f x + s * (f (x + (m : Real) • y) - f x) := by
    calc
      f (x + t • y) ≤ (1 - s) * f x + s * f (x + (m : Real) • y) := hineq
      _ = f x + s * (f (x + (m : Real) • y) - f x) := by ring
  have hdiff :
      f (x + t • y) - f x ≤ s * (f (x + (m : Real) • y) - f x) := by
    exact (sub_le_iff_le_add).2 (by simpa [add_comm, add_left_comm, add_assoc] using hineq')
  have hbound_n : f (x + (m : Real) • y) - f x ≤ (m : Real) * v := hstep_nat m x
  have hdiff' : f (x + t • y) - f x ≤ s * ((m : Real) * v) := by
    have hmul := mul_le_mul_of_nonneg_left hbound_n hs0'
    exact le_trans hdiff hmul
  calc
    f (x + t • y) - f x ≤ s * ((m : Real) * v) := hdiff'
    _ = (s * (m : Real)) * v := by ring
    _ = t * v := by simp [hsn]

/-- The ray bound rewritten in `EReal` form for the recession function. -/
lemma recessionFunction_ray_bound {n : Nat} {C : Set (Fin n → Real)}
    {f : (Fin n → Real) → Real} (hC : C = Set.univ)
    (hf : ProperConvexFunctionOn C (fun x => (f x : EReal))) :
    ∀ {y : Fin n → Real} {v : Real},
      (∀ x, ((f (x + y) - f x : Real) : EReal) ≤ (v : EReal)) →
      ∀ t > 0, ∀ x,
        ((f (x + t • y) - f x : Real) : EReal) ≤ ((t * v : Real) : EReal) := by
  intro y v hstep t ht x
  have hstep' : ∀ x, f (x + y) - f x ≤ v := by
    intro x
    have hx := hstep x
    exact (EReal.coe_le_coe_iff).1 (by simpa using hx)
  have hbound :
      f (x + t • y) - f x ≤ t * v :=
    recessionFunction_ray_bound_real (C := C) (f := f) hC hf hstep' t ht x
  exact (EReal.coe_le_coe_iff).2 (by simpa using hbound)

/-- A pointwise bound on `f0_plus` is equivalent to bounds on all ray difference quotients. -/
lemma recessionFunction_le_iff_ray {n : Nat} {C : Set (Fin n → Real)}
    {f : (Fin n → Real) → Real} {f0_plus : (Fin n → Real) → EReal}
    (hC : C = Set.univ)
    (hf : ProperConvexFunctionOn C (fun x => (f x : EReal)))
    (hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus y =
          sSup { r : EReal | ∃ x ∈ C, r = ((f (x + y) - f x : Real) : EReal) }) :
    ∀ y : Fin n → Real, ∀ v : Real,
      f0_plus y ≤ (v : EReal) ↔
        ∀ x : Fin n → Real, ∀ t : Real, 0 < t →
          ((f (x + t • y) - f x) / t : Real) ≤ v := by
  intro y v
  constructor
  · intro hle x t ht
    have hstep :
        ∀ x, ((f (x + y) - f x : Real) : EReal) ≤ (v : EReal) := by
      intro x
      have hx : x ∈ C := by simp [hC]
      exact
        (recessionFunction_le_iff (C := C) (f := f) (f0_plus := f0_plus) hf0_plus y v).1 hle x
          hx
    have hbound :
        ((f (x + t • y) - f x : Real) : EReal) ≤ ((t * v : Real) : EReal) :=
      recessionFunction_ray_bound (C := C) (f := f) hC hf (y := y) (v := v) hstep t ht x
    have hbound_real : f (x + t • y) - f x ≤ t * v := by
      exact (EReal.coe_le_coe_iff).1 (by simpa using hbound)
    have hbound_real' : f (x + t • y) - f x ≤ v * t := by
      simpa [mul_comm] using hbound_real
    exact (div_le_iff₀ ht).2 hbound_real'
  · intro h
    have hstep :
        ∀ x ∈ C, ((f (x + y) - f x : Real) : EReal) ≤ (v : EReal) := by
      intro x hx
      have h' :
          ((f (x + (1 : Real) • y) - f x) / (1 : Real) : Real) ≤ v :=
        h x 1 (by exact zero_lt_one)
      have h'' : f (x + y) - f x ≤ v := by
        simpa using h'
      exact (EReal.coe_le_coe_iff).2 h''
    exact
      (recessionFunction_le_iff (C := C) (f := f) (f0_plus := f0_plus) hf0_plus y v).2 hstep

/-- Subadditivity of the recession formula when the domain is the whole space. -/
lemma recessionFunction_subadditive_univ {n : Nat} {C : Set (Fin n → Real)}
    {f : (Fin n → Real) → Real} {f0_plus : (Fin n → Real) → EReal}
    (hC : C = Set.univ)
    (hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus y =
          sSup { r : EReal | ∃ x ∈ C, r = ((f (x + y) - f x : Real) : EReal) }) :
    ∀ y1 y2 : Fin n → Real, f0_plus (y1 + y2) ≤ f0_plus y1 + f0_plus y2 := by
  classical
  intro y1 y2
  have hle :
      sSup { r : EReal | ∃ x ∈ C, r = ((f (x + y1 + y2) - f x : Real) : EReal) } ≤
        f0_plus y1 + f0_plus y2 := by
    refine sSup_le ?_
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    have hx' : x + y1 ∈ C := by
      simp [hC]
    have h1 :
        ((f (x + y1) - f x : Real) : EReal) ≤ f0_plus y1 := by
      have hmem :
          ((f (x + y1) - f x : Real) : EReal) ∈
            { r : EReal | ∃ x ∈ C, r = ((f (x + y1) - f x : Real) : EReal) } := by
        exact ⟨x, hx, rfl⟩
      have hle :=
        le_sSup hmem
      simpa [hf0_plus] using hle
    have h2 :
        ((f (x + y1 + y2) - f (x + y1) : Real) : EReal) ≤ f0_plus y2 := by
      have h2' :
          ((f ((x + y1) + y2) - f (x + y1) : Real) : EReal) ≤ f0_plus y2 := by
        have hmem :
            ((f ((x + y1) + y2) - f (x + y1) : Real) : EReal) ∈
              { r : EReal | ∃ x ∈ C, r = ((f (x + y2) - f x : Real) : EReal) } := by
          exact ⟨x + y1, hx', rfl⟩
        have hle := le_sSup hmem
        simpa [hf0_plus] using hle
      simpa [add_assoc] using h2'
    have hsum_real :
        f (x + y1 + y2) - f x =
          (f (x + y1) - f x) + (f (x + y1 + y2) - f (x + y1)) := by
      ring
    have hsum :
        ((f (x + y1 + y2) - f x : Real) : EReal) =
          ((f (x + y1) - f x : Real) : EReal) +
            ((f (x + y1 + y2) - f (x + y1) : Real) : EReal) := by
      rw [hsum_real, EReal.coe_add]
    calc
      ((f (x + y1 + y2) - f x : Real) : EReal)
          = ((f (x + y1) - f x : Real) : EReal) +
              ((f (x + y1 + y2) - f (x + y1) : Real) : EReal) := hsum
      _ ≤ f0_plus y1 + f0_plus y2 := add_le_add h1 h2
  simpa [hf0_plus, add_assoc] using hle

/-- Convexity of the recession function on `Set.univ` from subadditivity and pos. homogeneity. -/
lemma recessionFunction_convex_univ {n : Nat} {C : Set (Fin n → Real)}
    {f : (Fin n → Real) → Real} {f0_plus : (Fin n → Real) → EReal}
    (hC : C = Set.univ)
    (hf : ProperConvexFunctionOn C (fun x => (f x : EReal)))
    (hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus y =
          sSup { r : EReal | ∃ x ∈ C, r = ((f (x + y) - f x : Real) : EReal) })
    (hpos : PositivelyHomogeneous f0_plus) :
    ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f0_plus := by
  have hsub :
      ∀ y1 y2 : Fin n → Real, f0_plus (y1 + y2) ≤ f0_plus y1 + f0_plus y2 :=
    recessionFunction_subadditive_univ (C := C) (f := f) (f0_plus := f0_plus) hC hf0_plus
  have hnotbot :
      ∀ y : Fin n → Real, f0_plus y ≠ (⊥ : EReal) :=
    recessionFunction_ne_bot (C := C) (f := f) (f0_plus := f0_plus) hf hf0_plus
  have hconv : ConvexFunction f0_plus :=
    convex_of_subadditive_posHom (hpos := hpos) hsub hnotbot
  simpa [ConvexFunction] using hconv

/-- Along a fixed ray, the difference quotient is monotone in the step length. -/
lemma differenceQuotient_monotone {n : Nat} {C : Set (Fin n → Real)}
    {f : (Fin n → Real) → Real} (hC : C = Set.univ)
    (hf : ProperConvexFunctionOn C (fun x => (f x : EReal))) :
    ∀ x y : Fin n → Real,
      Monotone (fun t : {t : ℝ // 0 < t} => (f (x + (t : ℝ) • y) - f x) / (t : ℝ)) := by
  classical
  intro x y s t hst
  let L : ℝ →ᵃ[ℝ] (Fin n → Real) := AffineMap.lineMap (k := ℝ) x (x + y)
  have hconv :
      ConvexOn ℝ (Set.univ : Set (Fin n → Real)) f :=
    convexOn_real_of_convexFunctionOn_ereal_univ (C := C) (f := f) hC hf
  have hconv_comp :
      ConvexOn ℝ (Set.univ : Set ℝ)
        (fun t => f (L t)) := by
    simpa [L] using (hconv.comp_affineMap (AffineMap.lineMap (k := ℝ) x (x + y)))
  have hlineMap :
      ∀ t : ℝ, L t = x + t • y := by
    intro t
    simpa [L, vadd_eq_add, add_comm, add_left_comm, add_assoc] using
      (AffineMap.lineMap_vadd_apply (k := ℝ) (p := x) (v := y) (c := t))
  have hx0 : L 0 = x := by
    simp [L]
  have hsec :
      (f (L (s : ℝ)) - f (L 0)) /
          ((s : ℝ) - 0) ≤
        (f (L (t : ℝ)) - f (L 0)) /
          ((t : ℝ) - 0) :=
    hconv_comp.secant_mono (a := 0) (x := (s : ℝ)) (y := (t : ℝ)) (by simp) (by simp) (by simp)
      (ne_of_gt s.2) (ne_of_gt t.2) (by simpa using hst)
  simpa [hlineMap, hx0] using hsec

/-- Rewrite the recession formula as an `iSup` over base points. -/
lemma recessionFunction_iSup_formula {n : Nat} {C : Set (Fin n → Real)}
    {f : (Fin n → Real) → Real} {f0_plus : (Fin n → Real) → EReal}
    (hC : C = Set.univ)
    (hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus y =
          sSup { r : EReal | ∃ x ∈ C, r = ((f (x + y) - f x : Real) : EReal) }) :
    ∀ y : Fin n → Real,
      f0_plus y =
        ⨆ x : Fin n → Real, ((f (x + y) - f x : Real) : EReal) := by
  intro y
  have hset :
      { r : EReal | ∃ x ∈ C, r = ((f (x + y) - f x : Real) : EReal) } =
        Set.range (fun x : Fin n → Real => ((f (x + y) - f x : Real) : EReal)) := by
    ext r
    constructor
    · intro hr
      rcases hr with ⟨x, hx, rfl⟩
      exact ⟨x, rfl⟩
    · intro hr
      rcases hr with ⟨x, rfl⟩
      exact ⟨x, by simp [hC], rfl⟩
  calc
    f0_plus y =
        sSup { r : EReal | ∃ x ∈ C, r = ((f (x + y) - f x : Real) : EReal) } := hf0_plus _
    _ = sSup (Set.range (fun x : Fin n → Real => ((f (x + y) - f x : Real) : EReal))) := by
        rw [hset]
    _ = ⨆ x : Fin n → Real, ((f (x + y) - f x : Real) : EReal) := by
        simp [sSup_range]

/-- Closedness of `f` implies lower semicontinuity of the recession function. -/
lemma recessionFunction_lsc_of_closed {n : Nat} {C : Set (Fin n → Real)}
    {f : (Fin n → Real) → Real} {f0_plus : (Fin n → Real) → EReal}
    (hC : C = Set.univ)
    (hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus y =
          sSup { r : EReal | ∃ x ∈ C, r = ((f (x + y) - f x : Real) : EReal) })
    (hclosed : ClosedConvexFunction (fun x => (f x : EReal))) :
    LowerSemicontinuous f0_plus := by
  have hf0_plus_iSup :=
    recessionFunction_iSup_formula (C := C) (f := f) (f0_plus := f0_plus) hC hf0_plus
  have hls_f : LowerSemicontinuous (fun x => (f x : EReal)) := hclosed.2
  have hclosed_sub :
      ∀ α : Real, IsClosed {x : Fin n → Real | (f x : EReal) ≤ (α : EReal)} :=
    (lowerSemicontinuous_iff_closed_sublevel (f := fun x => (f x : EReal))).1 hls_f
  have hls_diff :
      ∀ x : Fin n → Real,
        LowerSemicontinuous (fun y : Fin n → Real => ((f (x + y) - f x : Real) : EReal)) := by
    intro x
    refine
      (lowerSemicontinuous_iff_closed_sublevel
        (f := fun y => ((f (x + y) - f x : Real) : EReal))).2 ?_
    intro α
    have hset :
        {y : Fin n → Real | ((f (x + y) - f x : Real) : EReal) ≤ (α : EReal)} =
          {y : Fin n → Real | (f (x + y) : EReal) ≤ ((α + f x : Real) : EReal)} := by
      ext y
      constructor
      · intro hy
        have hy' : f (x + y) - f x ≤ α :=
          (EReal.coe_le_coe_iff).1 (by simpa using hy)
        have : f (x + y) ≤ α + f x := by linarith
        exact (EReal.coe_le_coe_iff).2 this
      · intro hy
        have hy' : f (x + y) ≤ α + f x :=
          (EReal.coe_le_coe_iff).1 (by simpa using hy)
        have : f (x + y) - f x ≤ α := by linarith
        exact (EReal.coe_le_coe_iff).2 this
    have hcont : Continuous (fun y : Fin n → Real => x + y) := by
      simpa using (continuous_const.add continuous_id)
    have hclosed_pre :
        IsClosed {y : Fin n → Real | (f (x + y) : EReal) ≤ ((α + f x : Real) : EReal)} := by
      have hclosed_sub' :
          IsClosed {z : Fin n → Real | (f z : EReal) ≤ ((α + f x : Real) : EReal)} :=
        hclosed_sub (α + f x)
      simpa [Set.preimage] using hclosed_sub'.preimage hcont
    exact hset ▸ hclosed_pre
  have hls :
      LowerSemicontinuous
        (fun y : Fin n → Real =>
          ⨆ x : Fin n → Real, ((f (x + y) - f x : Real) : EReal)) :=
    lowerSemicontinuous_iSup hls_diff
  have hf0_plus_eq :
      f0_plus = fun y : Fin n → Real => ⨆ x : Fin n → Real, ((f (x + y) - f x : Real) : EReal) := by
    funext y
    exact hf0_plus_iSup y
  simpa [hf0_plus_eq] using hls

/-- The embedded epigraph is closed when `f` is lower semicontinuous. -/
lemma closed_embedded_epigraph {n : Nat} {f : (Fin n → Real) → EReal}
    (hls : LowerSemicontinuous f) :
    let C : Set (EuclideanSpace Real (Fin (n + 1))) :=
      (appendAffineEquiv n 1) ''
        ((fun p : (Fin n → Real) × Real =>
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => p.2))) ''
          epigraph (S := (Set.univ : Set (Fin n → Real))) f)
    IsClosed C := by
  classical
  dsimp
  have hclosed_sub :
      ∀ α : Real, IsClosed {x : Fin n → Real | f x ≤ (α : EReal)} :=
    (lowerSemicontinuous_iff_closed_sublevel (f := f)).1 hls
  have hclosed_epi :
      IsClosed (epigraph (Set.univ : Set (Fin n → Real)) f) :=
    closed_epigraph_of_closed_sublevel (f := f) hclosed_sub
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
  have hclosed_g :
      IsClosed (g '' epigraph (Set.univ : Set (Fin n → Real)) f) := by
    let hhome := g.toHomeomorphOfFiniteDimensional
    have hclosed' :
        IsClosed ((hhome : _ → _) '' epigraph (Set.univ : Set (Fin n → Real)) f) :=
      (hhome.isClosed_image (s := epigraph (Set.univ : Set (Fin n → Real)) f)).2 hclosed_epi
    simpa [hhome, AffineEquiv.coe_toHomeomorphOfFiniteDimensional] using hclosed'
  have hclosed_C :
      IsClosed ((appendAffineEquiv n 1) '' (g '' epigraph (Set.univ : Set (Fin n → Real)) f)) := by
    let hhome := (appendAffineEquiv n 1).toHomeomorphOfFiniteDimensional
    have hclosed' :
        IsClosed ((hhome : _ → _) '' (g '' epigraph (Set.univ : Set (Fin n → Real)) f)) :=
      (hhome.isClosed_image (s := g '' epigraph (Set.univ : Set (Fin n → Real)) f)).2 hclosed_g
    simpa [hhome, AffineEquiv.coe_toHomeomorphOfFiniteDimensional] using hclosed'
  simpa [hC_eq] using hclosed_C

/-- The embedded epigraph map sends affine rays to affine rays. -/
lemma embedded_epigraph_add_smul {n : Nat} :
    let eN : (Fin n → Real) ≃ᵃ[Real] EuclideanSpace Real (Fin n) :=
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm.toLinearEquiv.toAffineEquiv
    let e1 : Real ≃ᵃ[Real] EuclideanSpace Real (Fin 1) :=
      ((ContinuousLinearEquiv.funUnique (ι := Fin 1) (R := Real)
            (M := Real)).symm.toLinearEquiv.trans
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm.toLinearEquiv).toAffineEquiv
    let g : (Fin n → Real) × Real ≃ᵃ[Real]
        (EuclideanSpace Real (Fin n) × EuclideanSpace Real (Fin 1)) :=
      AffineEquiv.prodCongr eN e1
    let embed : (Fin n → Real) × Real → EuclideanSpace Real (Fin (n + 1)) :=
      fun p => appendAffineEquiv n 1 (g p)
    let dir : (Fin n → Real) × Real → EuclideanSpace Real (Fin (n + 1)) :=
      fun q => (appendAffineEquiv n 1).linear (g.linear q)
    ∀ p q : (Fin n → Real) × Real, ∀ t : Real,
      embed (p + t • q) = embed p + t • dir q := by
  classical
  intro eN e1 g embed dir p q t
  let A : (Fin n → Real) × Real →ᵃ[Real] EuclideanSpace Real (Fin (n + 1)) :=
    (appendAffineEquiv n 1).toAffineMap.comp g
  have hA : embed = (A : (Fin n → Real) × Real → EuclideanSpace Real (Fin (n + 1))) := rfl
  have hdir : dir = fun q => A.linear q := rfl
  have hmap :
      A (p + t • q) = A.linear (t • q) + A p := by
    simpa [vadd_eq_add, add_comm, add_left_comm, add_assoc] using (A.map_vadd p (t • q))
  calc
    embed (p + t • q) = A (p + t • q) := rfl
    _ = A.linear (t • q) + A p := hmap
    _ = t • A.linear q + A p := by
      simp [map_smul]
    _ = A p + t • A.linear q := by
      exact add_comm _ _
    _ = embed p + t • dir q := by
      rw [hA, hdir]

/-- A ray bound at one base point extends to all base points for closed convex `f`. -/
lemma ray_bound_extend_closed {n : Nat} {f : (Fin n → Real) → Real}
    {x0 y : Fin n → Real} {v : Real}
    (hclosed : ClosedConvexFunction (fun x => (f x : EReal)))
    (hbound : ∀ t > 0, ((f (x0 + t • y) - f x0) / t : Real) ≤ v) :
    ∀ x : Fin n → Real, ∀ t : Real, 0 < t →
      ((f (x + t • y) - f x) / t : Real) ≤ v := by
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
  let Cemb : Set (EuclideanSpace Real (Fin (n + 1))) :=
    (appendAffineEquiv n 1) ''
      (g '' epigraph (Set.univ : Set (Fin n → Real)) (fun x => (f x : EReal)))
  have hdir_eq :
      ∀ p q : (Fin n → Real) × Real, ∀ t : Real,
        embed (p + t • q) = embed p + t • dir q := by
    intro p q t
    simpa [embed, dir, g, eN, e1] using
      (embedded_epigraph_add_smul (n := n) (p := p) (q := q) (t := t))
  have hCemb_closed : IsClosed Cemb := by
    simpa [Cemb, g, eN, e1] using
      (closed_embedded_epigraph (n := n) (f := fun x => (f x : EReal)) hclosed.2)
  have hCemb_convex : Convex ℝ Cemb := by
    have hconv : ConvexFunction (fun x => (f x : EReal)) := hclosed.1
    simpa [Cemb, g, eN, e1] using
      (convex_embedded_epigraph (n := n) (f := fun x => (f x : EReal)) hconv)
  have hCemb_nonempty : Cemb.Nonempty := by
    refine ⟨embed (0, f 0), ?_⟩
    refine ⟨g (0, f 0), ?_, rfl⟩
    refine ⟨(0, f 0), ?_, rfl⟩
    exact (mem_epigraph_univ_iff).2 (by simp)
  have hhalf :
      ∀ t : Real, 0 ≤ t → embed (x0, f x0) + t • dir (y, v) ∈ Cemb := by
    intro t ht
    have hmem_epi :
        (x0 + t • y, f x0 + t * v) ∈
          epigraph (Set.univ : Set (Fin n → Real)) (fun x => (f x : EReal)) := by
      by_cases ht0 : t = 0
      · subst ht0
        simp [mem_epigraph_univ_iff]
      · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
        have hq : ((f (x0 + t • y) - f x0) / t : Real) ≤ v := hbound t htpos
        have hineq : f (x0 + t • y) ≤ f x0 + t * v := by
          have hq' : f (x0 + t • y) - f x0 ≤ v * t := (div_le_iff₀ htpos).1 hq
          linarith
        exact (mem_epigraph_univ_iff).2 ((EReal.coe_le_coe_iff).2 hineq)
    have hmem_Cemb : embed (x0 + t • y, f x0 + t * v) ∈ Cemb := by
      refine ⟨g (x0 + t • y, f x0 + t * v), ?_, rfl⟩
      exact ⟨(x0 + t • y, f x0 + t * v), hmem_epi, rfl⟩
    have hdir' := hdir_eq (p := (x0, f x0)) (q := (y, v)) (t := t)
    have hdir'' :
        embed (x0 + t • y, f x0 + t * v) = embed (x0, f x0) + t • dir (y, v) := by
      simpa using hdir'
    simpa [hdir''] using hmem_Cemb
  have hdir_mem :
      dir (y, v) ∈ Set.recessionCone Cemb :=
    halfline_mem_recessionCone (C := Cemb) hCemb_nonempty hCemb_closed hCemb_convex
      (x0 := embed (x0, f x0)) (y := dir (y, v)) hhalf
  intro x t ht
  have hx_mem : embed (x, f x) ∈ Cemb := by
    refine ⟨g (x, f x), ?_, rfl⟩
    refine ⟨(x, f x), ?_, rfl⟩
    exact (mem_epigraph_univ_iff).2 (by simp)
  have hmem := hdir_mem hx_mem (t := t) (by exact le_of_lt ht)
  have hdir' := hdir_eq (p := (x, f x)) (q := (y, v)) (t := t)
  have hmem' : embed (x + t • y, f x + t * v) ∈ Cemb := by
    have hdir'' :
        embed (x + t • y, f x + t * v) = embed (x, f x) + t • dir (y, v) := by
      simpa using hdir'
    simpa [hdir''] using hmem
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
  have hle_real' : f (x + t • y) - f x ≤ v * t := by
    have hle' : f (x + t • y) - f x ≤ t * v := by linarith
    simpa [mul_comm] using hle'
  exact (div_le_iff₀ ht).2 hle_real'

/-- Closed convexity makes the ray supremum independent of the base point. -/
lemma ray_sSup_eq_of_closed {n : Nat} {C : Set (Fin n → Real)}
    {f : (Fin n → Real) → Real} {f0_plus : (Fin n → Real) → EReal}
    (hC : C = Set.univ)
    (hf : ProperConvexFunctionOn C (fun x => (f x : EReal)))
    (hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus y =
          sSup { r : EReal | ∃ x ∈ C, r = ((f (x + y) - f x : Real) : EReal) })
    (hpos : PositivelyHomogeneous f0_plus)
    (hclosed : ClosedConvexFunction (fun x => (f x : EReal))) :
    ∀ x y : Fin n → Real,
      f0_plus y =
        sSup { r : EReal |
          ∃ t : Real, 0 < t ∧ r = (((f (x + t • y) - f x) / t : Real) : EReal) } := by
  classical
  intro x y
  set S : Set EReal :=
      { r : EReal |
        ∃ t : Real, 0 < t ∧ r = (((f (x + t • y) - f x) / t : Real) : EReal) } with hS
  have hiff :
      ∀ v : Real, f0_plus y ≤ (v : EReal) ↔
        ∀ t > 0, ((f (x + t • y) - f x) / t : Real) ≤ v := by
    intro v
    constructor
    · intro hle t ht
      have hle' :=
        (recessionFunction_le_iff_ray (C := C) (f := f) (f0_plus := f0_plus) hC hf hf0_plus y v).1
          hle
      exact hle' x t ht
    · intro hbound
      have hbound' :
          ∀ x' : Fin n → Real, ∀ t : Real, 0 < t →
            ((f (x' + t • y) - f x') / t : Real) ≤ v := by
        intro x' t ht
        exact ray_bound_extend_closed (f := f) (x0 := x) (y := y) (v := v) hclosed hbound x' t ht
      exact
        (recessionFunction_le_iff_ray (C := C) (f := f) (f0_plus := f0_plus) hC hf hf0_plus y v).2
          hbound'
  have hle_sup : f0_plus y ≤ sSup S := by
    refine (le_sSup_iff).2 ?_
    intro b hb
    rcases (EReal.exists (p := fun r => r = b)).1 ⟨b, rfl⟩ with hb_bot | hb_top | hb_real
    · have hS_nonempty : S.Nonempty := by
        refine ⟨(((f (x + (1 : Real) • y) - f x) / (1 : Real) : Real) : EReal), ?_⟩
        exact ⟨1, by exact zero_lt_one, by simp⟩
      rcases hS_nonempty with ⟨r, hr⟩
      have hbot : r ≤ (⊥ : EReal) := by
        simpa [hb_bot.symm] using hb hr
      have hbot' : r = (⊥ : EReal) := (le_bot_iff).1 hbot
      rcases hr with ⟨t, ht, rfl⟩
      simp at hbot'
    · have hb_top' : b = (⊤ : EReal) := hb_top.symm
      simp [hb_top']
    · rcases hb_real with ⟨v, rfl⟩
      have hbound : ∀ t > 0, ((f (x + t • y) - f x) / t : Real) ≤ v := by
        intro t ht
        have hr : (((f (x + t • y) - f x) / t : Real) : EReal) ∈ S :=
          ⟨t, ht, rfl⟩
        have hr_le : (((f (x + t • y) - f x) / t : Real) : EReal) ≤ (v : EReal) := hb hr
        exact (EReal.coe_le_coe_iff).1 (by simpa using hr_le)
      exact (hiff v).2 hbound
  have hsup_le : sSup S ≤ f0_plus y := by
    refine (sSup_le_iff).2 ?_
    intro r hr
    rcases hr with ⟨t, ht, rfl⟩
    rcases (EReal.exists (p := fun r => r = f0_plus y)).1 ⟨f0_plus y, rfl⟩ with hbot | htop | hreal
    · have hne :
        f0_plus y ≠ (⊥ : EReal) :=
        recessionFunction_ne_bot (C := C) (f := f) (f0_plus := f0_plus) hf hf0_plus y
      exact (hne hbot.symm).elim
    · have htop' : f0_plus y = (⊤ : EReal) := htop.symm
      simp [htop']
    · rcases hreal with ⟨w, hw⟩
      have hx : x ∈ C := by simp [hC]
      have hle_sSup :
          ((f (x + t • y) - f x : Real) : EReal) ≤ f0_plus (t • y) := by
        have hmem :
            ((f (x + t • y) - f x : Real) : EReal) ∈
              { r : EReal | ∃ x ∈ C, r = ((f (x + t • y) - f x : Real) : EReal) } := by
          exact ⟨x, hx, rfl⟩
        have hsup := le_sSup hmem
        simpa [hf0_plus] using hsup
      have hpos' : f0_plus (t • y) = (t : EReal) * f0_plus y := hpos y t ht
      have hle' :
          ((f (x + t • y) - f x : Real) : EReal) ≤ (t : EReal) * (w : EReal) := by
        simpa [hpos', hw] using hle_sSup
      have hle_real :
          f (x + t • y) - f x ≤ t * w := by
        have hle'' :
            ((f (x + t • y) - f x : Real) : EReal) ≤ ((t * w : Real) : EReal) := by
          simpa [EReal.coe_mul, hw] using hle'
        exact (EReal.coe_le_coe_iff).1 hle''
      have hle_div : ((f (x + t • y) - f x) / t : Real) ≤ w := by
        exact (div_le_iff₀ ht).2 (by simpa [mul_comm] using hle_real)
      have hle_ereal :
          (((f (x + t • y) - f x) / t : Real) : EReal) ≤ (w : EReal) :=
        (EReal.coe_le_coe_iff).2 hle_div
      simpa [hw] using hle_ereal
  exact le_antisymm hle_sup hsup_le

/-- Along a fixed ray, the difference quotient converges to `f0_plus`. -/
lemma ray_limit_monotone {n : Nat} {C : Set (Fin n → Real)}
    {f : (Fin n → Real) → Real} {f0_plus : (Fin n → Real) → EReal}
    (hC : C = Set.univ)
    (hf : ProperConvexFunctionOn C (fun x => (f x : EReal)))
    (hf0_plus :
      ∀ y : Fin n → Real,
        f0_plus y =
          sSup { r : EReal | ∃ x ∈ C, r = ((f (x + y) - f x : Real) : EReal) })
    (hpos : PositivelyHomogeneous f0_plus)
    (hclosed : ClosedConvexFunction (fun x => (f x : EReal))) :
    ∀ x y : Fin n → Real,
      Filter.Tendsto
        (fun t : Real => (((f (x + t • y) - f x) / t : Real) : EReal))
        Filter.atTop (𝓝 (f0_plus y)) := by
  classical
  intro x y
  let fquot : ℝ → EReal :=
    fun t => (((f (x + t • y) - f x) / t : Real) : EReal)
  let q : {t : ℝ // 0 < t} → EReal :=
    fun t => fquot (t : ℝ)
  have hmono : Monotone q := by
    intro s t hst
    have hst' :=
      (differenceQuotient_monotone (C := C) (f := f) hC hf x y) hst
    exact (EReal.coe_le_coe_iff).2 (by simpa using hst')
  have htend_sub : Filter.Tendsto q Filter.atTop (𝓝 (⨆ t, q t)) :=
    tendsto_atTop_iSup hmono
  have hset :
      { r : EReal |
        ∃ t : Real, 0 < t ∧ r = (((f (x + t • y) - f x) / t : Real) : EReal) } =
        Set.range q := by
    ext r
    constructor
    · intro hr
      rcases hr with ⟨t, ht, rfl⟩
      refine ⟨⟨t, ht⟩, ?_⟩
      simp [q, fquot]
    · intro hr
      rcases hr with ⟨t, rfl⟩
      exact ⟨t, t.2, by simp [q, fquot]⟩
  have hsup_eq :
      f0_plus y = (⨆ t, q t) := by
    have hsup :=
      ray_sSup_eq_of_closed (C := C) (f := f) (f0_plus := f0_plus) hC hf hf0_plus hpos hclosed x y
    have hsup' :
        sSup { r : EReal |
          ∃ t : Real, 0 < t ∧ r = (((f (x + t • y) - f x) / t : Real) : EReal) } =
          (⨆ t, q t) := by
      calc
        sSup { r : EReal |
            ∃ t : Real, 0 < t ∧ r = (((f (x + t • y) - f x) / t : Real) : EReal) }
            = sSup (Set.range q) := by simp [hset]
        _ = ⨆ t, q t := by
            simp [sSup_range]
    exact hsup.trans hsup'
  have htend_sub' : Filter.Tendsto q Filter.atTop (𝓝 (f0_plus y)) := by
    simpa [hsup_eq] using htend_sub
  have htend_map :
      Filter.Tendsto fquot
        (Filter.map ((↑) : {t : ℝ // 0 < t} → ℝ) Filter.atTop) (𝓝 (f0_plus y)) := by
    exact (Filter.tendsto_map'_iff).2 (by simpa [q, fquot] using htend_sub')
  have hmap_eq :
      Filter.map ((↑) : {t : ℝ // 0 < t} → ℝ) Filter.atTop = Filter.atTop := by
    change Filter.map ((↑) : Set.Ioi (0 : ℝ) → ℝ) Filter.atTop = Filter.atTop
    simp
  have htend_map' : Filter.Tendsto fquot Filter.atTop (𝓝 (f0_plus y)) := by
    simpa [hmap_eq] using htend_map
  simpa [fquot] using htend_map'

end Section08
end Chap02
