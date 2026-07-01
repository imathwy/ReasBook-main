/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap01.section05_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section06_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section08_part8

noncomputable section
open scoped Pointwise
open scoped BigOperators
open scoped Topology
open scoped RealInnerProductSpace

section Chap02
section Section09

/-- Proposition 9.0.0.1. For a convex set `C` and linear map `A`, one has
`ri (A '' C) = A '' ri C`, while in general only `closure (A '' C) ⊇ A '' closure C`
(Theorem 6.6); the text asks when equality holds and when the image of a closed convex
set is closed. -/
theorem linearMap_relativeInterior_image_eq_and_image_closure_subset (n m : Nat)
    (C : Set (EuclideanSpace Real (Fin n))) (hC : Convex Real C)
    (A : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m)) :
    A '' euclideanRelativeInterior n C = euclideanRelativeInterior m (A '' C) ∧
      A '' closure C ⊆ closure (A '' C) := by
  rcases
      euclideanRelativeInterior_image_linearMap_eq_and_image_closure_subset n m C hC A with
    ⟨hri, hcl⟩
  exact ⟨hri.symm, hcl⟩

/-- The projected epigraph is not closed, and the induced `Ah` is not lsc at `0`. -/
lemma image_epigraph_not_closed_and_Ah_not_lsc :
    let h : (Fin 2 → Real) → EReal :=
      fun x =>
        if 0 ≤ x 0 ∧ 0 ≤ x 1 then
          (Real.exp (-(Real.sqrt (x 0 * x 1))) : EReal)
        else
          (⊤ : EReal)
    let A : (Fin 2 → Real) → Real := fun x => x 0
    let B : (Fin 2 → Real) × Real → Real × Real := fun p => (A p.1, p.2)
    let Ah : Real → EReal :=
      fun xi1 =>
        if 0 < xi1 then (0 : EReal) else if xi1 = 0 then (1 : EReal) else (⊤ : EReal)
    ¬ IsClosed (Set.image B (epigraph (Set.univ : Set (Fin 2 → Real)) h)) ∧
      ¬ LowerSemicontinuousAt Ah 0 := by
  classical
  simp
  set h : (Fin 2 → Real) → EReal :=
      fun x =>
        if 0 ≤ x 0 ∧ 0 ≤ x 1 then
          (Real.exp (-(Real.sqrt (x 0 * x 1))) : EReal)
        else
          (⊤ : EReal) with h_def
  set A : (Fin 2 → Real) → Real := fun x => x 0 with A_def
  set B : (Fin 2 → Real) × Real → Real × Real := fun p => (A p.1, p.2) with B_def
  set Ah : Real → EReal :=
      fun xi1 =>
        if 0 < xi1 then (0 : EReal) else if xi1 = 0 then (1 : EReal) else (⊤ : EReal) with Ah_def
  refine And.intro ?_ ?_
  · intro hclosed
    set S : Set (Real × Real) :=
        Set.image B (epigraph (Set.univ : Set (Fin 2 → Real)) h) with S_def
    have hmem_image :
        ∀ n : ℕ, (1, Real.exp (-(n : Real))) ∈ S := by
      intro n
      let x : Fin 2 → Real := fun i => if i = 0 then (1 : Real) else (n : Real) ^ 2
      have hx0 : x 0 = (1 : Real) := by simp [x]
      have hx1 : x 1 = (n : Real) ^ 2 := by simp [x]
      have hx_nonneg : 0 ≤ x 0 ∧ 0 ≤ x 1 := by
        exact ⟨by simp [hx0], by simp [hx1]⟩
      have hsqrt : Real.sqrt (x 0 * x 1) = (n : Real) := by
        have hn : (0 : Real) ≤ (n : Real) := by exact_mod_cast (Nat.cast_nonneg n)
        calc
          Real.sqrt (x 0 * x 1) = Real.sqrt ((n : Real) ^ 2) := by simp [hx0, hx1]
          _ = |(n : Real)| := Real.sqrt_sq_eq_abs _
          _ = (n : Real) := abs_of_nonneg hn
      have hval : h x = (Real.exp (-(n : Real)) : EReal) := by
        simp [h_def, hx_nonneg, hsqrt]
      have hmem_epi : (x, Real.exp (-(n : Real))) ∈
          epigraph (Set.univ : Set (Fin 2 → Real)) h := by
        refine And.intro ?_ ?_
        · trivial
        · simp [hval]
      refine ⟨(x, Real.exp (-(n : Real))), hmem_epi, ?_⟩
      simp [B_def, A_def, hx0]
    have hmem_closure : (1, (0 : Real)) ∈ closure S := by
      refine (mem_closure_iff_seq_limit).2 ?_
      refine ⟨fun n : ℕ => (1, Real.exp (-(n : Real))), ?_, ?_⟩
      · intro n
        simpa [S_def] using hmem_image n
      · have h1 :
            Filter.Tendsto (fun _ : ℕ => (1 : Real)) Filter.atTop (𝓝 (1 : Real)) :=
          tendsto_const_nhds
        have h2 :
            Filter.Tendsto (fun n : ℕ => Real.exp (-(n : Real))) Filter.atTop
              (𝓝 (0 : Real)) := by
          have h' :
              Filter.Tendsto (fun x : ℝ => Real.exp (-x)) Filter.atTop (𝓝 (0 : Real)) :=
            by simpa using (Real.tendsto_exp_neg_atTop_nhds_zero :
              Filter.Tendsto (fun x : ℝ => Real.exp (-x)) Filter.atTop (𝓝 (0 : Real)))
          exact h'.comp tendsto_natCast_atTop_atTop
        exact Filter.Tendsto.prodMk_nhds h1 h2
    have hnotmem : (1, (0 : Real)) ∉ S := by
      intro hmem
      rcases hmem with ⟨p, hp, hpB⟩
      rcases p with ⟨x, μ⟩
      have hx0 : x 0 = (1 : Real) := by
        have := congrArg Prod.fst hpB
        simpa [B_def, A_def] using this
      have hμ : μ = (0 : Real) := by
        have := congrArg Prod.snd hpB
        simpa [B_def] using this
      have hx0_nonneg : 0 ≤ x 0 := by simp [hx0]
      have hle : h x ≤ (0 : EReal) := by
        rcases hp with ⟨-, hle'⟩
        simpa [hμ] using hle'
      by_cases hx1 : 0 ≤ x 1
      · have hle' := hle
        simp [h_def, hx0_nonneg, hx1] at hle'
        exact (not_le_of_gt (Real.exp_pos _)) hle'
      · have hle' := hle
        simp [h_def, hx0_nonneg, hx1] at hle'
    have hclosure_eq : closure S = S := IsClosed.closure_eq hclosed
    have hmem' : (1, (0 : Real)) ∈ S := by
      simpa [hclosure_eq] using hmem_closure
    exact hnotmem hmem'
  · intro hls
    have hAh0 : Ah 0 = (1 : EReal) := by simp [Ah_def]
    have hy_real : (1 / 2 : ℝ) < (1 : ℝ) := by norm_num
    have hy : ((1 / 2 : ℝ) : EReal) < Ah 0 := by
      have hy' : ((1 / 2 : ℝ) : EReal) < (1 : EReal) :=
        (EReal.coe_lt_coe_iff).2 hy_real
      simpa [hAh0] using hy'
    have hnhds :
        {x : Real | ((1 / 2 : ℝ) : EReal) < Ah x} ∈ 𝓝 (0 : Real) := hls _ hy
    rcases (Metric.mem_nhds_iff.mp hnhds) with ⟨ε, hε, hball⟩
    have hxball : (ε / 2 : Real) ∈ Metric.ball (0 : Real) ε := by
      have hhalf_nonneg : 0 ≤ (ε / 2 : Real) := by nlinarith [hε]
      have hhalf_lt : (ε / 2 : Real) < ε := by nlinarith [hε]
      have hx' : |(ε / 2 : Real)| < ε := by
        simpa [abs_of_nonneg hhalf_nonneg] using hhalf_lt
      simpa [Metric.ball, Real.dist_eq] using hx'
    have hxmem : ((1 / 2 : ℝ) : EReal) < Ah (ε / 2) := hball hxball
    have hpos : 0 < (ε / 2 : Real) := by nlinarith [hε]
    have hAhpos : Ah (ε / 2) = (0 : EReal) := by simp [Ah_def, hpos]
    have hxmem' : ((1 / 2 : ℝ) : EReal) < (0 : EReal) := by
      simpa [hAhpos] using hxmem
    have : (1 / 2 : ℝ) < (0 : ℝ) := by
      simpa [EReal.coe_lt_coe_iff] using hxmem'
    nlinarith

/-- Image of the nonnegative orthant under `x ↦ -sqrt(x0*x1)` is `(-∞, 0]`. -/
lemma image_neg_sqrt_mul_nonneg :
    (fun x : Fin 2 → Real => -(Real.sqrt (x 0 * x 1))) '' {x | 0 ≤ x 0 ∧ 0 ≤ x 1} =
      Set.Iic (0 : Real) := by
  ext t; constructor
  · intro ht
    rcases ht with ⟨x, hx, rfl⟩
    have hsqrt_nonneg : 0 ≤ Real.sqrt (x 0 * x 1) := Real.sqrt_nonneg _
    exact neg_nonpos.mpr hsqrt_nonneg
  · intro ht
    have ht' : t ≤ (0 : Real) := by simpa using ht
    have hnonneg : 0 ≤ -t := by linarith
    let x : Fin 2 → Real := fun i => if i = 0 then (1 : Real) else (-t) ^ 2
    have hx0 : x 0 = (1 : Real) := by simp [x]
    have hx1 : x 1 = (-t) ^ 2 := by simp [x]
    have hx_nonneg : 0 ≤ x 0 ∧ 0 ≤ x 1 := by
      refine ⟨by simp [hx0], ?_⟩
      have hx1_nonneg : 0 ≤ (-t) ^ 2 := by nlinarith
      simpa [hx1] using hx1_nonneg
    refine ⟨x, hx_nonneg, ?_⟩
    have hsqrt : Real.sqrt (x 0 * x 1) = -t := by
      calc
        Real.sqrt (x 0 * x 1) = Real.sqrt ((-t) ^ 2) := by simp [hx0, hx1]
        _ = |(-t)| := Real.sqrt_sq_eq_abs _
        _ = -t := abs_of_nonneg hnonneg
    simp [hsqrt]

/-- Convexity of `x ↦ exp(-sqrt(x0*x1))` on the nonnegative orthant. -/
lemma convexOn_exp_neg_sqrt_mul_nonneg :
    ConvexOn ℝ {x : Fin 2 → Real | 0 ≤ x 0 ∧ 0 ≤ x 1}
      (fun x => Real.exp (-(Real.sqrt (x 0 * x 1)))) := by
  classical
  let C : Set (Fin 2 → Real) := {x | 0 ≤ x 0 ∧ 0 ≤ x 1}
  have hconv_neg :
      ConvexOn ℝ C (fun x => -(Real.sqrt (x 0 * x 1))) := by
    have hconv_rpow :
        ConvexOn ℝ C (fun x => -(Real.rpow (x 0 * x 1) (1 / (2 : Real)))) := by
      simpa [C, Fin.forall_fin_two, Fin.prod_univ_two] using
        (convexOn_negGeomMean_nonneg (n := 2) (by decide))
    refine hconv_rpow.congr ?_
    intro x hx
    simp [Real.sqrt_eq_rpow]
  have hconv_exp_Iic : ConvexOn ℝ (Set.Iic (0 : Real)) Real.exp := by
    have hconv_univ : ConvexOn ℝ (Set.univ : Set Real) Real.exp := convexOn_exp
    refine (ConvexOn.subset (s := Set.Iic (0 : Real)) (t := Set.univ) hconv_univ ?_ ?_)
    · intro x hx; exact Set.mem_univ x
    · simpa using (convex_Iic (r := (0 : Real)))
  have hconv_exp :
      ConvexOn ℝ ((fun x : Fin 2 → Real => -(Real.sqrt (x 0 * x 1))) '' C) Real.exp := by
    simpa [C, image_neg_sqrt_mul_nonneg] using hconv_exp_Iic
  have hmono :
      MonotoneOn Real.exp ((fun x : Fin 2 → Real => -(Real.sqrt (x 0 * x 1))) '' C) := by
    intro x hx y hy hxy
    exact Real.exp_monotone hxy
  have hcomp :=
    (ConvexOn.comp (g := Real.exp)
      (f := fun x : Fin 2 → Real => -(Real.sqrt (x 0 * x 1))) (s := C) hconv_exp hconv_neg
      hmono)
  simpa [C, Function.comp] using hcomp

/-- Convexity of the extended-value function `h` on `Set.univ`. -/
lemma h_convexFunctionOn_univ :
    ConvexFunctionOn (Set.univ : Set (Fin 2 → Real))
      (fun x =>
        if 0 ≤ x 0 ∧ 0 ≤ x 1 then
          (Real.exp (-(Real.sqrt (x 0 * x 1))) : EReal)
        else
          (⊤ : EReal)) := by
  classical
  let C : Set (Fin 2 → Real) := {x | 0 ≤ x 0 ∧ 0 ≤ x 1}
  have hconv : ConvexOn ℝ C (fun x => Real.exp (-(Real.sqrt (x 0 * x 1)))) := by
    simpa [C] using convexOn_exp_neg_sqrt_mul_nonneg
  have hconv_on :=
    convexFunctionOn_univ_if_top (C := C)
      (g := fun x => Real.exp (-(Real.sqrt (x 0 * x 1)))) hconv
  simpa [C] using hconv_on

/-- Properness of the function `h`. -/
lemma h_proper :
    ProperConvexFunctionOn (Set.univ : Set (Fin 2 → Real))
      (fun x =>
        if 0 ≤ x 0 ∧ 0 ≤ x 1 then
          (Real.exp (-(Real.sqrt (x 0 * x 1))) : EReal)
        else
          (⊤ : EReal)) := by
  classical
  have hconv_on :
      ConvexFunctionOn (Set.univ : Set (Fin 2 → Real))
        (fun x =>
          if 0 ≤ x 0 ∧ 0 ≤ x 1 then
            (Real.exp (-(Real.sqrt (x 0 * x 1))) : EReal)
          else
            (⊤ : EReal)) := h_convexFunctionOn_univ
  have hne :
      Set.Nonempty
        (epigraph (Set.univ : Set (Fin 2 → Real))
          (fun x =>
            if 0 ≤ x 0 ∧ 0 ≤ x 1 then
              (Real.exp (-(Real.sqrt (x 0 * x 1))) : EReal)
            else
              (⊤ : EReal))) := by
    refine ⟨((fun _ : Fin 2 => (0 : Real)), (1 : Real)), ?_⟩
    have hmem : (fun _ : Fin 2 => (0 : Real)) ∈ (Set.univ : Set (Fin 2 → Real)) := by simp
    have hle :
        (if 0 ≤ (0 : Real) ∧ 0 ≤ (0 : Real) then
          (Real.exp (-(Real.sqrt ((0 : Real) * (0 : Real)))) : EReal)
        else
          (⊤ : EReal)) ≤ (1 : EReal) := by
      simp
    exact ⟨hmem, hle⟩
  have hbot :
      ∀ x ∈ (Set.univ : Set (Fin 2 → Real)),
        (if 0 ≤ x 0 ∧ 0 ≤ x 1 then
          (Real.exp (-(Real.sqrt (x 0 * x 1))) : EReal)
        else
          (⊤ : EReal)) ≠ (⊥ : EReal) := by
    intro x hx
    by_cases hx0 : 0 ≤ x 0 ∧ 0 ≤ x 1
    · simp [hx0]
    · simp [hx0]
  exact ⟨hconv_on, hne, hbot⟩

/-- Lower semicontinuity of the function `h`. -/
lemma h_lowerSemicontinuous :
    LowerSemicontinuous
      (fun x : Fin 2 → Real =>
        if 0 ≤ x 0 ∧ 0 ≤ x 1 then
          (Real.exp (-(Real.sqrt (x 0 * x 1))) : EReal)
        else
          (⊤ : EReal)) := by
  classical
  refine (lowerSemicontinuous_iff_closed_sublevel
    (f := fun x : Fin 2 → Real =>
      if 0 ≤ x 0 ∧ 0 ≤ x 1 then
        (Real.exp (-(Real.sqrt (x 0 * x 1))) : EReal)
      else
        (⊤ : EReal))).2 ?_
  intro α
  let C : Set (Fin 2 → Real) := {x | 0 ≤ x 0 ∧ 0 ≤ x 1}
  let g : (Fin 2 → Real) → Real := fun x => Real.exp (-(Real.sqrt (x 0 * x 1)))
  have hset :
      {x | (if 0 ≤ x 0 ∧ 0 ≤ x 1 then (g x : EReal) else (⊤ : EReal)) ≤ (α : EReal)} =
        C ∩ {x | g x ≤ α} := by
    ext x; by_cases hx : 0 ≤ x 0 ∧ 0 ≤ x 1
    · simp [C, g, hx, EReal.coe_le_coe_iff]
    · simp [C, g, hx]
  have hclosed0 : IsClosed {x : Fin 2 → Real | 0 ≤ x 0} := by
    simpa using (isClosed_le continuous_const (continuous_apply 0))
  have hclosed1 : IsClosed {x : Fin 2 → Real | 0 ≤ x 1} := by
    simpa using (isClosed_le continuous_const (continuous_apply 1))
  have hclosedC : IsClosed C := by
    simpa [C, Set.setOf_and] using hclosed0.inter hclosed1
  have hcont_mul : Continuous (fun x : Fin 2 → Real => x 0 * x 1) :=
    (continuous_apply 0).mul (continuous_apply 1)
  have hcont_sqrt :
      Continuous (fun x : Fin 2 → Real => Real.sqrt (x 0 * x 1)) :=
    Real.continuous_sqrt.comp hcont_mul
  have hcont_neg :
      Continuous (fun x : Fin 2 → Real => -(Real.sqrt (x 0 * x 1))) := hcont_sqrt.neg
  have hcont_g : Continuous g := Real.continuous_exp.comp hcont_neg
  have hclosed_sub : IsClosed {x | g x ≤ α} := by
    simpa [g] using (isClosed_le hcont_g continuous_const)
  have hclosed_inter : IsClosed (C ∩ {x | g x ≤ α}) := hclosedC.inter hclosed_sub
  rw [hset]
  exact hclosed_inter

/-- Example 9.0.0.2. Let `h : R^2 -> (-infty, +infty]` be given by
`h(x) = exp[-(xi1 * xi2)^(1/2)]` for `x = (xi1, xi2) ≥ 0`, and `h(x) = +infty` otherwise.
For the projection `A (xi1, xi2) = xi1` and `B (x, mu) = (A x, mu)`, the image of
`epi h` under `B` need not be closed (even though `h` is closed proper convex), and the
image function `(Ah)` satisfies `(Ah)(xi1) = 0` for `xi1 > 0`, `(Ah)(0) = 1`,
and `(Ah)(xi1) = +infty` for `xi1 < 0`, so `(Ah)` is not lower semicontinuous at `0`. -/
theorem projection_epigraph_not_closed_example :
    let h : (Fin 2 → Real) → EReal :=
      fun x =>
        if 0 ≤ x 0 ∧ 0 ≤ x 1 then
          (Real.exp (-(Real.sqrt (x 0 * x 1))) : EReal)
        else
          (⊤ : EReal)
    let A : (Fin 2 → Real) → Real := fun x => x 0
    let B : (Fin 2 → Real) × Real → Real × Real := fun p => (A p.1, p.2)
    let Ah : Real → EReal :=
      fun xi1 =>
        if 0 < xi1 then (0 : EReal) else if xi1 = 0 then (1 : EReal) else (⊤ : EReal)
    ClosedConvexFunction h ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin 2 → Real)) h ∧
      ¬ IsClosed (Set.image B (epigraph (Set.univ : Set (Fin 2 → Real)) h)) ∧
      ¬ LowerSemicontinuousAt Ah 0 := by
  classical
  simp
  set h : (Fin 2 → Real) → EReal :=
      fun x =>
        if 0 ≤ x 0 ∧ 0 ≤ x 1 then
          (Real.exp (-(Real.sqrt (x 0 * x 1))) : EReal)
        else
          (⊤ : EReal) with h_def
  set A : (Fin 2 → Real) → Real := fun x => x 0 with A_def
  set B : (Fin 2 → Real) × Real → Real × Real := fun p => (A p.1, p.2) with B_def
  set Ah : Real → EReal :=
      fun xi1 =>
        if 0 < xi1 then (0 : EReal) else if xi1 = 0 then (1 : EReal) else (⊤ : EReal) with Ah_def
  have hnot :
      ¬ IsClosed (Set.image B (epigraph (Set.univ : Set (Fin 2 → Real)) h)) ∧
        ¬ LowerSemicontinuousAt Ah 0 := by
    simpa [h_def, A_def, B_def, Ah_def] using (image_epigraph_not_closed_and_Ah_not_lsc)
  refine ⟨?_, ?_, hnot.1, hnot.2⟩
  · have hconv_on : ConvexFunctionOn (Set.univ : Set (Fin 2 → Real)) h := by
      simpa [h_def] using h_convexFunctionOn_univ
    have hconv : ConvexFunction h := by
      simpa [ConvexFunction] using hconv_on
    have hlsc : LowerSemicontinuous h := by
      simpa [h_def] using h_lowerSemicontinuous
    exact ⟨hconv, hlsc⟩
  · simpa [h_def] using h_proper

/-- If `x0` minimizes `h` on the fiber `A x = y`, then the vertical section of `F`
is the closed half-line starting at `h x0`. -/
lemma verticalLine_intersection_eq_closedHalfLine_of_minimizer
    {X Y : Type*} {A : X → Y} {h : X → Real} {y : Y} {F : Set (Y × Real)}
    (hF : F = {p | ∃ x, A x = p.1 ∧ h x ≤ p.2})
    {x0 : X} (hx0 : A x0 = y ∧ ∀ z, A z = y → h x0 ≤ h z) :
    (let verticalLine : Set (Y × Real) := {p | p.1 = y}
     let closedHalfLine : Real → Set (Y × Real) := fun mu0 => {p | p.1 = y ∧ mu0 ≤ p.2}
     verticalLine ∩ F = closedHalfLine (h x0)) := by
  classical
  change ({p : Y × Real | p.1 = y} ∩ F =
    {p : Y × Real | p.1 = y ∧ h x0 ≤ p.2})
  ext p
  constructor
  · intro hp
    rcases hp with ⟨hp1, hpF⟩
    have hpF' : ∃ x, A x = p.1 ∧ h x ≤ p.2 := by
      simpa [hF] using hpF
    rcases hpF' with ⟨x, hxA, hxle⟩
    have hx0_le : h x0 ≤ h x := hx0.2 x (hxA.trans hp1)
    exact ⟨hp1, le_trans hx0_le hxle⟩
  · intro hp
    rcases hp with ⟨hp1, hp2⟩
    refine ⟨hp1, ?_⟩
    have hx0A : A x0 = p.1 := by simpa [hp1] using hx0.1
    have : ∃ x, A x = p.1 ∧ h x ≤ p.2 := ⟨x0, hx0A, hp2⟩
    simpa [hF] using this

/-- If the vertical section is a closed half-line, then `h` attains its infimum
on the fiber `A x = y`. -/
lemma minimizer_of_verticalLine_eq_closedHalfLine
    {X Y : Type*} {A : X → Y} {h : X → Real} {y : Y} {F : Set (Y × Real)}
    (hF : F = {p | ∃ x, A x = p.1 ∧ h x ≤ p.2}) {mu0 : Real}
    (hline :
      (let verticalLine : Set (Y × Real) := {p | p.1 = y}
       let closedHalfLine : Real → Set (Y × Real) := fun mu0 => {p | p.1 = y ∧ mu0 ≤ p.2}
       verticalLine ∩ F = closedHalfLine mu0)) :
    ∃ x, A x = y ∧ ∀ z, A z = y → h x ≤ h z := by
  classical
  have hline' :
      ({p : Y × Real | p.1 = y} ∩ F) =
        {p : Y × Real | p.1 = y ∧ mu0 ≤ p.2} := by
    simpa using hline
  have hmem : (y, mu0) ∈ ({p : Y × Real | p.1 = y} ∩ F) := by
    simp [hline']
  have hmemF : (y, mu0) ∈ F := hmem.2
  have hx : ∃ x, A x = y ∧ h x ≤ mu0 := by
    have : ∃ x, A x = (y, mu0).1 ∧ h x ≤ (y, mu0).2 := by
      simpa [hF] using hmemF
    simpa using this
  rcases hx with ⟨x0, hx0A, hx0le⟩
  refine ⟨x0, hx0A, ?_⟩
  intro z hzA
  have hzmemF : (y, h z) ∈ F := by
    have : ∃ x, A x = (y, h z).1 ∧ h x ≤ (y, h z).2 := by
      exact ⟨z, by simpa using hzA, le_rfl⟩
    simpa [hF] using this
  have hzmem : (y, h z) ∈ ({p : Y × Real | p.1 = y} ∩ F) := by
    exact ⟨rfl, hzmemF⟩
  have hzmem' : (y, h z) ∈ {p : Y × Real | p.1 = y ∧ mu0 ≤ p.2} := by
    simpa [hline'] using hzmem
  have hmu0_le : mu0 ≤ h z := hzmem'.2
  exact le_trans hx0le hmu0_le

/-- Proposition 9.0.0.3. The value `(A h)(y)` is the infimum of `h` on the affine set
`{x | A x = y}`; the infimum is attained iff the vertical line `{(y, mu) | mu ∈ Real}`
meets `F` in a closed half-line (or is empty), which would hold if `F` is closed and
has no downward direction of recession. -/
lemma infimum_attained_iff_verticalLine_intersection_closedHalfLine
    {X Y : Type*} (A : X → Y) (h : X → Real) (y : Y) (F : Set (Y × Real))
    (hF : F = {p | ∃ x, A x = p.1 ∧ h x ≤ p.2}) (hne : ∃ x, A x = y) :
    (∃ x, A x = y ∧ ∀ z, A z = y → h x ≤ h z) ↔
      (let verticalLine : Set (Y × Real) := {p | p.1 = y}
       let closedHalfLine : Real → Set (Y × Real) :=
         fun mu0 => {p | p.1 = y ∧ mu0 ≤ p.2}
       (∃ mu0, verticalLine ∩ F = closedHalfLine mu0) ∨ verticalLine ∩ F = ∅) := by
  classical
  constructor
  · rintro ⟨x0, hx0A, hx0min⟩
    refine Or.inl ?_
    refine ⟨h x0, ?_⟩
    simpa using
      (verticalLine_intersection_eq_closedHalfLine_of_minimizer (A:=A) (h:=h) (y:=y) (F:=F)
        hF ⟨hx0A, hx0min⟩)
  · intro hsection
    rcases hsection with ⟨mu0, hline⟩ | hempty
    · exact minimizer_of_verticalLine_eq_closedHalfLine (A:=A) (h:=h) (y:=y) (F:=F) hF hline
    · exfalso
      rcases hne with ⟨x0, hx0A⟩
      have hx0memF : (y, h x0) ∈ F := by
        have : ∃ x, A x = (y, h x0).1 ∧ h x ≤ (y, h x0).2 := by
          exact ⟨x0, by simpa using hx0A, le_rfl⟩
        simpa [hF] using this
      have hx0mem : (y, h x0) ∈ ({p : Y × Real | p.1 = y} ∩ F) := by
        exact ⟨rfl, hx0memF⟩
      have hempty' : ({p : Y × Real | p.1 = y} ∩ F) = ∅ := by
        simpa using hempty
      simp [hempty'] at hx0mem

/-- The projection of `C` is `(0, +∞)`. -/
lemma image_A_C_eq_Ioi :
    Set.image (fun x : Fin 2 → Real => x 0)
        {x : Fin 2 → Real | 0 < x 0 ∧ x 1 ≥ (x 0)⁻¹} = Set.Ioi (0 : Real) := by
  ext y; constructor
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hx.1
  · intro hy
    let x : Fin 2 → Real := fun i => if i = 0 then y else y⁻¹
    refine ⟨x, ?_, ?_⟩
    · have hx0 : x 0 = y := by simp [x]
      have hx1 : x 1 = y⁻¹ := by simp [x]
      refine ⟨?_, ?_⟩
      · simpa [hx0] using hy
      · simp [hx0, hx1]
    · simp [x]

/-- Convexity of the set `{x | 0 < x 0 ∧ x 1 ≥ (x 0)⁻¹}`. -/
lemma convex_C :
    Convex Real {x : Fin 2 → Real | 0 < x 0 ∧ x 1 ≥ (x 0)⁻¹} := by
  intro x hx y hy a b ha hb hab
  have hx0 : 0 < x 0 := hx.1
  have hy0 : 0 < y 0 := hy.1
  have hx1 : (x 0)⁻¹ ≤ x 1 := hx.2
  have hy1 : (y 0)⁻¹ ≤ y 1 := hy.2
  have hpos : 0 < a * x 0 + b * y 0 := by
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      simpa [ha0, hb1] using hy0
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hpos1 : 0 < a * x 0 := mul_pos ha_pos hx0
      have hnonneg : 0 ≤ b * y 0 := mul_nonneg hb (le_of_lt hy0)
      exact add_pos_of_pos_of_nonneg hpos1 hnonneg
  have hconv :
      (a * x 0 + b * y 0)⁻¹ ≤ a * (x 0)⁻¹ + b * (y 0)⁻¹ := by
    have hxpos : x 0 ∈ Set.Ioi (0 : Real) := hx0
    have hypos : y 0 ∈ Set.Ioi (0 : Real) := hy0
    simpa [smul_eq_mul] using (convexOn_inv_Ioi).2 hxpos hypos ha hb hab
  have hle1 : a * (x 0)⁻¹ + b * (y 0)⁻¹ ≤ a * x 1 + b * y 1 := by
    have hle1a : a * (x 0)⁻¹ ≤ a * x 1 := mul_le_mul_of_nonneg_left hx1 ha
    have hle1b : b * (y 0)⁻¹ ≤ b * y 1 := mul_le_mul_of_nonneg_left hy1 hb
    exact add_le_add hle1a hle1b
  have hineq : (a * x 0 + b * y 0)⁻¹ ≤ a * x 1 + b * y 1 := le_trans hconv hle1
  refine ⟨?_, ?_⟩
  · simpa [smul_eq_mul] using hpos
  · simpa [smul_eq_mul] using hineq

/-- Sequential closedness of the set `{x | 0 < x 0 ∧ x 1 ≥ (x 0)⁻¹}`. -/
lemma seqClosed_C :
    IsSeqClosed {x : Fin 2 → Real | 0 < x 0 ∧ x 1 ≥ (x 0)⁻¹} := by
  intro u x hu hx
  have h0 : Filter.Tendsto (fun n => u n 0) Filter.atTop (𝓝 (x 0)) :=
    (tendsto_pi_nhds.mp hx) 0
  have h1 : Filter.Tendsto (fun n => u n 1) Filter.atTop (𝓝 (x 1)) :=
    (tendsto_pi_nhds.mp hx) 1
  have hpos : ∀ n, 0 < u n 0 := fun n => (hu n).1
  have hineq : ∀ n, (u n 0)⁻¹ ≤ u n 1 := fun n => (hu n).2
  have hx0_nonneg : 0 ≤ x 0 := by
    have hclosed : IsClosed (Set.Ici (0 : Real)) := isClosed_Ici
    have hmem : ∀ᶠ n in Filter.atTop, u n 0 ∈ Set.Ici (0 : Real) := by
      refine Filter.Eventually.of_forall ?_
      intro n
      have : 0 ≤ u n 0 := le_of_lt (hpos n)
      simpa [Set.mem_Ici] using this
    have hxmem : x 0 ∈ Set.Ici (0 : Real) := hclosed.mem_of_tendsto h0 hmem
    simpa [Set.mem_Ici] using hxmem
  have hx0_pos : 0 < x 0 := by
    by_contra hx0_notpos
    have hx0_le : x 0 ≤ 0 := le_of_not_gt hx0_notpos
    have hx0_eq : x 0 = 0 := le_antisymm hx0_le hx0_nonneg
    have h0_to0 : Filter.Tendsto (fun n => u n 0) Filter.atTop (𝓝 (0 : Real)) := by
      simpa [hx0_eq] using h0
    have h0_within : Filter.Tendsto (fun n => u n 0) Filter.atTop (𝓝[>] (0 : Real)) := by
      refine (tendsto_nhdsWithin_iff.2 ?_)
      refine ⟨h0_to0, ?_⟩
      refine Filter.Eventually.of_forall ?_
      intro n
      have : 0 < u n 0 := hpos n
      simpa [Set.mem_Ioi] using this
    have h_inv : Filter.Tendsto (fun n => (u n 0)⁻¹) Filter.atTop Filter.atTop :=
      (tendsto_inv_nhdsGT_zero.comp h0_within)
    have h_inv_large :
        ∀ᶠ n in Filter.atTop, (x 1 + 1) ≤ (u n 0)⁻¹ := by
      rcases (Filter.tendsto_atTop_atTop.1 h_inv) (x 1 + 1) with ⟨N, hN⟩
      exact Filter.eventually_atTop.2 ⟨N, hN⟩
    have h_upper : ∀ᶠ n in Filter.atTop, u n 1 < x 1 + 1 := by
      have h := (tendsto_order.1 h1).2 (x 1 + 1) (by linarith)
      simpa using h
    rcases (Filter.eventually_atTop.1 h_inv_large) with ⟨N1, hN1⟩
    rcases (Filter.eventually_atTop.1 h_upper) with ⟨N2, hN2⟩
    let N := max N1 N2
    have hlow : x 1 + 1 ≤ (u N 0)⁻¹ := hN1 _ (le_max_left _ _)
    have hle : x 1 + 1 ≤ u N 1 := le_trans hlow (hineq N)
    have hhigh : u N 1 < x 1 + 1 := hN2 _ (le_max_right _ _)
    exact (not_le_of_gt hhigh) hle
  have h_inv :
      Filter.Tendsto (fun n => (u n 0)⁻¹) Filter.atTop (𝓝 (x 0)⁻¹) :=
    (tendsto_inv₀ (by exact ne_of_gt hx0_pos)).comp h0
  have hx1_ge : (x 0)⁻¹ ≤ x 1 :=
    le_of_tendsto_of_tendsto h_inv h1 (Filter.Eventually.of_forall hineq)
  exact ⟨hx0_pos, hx1_ge⟩

/-- Example 9.0.0.4. The closed convex set
`C = {(xi1, xi2) | xi1 > 0, xi2 ≥ xi1^{-1}}` in `ℝ^2` has nonclosed projection
`A (xi1, xi2) = xi1`; the difficulty is that `C` is asymptotic to a vertical line,
and the recession cone condition rules out directions `(0,1)` and `(0,-1)`. -/
theorem projection_closed_convex_not_closed_image_example :
    let C : Set (Fin 2 → Real) := {x | 0 < x 0 ∧ x 1 ≥ (x 0)⁻¹}
    let A : (Fin 2 → Real) → Real := fun x => x 0
    IsClosed C ∧ Convex Real C ∧ ¬ IsClosed (Set.image A C) := by
  classical
  simp
  set C : Set (Fin 2 → Real) := {x | 0 < x 0 ∧ x 1 ≥ (x 0)⁻¹} with C_def
  set A : (Fin 2 → Real) → Real := fun x => x 0 with A_def
  refine ⟨?_, ?_, ?_⟩
  · have hseq : IsSeqClosed C := by
      simpa [C_def] using seqClosed_C
    exact (isSeqClosed_iff_isClosed).1 hseq
  · simpa [C_def] using convex_C
  · have himage : Set.image A C = Set.Ioi (0 : Real) := by
      simpa [A_def, C_def] using image_A_C_eq_Ioi
    have hnot : ¬ IsClosed (Set.Ioi (0 : Real)) := by
      intro hclosed
      have hmem : (0 : Real) ∈ closure (Set.Ioi (0 : Real)) := by
        rw [closure_Ioi]
        simp
      have hmem' := hmem
      rw [hclosed.closure_eq] at hmem'
      simp at hmem'
    simpa [himage] using hnot

/-- Theorem 9.1. Let `C` be a non-empty convex set in `ℝ^n`, and let `A` be a linear
transformation from `ℝ^n` to `ℝ^m`. Assume that every non-zero vector `z ∈ 0+ (cl C)`
satisfying `Az = 0` belongs to the lineality space of `cl C`. Then `cl (A C) = A (cl C)`
and `0+ (A (cl C)) = A (0+ (cl C))`. In particular, if `C` is closed, and `z = 0` is the
only `z ∈ 0+ C` such that `Az = 0`, then `A C` is closed. -/
-- The lineality space of `closure C` meets `A.ker` at `0`.
lemma lineality_inter_kernel_nonempty
    {n m : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (A : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m)) :
    (Set.linealitySpace (closure C) ∩ (LinearMap.ker A : Set _)).Nonempty := by
  refine ⟨0, ?_⟩
  have hrec : (0 : EuclideanSpace Real (Fin n)) ∈ Set.recessionCone (closure C) := by
    intro x hx t ht
    simpa using hx
  have hlin : (0 : EuclideanSpace Real (Fin n)) ∈ Set.linealitySpace (closure C) := by
    change (0 : EuclideanSpace Real (Fin n)) ∈
        (-Set.recessionCone (closure C)) ∩ Set.recessionCone (closure C)
    refine ⟨?_, hrec⟩
    change (-(0 : EuclideanSpace Real (Fin n))) ∈ Set.recessionCone (closure C)
    simpa using hrec
  have hker : (0 : EuclideanSpace Real (Fin n)) ∈ (LinearMap.ker A : Set _) := by
    change A 0 = 0
    simp
  exact ⟨hlin, hker⟩

/-- Kernel intersection of the recession cone equals the kernel intersection of the
lineality space under the kernel-lineality hypothesis. -/
lemma recessionCone_inter_kernel_eq_lineality_inter_kernel
    {n m : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (A : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m))
    (hlineal :
      ∀ z, z ≠ 0 → z ∈ Set.recessionCone (closure C) → A z = 0 →
        z ∈ Set.linealitySpace (closure C)) :
    Set.recessionCone (closure C) ∩ (LinearMap.ker A : Set _) =
      Set.linealitySpace (closure C) ∩ (LinearMap.ker A : Set _) := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨hzrec, hzker⟩
    have hAz : A z = 0 := by
      simpa using hzker
    by_cases hz0 : z = 0
    · subst hz0
      have hrec : (0 : EuclideanSpace Real (Fin n)) ∈ Set.recessionCone (closure C) := by
        intro x hx t ht
        simpa using hx
      have hneg : (0 : EuclideanSpace Real (Fin n)) ∈ -Set.recessionCone (closure C) := by
        change (-(0 : EuclideanSpace Real (Fin n))) ∈ Set.recessionCone (closure C)
        simpa using hrec
      have hlin : (0 : EuclideanSpace Real (Fin n)) ∈ Set.linealitySpace (closure C) :=
        ⟨hneg, hrec⟩
      exact ⟨hlin, by simp⟩
    · have hlin : z ∈ Set.linealitySpace (closure C) := hlineal z hz0 hzrec hAz
      exact ⟨hlin, hzker⟩
  · intro hz
    rcases hz with ⟨hzlin, hzker⟩
    have hzlin' :
        z ∈ (-Set.recessionCone (closure C)) ∩ Set.recessionCone (closure C) := by
      simpa [Set.linealitySpace] using hzlin
    exact ⟨hzlin'.2, hzker⟩

/-- Projecting along `lin(closure C) ∩ ker A` preserves the image of `closure C`. -/
lemma image_closure_eq_image_Lperp_inter
    {n m : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hCne : Set.Nonempty C) (hCconv : Convex Real C)
    (A : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m))
    (L0 : Submodule Real (EuclideanSpace Real (Fin n)))
    (hL0 : (L0 : Set _) = Set.linealitySpace (closure C)) :
    let L : Submodule Real (EuclideanSpace Real (Fin n)) := L0 ⊓ LinearMap.ker A
    A '' closure C = A '' ((Lᗮ : Set _) ∩ closure C) := by
  classical
  let L : Submodule Real (EuclideanSpace Real (Fin n)) := L0 ⊓ LinearMap.ker A
  have hCne' : (closure C).Nonempty := hCne.closure
  have hCconv' : Convex Real (closure C) := convex_closure_of_convex n C hCconv
  have hlineality_eq :
      Set.linealitySpace (closure C) =
        {y | Set.image (fun x => x + y) (closure C) = closure C} := by
    simpa [Set.linealitySpace] using
      (linealitySpace_eq_translation (C := closure C) hCne' hCconv')
  have hLsubset : (L : Set _) ⊆ Set.linealitySpace (closure C) := by
    intro z hz
    have hz' : z ∈ (L0 : Set _) := (Submodule.mem_inf.mp hz).1
    simpa [hL0] using hz'
  have hLker : L ≤ LinearMap.ker A := by
    intro z hz
    exact (Submodule.mem_inf.mp hz).2
  have hsubset_image :
      A '' ((Lᗮ : Set _) ∩ closure C) ⊆ A '' closure C := by
    exact Set.image_mono (by intro z hz; exact hz.2)
  have hsubset_image' : A '' closure C ⊆ A '' ((Lᗮ : Set _) ∩ closure C) := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hproj_mem : L.starProjection x ∈ L := by
      exact Submodule.starProjection_apply_mem (U := L) (x := x)
    have hproj_neg_mem : -L.starProjection x ∈ L := L.neg_mem hproj_mem
    have hproj_lineal : -L.starProjection x ∈ Set.linealitySpace (closure C) :=
      hLsubset hproj_neg_mem
    have htrans :
        Set.image (fun z => z + (-L.starProjection x)) (closure C) = closure C := by
      have hmem :
          -L.starProjection x ∈
            {y | Set.image (fun z => z + y) (closure C) = closure C} := by
        simpa [hlineality_eq] using hproj_lineal
      exact hmem
    have hxcl : x - L.starProjection x ∈ closure C := by
      have hxmem :
          x + (-L.starProjection x) ∈
            Set.image (fun z => z + (-L.starProjection x)) (closure C) := by
        exact ⟨x, hx, rfl⟩
      have hxmem' : x + (-L.starProjection x) ∈ closure C := by
        simpa [htrans] using hxmem
      simpa [sub_eq_add_neg] using hxmem'
    have hxperp : x - L.starProjection x ∈ Lᗮ := by
      exact Submodule.sub_starProjection_mem_orthogonal (K := L) (v := x)
    have hAproj : A (L.starProjection x) = 0 := by
      have hker_mem : L.starProjection x ∈ LinearMap.ker A := hLker hproj_mem
      simpa using hker_mem
    have hAeq : A (x - L.starProjection x) = A x := by
      simp [sub_eq_add_neg, hAproj]
    refine ⟨x - L.starProjection x, ?_, hAeq⟩
    exact ⟨hxperp, hxcl⟩
  have hEq : A '' closure C = A '' ((Lᗮ : Set _) ∩ closure C) :=
    Set.Subset.antisymm hsubset_image' hsubset_image
  simpa [L] using hEq

/-- The recession cone of a submodule is the submodule itself. -/
lemma recessionCone_submodule_eq {n : Nat}
    (L : Submodule Real (EuclideanSpace Real (Fin n))) :
    Set.recessionCone (L : Set (EuclideanSpace Real (Fin n))) =
      (L : Set (EuclideanSpace Real (Fin n))) := by
  ext y
  constructor
  · intro hy
    have hy' := hy (x := (0 : EuclideanSpace Real (Fin n))) (by simp)
      (t := (1 : Real)) (by norm_num)
    simpa using hy'
  · intro hy x hx t ht
    have hx' : x ∈ L := by simpa using hx
    have hy' : y ∈ L := by simpa using hy
    have hmem : x + t • y ∈ L := L.add_mem hx' (L.smul_mem t hy')
    simpa using hmem

/-- The approximation sets near a closure point of the image are closed and bounded. -/
lemma Ceps_nonempty_closed_bounded
    {n m : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hCne : Set.Nonempty C) (hCconv : Convex Real C)
    (A : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m))
    (L0 : Submodule Real (EuclideanSpace Real (Fin n)))
    (hL0 : (L0 : Set _) = Set.linealitySpace (closure C))
    (hlineal :
      ∀ z, z ≠ 0 → z ∈ Set.recessionCone (closure C) → A z = 0 →
        z ∈ Set.linealitySpace (closure C))
    {y : EuclideanSpace Real (Fin m)} (hy : y ∈ closure (A '' C))
    {ε : ℝ} (hε : 0 < ε) :
    let L : Submodule Real (EuclideanSpace Real (Fin n)) := L0 ⊓ LinearMap.ker A
    let Dε : Set (EuclideanSpace Real (Fin n)) := A ⁻¹' Metric.closedBall y ε
    let Cε : Set (EuclideanSpace Real (Fin n)) := ((Lᗮ : Set _) ∩ closure C) ∩ Dε
    Cε.Nonempty ∧ IsClosed Cε ∧ Bornology.IsBounded Cε := by
  classical
  intro L Dε Cε
  have himage : A '' closure C = A '' ((Lᗮ : Set _) ∩ closure C) := by
    simpa [L] using
      (image_closure_eq_image_Lperp_inter (hCne := hCne) (hCconv := hCconv) A L0 hL0)
  have hsubset : A '' C ⊆ A '' ((Lᗮ : Set _) ∩ closure C) := by
    intro y hy
    have : y ∈ A '' closure C := by
      rcases hy with ⟨x, hx, rfl⟩
      exact ⟨x, subset_closure hx, rfl⟩
    simpa [himage] using this
  have hy' : y ∈ closure (A '' ((Lᗮ : Set _) ∩ closure C)) :=
    (closure_mono hsubset) hy
  obtain ⟨x, hx, hdist⟩ :=
    (Metric.mem_closure_iff.mp hy') ε hε
  rcases hx with ⟨x, hx, rfl⟩
  have hxD : x ∈ Dε := by
    have hxball : A x ∈ Metric.closedBall y ε := by
      simpa [Metric.mem_closedBall, dist_comm] using (le_of_lt hdist)
    simpa [Dε] using hxball
  have hCeps_ne : Cε.Nonempty := ⟨x, ⟨hx, hxD⟩⟩
  have hLclosed : IsClosed (Lᗮ : Set (EuclideanSpace Real (Fin n))) :=
    Submodule.closed_of_finiteDimensional (Lᗮ)
  have hCclosed : IsClosed (closure C) := isClosed_closure
  have hDclosed : IsClosed Dε := by
    have hclosed : IsClosed (Metric.closedBall y ε) := Metric.isClosed_closedBall
    simpa [Dε] using hclosed.preimage A.continuous_of_finiteDimensional
  have hCeps_closed : IsClosed Cε :=
    (hLclosed.inter hCclosed).inter hDclosed
  have hLconv : Convex Real (Lᗮ : Set (EuclideanSpace Real (Fin n))) :=
    Submodule.convex _
  have hCconv' : Convex Real (closure C) := convex_closure_of_convex n C hCconv
  have hDconv : Convex Real Dε := by
    have hconv : Convex Real (Metric.closedBall y ε) := convex_closedBall y ε
    simpa [Dε] using hconv.linear_preimage A
  have hCeps_conv : Convex Real Cε :=
    (hLconv.inter hCconv').inter hDconv
  have hDne : Dε.Nonempty := by
    rcases hCeps_ne with ⟨x, hx⟩
    exact ⟨x, hx.2⟩
  have hCDne : (closure C ∩ Dε).Nonempty := by
    rcases hCeps_ne with ⟨x, hx⟩
    exact ⟨x, hx.1.2, hx.2⟩
  have hrec_ball : Set.recessionCone (Metric.closedBall y ε) = {0} := by
    have hball_ne : (Metric.closedBall y ε).Nonempty := by
      refine ⟨y, ?_⟩
      have : (0 : ℝ) ≤ ε := le_of_lt hε
      simpa [Metric.mem_closedBall] using this
    have hball_closed : IsClosed (Metric.closedBall y ε) := Metric.isClosed_closedBall
    have hball_conv : Convex Real (Metric.closedBall y ε) := convex_closedBall y ε
    have hball_bdd : Bornology.IsBounded (Metric.closedBall y ε) := Metric.isBounded_closedBall
    exact
      (bounded_iff_recessionCone_eq_singleton_zero (C := Metric.closedBall y ε)
          hball_ne hball_closed hball_conv).1 hball_bdd
  have hrec_D : Set.recessionCone Dε = (LinearMap.ker A : Set _) := by
    have hrec :
        Set.recessionCone Dε = A ⁻¹' Set.recessionCone (Metric.closedBall y ε) := by
      simpa [Dε] using
        (recessionCone_preimage_linearMap (A := A) (C := Metric.closedBall y ε)
          Metric.isClosed_closedBall (convex_closedBall y ε) (by simpa [Dε] using hDne))
    simpa [hrec_ball] using hrec
  have hrecCeps :
      Set.recessionCone Cε =
        (Lᗮ : Set _) ∩ (Set.recessionCone (closure C) ∩ (LinearMap.ker A : Set _)) := by
    have hrec1 :
        Set.recessionCone Cε =
          Set.recessionCone (Lᗮ : Set _) ∩ Set.recessionCone (closure C ∩ Dε) := by
      have hABne : ((Lᗮ : Set _) ∩ (closure C ∩ Dε)).Nonempty := by
        simpa [Cε, Set.inter_assoc] using hCeps_ne
      simpa [Cε, Set.inter_assoc] using
        (recessionCone_inter_eq (A := (Lᗮ : Set _)) (B := closure C ∩ Dε)
          hLclosed (hCclosed.inter hDclosed) hLconv (hCconv'.inter hDconv) hABne)
    have hrec2 :
        Set.recessionCone (closure C ∩ Dε) =
          Set.recessionCone (closure C) ∩ Set.recessionCone Dε := by
      exact
        recessionCone_inter_eq (A := closure C) (B := Dε)
          hCclosed hDclosed hCconv' hDconv hCDne
    calc
      Set.recessionCone Cε
          = Set.recessionCone (Lᗮ : Set _) ∩ Set.recessionCone (closure C ∩ Dε) := hrec1
      _ = (Lᗮ : Set _) ∩ (Set.recessionCone (closure C) ∩ Set.recessionCone Dε) := by
            simp [hrec2, recessionCone_submodule_eq]
      _ = (Lᗮ : Set _) ∩ (Set.recessionCone (closure C) ∩ (LinearMap.ker A : Set _)) := by
            simp [hrec_D]
  have hrecKer :
      Set.recessionCone (closure C) ∩ (LinearMap.ker A : Set _) =
        Set.linealitySpace (closure C) ∩ (LinearMap.ker A : Set _) :=
    recessionCone_inter_kernel_eq_lineality_inter_kernel (A := A) hlineal
  have hLset :
      (L : Set (EuclideanSpace Real (Fin n))) =
        Set.linealitySpace (closure C) ∩ (LinearMap.ker A : Set _) := by
    ext x
    constructor
    · intro hx
      have hx' := Submodule.mem_inf.mp hx
      have hxL0 : x ∈ (L0 : Set _) := hx'.1
      have hxker : x ∈ (LinearMap.ker A : Set _) := hx'.2
      exact ⟨by simpa [hL0] using hxL0, hxker⟩
    · intro hx
      have hxL0 : x ∈ (L0 : Set _) := by simpa [hL0] using hx.1
      exact Submodule.mem_inf.mpr ⟨hxL0, hx.2⟩
  have hrecCeps' : Set.recessionCone Cε = (Lᗮ : Set _) ∩ (L : Set _) := by
    simpa [hrecKer, hLset] using hrecCeps
  have horth :
      (Lᗮ : Set _) ∩ (L : Set _) =
        ({0} : Set (EuclideanSpace Real (Fin n))) := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ (L ⊓ Lᗮ : Submodule Real (EuclideanSpace Real (Fin n))) :=
        Submodule.mem_inf.mpr ⟨by simpa using hx.2, by simpa using hx.1⟩
      have hbot : (L ⊓ Lᗮ : Submodule Real (EuclideanSpace Real (Fin n))) = ⊥ := by
        simpa using (Submodule.inf_orthogonal_eq_bot (K := L))
      have : x ∈ (⊥ : Submodule Real (EuclideanSpace Real (Fin n))) := by
        simpa [hbot] using hx'
      simpa using this
    · intro hx
      subst hx
      simp
  have hrecCeps_zero : Set.recessionCone Cε = {0} := by
    simpa [horth] using hrecCeps'
  have hCeps_bdd : Bornology.IsBounded Cε :=
    (bounded_iff_recessionCone_eq_singleton_zero (C := Cε)
      hCeps_ne hCeps_closed hCeps_conv).2 hrecCeps_zero
  exact ⟨hCeps_ne, hCeps_closed, hCeps_bdd⟩

/-- Closure of the image equals the image of the closure under the kernel-lineality hypothesis. -/
lemma closure_image_eq_image_closure_of_kernel_lineality
    {n m : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hCne : Set.Nonempty C) (hCconv : Convex Real C)
    (A : EuclideanSpace Real (Fin n) →ₗ[Real] EuclideanSpace Real (Fin m))
    (hlineal :
      ∀ z, z ≠ 0 → z ∈ Set.recessionCone (closure C) → A z = 0 →
        z ∈ Set.linealitySpace (closure C)) :
    closure (A '' C) = A '' closure C := by
  classical
  have hsubset :
      A '' closure C ⊆ closure (A '' C) :=
    image_closure_subset_closure_image_linearMap n m C A
  have hsubset' : closure (A '' C) ⊆ A '' closure C := by
    rcases linealitySpace_isSubmodule (C := closure C)
        (hCconv := convex_closure_of_convex n C hCconv) with ⟨L0, hL0⟩
    intro y hy
    let L : Submodule Real (EuclideanSpace Real (Fin n)) := L0 ⊓ LinearMap.ker A
    let Dε : ℝ → Set (EuclideanSpace Real (Fin n)) := fun ε => A ⁻¹' Metric.closedBall y ε
    let Cε : ℝ → Set (EuclideanSpace Real (Fin n)) :=
      fun ε => ((Lᗮ : Set _) ∩ closure C) ∩ Dε ε
    have hCeps :
        ∀ ε > 0, (Cε ε).Nonempty ∧ IsClosed (Cε ε) ∧ Bornology.IsBounded (Cε ε) := by
      intro ε hε
      simpa [L, Dε, Cε] using
        (Ceps_nonempty_closed_bounded (hCne := hCne) (hCconv := hCconv) A L0 hL0 hlineal
          (y := y) hy (ε := ε) hε)
    let eps : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
    let t : ℕ → Set (EuclideanSpace Real (Fin n)) := fun k => Cε (eps k)
    have hpos : ∀ k, 0 < eps k := by
      intro k
      have hk : 0 < (k : ℝ) + 1 := by linarith
      simpa [eps] using (one_div_pos.mpr hk)
    have htn : ∀ k, (t k).Nonempty := by
      intro k
      simpa [t] using (hCeps (eps k) (hpos k)).1
    have htclosed : ∀ k, IsClosed (t k) := by
      intro k
      simpa [t] using (hCeps (eps k) (hpos k)).2.1
    have htbdd : ∀ k, Bornology.IsBounded (t k) := by
      intro k
      simpa [t] using (hCeps (eps k) (hpos k)).2.2
    have hcompact0 : IsCompact (t 0) := by
      exact Metric.isCompact_of_isClosed_isBounded (htclosed 0) (htbdd 0)
    have hmono : ∀ k, t (k + 1) ⊆ t k := by
      intro k x hx
      have hle : eps (k + 1) ≤ eps k := by
        dsimp [eps]
        have hk : 0 < (k : ℝ) + 1 := by linarith
        have hk' : (k : ℝ) + 1 ≤ (k : ℝ) + 1 + 1 := by linarith
        have hle' :
            1 / ((k : ℝ) + 1 + 1) ≤ 1 / ((k : ℝ) + 1) :=
          one_div_le_one_div_of_le hk hk'
        simpa [one_div, Nat.cast_add, Nat.cast_one, add_assoc] using hle'
      have hx' : x ∈ Cε (eps (k + 1)) := by simpa [t] using hx
      have hxD : x ∈ Dε (eps (k + 1)) := hx'.2
      have hxball : A x ∈ Metric.closedBall y (eps (k + 1)) := by
        simpa [Dε] using hxD
      have hxball' : A x ∈ Metric.closedBall y (eps k) := by
        have hxball' : dist (A x) y ≤ eps (k + 1) := by
          simpa [Metric.mem_closedBall] using hxball
        have hxball'' : dist (A x) y ≤ eps k := le_trans hxball' hle
        simpa [Metric.mem_closedBall] using hxball''
      have hxD' : x ∈ Dε (eps k) := by
        simpa [Dε] using hxball'
      exact ⟨hx'.1, hxD'⟩
    have hinter : (⋂ k, t k).Nonempty :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t hmono htn hcompact0
        htclosed
    rcases hinter with ⟨x, hx⟩
    have hx0 : x ∈ t 0 := by
      exact (Set.mem_iInter.mp hx 0)
    have hxC : x ∈ closure C := by
      have hx' : x ∈ (Lᗮ : Set _) ∩ closure C := hx0.1
      exact hx'.2
    have hdist : ∀ k, dist (A x) y ≤ eps k := by
      intro k
      have hxk : x ∈ t k := by
        exact (Set.mem_iInter.mp hx k)
      have hxD : x ∈ Dε (eps k) := hxk.2
      have hxball : A x ∈ Metric.closedBall y (eps k) := by
        simpa [Dε] using hxD
      simpa [Metric.mem_closedBall] using hxball
    have hdist_le0 : dist (A x) y ≤ 0 := by
      have hlim :
          Filter.Tendsto eps Filter.atTop (𝓝 (0 : ℝ)) := by
        simpa [eps] using
          (tendsto_one_div_add_atTop_nhds_zero_nat :
            Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 (0 : ℝ)))
      exact
        le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Filter.Eventually.of_forall hdist)
    have hdist_eq : dist (A x) y = 0 :=
      le_antisymm hdist_le0 dist_nonneg
    have hxy : A x = y := by
      simpa using (dist_eq_zero.mp hdist_eq)
    exact ⟨x, hxC, hxy⟩
  exact Set.Subset.antisymm hsubset' hsubset

/-- The recession cone of a convex set is closed under addition. -/
lemma recessionCone_add_mem {n : Nat} {C : Set (EuclideanSpace Real (Fin n))}
    (hCconv : Convex Real C) {y₁ y₂ : EuclideanSpace Real (Fin n)}
    (hy₁ : y₁ ∈ Set.recessionCone C) (hy₂ : y₂ ∈ Set.recessionCone C) :
    y₁ + y₂ ∈ Set.recessionCone C := by
  have hconv : Convex Real (Set.recessionCone C) := recessionCone_convex (C := C) hCconv
  have hhalf :
      (1 / 2 : ℝ) • y₁ + (1 / 2 : ℝ) • y₂ ∈ Set.recessionCone C := by
    have hsum : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by ring
    exact hconv hy₁ hy₂ (by norm_num) (by norm_num) hsum
  have hsum :
      (2 : ℝ) • ((1 / 2 : ℝ) • y₁ + (1 / 2 : ℝ) • y₂) = y₁ + y₂ := by
    simp [smul_add, smul_smul]
  have hsum_mem :
      (2 : ℝ) • ((1 / 2 : ℝ) • y₁ + (1 / 2 : ℝ) • y₂) ∈ Set.recessionCone C :=
    recessionCone_smul_pos (C := C) hhalf (by norm_num)
  simpa [hsum] using hsum_mem

end Section09
end Chap02
