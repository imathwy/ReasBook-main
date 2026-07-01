/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xinyi Guo, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part1

noncomputable section
open scoped Topology

section Chap02
section Section07

/-- The `α`-sublevel of the liminf is the intersection of closed `μ`-sublevel sets above `α`. -/
lemma sublevel_liminf_eq_iInter_closure_sublevel {n : Nat}
    (f : (Fin n → Real) → EReal) (α : Real) :
    {x | Filter.liminf (fun y : Fin n → Real => f y) (𝓝 x) ≤ (α : EReal)} =
      ⋂ (μ : {μ : Real // μ > α}),
        closure {x | f x ≤ ((μ : Real) : EReal)} := by
  ext x
  constructor
  · intro hx
    exact liminf_le_mem_iInter_closure_sublevel (f := f) (α := α) (x := x) hx
  · intro hx
    exact liminf_le_of_mem_iInter_closure_sublevel (f := f) (α := α) (x := x) hx

/-- Text 7.0.11: For each `α ∈ ℝ`,
`{x | (convexFunctionClosure f) x ≤ α} = ⋂ (μ > α), closure {x | f x ≤ μ}`. -/
theorem sublevel_convexFunctionClosure_eq_iInter_closure_sublevel {n : Nat}
    (f : (Fin n → Real) → EReal) (α : Real) (hbot : ∀ x, f x ≠ (⊥ : EReal)) :
    {x | convexFunctionClosure f x ≤ (α : EReal)} =
      ⋂ (μ : {μ : Real // μ > α}),
        closure {x | f x ≤ ((μ : Real) : EReal)} := by
  have hliminf := (epigraph_convexFunctionClosure_eq_closure_epigraph (f := f) hbot).2
  ext x
  constructor
  · intro hx
    have hx' :
        Filter.liminf (fun y : Fin n → Real => f y) (𝓝 x) ≤ (α : EReal) := by
      simpa [hliminf x] using hx
    exact liminf_le_mem_iInter_closure_sublevel (f := f) (α := α) (x := x) hx'
  · intro hx
    have hx' :
        Filter.liminf (fun y : Fin n → Real => f y) (𝓝 x) ≤ (α : EReal) :=
      liminf_le_of_mem_iInter_closure_sublevel (f := f) (α := α) (x := x) hx
    simpa [hliminf x] using hx'

/-- The closure of a function is pointwise below the function itself. -/
lemma convexFunctionClosure_le_self {n : Nat} (f : (Fin n → Real) → EReal) :
    convexFunctionClosure f ≤ f := by
  classical
  by_cases hbot : ∀ x, f x ≠ (⊥ : EReal)
  · have hspec :=
      Classical.choose_spec (exists_lowerSemicontinuousHull (n := n) f)
    have hle : lowerSemicontinuousHull f ≤ f := by
      simpa [lowerSemicontinuousHull] using hspec.2.1
    simpa [convexFunctionClosure, hbot] using hle
  · push_neg at hbot
    have hcl :
        convexFunctionClosure f = (fun _ => (⊥ : EReal)) :=
      convexFunctionClosure_eq_bot_of_exists_bot (f := f) hbot
    intro x
    simp [hcl]

/-- The closure operator is monotone with respect to the pointwise order. -/
lemma convexFunctionClosure_mono {n : Nat} {f1 f2 : (Fin n → Real) → EReal}
    (h12 : f1 ≤ f2) : convexFunctionClosure f1 ≤ convexFunctionClosure f2 := by
  classical
  by_cases hbot1 : ∀ x, f1 x ≠ (⊥ : EReal)
  · have hbot2 : ∀ x, f2 x ≠ (⊥ : EReal) := by
      intro x hx
      have hle : f1 x ≤ (⊥ : EReal) := by simpa [hx] using h12 x
      have hbot1x : f1 x = (⊥ : EReal) := (le_bot_iff).1 hle
      exact hbot1 x hbot1x
    have hspec1 :=
      Classical.choose_spec (exists_lowerSemicontinuousHull (n := n) f1)
    have hspec2 :=
      Classical.choose_spec (exists_lowerSemicontinuousHull (n := n) f2)
    have hls1 : LowerSemicontinuous (lowerSemicontinuousHull f1) := by
      simpa [lowerSemicontinuousHull] using hspec1.1
    have hle1 : lowerSemicontinuousHull f1 ≤ f1 := by
      simpa [lowerSemicontinuousHull] using hspec1.2.1
    have hle1' : lowerSemicontinuousHull f1 ≤ f2 := by
      intro x
      exact le_trans (hle1 x) (h12 x)
    have hle12 : lowerSemicontinuousHull f1 ≤ lowerSemicontinuousHull f2 := by
      have hmax2 :
          ∀ h : (Fin n → Real) → EReal, LowerSemicontinuous h → h ≤ f2 →
            h ≤ lowerSemicontinuousHull f2 := by
        intro h hlsc hle
        simpa [lowerSemicontinuousHull] using hspec2.2.2 h hlsc hle
      exact hmax2 _ hls1 hle1'
    simpa [convexFunctionClosure, hbot1, hbot2] using hle12
  · push_neg at hbot1
    have hcl1 :
        convexFunctionClosure f1 = (fun _ => (⊥ : EReal)) :=
      convexFunctionClosure_eq_bot_of_exists_bot (f := f1) hbot1
    intro x
    simp [hcl1]

/-- The infimum of a function equals the infimum of its closure. -/
lemma iInf_convexFunctionClosure_eq {n : Nat} (f : (Fin n → Real) → EReal) :
    iInf (fun x => f x) = iInf (fun x => convexFunctionClosure f x) := by
  classical
  by_cases hbot : ∀ x, f x ≠ (⊥ : EReal)
  · have hspec :=
      Classical.choose_spec (exists_lowerSemicontinuousHull (n := n) f)
    have hmax :
        ∀ h : (Fin n → Real) → EReal, LowerSemicontinuous h → h ≤ f →
          h ≤ lowerSemicontinuousHull f := by
      intro h hlsc hle
      simpa [lowerSemicontinuousHull] using hspec.2.2 h hlsc hle
    have hconst_lsc :
        LowerSemicontinuous
          (fun _ : (Fin n → Real) => iInf (fun x => f x)) := by
      simpa using
        (lowerSemicontinuous_const :
          LowerSemicontinuous (fun _ : (Fin n → Real) => iInf (fun x => f x)))
    have hconst_le : (fun _ : (Fin n → Real) => iInf (fun x => f x)) ≤ f := by
      intro x
      exact iInf_le (fun x => f x) x
    have hconst_le_hull :
        (fun _ : (Fin n → Real) => iInf (fun x => f x)) ≤
          lowerSemicontinuousHull f :=
      hmax _ hconst_lsc hconst_le
    have hle_closure : iInf (fun x => convexFunctionClosure f x) ≤ iInf (fun x => f x) :=
      iInf_mono (convexFunctionClosure_le_self (f := f))
    have hle_inf : iInf (fun x => f x) ≤ iInf (fun x => convexFunctionClosure f x) := by
      refine le_iInf ?_
      intro x
      have hx : iInf (fun x => f x) ≤ lowerSemicontinuousHull f x :=
        hconst_le_hull x
      simpa [convexFunctionClosure, hbot] using hx
    exact le_antisymm hle_inf hle_closure
  · push_neg at hbot
    rcases hbot with ⟨x, hx⟩
    have hcl :
        convexFunctionClosure f = (fun _ => (⊥ : EReal)) :=
      convexFunctionClosure_eq_bot_of_exists_bot (f := f) ⟨x, hx⟩
    have hInf_le : iInf (fun x => f x) ≤ (⊥ : EReal) := by
      simpa [hx] using (iInf_le (fun x => f x) x)
    have hInf_eq : iInf (fun x => f x) = (⊥ : EReal) :=
      le_antisymm hInf_le bot_le
    calc
      iInf (fun x => f x) = (⊥ : EReal) := hInf_eq
      _ = iInf (fun x => convexFunctionClosure f x) := by
        simp [hcl]

/-- Text 7.0.12: For any extended-real-valued function `f : ℝ^n → [-∞, +∞]`,
one has `cl f ≤ f`. Moreover, if `f₁ ≤ f₂`, then `cl f₁ ≤ cl f₂`.
In addition, `inf_{x ∈ ℝ^n} f x = inf_{x ∈ ℝ^n} (cl f) x`. Here `cl f`
is `convexFunctionClosure f`. -/
theorem convexFunctionClosure_properties {n : Nat} :
    (∀ f : (Fin n → Real) → EReal, convexFunctionClosure f ≤ f) ∧
    (∀ f1 f2 : (Fin n → Real) → EReal, f1 ≤ f2 →
        convexFunctionClosure f1 ≤ convexFunctionClosure f2) ∧
      (∀ f : (Fin n → Real) → EReal,
        iInf (fun x => f x) = iInf (fun x => convexFunctionClosure f x)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f
    exact convexFunctionClosure_le_self (f := f)
  · intro f1 f2 h12
    exact convexFunctionClosure_mono (f1 := f1) (f2 := f2) h12
  · intro f
    exact iInf_convexFunctionClosure_eq (f := f)

/-- Points with positive coordinate appear frequently near the origin. -/
lemma frequently_pos_coord_nhds_zero :
    ∃ᶠ y in 𝓝 (0 : Fin 1 → Real), 0 < y 0 := by
  have hclosure :
      (0 : Fin 1 → Real) ∈ closure {y : Fin 1 → Real | 0 < y 0} := by
    refine (mem_closure_iff_seq_limit).2 ?_
    refine ⟨(fun n : ℕ => fun _ : Fin 1 => (1 : Real) / ((n : Real) + 1)), ?_, ?_⟩
    · intro n
      have hpos' : (0 : Real) < (n : Real) + 1 := by
        have hnonneg : (0 : Real) ≤ (n : Real) := by
          exact_mod_cast (Nat.zero_le n)
        linarith
      have hpos : 0 < (1 : Real) / ((n : Real) + 1) := (one_div_pos).2 hpos'
      simpa using hpos
    · refine (tendsto_pi_nhds).2 ?_
      intro i
      fin_cases i
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  exact (mem_closure_iff_frequently).1 hclosure

/-- At a point with positive coordinate, the liminf of the step function is `0`. -/
lemma liminf_example_origin_pos {x : Fin 1 → Real} (hx : 0 < x 0) :
    Filter.liminf (fun y : Fin 1 → Real =>
      if 0 < y 0 then (0 : EReal) else (⊤ : EReal)) (𝓝 x) = (0 : EReal) := by
  have hopen : IsOpen {y : Fin 1 → Real | 0 < y 0} := by
    simpa using (isOpen_lt (continuous_const) (continuous_apply 0))
  have hmem : {y : Fin 1 → Real | 0 < y 0} ∈ 𝓝 x := by
    exact hopen.mem_nhds hx
  have hEq :
      ∀ᶠ y in 𝓝 x,
        (if 0 < y 0 then (0 : EReal) else (⊤ : EReal)) = (0 : EReal) := by
    refine Filter.mem_of_superset hmem ?_
    intro y hy
    simp [hy]
  have hlim :
      Filter.liminf (fun y : Fin 1 → Real =>
        if 0 < y 0 then (0 : EReal) else (⊤ : EReal)) (𝓝 x) =
        Filter.liminf (fun _ : Fin 1 → Real => (0 : EReal)) (𝓝 x) :=
    Filter.liminf_congr hEq
  simp [hlim]

/-- At a point with negative coordinate, the liminf of the step function is `⊤`. -/
lemma liminf_example_origin_neg {x : Fin 1 → Real} (hx : x 0 < 0) :
    Filter.liminf (fun y : Fin 1 → Real =>
      if 0 < y 0 then (0 : EReal) else (⊤ : EReal)) (𝓝 x) = (⊤ : EReal) := by
  have hopen : IsOpen {y : Fin 1 → Real | y 0 < 0} := by
    simpa using (isOpen_lt (continuous_apply 0) (continuous_const))
  have hmem : {y : Fin 1 → Real | y 0 < 0} ∈ 𝓝 x := by
    exact hopen.mem_nhds hx
  have hEq :
      ∀ᶠ y in 𝓝 x,
        (if 0 < y 0 then (0 : EReal) else (⊤ : EReal)) = (⊤ : EReal) := by
    refine Filter.mem_of_superset hmem ?_
    intro y hy
    have hnot : ¬ 0 < y 0 := by
      exact not_lt_of_gt hy
    change (if 0 < y 0 then (0 : EReal) else (⊤ : EReal)) = (⊤ : EReal)
    simp [hnot]
  have hlim :
      Filter.liminf (fun y : Fin 1 → Real =>
        if 0 < y 0 then (0 : EReal) else (⊤ : EReal)) (𝓝 x) =
        Filter.liminf (fun _ : Fin 1 → Real => (⊤ : EReal)) (𝓝 x) :=
    Filter.liminf_congr hEq
  simp [hlim]

/-- At the origin, the liminf of the step function is `0`. -/
lemma liminf_example_origin_zero :
    Filter.liminf (fun y : Fin 1 → Real =>
      if 0 < y 0 then (0 : EReal) else (⊤ : EReal)) (𝓝 (0 : Fin 1 → Real)) =
      (0 : EReal) := by
  have hle :
      (0 : EReal) ≤ Filter.liminf (fun y : Fin 1 → Real =>
        if 0 < y 0 then (0 : EReal) else (⊤ : EReal)) (𝓝 (0 : Fin 1 → Real)) := by
    refine (Filter.le_liminf_of_le (f := 𝓝 (0 : Fin 1 → Real)) (a := (0 : EReal))
      (u := fun y : Fin 1 → Real =>
        if 0 < y 0 then (0 : EReal) else (⊤ : EReal)) (h := ?_))
    refine Filter.Eventually.of_forall ?_
    intro y
    by_cases hy : 0 < y 0 <;> simp [hy]
  have hfreq_pos :
      ∃ᶠ y in 𝓝 (0 : Fin 1 → Real), 0 < y 0 :=
    frequently_pos_coord_nhds_zero
  have hfreq :
      ∃ᶠ y in 𝓝 (0 : Fin 1 → Real),
        (if 0 < y 0 then (0 : EReal) else (⊤ : EReal)) ≤ (0 : EReal) := by
    exact hfreq_pos.mono (fun y hy => by simp [hy])
  have hge :
      Filter.liminf (fun y : Fin 1 → Real =>
        if 0 < y 0 then (0 : EReal) else (⊤ : EReal)) (𝓝 (0 : Fin 1 → Real)) ≤
        (0 : EReal) :=
    Filter.liminf_le_of_frequently_le (f := 𝓝 (0 : Fin 1 → Real))
      (u := fun y : Fin 1 → Real =>
        if 0 < y 0 then (0 : EReal) else (⊤ : EReal))
      (b := (0 : EReal)) hfreq
  exact le_antisymm hge hle

/-- Text 7.0.13: If `f : ℝ → [-∞, +∞]` is defined by `f(x) = 0` for `x > 0` and
`f(x) = +∞` for `x ≤ 0`, then `cl f` agrees with `f` except at the origin, where
`(cl f)(0) = 0` rather than `+∞`. -/
theorem convexFunctionClosure_example_origin :
    convexFunctionClosure (fun x : Fin 1 → Real =>
      if 0 < x 0 then (0 : EReal) else (⊤ : EReal)) =
      fun x => if x 0 < 0 then (⊤ : EReal) else (0 : EReal) := by
  classical
  let f : (Fin 1 → Real) → EReal :=
    fun x => if 0 < x 0 then (0 : EReal) else (⊤ : EReal)
  have hbot : ∀ x, f x ≠ (⊥ : EReal) := by
    intro x
    by_cases hx : 0 < x 0 <;> simp [f, hx]
  have hliminf := (epigraph_convexFunctionClosure_eq_closure_epigraph (f := f) hbot).2
  funext x
  by_cases hxneg : x 0 < 0
  · have hlim :
        Filter.liminf (fun y : Fin 1 → Real =>
          if 0 < y 0 then (0 : EReal) else (⊤ : EReal)) (𝓝 x) = (⊤ : EReal) :=
      liminf_example_origin_neg (x := x) hxneg
    simp [f, hxneg, hliminf x, hlim]
  · by_cases hxpos : 0 < x 0
    · have hlim :
          Filter.liminf (fun y : Fin 1 → Real =>
            if 0 < y 0 then (0 : EReal) else (⊤ : EReal)) (𝓝 x) = (0 : EReal) :=
        liminf_example_origin_pos (x := x) hxpos
      simp [f, hxneg, hliminf x, hlim]
    · have hxge : 0 ≤ x 0 := le_of_not_gt hxneg
      have hxle : x 0 ≤ 0 := le_of_not_gt hxpos
      have hxzero : x 0 = 0 := le_antisymm hxle hxge
      have hx : x = 0 := by
        ext i
        fin_cases i
        simp [hxzero]
      have hlim :
          Filter.liminf (fun y : Fin 1 → Real =>
            if 0 < y 0 then (0 : EReal) else (⊤ : EReal)) (𝓝 x) = (0 : EReal) := by
        simpa [hx] using liminf_example_origin_zero
      simp [f, hxneg, hliminf x, hlim]

/-- Points in the closure of the unit ball are frequently in the unit ball. -/
lemma frequently_mem_ball_of_mem_closure {x : Fin 2 → Real}
    (hx : x ∈ closure (Metric.ball (0 : Fin 2 → Real) 1)) :
    ∃ᶠ y in 𝓝 x, y ∈ Metric.ball (0 : Fin 2 → Real) 1 := by
  simpa using (mem_closure_iff_frequently.1 hx)

/-- Points outside the closure of the unit ball have a neighborhood outside it. -/
lemma eventually_not_mem_closure_of_not_mem {x : Fin 2 → Real}
    (hx : x ∉ closure (Metric.ball (0 : Fin 2 → Real) 1)) :
    ∀ᶠ y in 𝓝 x, y ∉ closure (Metric.ball (0 : Fin 2 → Real) 1) := by
  have hopen : IsOpen ((closure (Metric.ball (0 : Fin 2 → Real) 1))ᶜ) :=
    isClosed_closure.isOpen_compl
  have hxmem : x ∈ (closure (Metric.ball (0 : Fin 2 → Real) 1))ᶜ := by
    simpa using hx
  have hmem : (closure (Metric.ball (0 : Fin 2 → Real) 1))ᶜ ∈ 𝓝 x :=
    hopen.mem_nhds hxmem
  refine Filter.mem_of_superset hmem ?_
  intro y hy
  simpa using hy

/-- On the closure of the unit ball, the liminf of `f` is `0`. -/
lemma liminf_unitDisk_closure_eq_zero
    (f : (Fin 2 → Real) → EReal)
    (h0 : ∀ x, x ∈ Metric.ball (0 : Fin 2 → Real) 1 → f x = (0 : EReal))
    (hnonneg : ∀ x, (0 : EReal) ≤ f x) {x : Fin 2 → Real}
    (hx : x ∈ closure (Metric.ball (0 : Fin 2 → Real) 1)) :
    Filter.liminf (fun y : Fin 2 → Real => f y) (𝓝 x) = (0 : EReal) := by
  have hle :
      (0 : EReal) ≤ Filter.liminf (fun y : Fin 2 → Real => f y) (𝓝 x) := by
    refine (Filter.le_liminf_of_le (f := 𝓝 x) (a := (0 : EReal))
      (u := fun y : Fin 2 → Real => f y) (h := ?_))
    exact Filter.Eventually.of_forall (fun y => hnonneg y)
  have hfreq_mem :
      ∃ᶠ y in 𝓝 x, y ∈ Metric.ball (0 : Fin 2 → Real) 1 :=
    frequently_mem_ball_of_mem_closure (x := x) hx
  have hfreq :
      ∃ᶠ y in 𝓝 x, f y ≤ (0 : EReal) := by
    refine hfreq_mem.mono ?_
    intro y hy
    have hfy : f y = (0 : EReal) := h0 y hy
    simp [hfy]
  have hge :
      Filter.liminf (fun y : Fin 2 → Real => f y) (𝓝 x) ≤ (0 : EReal) :=
    Filter.liminf_le_of_frequently_le (f := 𝓝 x)
      (u := fun y : Fin 2 → Real => f y) (b := (0 : EReal)) hfreq
  exact le_antisymm hge hle

/-- Outside the closure of the unit ball, the liminf of `f` is `⊤`. -/
lemma liminf_unitDisk_outside_eq_top
    (f : (Fin 2 → Real) → EReal)
    (hInf : ∀ x, x ∉ closure (Metric.ball (0 : Fin 2 → Real) 1) →
      f x = (⊤ : EReal)) {x : Fin 2 → Real}
    (hx : x ∉ closure (Metric.ball (0 : Fin 2 → Real) 1)) :
    Filter.liminf (fun y : Fin 2 → Real => f y) (𝓝 x) = (⊤ : EReal) := by
  have hEq : ∀ᶠ y in 𝓝 x, f y = (⊤ : EReal) := by
    have hmem :
        ∀ᶠ y in 𝓝 x, y ∉ closure (Metric.ball (0 : Fin 2 → Real) 1) :=
      eventually_not_mem_closure_of_not_mem (x := x) hx
    refine hmem.mono ?_
    intro y hy
    simp [hInf y hy]
  have hlim :
      Filter.liminf (fun y : Fin 2 → Real => f y) (𝓝 x) =
        Filter.liminf (fun _ : Fin 2 → Real => (⊤ : EReal)) (𝓝 x) :=
    Filter.liminf_congr hEq
  simp [hlim]

/-- Text 7.0.14: If `C` is the unit disk in `ℝ^2` and `f(x) = 0` for `x ∈ C` while
`f(x) = +∞` for `x ∉ C` (with arbitrary boundary values), then `cl f(x) = 0` for all
`x ∈ cl C` and `+∞` elsewhere. -/
theorem convexFunctionClosure_example_unitDisk
    (f : (Fin 2 → Real) → EReal)
    (h0 : ∀ x, x ∈ Metric.ball (0 : Fin 2 → Real) 1 → f x = (0 : EReal))
    (hInf : ∀ x, x ∉ closure (Metric.ball (0 : Fin 2 → Real) 1) → f x = (⊤ : EReal))
    (hnonneg : ∀ x, (0 : EReal) ≤ f x) :
    (∀ x, x ∈ closure (Metric.ball (0 : Fin 2 → Real) 1) →
        convexFunctionClosure f x = (0 : EReal)) ∧
      (∀ x, x ∉ closure (Metric.ball (0 : Fin 2 → Real) 1) →
        convexFunctionClosure f x = (⊤ : EReal)) := by
  classical
  have hbot : ∀ x, f x ≠ (⊥ : EReal) := by
    intro x hx
    have hle : (0 : EReal) ≤ (⊥ : EReal) := by
      simpa [hx] using hnonneg x
    have hzero : (0 : EReal) = (⊥ : EReal) := (le_bot_iff).1 hle
    exact (EReal.zero_ne_bot hzero)
  have hliminf := (epigraph_convexFunctionClosure_eq_closure_epigraph (f := f) hbot).2
  refine ⟨?_, ?_⟩
  · intro x hx
    have hlim :
        Filter.liminf (fun y : Fin 2 → Real => f y) (𝓝 x) = (0 : EReal) :=
      liminf_unitDisk_closure_eq_zero (f := f) h0 hnonneg (x := x) hx
    simp [hliminf x, hlim]
  · intro x hx
    have hlim :
        Filter.liminf (fun y : Fin 2 → Real => f y) (𝓝 x) = (⊤ : EReal) :=
      liminf_unitDisk_outside_eq_top (f := f) hInf (x := x) hx
    simp [hliminf x, hlim]

end Section07
end Chap02
