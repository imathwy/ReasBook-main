/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Changyu Zou, Yunxi Duan, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section18_part8

open scoped Pointwise Topology RealInnerProductSpace
open Filter
open PiLp

section Chap04
section Section18

noncomputable section

variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]

set_option maxHeartbeats 600000

/-- A closed convex set with no lines and no extreme points must be empty. -/
lemma closedConvex_eq_empty_of_extremePoints_eq_empty {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hNoLines :
      ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧ y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C)
    (hExt : C.extremePoints ℝ = ∅) :
    C = ∅ := by
  classical
  have hEq :=
    closedConvex_eq_mixedConvexHull_extremePoints_extremeDirections (n := n) (C := C) hCclosed
      hCconv hNoLines
  calc
    C =
        mixedConvexHull (n := n) (C.extremePoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := hEq
    _ =
        mixedConvexHull (n := n) (∅ : Set (Fin n → ℝ))
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := by
          simp [hExt]
    _ = (∅ : Set (Fin n → ℝ)) := by
          simpa using
            (mixedConvexHull_empty_points (n := n)
              ({d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}))

/-- Corollary 18.5.3. A nonempty closed convex set containing no lines has an extreme point. -/
theorem extremePoints_nonempty_of_closedConvex_noLines {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hNoLines :
      ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧ y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C)
    (hCne : C.Nonempty) :
    (C.extremePoints ℝ).Nonempty := by
  classical
  by_contra hExtne
  have hExt : C.extremePoints ℝ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hExtne ⟨x, hx⟩
  have hCeq :
      C = ∅ :=
    closedConvex_eq_empty_of_extremePoints_eq_empty (n := n) (C := C) hCclosed hCconv hNoLines
      hExt
  exact hCne.ne_empty hCeq

/-- The closed unit disk in the `xy`-plane. -/
def text18_5_2_C1 : Set (EuclideanSpace ℝ (Fin 3)) :=
  {v | v 2 = 0 ∧ (v 0) ^ 2 + (v 1) ^ 2 ≤ 1}

/-- The vertical segment through `(1,0,0)` of length `2`. -/
def text18_5_2_C2 : Set (EuclideanSpace ℝ (Fin 3)) :=
  {v | v 0 = 1 ∧ v 1 = 0 ∧ |v 2| ≤ 1}

/-- The base set for the convex hull. -/
def text18_5_2_S : Set (EuclideanSpace ℝ (Fin 3)) :=
  text18_5_2_C1 ∪ text18_5_2_C2

/-- The convex closed hull used in the construction. -/
def text18_5_2_C : Set (EuclideanSpace ℝ (Fin 3)) :=
  closedConvexHull ℝ text18_5_2_S

/-- The midpoint of the vertical segment. -/
def text18_5_2_p : EuclideanSpace ℝ (Fin 3) :=
  (WithLp.toLp (p := 2) (V := Fin 3 → ℝ) ![(1 : ℝ), 0, 0])

/-- The top endpoint of the vertical segment. -/
def text18_5_2_zTop : EuclideanSpace ℝ (Fin 3) :=
  (WithLp.toLp (p := 2) (V := Fin 3 → ℝ) ![(1 : ℝ), 0, 1])

/-- The bottom endpoint of the vertical segment. -/
def text18_5_2_zBot : EuclideanSpace ℝ (Fin 3) :=
  (WithLp.toLp (p := 2) (V := Fin 3 → ℝ) ![(1 : ℝ), 0, (-1 : ℝ)])

/-- The auxiliary scalar sequence `yₙ = 1/(n+2)`. -/
def text18_5_2_y (n : ℕ) : ℝ :=
  (1 : ℝ) / ((n : ℝ) + 2)

/-- The auxiliary sequence of points on the circle in the `xy`-plane. -/
def text18_5_2_q (n : ℕ) : EuclideanSpace ℝ (Fin 3) :=
  (WithLp.toLp (p := 2) (V := Fin 3 → ℝ)
    ![Real.sqrt (1 - (text18_5_2_y n) ^ 2), text18_5_2_y n, (0 : ℝ)])

/-- The auxiliary sequence `yₙ` is positive. -/
lemma text18_5_2_y_pos (n : ℕ) : 0 < text18_5_2_y n := by
  have hpos : 0 < (n : ℝ) + 2 := by nlinarith
  simpa [text18_5_2_y] using (one_div_pos.mpr hpos)

/-- The auxiliary sequence satisfies `yₙ^2 < 1`. -/
lemma text18_5_2_y_sq_lt_one (n : ℕ) : (text18_5_2_y n) ^ 2 < 1 := by
  have hge : (2 : ℝ) ≤ (n : ℝ) + 2 := by nlinarith
  have hle : text18_5_2_y n ≤ (1 / 2 : ℝ) := by
    -- `n+2 ≥ 2` implies `1/(n+2) ≤ 1/2`
    have hle' : (1 : ℝ) / ((n : ℝ) + 2) ≤ (1 : ℝ) / 2 :=
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hge
    simpa [text18_5_2_y] using hle'
  have hsq : (text18_5_2_y n) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    nlinarith [hle, text18_5_2_y_pos n]
  have hsq_lt : (1 / 2 : ℝ) ^ 2 < 1 := by norm_num
  exact lt_of_le_of_lt hsq hsq_lt

/-- The point `qₙ` lies on the boundary circle of `C1`. -/
lemma text18_5_2_q_mem_C1 (n : ℕ) : text18_5_2_q n ∈ text18_5_2_C1 := by
  have h0 : 0 ≤ 1 - (text18_5_2_y n) ^ 2 := by
    nlinarith [le_of_lt (text18_5_2_y_sq_lt_one n)]
  have hsqrt :
      (Real.sqrt (1 - (text18_5_2_y n) ^ 2)) ^ 2 = 1 - (text18_5_2_y n) ^ 2 := by
    simpa [pow_two] using Real.sq_sqrt h0
  refine ⟨?_, ?_⟩
  · simp [text18_5_2_q, toLp_apply]
  ·
    have hsum :
        (Real.sqrt (1 - (text18_5_2_y n) ^ 2)) ^ 2 + (text18_5_2_y n) ^ 2 ≤ 1 := by
      nlinarith [hsqrt]
    simpa [text18_5_2_q, toLp_apply] using hsum

/-- Expand the squared norm in `ℝ³` as the sum of squares of coordinates. -/
lemma text18_5_2_norm_sq_eq (v : EuclideanSpace ℝ (Fin 3)) :
    ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 := by
  -- `EuclideanSpace.norm_sq_eq` gives a sum over `Fin 3`, then we expand it.
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]

/-- The disk `C1` is contained in the closed unit ball. -/
lemma text18_5_2_C1_subset_closedBall_one :
    text18_5_2_C1 ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  intro v hv
  rcases hv with ⟨hv2, hxy⟩
  have hnormsq : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 :=
    text18_5_2_norm_sq_eq v
  have hnormsq' : ‖v‖ ^ 2 ≤ 1 := by
    nlinarith [hnormsq, hv2, hxy]
  have hnorm : ‖v‖ ≤ 1 := by
    have hnonneg : 0 ≤ ‖v‖ := norm_nonneg _
    nlinarith
  simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm

/-- The disk `C1` is contained in a closed ball of radius `2`. -/
lemma text18_5_2_C1_subset_closedBall :
    text18_5_2_C1 ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2 := by
  intro v hv
  rcases hv with ⟨hv2, hxy⟩
  have hnormsq : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 :=
    text18_5_2_norm_sq_eq v
  have hnormsq' : ‖v‖ ^ 2 ≤ 4 := by
    -- use `v 2 = 0` and the disk inequality
    nlinarith [hnormsq, hv2, hxy]
  have hnorm : ‖v‖ ≤ 2 := by
    have hnonneg : 0 ≤ ‖v‖ := norm_nonneg _
    nlinarith
  simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm

/-- The segment `C2` is contained in a closed ball of radius `2`. -/
lemma text18_5_2_C2_subset_closedBall :
    text18_5_2_C2 ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2 := by
  intro v hv
  rcases hv with ⟨hv0, hv1, hv2⟩
  have hnormsq : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 :=
    text18_5_2_norm_sq_eq v
  have hnormsq' : ‖v‖ ^ 2 ≤ 4 := by
    -- bound each coordinate using `v 0 = 1`, `v 1 = 0`, and `|v 2| ≤ 1`
    have h2 : (v 2) ^ 2 ≤ 1 := by
      have h2' : |v 2| ^ 2 ≤ 1 := by
        have hnonneg : 0 ≤ |v 2| := abs_nonneg _
        nlinarith [hv2, hnonneg]
      simpa [pow_two, abs_mul_self] using h2'
    nlinarith [hnormsq, hv0, hv1, h2]
  have hnorm : ‖v‖ ≤ 2 := by
    have hnonneg : 0 ≤ ‖v‖ := norm_nonneg _
    nlinarith
  simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm

/-- Basic properties of the convex closed hull `C`. -/
lemma text18_5_2_C_def_and_basic_props :
    IsClosed text18_5_2_C ∧ Bornology.IsBounded text18_5_2_C ∧ Convex ℝ text18_5_2_C := by
  refine ⟨isClosed_closedConvexHull, ?_, convex_closedConvexHull⟩
  have hC1 : Bornology.IsBounded text18_5_2_C1 := by
    exact (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin 3))) (r := 2)).subset
      text18_5_2_C1_subset_closedBall
  have hC2 : Bornology.IsBounded text18_5_2_C2 := by
    exact (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin 3))) (r := 2)).subset
      text18_5_2_C2_subset_closedBall
  have hS : Bornology.IsBounded text18_5_2_S := hC1.union hC2
  have hHull : Bornology.IsBounded (convexHull ℝ text18_5_2_S) := by
    simpa using (isBounded_convexHull (s := text18_5_2_S)).2 hS
  have hCeq : text18_5_2_C = closure (convexHull ℝ text18_5_2_S) := by
    simpa [text18_5_2_C] using
      (closedConvexHull_eq_closure_convexHull (𝕜 := ℝ) (s := text18_5_2_S))
  simpa [hCeq] using hHull.closure

/-- The midpoint of the vertical segment is not an extreme point of `C`. -/
lemma text18_5_2_p_not_mem_extremePoints :
    text18_5_2_p ∉ (text18_5_2_C).extremePoints ℝ := by
  classical
  have hpC2 : text18_5_2_p ∈ text18_5_2_C2 := by
    simp [text18_5_2_C2, text18_5_2_p]
  have hpS : text18_5_2_p ∈ text18_5_2_S := Or.inr hpC2
  have hpC : text18_5_2_p ∈ text18_5_2_C :=
    (subset_closedConvexHull (𝕜 := ℝ) (s := text18_5_2_S)) hpS
  have hzTopC2 : text18_5_2_zTop ∈ text18_5_2_C2 := by
    simp [text18_5_2_C2, text18_5_2_zTop]
  have hzBotC2 : text18_5_2_zBot ∈ text18_5_2_C2 := by
    simp [text18_5_2_C2, text18_5_2_zBot]
  have hzTopC : text18_5_2_zTop ∈ text18_5_2_C :=
    (subset_closedConvexHull (𝕜 := ℝ) (s := text18_5_2_S)) (Or.inr hzTopC2)
  have hzBotC : text18_5_2_zBot ∈ text18_5_2_C :=
    (subset_closedConvexHull (𝕜 := ℝ) (s := text18_5_2_S)) (Or.inr hzBotC2)
  have hseg : text18_5_2_p ∈ openSegment ℝ text18_5_2_zTop text18_5_2_zBot := by
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
    ext i
    fin_cases i <;>
      norm_num [text18_5_2_p, text18_5_2_zTop, text18_5_2_zBot, toLp_apply]
  intro hpExt
  rcases (mem_extremePoints_iff_left (𝕜 := ℝ) (A := text18_5_2_C) (x := text18_5_2_p)).1 hpExt
    with ⟨_hpC, hpExt'⟩
  have hEq := hpExt' _ hzTopC _ hzBotC hseg
  have hne : text18_5_2_zTop ≠ text18_5_2_p := by
    intro h
    have : (text18_5_2_zTop : EuclideanSpace ℝ (Fin 3)) 2 =
        (text18_5_2_p : EuclideanSpace ℝ (Fin 3)) 2 := congrArg (fun v => v 2) h
    simp [text18_5_2_zTop, text18_5_2_p, toLp_apply] at this
  exact hne hEq

/-- The auxiliary sequence `yₙ` tends to `0`. -/
lemma text18_5_2_y_tendsto_zero : Tendsto text18_5_2_y atTop (𝓝 (0 : ℝ)) := by
  have hf : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hf' :
      Tendsto (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_add_atTop_iff_nat (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) 1).2 hf
  have hf'' : Tendsto (fun n : ℕ => ((n : ℝ) + 1 + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa [Nat.cast_add, add_assoc, one_div] using hf'
  have hfun : (fun n : ℕ => ((n : ℝ) + 1 + 1)⁻¹) = text18_5_2_y := by
    funext n
    have h1 : (1 : ℝ) + 1 = 2 := by norm_num
    simp [text18_5_2_y, one_div, h1, add_assoc]
  simpa [hfun] using hf''

/-- The auxiliary sequence of points on the circle converges to `p`. -/
lemma text18_5_2_tendsto_q : Tendsto text18_5_2_q atTop (𝓝 text18_5_2_p) := by
  have hy : Tendsto text18_5_2_y atTop (𝓝 (0 : ℝ)) := text18_5_2_y_tendsto_zero
  have hy2 : Tendsto (fun n : ℕ => (text18_5_2_y n) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa [pow_two] using (hy.mul hy)
  have h1' :
      Tendsto (fun n : ℕ => 1 - (text18_5_2_y n) ^ 2) atTop (𝓝 (1 - (0 : ℝ) ^ 2)) := by
    simpa using (tendsto_const_nhds.sub hy2)
  have h1 :
      Tendsto (fun n : ℕ => 1 - (text18_5_2_y n) ^ 2) atTop (𝓝 (1 : ℝ)) := by
    simpa using h1'
  have hsqrt :
      Tendsto (fun n : ℕ => Real.sqrt (1 - (text18_5_2_y n) ^ 2)) atTop (𝓝 (1 : ℝ)) := by
    have hsqrt' :
        Tendsto (fun n : ℕ => Real.sqrt (1 - (text18_5_2_y n) ^ 2)) atTop
          (𝓝 (Real.sqrt (1 - (0 : ℝ) ^ 2))) :=
      (Real.continuous_sqrt.tendsto _).comp h1'
    simpa using hsqrt'
  -- work in the underlying function space, then apply continuity of `toLp`
  let qfun : ℕ → (Fin 3 → ℝ) :=
    fun n => ![Real.sqrt (1 - (text18_5_2_y n) ^ 2), text18_5_2_y n, (0 : ℝ)]
  let pfun : Fin 3 → ℝ := ![(1 : ℝ), 0, 0]
  have hfun : Tendsto qfun atTop (𝓝 pfun) := by
    refine tendsto_pi_nhds.2 ?_
    intro i
    fin_cases i
    · simpa [qfun, pfun] using hsqrt
    · simpa [qfun, pfun] using hy
    ·
      simp [qfun, pfun]
  have hcont :
      Continuous (WithLp.toLp (p := 2) (V := Fin 3 → ℝ)) :=
    (continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ))
  have h := (hcont.tendsto pfun).comp hfun
  simpa [text18_5_2_q, text18_5_2_p, qfun, pfun] using h

/-- The `x`-coordinate of `qₙ` is strictly less than `1`. -/
lemma text18_5_2_q0_lt_one (n : ℕ) :
    Real.sqrt (1 - (text18_5_2_y n) ^ 2) < (1 : ℝ) := by
  have h0 : 0 ≤ 1 - (text18_5_2_y n) ^ 2 := by
    nlinarith [le_of_lt (text18_5_2_y_sq_lt_one n)]
  have hlt : 1 - (text18_5_2_y n) ^ 2 < 1 := by
    nlinarith [text18_5_2_y_pos n]
  have h := Real.sqrt_lt_sqrt h0 hlt
  simpa using h

/-- The point `qₙ` has norm `1`. -/
lemma text18_5_2_q_norm (n : ℕ) : ‖text18_5_2_q n‖ = 1 := by
  have h0 : 0 ≤ 1 - (text18_5_2_y n) ^ 2 := by
    nlinarith [le_of_lt (text18_5_2_y_sq_lt_one n)]
  have hsqrt :
      (Real.sqrt (1 - (text18_5_2_y n) ^ 2)) ^ 2 = 1 - (text18_5_2_y n) ^ 2 := by
    simpa [pow_two] using Real.sq_sqrt h0
  have hnormsq :
      ‖text18_5_2_q n‖ ^ 2 = 1 := by
    have hnormsq' :
        ‖text18_5_2_q n‖ ^ 2 =
          (Real.sqrt (1 - (text18_5_2_y n) ^ 2)) ^ 2 +
            (text18_5_2_y n) ^ 2 + (0 : ℝ) ^ 2 := by
      simpa [text18_5_2_q] using text18_5_2_norm_sq_eq (text18_5_2_q n)
    nlinarith [hnormsq', hsqrt]
  have hnonneg : 0 ≤ ‖text18_5_2_q n‖ := norm_nonneg _
  nlinarith

/-- Any point in the convex hull of `S` splits into a two-piece convex combination. -/
lemma text18_5_2_mem_convexHull_S_decomp
    {v : EuclideanSpace ℝ (Fin 3)} (hv : v ∈ convexHull ℝ text18_5_2_S) :
    ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧
      ∃ u ∈ convexHull ℝ text18_5_2_C1, ∃ w ∈ convexHull ℝ text18_5_2_C2,
        v = (1 - t) • u + t • w := by
  have hC1ne : (text18_5_2_C1).Nonempty := by
    refine ⟨0, ?_⟩
    simp [text18_5_2_C1]
  have hC2ne : (text18_5_2_C2).Nonempty := by
    refine ⟨text18_5_2_p, ?_⟩
    simp [text18_5_2_C2, text18_5_2_p]
  have hEq :
      convexHull ℝ text18_5_2_S =
        convexJoin ℝ (convexHull ℝ text18_5_2_C1) (convexHull ℝ text18_5_2_C2) := by
    simpa [text18_5_2_S] using
      (convexHull_union (𝕜 := ℝ) (s := text18_5_2_C1) (t := text18_5_2_C2) hC1ne hC2ne)
  have hv' :
      v ∈ convexJoin ℝ (convexHull ℝ text18_5_2_C1) (convexHull ℝ text18_5_2_C2) := by
    simpa [hEq] using hv
  rcases (mem_convexJoin).1 hv' with ⟨u, hu, w, hw, hvseg⟩
  rcases hvseg with ⟨a, b, ha, hb, hab, rfl⟩
  have hb' : b ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨hb, ?_⟩
    have : b ≤ a + b := by nlinarith [ha]
    simpa [hab] using this
  have ha' : a = 1 - b := by nlinarith [hab]
  refine ⟨b, hb', u, hu, w, hw, ?_⟩
  simp [ha']

/-- On the convex hull of `C2`, the supporting functional is at most `qₙ`'s `x`-coordinate. -/
lemma text18_5_2_q_inner_le_q0_on_convexHull_C2 (n : ℕ) :
    ∀ v ∈ convexHull ℝ text18_5_2_C2,
      ⟪text18_5_2_q n, v⟫ ≤ Real.sqrt (1 - (text18_5_2_y n) ^ 2) := by
  classical
  let q := text18_5_2_q n
  let q0 : ℝ := Real.sqrt (1 - (text18_5_2_y n) ^ 2)
  have hconv : Convex ℝ {v : EuclideanSpace ℝ (Fin 3) | ⟪q, v⟫ ≤ q0} := by
    have hIic : Convex ℝ (Set.Iic q0) := convex_Iic q0
    simpa [Set.preimage, Set.mem_Iic, q0] using
      (hIic.linear_preimage (innerSL ℝ q).toLinearMap)
  have hsubset : text18_5_2_C2 ⊆ {v : EuclideanSpace ℝ (Fin 3) | ⟪q, v⟫ ≤ q0} := by
    intro v hv
    rcases hv with ⟨hv0, hv1, _hv2⟩
    have hinner : ⟪q, v⟫ = q0 := by
      simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three, q, q0, hv0,
        hv1, text18_5_2_q, star_trivial]
    simp [hinner.symm]
  have hHull : convexHull ℝ text18_5_2_C2 ⊆ {v : EuclideanSpace ℝ (Fin 3) | ⟪q, v⟫ ≤ q0} :=
    convexHull_min hsubset hconv
  intro v hv
  have hv' := hHull hv
  simpa [Set.mem_setOf_eq, q, q0] using hv'

/-- The supporting functional is bounded by `1` on `C`. -/
lemma text18_5_2_q_inner_le_one_on_C (n : ℕ) :
    ∀ v ∈ text18_5_2_C, ⟪text18_5_2_q n, v⟫ ≤ 1 := by
  classical
  let q := text18_5_2_q n
  have hconv : Convex ℝ {v : EuclideanSpace ℝ (Fin 3) | ⟪q, v⟫ ≤ (1 : ℝ)} := by
    have hIic : Convex ℝ (Set.Iic (1 : ℝ)) := convex_Iic (1 : ℝ)
    simpa [Set.preimage, Set.mem_Iic] using
      (hIic.linear_preimage (innerSL ℝ q).toLinearMap)
  have hclosed : IsClosed {v : EuclideanSpace ℝ (Fin 3) | ⟪q, v⟫ ≤ (1 : ℝ)} := by
    have hIic : IsClosed (Set.Iic (1 : ℝ)) := isClosed_Iic
    simpa [Set.preimage, Set.mem_Iic] using hIic.preimage (innerSL ℝ q).continuous
  have hsubset : text18_5_2_S ⊆ {v : EuclideanSpace ℝ (Fin 3) | ⟪q, v⟫ ≤ (1 : ℝ)} := by
    intro v hv
    rcases hv with hv | hv
    · -- `v ∈ C1`
      have hvball : v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
        text18_5_2_C1_subset_closedBall_one hv
      have hvnorm : ‖v‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hvball
      have hqnorm : ‖q‖ = 1 := by
        simpa [q] using text18_5_2_q_norm n
      have hinner : ⟪q, v⟫ ≤ ‖q‖ * ‖v‖ := real_inner_le_norm q v
      have hbound : ‖q‖ * ‖v‖ ≤ 1 := by nlinarith [hvnorm, hqnorm]
      exact (le_trans hinner hbound)
    · -- `v ∈ C2`
      rcases hv with ⟨hv0, hv1, _hv2⟩
      have hinner : ⟪q, v⟫ = Real.sqrt (1 - (text18_5_2_y n) ^ 2) := by
        simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three, q, hv0, hv1,
          text18_5_2_q, star_trivial]
      have hq0 : Real.sqrt (1 - (text18_5_2_y n) ^ 2) < (1 : ℝ) := text18_5_2_q0_lt_one n
      have hq0' : ⟪q, v⟫ < (1 : ℝ) := by
        simpa [hinner.symm] using hq0
      exact le_of_lt hq0'
  have hCsubset :
      text18_5_2_C ⊆ {v : EuclideanSpace ℝ (Fin 3) | ⟪q, v⟫ ≤ (1 : ℝ)} :=
    closedConvexHull_min (s := text18_5_2_S) (t := {v | ⟪q, v⟫ ≤ (1 : ℝ)})
      hsubset hconv hclosed
  intro v hv
  have hv' := hCsubset hv
  simpa [Set.mem_setOf_eq, q] using hv'

/-- Points of `C` attaining the maximum of the supporting functional are exactly `qₙ`. -/
lemma text18_5_2_eq_of_mem_C_and_inner_eq_one (n : ℕ) :
    ∀ v ∈ text18_5_2_C, ⟪text18_5_2_q n, v⟫ = 1 → v = text18_5_2_q n := by
  classical
  intro v hv hinner
  let q := text18_5_2_q n
  let q0 : ℝ := Real.sqrt (1 - (text18_5_2_y n) ^ 2)
  have hq0 : q0 < 1 := by
    simpa [q0] using text18_5_2_q0_lt_one n
  have hqnorm : ‖q‖ = 1 := by
    simpa [q] using text18_5_2_q_norm n
  have hCeq : text18_5_2_C = closure (convexHull ℝ text18_5_2_S) := by
    simpa [text18_5_2_C] using
      (closedConvexHull_eq_closure_convexHull (𝕜 := ℝ) (s := text18_5_2_S))
  have hv' : v ∈ closure (convexHull ℝ text18_5_2_S) := by
    simpa [hCeq] using hv
  rcases mem_closure_iff_seq_limit.1 hv' with ⟨vseq, hvseq_mem, hvseq_tendsto⟩
  choose t ht u hu w hw hrepr using
    (fun k => text18_5_2_mem_convexHull_S_decomp (v := vseq k) (hvseq_mem k))
  have hC1S : text18_5_2_C1 ⊆ text18_5_2_S := by
    intro x hx; exact Or.inl hx
  have hC2S : text18_5_2_C2 ⊆ text18_5_2_S := by
    intro x hx; exact Or.inr hx
  have huC : ∀ k, u k ∈ text18_5_2_C := by
    intro k
    have hu' : u k ∈ convexHull ℝ text18_5_2_S :=
      (convexHull_mono hC1S) (hu k)
    exact (convexHull_subset_closedConvexHull (𝕜 := ℝ) (s := text18_5_2_S)) hu'
  have hu_inner : ∀ k, ⟪q, u k⟫ ≤ 1 := by
    intro k
    have := text18_5_2_q_inner_le_one_on_C n (u k) (huC k)
    simpa [q] using this
  have hw_inner : ∀ k, ⟪q, w k⟫ ≤ q0 := by
    intro k
    have := text18_5_2_q_inner_le_q0_on_convexHull_C2 n (w k) (hw k)
    simpa [q, q0] using this
  have ht0 : ∀ k, 0 ≤ t k := fun k => (ht k).1
  have ht1 : ∀ k, t k ≤ 1 := fun k => (ht k).2
  have hinner_seq :
      ∀ k, ⟪q, vseq k⟫ ≤ 1 - t k * (1 - q0) := by
    intro k
    have hlin :
        ⟪q, vseq k⟫ =
          (1 - t k) * ⟪q, u k⟫ + t k * ⟪q, w k⟫ := by
      -- expand the inner product of the convex combination
      calc
        ⟪q, vseq k⟫ =
            ⟪q, (1 - t k) • u k + t k • w k⟫ := by simp [hrepr k]
        _ = ⟪q, (1 - t k) • u k⟫ + ⟪q, t k • w k⟫ := by
              simp [inner_add_right]
        _ = (1 - t k) * ⟪q, u k⟫ + t k * ⟪q, w k⟫ := by
              simp [inner_smul_right]
    have h1t : 0 ≤ 1 - t k := by nlinarith [ht1 k]
    nlinarith [hlin, hu_inner k, hw_inner k, ht0 k, h1t]
  have hinner_tendsto :
      Tendsto (fun k => ⟪q, vseq k⟫) atTop (𝓝 (⟪q, v⟫)) := by
    have h := (innerSL ℝ q).continuous.tendsto _ |>.comp hvseq_tendsto
    simpa [innerSL_apply_apply, q] using h
  have hinner_tendsto1 : Tendsto (fun k => ⟪q, vseq k⟫) atTop (𝓝 (1 : ℝ)) := by
    simpa [q, hinner] using hinner_tendsto
  have hdiff0 : Tendsto (fun k => 1 - ⟪q, vseq k⟫) atTop (𝓝 ((1 : ℝ) - 1)) := by
    simpa using (tendsto_const_nhds.sub hinner_tendsto1 :
      Tendsto (fun k => (1 : ℝ) - ⟪q, vseq k⟫) atTop (𝓝 ((1 : ℝ) - 1)))
  have hdiff : Tendsto (fun k => 1 - ⟪q, vseq k⟫) atTop (𝓝 (0 : ℝ)) := by
    simpa using hdiff0
  have hdiff' :
      Tendsto (fun k => (1 - ⟪q, vseq k⟫) / (1 - q0)) atTop (𝓝 (0 : ℝ)) := by
    have hmul := (Filter.Tendsto.mul_const (b := (1 - q0)⁻¹) hdiff)
    simpa [div_eq_mul_inv] using hmul
  have ht_le : ∀ k, t k ≤ (1 - ⟪q, vseq k⟫) / (1 - q0) := by
    intro k
    have hpos : 0 < (1 - q0) := by nlinarith [hq0]
    have hineq := hinner_seq k
    -- rearrange the inequality
    have hineq' : t k * (1 - q0) ≤ 1 - ⟪q, vseq k⟫ := by
      nlinarith [hineq]
    have := (le_div_iff₀ hpos).2 hineq'
    simpa using this
  have ht_tendsto : Tendsto t atTop (𝓝 (0 : ℝ)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (f := t)
      (g := fun _ : ℕ => (0 : ℝ))
      (h := fun k => (1 - ⟪q, vseq k⟫) / (1 - q0))
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ))) hdiff' ?_ ?_
    · intro k; exact ht0 k
    · intro k; exact ht_le k
  have hbound_u : ∀ k, ‖u k‖ ≤ 1 := by
    intro k
    have hHull :
        convexHull ℝ text18_5_2_C1 ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
      convexHull_min text18_5_2_C1_subset_closedBall_one (convex_closedBall (0 : _) 1)
    have hu' : u k ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := hHull (hu k)
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu'
  have hbound_w : ∀ k, ‖w k‖ ≤ 2 := by
    intro k
    have hHull :
        convexHull ℝ text18_5_2_C2 ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2 :=
      convexHull_min text18_5_2_C2_subset_closedBall (convex_closedBall (0 : _) 2)
    have hw' : w k ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2 := hHull (hw k)
    simpa [Metric.mem_closedBall, dist_eq_norm] using hw'
  have hdiff_eq : ∀ k, vseq k - u k = t k • (w k - u k) := by
    intro k
    have h1 : (1 - t k) • u k - u k = (-t k) • u k := by
      calc
        (1 - t k) • u k - u k = (1 - t k) • u k - (1 : ℝ) • u k := by simp
        _ = ((1 - t k) - 1) • u k := by
          simpa using (sub_smul (1 - t k) (1 : ℝ) (u k)).symm
        _ = (-t k) • u k := by ring_nf
    calc
      vseq k - u k = (1 - t k) • u k + t k • w k - u k := by
        simp [hrepr k]
      _ = t k • w k + ((1 - t k) • u k - u k) := by
        simp [sub_eq_add_neg, add_assoc, add_comm]
      _ = t k • w k + (-t k) • u k := by simp [h1]
      _ = t k • (w k - u k) := by
        simp [sub_eq_add_neg]
  have hdiff_norm :
      Tendsto (fun k => ‖vseq k - u k‖) atTop (𝓝 (0 : ℝ)) := by
    have hbound : ∀ k, ‖vseq k - u k‖ ≤ t k * 3 := by
      intro k
      have hnorm :
          ‖vseq k - u k‖ = |t k| * ‖w k - u k‖ := by
        simpa [hdiff_eq k] using (norm_smul (t k) (w k - u k))
      have hwu : ‖w k - u k‖ ≤ 3 := by
        have hwu' : ‖w k - u k‖ ≤ ‖w k‖ + ‖u k‖ := norm_sub_le _ _
        have hwub : ‖w k‖ + ‖u k‖ ≤ 3 := by nlinarith [hbound_w k, hbound_u k]
        exact le_trans hwu' hwub
      have hmul : |t k| * ‖w k - u k‖ ≤ |t k| * 3 := by
        exact mul_le_mul_of_nonneg_left hwu (abs_nonneg _)
      have hnorm' : ‖vseq k - u k‖ ≤ |t k| * 3 := by
        simpa [hnorm] using hmul
      have htabs : |t k| = t k := abs_of_nonneg (ht0 k)
      simpa [htabs] using hnorm'
    have ht3 : Tendsto (fun k => t k * (3 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
      simpa using (Filter.Tendsto.mul_const (b := (3 : ℝ)) ht_tendsto)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      (f := fun k => ‖vseq k - u k‖)
      (g := fun _ : ℕ => (0 : ℝ))
      (h := fun k => t k * (3 : ℝ))
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ))) ht3 ?_ ?_
    · intro k; exact norm_nonneg _
    · intro k; exact hbound k
  have huv : Tendsto u atTop (𝓝 v) := by
    -- use `‖u k - v‖ ≤ ‖u k - vseq k‖ + ‖vseq k - v‖`
    have hvseq_norm : Tendsto (fun k => ‖vseq k - v‖) atTop (𝓝 (0 : ℝ)) := by
      exact (tendsto_iff_norm_sub_tendsto_zero).1 hvseq_tendsto
    have hnorm : Tendsto (fun k => ‖u k - v‖) atTop (𝓝 (0 : ℝ)) := by
      have hbound : ∀ k, ‖u k - v‖ ≤ ‖u k - vseq k‖ + ‖vseq k - v‖ := by
        intro k
        have := norm_add_le (u k - vseq k) (vseq k - v)
        -- rewrite `u k - v` as a sum
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      have hleft :
          Tendsto (fun k => ‖u k - vseq k‖ + ‖vseq k - v‖) atTop (𝓝 (0 : ℝ)) := by
        have h1 : Tendsto (fun k => ‖u k - vseq k‖) atTop (𝓝 (0 : ℝ)) := by
          simpa [norm_sub_rev] using hdiff_norm
        simpa using h1.add hvseq_norm
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le
        (f := fun k => ‖u k - v‖)
        (g := fun _ : ℕ => (0 : ℝ))
        (h := fun k => ‖u k - vseq k‖ + ‖vseq k - v‖)
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ))) hleft ?_ ?_
      · intro k; exact norm_nonneg _
      · intro k; exact hbound k
    exact (tendsto_iff_norm_sub_tendsto_zero).2 hnorm
  have hvC1closure : v ∈ closure (convexHull ℝ text18_5_2_C1) := by
    refine mem_closure_of_tendsto huv ?_
    exact Filter.Eventually.of_forall hu
  have hBall :
      closure (convexHull ℝ text18_5_2_C1) ⊆
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    have hHull :
        convexHull ℝ text18_5_2_C1 ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
      convexHull_min text18_5_2_C1_subset_closedBall_one (convex_closedBall (0 : _) 1)
    exact closure_minimal hHull Metric.isClosed_closedBall
  have hvball : v ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    hBall hvC1closure
  have hvnorm : ‖v‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hvball
  have hinner' : ⟪q, v⟫ = ‖q‖ * ‖v‖ := by
    have hineq : ⟪q, v⟫ ≤ ‖q‖ * ‖v‖ := real_inner_le_norm q v
    have hineq' : 1 ≤ ‖q‖ * ‖v‖ := by
      have hqv : (1 : ℝ) = ⟪q, v⟫ := by simpa [q] using hinner.symm
      nlinarith [hineq, hqv]
    have hqv : (1 : ℝ) = ⟪q, v⟫ := by simpa [q] using hinner.symm
    have hqnorm' : ‖q‖ = 1 := hqnorm
    have hvnorm' : ‖v‖ = 1 := by
      have : (1 : ℝ) ≤ ‖v‖ := by nlinarith [hineq', hqnorm']
      exact le_antisymm hvnorm (by nlinarith [this])
    nlinarith [hqv, hqnorm', hvnorm']
  have hcol : (‖v‖ : ℝ) • q = (‖q‖ : ℝ) • v := by
    -- equality case of Cauchy-Schwarz
    have h := (inner_eq_norm_mul_iff_real (x := q) (y := v)).1 hinner'
    simpa [mul_comm] using h
  -- With both norms `1`, we can conclude `v = q`.
  have hvnorm' : ‖v‖ = 1 := by
    have hqv : (1 : ℝ) = ⟪q, v⟫ := by simpa [q] using hinner.symm
    have hineq : ⟪q, v⟫ ≤ ‖q‖ * ‖v‖ := real_inner_le_norm q v
    have hqnorm' : ‖q‖ = 1 := hqnorm
    have : (1 : ℝ) ≤ ‖v‖ := by nlinarith [hineq, hqv, hqnorm']
    exact le_antisymm hvnorm (by nlinarith [this])
  have hqnorm' : ‖q‖ = 1 := hqnorm
  -- simplify the collinearity relation
  have : v = q := by
    simpa [hvnorm', hqnorm'] using hcol.symm
  simpa [q] using this

/-- Each point `qₙ` is an exposed point of `C`. -/
lemma text18_5_2_q_mem_exposedPoints (n : ℕ) :
    text18_5_2_q n ∈ (text18_5_2_C).exposedPoints ℝ := by
  classical
  refine (exposed_point_def).2 ?_
  refine ⟨?_, ?_⟩
  · -- `qₙ` belongs to `C`
    have hqC1 : text18_5_2_q n ∈ text18_5_2_C1 := text18_5_2_q_mem_C1 n
    have hqS : text18_5_2_q n ∈ text18_5_2_S := Or.inl hqC1
    exact (subset_closedConvexHull (𝕜 := ℝ) (s := text18_5_2_S)) hqS
  ·
    -- use the supporting functional `l := innerSL ℝ (qₙ)`
    refine ⟨innerSL ℝ (text18_5_2_q n), ?_⟩
    intro v hv
    have hle : ⟪text18_5_2_q n, v⟫ ≤ 1 :=
      text18_5_2_q_inner_le_one_on_C n v hv
    have hqeq : (innerSL ℝ (text18_5_2_q n)) (text18_5_2_q n) = (1 : ℝ) := by
      have hqnorm : ‖text18_5_2_q n‖ = 1 := text18_5_2_q_norm n
      -- `inner q q = ‖q‖^2`
      simp [innerSL_apply_apply, hqnorm, inner_self_eq_norm_sq_to_K]
    refine ⟨?_, ?_⟩
    · -- bound by `1`
      simpa [innerSL_apply_apply, hqeq] using hle
    · intro hvge
      have hinner : ⟪text18_5_2_q n, v⟫ = 1 := by
        -- combine `hle` and `hvge`
        have hvge' : (1 : ℝ) ≤ ⟪text18_5_2_q n, v⟫ := by
          simpa [innerSL_apply_apply, hqeq] using hvge
        exact le_antisymm hle hvge'
      exact text18_5_2_eq_of_mem_C_and_inner_eq_one n v hv hinner

/-- Each point `qₙ` is an extreme point of `C`. -/
lemma text18_5_2_q_mem_extremePoints (n : ℕ) :
    text18_5_2_q n ∈ (text18_5_2_C).extremePoints ℝ := by
  exact (exposedPoints_subset_extremePoints (A := text18_5_2_C) (𝕜 := ℝ))
    (text18_5_2_q_mem_exposedPoints n)

/-- A sequence of extreme points approaches `p`, so `extremePoints` is not closed. -/
lemma text18_5_2_limit_point_in_closure_extremePoints :
    text18_5_2_p ∈ closure ((text18_5_2_C).extremePoints ℝ) := by
  have hmem : ∀ n, text18_5_2_q n ∈ (text18_5_2_C).extremePoints ℝ := by
    intro n
    exact text18_5_2_q_mem_extremePoints n
  exact mem_closure_of_tendsto text18_5_2_tendsto_q (Filter.Eventually.of_forall hmem)

/-- Text 18.5.2 (Non-Closedness of the Set of Extreme Points). There exists a closed and bounded
(hence compact) convex set `C ⊆ ℝ³` such that the set of its extreme points `ext(C)` (formalized as
`C.extremePoints ℝ`) is not closed. -/
theorem exists_closed_bounded_convex_extremePoints_not_isClosed :
    ∃ C : Set (EuclideanSpace ℝ (Fin 3)),
      IsClosed C ∧ Bornology.IsBounded C ∧ Convex ℝ C ∧ ¬ IsClosed (C.extremePoints ℝ) := by
  refine ⟨text18_5_2_C, ?_, ?_, ?_, ?_⟩
  · exact (text18_5_2_C_def_and_basic_props).1
  · exact (text18_5_2_C_def_and_basic_props).2.1
  · exact (text18_5_2_C_def_and_basic_props).2.2
  · intro hClosed
    have hpClosure : text18_5_2_p ∈ closure ((text18_5_2_C).extremePoints ℝ) :=
      text18_5_2_limit_point_in_closure_extremePoints
    have hpMem : text18_5_2_p ∈ (text18_5_2_C).extremePoints ℝ := by
      -- closedness forces the closure to equal the set itself
      simpa [hClosed.closure_eq] using hpClosure
    exact text18_5_2_p_not_mem_extremePoints hpMem

end
end Section18
end Chap04
