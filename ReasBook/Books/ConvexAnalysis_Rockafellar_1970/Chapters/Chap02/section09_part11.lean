/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part10
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part4

noncomputable section
open scoped Pointwise
open scoped BigOperators
open scoped Topology
open scoped RealInnerProductSpace
open Filter

/-- A pointwise true predicate holds eventually. -/
lemma eventually_of_forall {α} {l : Filter α} {p : α → Prop} (hp : ∀ x, p x) :
    Filter.Eventually p l := by
  have hset : {x | p x} = (Set.univ : Set α) := by
    ext x; exact ⟨fun _ => trivial, fun _ => hp x⟩
  simp [Filter.Eventually, hset, Filter.univ_mem]

section Chap02
section Section09

/-- The vertical line `{(1, t)}` is unbounded. -/
lemma lineSet_unbounded :
    ¬ Bornology.IsBounded {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]} := by
  intro hbounded
  set S : Set (Fin 2 → Real) :=
    {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]}
  have hbounded_eval : Bornology.IsBounded (Function.eval 1 '' S) := by
    simpa [S] using (Bornology.IsBounded.image_eval (s := S) hbounded 1)
  have hEval : Function.eval 1 '' S = (Set.univ : Set Real) := by
    ext r
    constructor
    · intro _; trivial
    · intro _
      refine ⟨![1, 0] + r • ![0, 1], ?_, ?_⟩
      · exact ⟨r, rfl⟩
      · simp
  have hbounded_univ : Bornology.IsBounded (Set.univ : Set Real) := by
    simpa [hEval] using hbounded_eval
  exact (NormedSpace.unbounded_univ (𝕜 := Real) (E := Real)) hbounded_univ

/-- The recession cone of the closed ball centered at `![1, 0]` is `{0}`. -/
lemma recC_closedBall_eq_zero :
    let C : Set (Fin 2 → Real) :=
      Metric.closedBall (![1, 0]) ‖(![1, 0] : Fin 2 → Real)‖
    let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 2))
    let C' : Set (EuclideanSpace Real (Fin 2)) := Set.image e.symm C
    let recC : Set (Fin 2 → Real) := Set.image e (Set.recessionCone C')
    recC = ({0} : Set (Fin 2 → Real)) := by
  classical
  intro C e C' recC
  have hCne : Set.Nonempty C := by
    refine ⟨![1, 0], ?_⟩
    simp [C, Metric.mem_closedBall]
  have hCclosed : IsClosed C := by
    simpa [C] using
      (Metric.isClosed_closedBall (x := (![1, 0] : Fin 2 → Real))
        (ε := ‖(![1, 0] : Fin 2 → Real)‖))
  have hCconv : Convex Real C := by
    simpa [C] using
      (convex_closedBall (a := (![1, 0] : Fin 2 → Real))
        (r := ‖(![1, 0] : Fin 2 → Real)‖))
  have hCbdd : Bornology.IsBounded C := by
    simpa [C] using
      (Metric.isBounded_closedBall (x := (![1, 0] : Fin 2 → Real))
        (r := ‖(![1, 0] : Fin 2 → Real)‖))
  have hrecC :
      Set.recessionCone C' = ({0} : Set (EuclideanSpace Real (Fin 2))) := by
    simpa [e, C'] using
      (recCone_eq_singleton_zero_of_bounded_image (C := C) hCne hCclosed hCconv hCbdd)
  simp [recC, hrecC]

/-- Nonzero points in the cone over the closed ball centered at `![1, 0]` have positive
first coordinate. -/
lemma cone_closedBall_imp_pos_first {x : Fin 2 → Real}
    (hx :
      x ∈ convexConeGenerated 2
        (Metric.closedBall (![1, 0]) ‖(![1, 0] : Fin 2 → Real)‖))
    (hx0 : x ≠ 0) : 0 ≤ x 0 := by
  set a : Fin 2 → Real := ![1, 0]
  set C : Set (Fin 2 → Real) := Metric.closedBall a ‖a‖
  have hx' :
      x = 0 ∨ x ∈ (ConvexCone.hull Real C : Set (Fin 2 → Real)) := by
    simpa [C, a, convexConeGenerated, Set.mem_insert_iff] using hx
  rcases hx' with hx0' | hxHull
  · exact (hx0 hx0').elim
  · have hCconv : Convex Real C := by
      simpa [C, a] using (convex_closedBall (a := a) (r := ‖a‖))
    rcases (ConvexCone.mem_hull_of_convex (s := C) hCconv).1 hxHull with
      ⟨t, htpos, htmem⟩
    rcases htmem with ⟨c, hcC, rfl⟩
    have hnorm_le : ‖c - a‖ ≤ ‖a‖ := by
      simpa [C, Metric.mem_closedBall] using hcC
    have ha_le : ‖a‖ ≤ (1 : Real) := by
      refine (pi_norm_le_iff_of_nonneg (x := a) (r := (1 : Real)) (by linarith)).2 ?_
      intro i; fin_cases i <;> simp [a]
    have hnorm_le' : ‖c - a‖ ≤ (1 : Real) := le_trans hnorm_le ha_le
    have hcoord : ‖c 0 - 1‖ ≤ (1 : Real) := by
      have h := norm_le_pi_norm (f := c - a) (i := (0 : Fin 2))
      have h' : ‖c 0 - 1‖ ≤ ‖c - a‖ := by
        simpa [a] using h
      exact le_trans h' hnorm_le'
    have habs : |c 0 - 1| ≤ (1 : Real) := by
      simpa using hcoord
    have hle : -1 ≤ c 0 - 1 := (abs_le.mp habs).1
    have hc0_nonneg : 0 ≤ c 0 := by linarith
    have : 0 ≤ t * c 0 := mul_nonneg (le_of_lt htpos) hc0_nonneg
    simpa using this

/-- Points with positive first coordinate lie in the cone over the closed ball centered at
`![1, 0]`. -/
lemma pos_first_mem_cone_closedBall {x : Fin 2 → Real} (hx : 0 < x 0) :
    x ∈ convexConeGenerated 2
      (Metric.closedBall (![1, 0]) ‖(![1, 0] : Fin 2 → Real)‖) := by
  set a : Fin 2 → Real := ![1, 0]
  set C : Set (Fin 2 → Real) := Metric.closedBall a ‖a‖
  have hCconv : Convex Real C := by
    simpa [C, a] using (convex_closedBall (a := a) (r := ‖a‖))
  have ha_ge : (1 : Real) ≤ ‖a‖ := by
    have h := norm_le_pi_norm (f := a) (i := (0 : Fin 2))
    simpa [a] using h
  have hxHull :
      x ∈ (ConvexCone.hull Real C : Set (Fin 2 → Real)) := by
    refine (ConvexCone.mem_hull_of_convex (s := C) hCconv).2 ?_
    by_cases hle : |x 1| ≤ x 0
    · refine ⟨x 0, hx, ?_⟩
      refine ⟨![1, x 1 / x 0], ?_, ?_⟩
      · have hx0pos : 0 < x 0 := hx
        have hnorm_le1 : ‖![1, x 1 / x 0] - a‖ ≤ (1 : Real) := by
          refine (pi_norm_le_iff_of_nonneg
            (x := ![1, x 1 / x 0] - a) (r := (1 : Real)) (by linarith)).2 ?_
          intro i; fin_cases i
          · simp [a]
          · have hle' : |x 1| / x 0 ≤ (1 : Real) := (div_le_one hx0pos).2 hle
            simpa [a, abs_div, abs_of_pos hx0pos] using hle'
        have hnorm_le : ‖![1, x 1 / x 0] - a‖ ≤ ‖a‖ := le_trans hnorm_le1 ha_ge
        simpa [C, Metric.mem_closedBall, dist_eq_norm] using hnorm_le
      · have hxne : x 0 ≠ 0 := ne_of_gt hx
        ext i; fin_cases i
        · simp
        · have h : x 0 * (x 1 / x 0) = x 1 := by
            field_simp [hxne]
          simpa using h
    · have hlt : x 0 < |x 1| := lt_of_not_ge hle
      have hx1pos : 0 < |x 1| := lt_trans hx hlt
      refine ⟨|x 1|, hx1pos, ?_⟩
      refine ⟨![x 0 / |x 1|, x 1 / |x 1|], ?_, ?_⟩
      · have hx1ne : |x 1| ≠ 0 := ne_of_gt hx1pos
        have hratio_nonneg : 0 ≤ x 0 / |x 1| := by
          exact div_nonneg (le_of_lt hx) (le_of_lt hx1pos)
        have hratio_le : x 0 / |x 1| ≤ (1 : Real) := by
          exact (div_le_one hx1pos).2 (le_of_lt hlt)
        have hcoord0 : |x 0 / |x 1| - 1| ≤ (1 : Real) := by
          have h1 : -1 ≤ x 0 / |x 1| - 1 := by linarith
          have h2 : x 0 / |x 1| - 1 ≤ 1 := by linarith
          exact abs_le.mpr ⟨h1, h2⟩
        have hcoord1 : |x 1| / |x 1| ≤ (1 : Real) := by
          have habs : |x 1| / |x 1| = (1 : Real) := by
            field_simp [hx1ne]
          exact le_of_eq habs
        have hnorm_le1 :
            ‖![x 0 / |x 1|, x 1 / |x 1|] - a‖ ≤ (1 : Real) := by
          refine (pi_norm_le_iff_of_nonneg
            (x := ![x 0 / |x 1|, x 1 / |x 1|] - a)
            (r := (1 : Real)) (by linarith)).2 ?_
          intro i; fin_cases i
          · simpa [a] using hcoord0
          · simpa [a, abs_div] using hcoord1
        have hnorm_le :
            ‖![x 0 / |x 1|, x 1 / |x 1|] - a‖ ≤ ‖a‖ := le_trans hnorm_le1 ha_ge
        simpa [C, Metric.mem_closedBall, dist_eq_norm] using hnorm_le
      · have hx1ne : |x 1| ≠ 0 := ne_of_gt hx1pos
        ext i; fin_cases i
        · have h : |x 1| * (x 0 / |x 1|) = x 0 := by
            field_simp [hx1ne]
          simpa using h
        · have h : |x 1| * (x 1 / |x 1|) = x 1 := by
            field_simp [hx1ne]
          simpa using h
  have hxK :
      x = 0 ∨ x ∈ (ConvexCone.hull Real C : Set (Fin 2 → Real)) := Or.inr hxHull
  simpa [convexConeGenerated, Set.mem_insert_iff, C, a] using hxK

/-- The point `(0, 1)` lies in the closure of the cone over the closed ball centered at
`![1, 0]`. -/
lemma closure_cone_closedBall_has_point :
    (![0, 1] : Fin 2 → Real) ∈
      closure (convexConeGenerated 2
        (Metric.closedBall (![1, 0]) ‖(![1, 0] : Fin 2 → Real)‖)) := by
  refine (mem_closure_iff_seq_limit).2 ?_
  refine ⟨fun n : ℕ => ![(1 : Real) / (n + 1), 1], ?_, ?_⟩
  · intro n
    have hpos : 0 < (1 : Real) / (n + 1) := by
      have : 0 < (n + 1 : Real) := by
        exact_mod_cast (Nat.succ_pos n)
      exact one_div_pos.mpr this
    simpa using (pos_first_mem_cone_closedBall (x := ![(1 : Real) / (n + 1), 1]) hpos)
  · refine (tendsto_pi_nhds.2 ?_)
    intro i
    fin_cases i
    · have h :
        Tendsto (fun n : ℕ => (1 : Real) / ((n : Real) + 1)) atTop (𝓝 (0 : Real)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa [one_div, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using h
    · simp

/-- Remark 9.6.1.2. The need for the condition `0 ∉ C` in Theorem 9.6 and Corollary 9.6.1 is
shown by the case where `C` is a closed ball with the origin on its boundary. The need for
the boundedness assumption in Corollary 9.6.1 is shown by the case where `C` is a line not
passing through the origin. -/
lemma counterexample_origin_boundary_or_unbounded_line :
    (∃ (n : Nat) (x0 : Fin n → Real) (r : Real),
        let C : Set (Fin n → Real) := Metric.closedBall x0 r
        (0 : Fin n → Real) ∈ Metric.sphere x0 r ∧
          IsClosed C ∧ Convex Real C ∧ True) ∧
      (∃ (n : Nat) (x0 v : Fin n → Real),
        let C : Set (Fin n → Real) := {x | ∃ t : Real, x = x0 + t • v}
        (0 : Fin n → Real) ∉ C ∧ IsClosed C ∧ Convex Real C ∧
          (¬ Bornology.IsBounded C) ∧ ¬ IsClosed (convexConeGenerated n C)) := by
  classical
  refine ⟨?_, ?_⟩
  · refine ⟨2, ![1, 0], ‖(![1, 0] : Fin 2 → Real)‖, ?_⟩
    dsimp
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h :
          ‖-(![1, 0] : Fin 2 → Real)‖ = ‖(![1, 0] : Fin 2 → Real)‖ := by
        simpa using (norm_neg (![1, 0] : Fin 2 → Real))
      simpa [Metric.sphere, dist_eq_norm] using h
    · simpa using
        (Metric.isClosed_closedBall (x := (![1, 0] : Fin 2 → Real))
          (ε := ‖(![1, 0] : Fin 2 → Real)‖))
    · simpa using
        (convex_closedBall (a := (![1, 0] : Fin 2 → Real))
          (r := ‖(![1, 0] : Fin 2 → Real)‖))
    · trivial
  · refine ⟨2, ![1, 0], ![0, 1], ?_⟩
    -- reduce the set to the vertical line `lineSet`
    have hnot_mem :
        (0 : Fin 2 → Real) ∉
          {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]} := by
      intro h
      rcases h with ⟨t, ht⟩
      have : (0 : Real) = (1 : Real) := by
        simpa using congrArg (fun f => f 0) ht
      exact (one_ne_zero this.symm).elim
    have hnot_closed :
        ¬ IsClosed
          (convexConeGenerated 2
            {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]}) := by
      intro hclosed
      have hmem :
          (![0, 1] : Fin 2 → Real) ∈
            (convexConeGenerated 2
              {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]}) := by
        have hclosure :
            closure
                (convexConeGenerated 2
                  {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]}) =
              (convexConeGenerated 2
                {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]}) := by
          exact (closure_eq_iff_isClosed
            (s := convexConeGenerated 2
              {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]})).2 hclosed
        have hcl :
            (![0, 1] : Fin 2 → Real) ∈
              closure
                (convexConeGenerated 2
                  {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]}) :=
          closure_cone_line_has_point
        have hcl' := hcl
        rw [hclosure] at hcl'
        exact hcl'
      have hnot :
          (![0, 1] : Fin 2 → Real) ∉
            convexConeGenerated 2
              {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]} := by
        intro hx
        have hpos :=
          cone_line_pos_first (x := (![0, 1] : Fin 2 → Real)) hx (by simp)
        simp at hpos
      exact hnot hmem
    simpa using
      (show
          (0 : Fin 2 → Real) ∉
              {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]} ∧
            IsClosed
              {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]} ∧
            Convex Real
              {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]} ∧
            (¬ Bornology.IsBounded
              {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]}) ∧
            ¬ IsClosed
              (convexConeGenerated 2
                {x : Fin 2 → Real | ∃ t : Real, x = ![1, 0] + t • ![0, 1]}) from
        ⟨hnot_mem, closed_lineSet, convex_lineSet, lineSet_unbounded, hnot_closed⟩)

/-- Coordinate version of `prodLinearEquiv_append` landing in `Fin (n + 1) → Real`. -/
def prodLinearEquiv_append_coord (n : Nat) :
    ((Fin n → Real) × Real) ≃ₗ[Real] (Fin (n + 1) → Real) :=
  (prodLinearEquiv_append (n := n)).trans
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (n + 1))).toLinearEquiv

/-- The epigraph of a positive right scalar multiple is the scaled epigraph. -/
lemma epigraph_rightScalarMultiple_eq_smul {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {lam : Real} (hlam : 0 < lam) :
    epigraph (Set.univ : Set (Fin n → Real)) (rightScalarMultiple f lam) =
      (fun p : (Fin n → Real) × Real => lam • p) ''
        epigraph (Set.univ : Set (Fin n → Real)) f := by
  ext p
  rcases p with ⟨x, μ⟩
  constructor
  · intro hp
    have hle :
        rightScalarMultiple f lam x ≤ (μ : EReal) :=
      (mem_epigraph_univ_iff (f := rightScalarMultiple f lam)).1 hp
    have hmul :
        (lam : EReal) * f (lam⁻¹ • x) ≤ (μ : EReal) := by
      simpa [rightScalarMultiple_pos (f := f) (lam := lam) hf hlam x] using hle
    have hpos' : 0 < (lam⁻¹ : Real) := inv_pos.mpr hlam
    have hmul' :=
      ereal_mul_le_mul_of_pos_left_general (t := (lam⁻¹ : Real)) (ht := hpos') hmul
    have hle'' : f (lam⁻¹ • x) ≤ ((lam⁻¹ : Real) : EReal) * (μ : EReal) := by
      have hmul'' :
          (lam : EReal) * ((lam⁻¹ : EReal) * f (lam⁻¹ • x)) ≤
            ((lam⁻¹ : Real) : EReal) * (μ : EReal) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul'
      simpa [ereal_mul_inv_smul (t := lam) (ht := hlam) (x := f (lam⁻¹ • x))] using hmul''
    have hle' : f (lam⁻¹ • x) ≤ ((μ / lam : Real) : EReal) := by
      have hle''' : f (lam⁻¹ • x) ≤ ((μ * lam⁻¹ : Real) : EReal) := by
        simpa [mul_comm] using hle''
      simpa [div_eq_mul_inv] using hle'''
    exact (mem_image_smul_epigraph_iff (f := f) (lam := lam) hlam).2 hle'
  · intro hp
    have hle' :
        f (lam⁻¹ • x) ≤ ((μ / lam : Real) : EReal) :=
      (mem_image_smul_epigraph_iff (f := f) (lam := lam) hlam).1 hp
    have hmul' :=
      ereal_mul_le_mul_of_pos_left_general (t := lam) (ht := hlam) hle'
    have hmul :
        (lam : EReal) * f (lam⁻¹ • x) ≤ (μ : EReal) := by
      have hmul'' :
          (lam : EReal) * f (lam⁻¹ • x) ≤ (lam : EReal) * ((μ * lam⁻¹ : Real) : EReal) := by
        simpa [div_eq_mul_inv] using hmul'
      have hright :
          (lam : EReal) * ((μ * lam⁻¹ : Real) : EReal) = (μ : EReal) := by
        have hreal : (μ * lam⁻¹ : Real) = lam⁻¹ * μ := by
          ring
        calc
          (lam : EReal) * ((μ * lam⁻¹ : Real) : EReal)
              = (lam : EReal) * ((lam⁻¹ * μ : Real) : EReal) := by simp [hreal]
          _ = (lam : EReal) * ((lam⁻¹ : EReal) * (μ : EReal)) := by
              simp [EReal.coe_mul, EReal.coe_inv]
          _ = (μ : EReal) := by
              simpa using
                (ereal_mul_inv_smul (t := lam) (ht := hlam) (x := (μ : EReal)))
      calc
        (lam : EReal) * f (lam⁻¹ • x) ≤ (lam : EReal) * ((μ * lam⁻¹ : Real) : EReal) := hmul''
        _ = (μ : EReal) := hright
    have hle :
        rightScalarMultiple f lam x ≤ (μ : EReal) := by
      simpa [rightScalarMultiple_pos (f := f) (lam := lam) hf hlam x] using hmul
    exact (mem_epigraph_univ_iff (f := rightScalarMultiple f lam)).2 hle

/-- Scaling the embedded epigraph corresponds to the right scalar multiple. -/
lemma smul_embedded_epigraph_eq_embedded_epigraph_rightScalarMultiple {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hf : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {lam : Real} (hlam : 0 < lam) :
    (lam • ((prodLinearEquiv_append_coord (n := n)) ''
        epigraph (Set.univ : Set (Fin n → Real)) f)) =
      (prodLinearEquiv_append_coord (n := n)) ''
        epigraph (Set.univ : Set (Fin n → Real)) (rightScalarMultiple f lam) := by
  classical
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨p, hp, rfl⟩
    refine ⟨lam • p, ?_, ?_⟩
    · have hp' :
        lam • p ∈ (fun q : (Fin n → Real) × Real => lam • q) ''
          epigraph (Set.univ : Set (Fin n → Real)) f := ⟨p, hp, rfl⟩
      have hEq :=
        epigraph_rightScalarMultiple_eq_smul (f := f) (hf := hf) (lam := lam) hlam
      simpa [hEq] using hp'
    · simp
  · rintro ⟨p, hp, rfl⟩
    have hEq :=
      epigraph_rightScalarMultiple_eq_smul (f := f) (hf := hf) (lam := lam) hlam
    have hp' :
        p ∈ (fun q : (Fin n → Real) × Real => lam • q) ''
          epigraph (Set.univ : Set (Fin n → Real)) f := by
      simpa [hEq] using hp
    rcases hp' with ⟨q, hq, rfl⟩
    refine ⟨(prodLinearEquiv_append_coord (n := n)) q, ?_, ?_⟩
    · exact ⟨q, hq, rfl⟩
    · simp

/-- The closure of the cone over the embedded epigraph is the union of embedded
right-scalar multiples and the embedded recession epigraph. -/
lemma closure_convexConeGenerated_embedded_epigraph_eq_union {n : Nat}
    {f f0_plus : (Fin n → Real) → EReal}
    (hf : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hrec :
      Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) f) =
        epigraph (Set.univ : Set (Fin n → Real)) f0_plus)
    (hCne :
      Set.Nonempty
        ((prodLinearEquiv_append_coord (n := n)) ''
          epigraph (Set.univ : Set (Fin n → Real)) f))
    (hCclosed :
      IsClosed
        ((prodLinearEquiv_append_coord (n := n)) ''
          epigraph (Set.univ : Set (Fin n → Real)) f))
    (hCconv :
      Convex Real
        ((prodLinearEquiv_append_coord (n := n)) ''
          epigraph (Set.univ : Set (Fin n → Real)) f))
    (hC0 :
      (0 : Fin (n + 1) → Real) ∉
        ((prodLinearEquiv_append_coord (n := n)) ''
          epigraph (Set.univ : Set (Fin n → Real)) f)) :
    let C : Set (Fin (n + 1) → Real) :=
      (prodLinearEquiv_append_coord (n := n)) '' epigraph (Set.univ : Set (Fin n → Real)) f
    closure (convexConeGenerated (n + 1) C) =
      (⋃ (lam : Real) (_ : 0 < lam),
        (prodLinearEquiv_append_coord (n := n)) ''
          epigraph (Set.univ : Set (Fin n → Real)) (rightScalarMultiple f lam)) ∪
      (prodLinearEquiv_append_coord (n := n)) ''
        epigraph (Set.univ : Set (Fin n → Real)) f0_plus := by
  classical
  intro C
  let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (n + 1)))
  let C' : Set (EuclideanSpace Real (Fin (n + 1))) := Set.image e.symm C
  let recC : Set (Fin (n + 1) → Real) := Set.image e (Set.recessionCone C')
  let K : Set (Fin (n + 1) → Real) := convexConeGenerated (n + 1) C
  have hclosure :
      closure K = K ∪ recC ∧
        K ∪ recC = (⋃ (t : Real) (_ : 0 < t), (t • C)) ∪ recC := by
    simpa [e, C', recC, K] using
      (closure_convexConeGenerated_eq_union_recessionCone (C := C) hCne hCclosed hCconv hC0)
  have hclosure' :
      closure K = (⋃ (t : Real) (_ : 0 < t), (t • C)) ∪ recC := by
    calc
      closure K = K ∪ recC := hclosure.1
      _ = (⋃ (t : Real) (_ : 0 < t), (t • C)) ∪ recC := hclosure.2
  have hrecC' :
      recC = Set.recessionCone C := by
    have hrecC'' :
        Set.recessionCone C' = e.symm '' Set.recessionCone C := by
      simpa [C'] using
        (recessionCone_image_linearEquiv (e := e.symm.toLinearEquiv) (C := C))
    simp [recC, hrecC'', Set.image_image]
  have hrecC :
      recC =
        (prodLinearEquiv_append_coord (n := n)) ''
          epigraph (Set.univ : Set (Fin n → Real)) f0_plus := by
    have hrecC0 :
        Set.recessionCone C =
          (prodLinearEquiv_append_coord (n := n)) ''
            epigraph (Set.univ : Set (Fin n → Real)) f0_plus := by
      have hrecC0' :
          Set.recessionCone C =
            (prodLinearEquiv_append_coord (n := n)) ''
              Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) f) := by
        simpa [C] using
          (recessionCone_image_linearEquiv
            (e := prodLinearEquiv_append_coord (n := n))
            (C := epigraph (Set.univ : Set (Fin n → Real)) f))
      simpa [hrec] using hrecC0'
    simpa [hrecC'] using hrecC0
  have hUnion :
      (⋃ (t : Real) (_ : 0 < t), (t • C)) =
        ⋃ (t : Real) (_ : 0 < t),
          (prodLinearEquiv_append_coord (n := n)) ''
            epigraph (Set.univ : Set (Fin n → Real)) (rightScalarMultiple f t) := by
    ext y
    constructor
    · intro hy
      rcases (Set.mem_iUnion).1 hy with ⟨t, hy⟩
      rcases (Set.mem_iUnion).1 hy with ⟨ht, hy⟩
      have hsmul :=
        smul_embedded_epigraph_eq_embedded_epigraph_rightScalarMultiple
          (f := f) (hf := hf) (lam := t) ht
      have hsmul' :
          t • C =
            (prodLinearEquiv_append_coord (n := n)) ''
              epigraph (Set.univ : Set (Fin n → Real)) (rightScalarMultiple f t) := by
        simpa [C] using hsmul
      have hy' :
          y ∈
            (prodLinearEquiv_append_coord (n := n)) ''
              epigraph (Set.univ : Set (Fin n → Real)) (rightScalarMultiple f t) := by
        simpa [hsmul'] using hy
      refine Set.mem_iUnion.2 ⟨t, ?_⟩
      refine Set.mem_iUnion.2 ⟨ht, ?_⟩
      exact hy'
    · intro hy
      rcases (Set.mem_iUnion).1 hy with ⟨t, hy⟩
      rcases (Set.mem_iUnion).1 hy with ⟨ht, hy⟩
      have hsmul :=
        smul_embedded_epigraph_eq_embedded_epigraph_rightScalarMultiple
          (f := f) (hf := hf) (lam := t) ht
      have hsmul' :
          t • C =
            (prodLinearEquiv_append_coord (n := n)) ''
              epigraph (Set.univ : Set (Fin n → Real)) (rightScalarMultiple f t) := by
        simpa [C] using hsmul
      have hy' : y ∈ t • C := by
        simpa [hsmul'] using hy
      refine Set.mem_iUnion.2 ⟨t, ?_⟩
      refine Set.mem_iUnion.2 ⟨ht, ?_⟩
      exact hy'
  calc
    closure (convexConeGenerated (n + 1) C) =
        (⋃ (t : Real) (_ : 0 < t), (t • C)) ∪ recC := by
      simpa [K] using hclosure'
    _ =
        (⋃ (t : Real) (_ : 0 < t),
          (prodLinearEquiv_append_coord (n := n)) ''
            epigraph (Set.univ : Set (Fin n → Real)) (rightScalarMultiple f t)) ∪ recC := by
      simp [hUnion]
    _ =
        (⋃ (t : Real) (_ : 0 < t),
          (prodLinearEquiv_append_coord (n := n)) ''
            epigraph (Set.univ : Set (Fin n → Real)) (rightScalarMultiple f t)) ∪
          (prodLinearEquiv_append_coord (n := n)) ''
            epigraph (Set.univ : Set (Fin n → Real)) f0_plus := by
      simp [hrecC]

/-- The embedded image of the generated epigraph cone equals the generated cone of the embedded
epigraph. -/
lemma convexConeGenerated_embedded_epigraph_eq_image_convexConeGeneratedEpigraph {n : Nat}
    {f : (Fin n → Real) → EReal}
    (hf : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    let C : Set (Fin (n + 1) → Real) :=
      (prodLinearEquiv_append_coord (n := n)) '' epigraph (Set.univ : Set (Fin n → Real)) f
    (prodLinearEquiv_append_coord (n := n)) '' convexConeGeneratedEpigraph f =
      convexConeGenerated (n + 1) C := by
  classical
  intro C
  have hCconv : Convex Real C := by
    have hconv_epi :
        Convex Real (epigraph (Set.univ : Set (Fin n → Real)) f) := by
      simpa [ConvexFunctionOn] using hf
    simpa [C] using hconv_epi.linear_image (prodLinearEquiv_append_coord (n := n)).toLinearMap
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp' :=
      (mem_convexConeGeneratedEpigraph_iff (h := f) hf (p := p)).1 hp
    rcases hp' with rfl | ⟨lam, hlam, hp⟩
    · have hmem : (0 : Fin (n + 1) → Real) ∈ convexConeGenerated (n + 1) C := by
        exact (Set.mem_insert_iff).2 (Or.inl rfl)
      simpa using hmem
    · rcases hp with ⟨q, hq, rfl⟩
      have hqC : (prodLinearEquiv_append_coord (n := n)) q ∈ C := ⟨q, hq, rfl⟩
      have hmem :
          lam • (prodLinearEquiv_append_coord (n := n)) q ∈
            (ConvexCone.hull Real C : Set (Fin (n + 1) → Real)) := by
        refine (ConvexCone.mem_hull_of_convex (s := C) hCconv).2 ?_
        refine ⟨lam, hlam, ?_⟩
        exact ⟨(prodLinearEquiv_append_coord (n := n)) q, hqC, rfl⟩
      have hmap :
          (prodLinearEquiv_append_coord (n := n)) (lam • q) =
            lam • (prodLinearEquiv_append_coord (n := n)) q := by
        simp
      have hmem' :
          (prodLinearEquiv_append_coord (n := n)) (lam • q) ∈
            Set.insert (0 : Fin (n + 1) → Real)
              ((ConvexCone.hull Real C : Set (Fin (n + 1) → Real))) := by
        simpa [hmap] using (Set.mem_insert_iff).2 (Or.inr hmem)
      simpa [convexConeGenerated] using hmem'
  · intro hy
    have hy' :
        y = 0 ∨ y ∈ (ConvexCone.hull Real C : Set (Fin (n + 1) → Real)) := by
      simpa [convexConeGenerated, Set.mem_insert_iff] using hy
    rcases hy' with rfl | hyHull
    · have h0mem : (0 : (Fin n → Real) × Real) ∈ convexConeGeneratedEpigraph f := by
        exact (Set.mem_insert_iff).2 (Or.inl rfl)
      refine ⟨0, h0mem, ?_⟩
      simp
    · rcases
        (ConvexCone.mem_hull_of_convex (s := C) hCconv).1 hyHull with
        ⟨lam, hlam, hyC⟩
      rcases hyC with ⟨c, hcC, rfl⟩
      rcases hcC with ⟨q, hq, rfl⟩
      have hq' :
          q ∈ convexConeGeneratedEpigraph f := by
        have hq'' :
            q ∈ (ConvexCone.hull ℝ (epigraph (Set.univ : Set (Fin n → Real)) f) :
              Set ((Fin n → Real) × Real)) :=
          ConvexCone.subset_hull hq
        exact (Set.mem_insert_iff).2 (Or.inr hq'')
      have hsmul :
          lam • q ∈ convexConeGeneratedEpigraph f :=
        smul_mem_convexConeGeneratedEpigraph (h := f) hlam hq'
      refine ⟨lam • q, hsmul, ?_⟩
      simp

/-- The generated epigraph cone lies in the epigraph of its inf-section. -/
lemma convexConeGeneratedEpigraph_subset_epigraph_posHom {n : Nat}
    {f : (Fin n → Real) → EReal} :
    let k := positivelyHomogeneousConvexFunctionGenerated f
    convexConeGeneratedEpigraph f ⊆ epigraph (Set.univ : Set (Fin n → Real)) k := by
  classical
  intro k p hp
  rcases p with ⟨x, μ⟩
  have hmem :
      (μ : EReal) ∈
        (fun t : ℝ => (t : EReal)) '' {t : ℝ | (x, t) ∈ convexConeGeneratedEpigraph f} := by
    exact ⟨μ, hp, rfl⟩
  have hle : k x ≤ (μ : EReal) := by
    dsimp [k, positivelyHomogeneousConvexFunctionGenerated]
    exact sInf_le hmem
  exact (mem_epigraph_univ_iff (f := k)).2 hle

/-- Remove the `prodLinearEquiv_append_coord` embedding from the closure/union formula. -/
lemma closure_convexConeGeneratedEpigraph_eq_union {n : Nat}
    {f f0_plus : (Fin n → Real) → EReal}
    (hclosure_union' :
      closure ((prodLinearEquiv_append_coord (n := n)) '' convexConeGeneratedEpigraph f) =
        (⋃ (lam : Real) (_ : 0 < lam),
          (prodLinearEquiv_append_coord (n := n)) ''
            epigraph (Set.univ : Set (Fin n → Real)) (rightScalarMultiple f lam)) ∪
        (prodLinearEquiv_append_coord (n := n)) ''
          epigraph (Set.univ : Set (Fin n → Real)) f0_plus) :
    closure (convexConeGeneratedEpigraph f) =
      (⋃ (lam : Real) (_ : 0 < lam),
        epigraph (Set.univ : Set (Fin n → Real)) (rightScalarMultiple f lam)) ∪
      epigraph (Set.univ : Set (Fin n → Real)) f0_plus := by
  classical
  let e := prodLinearEquiv_append_coord (n := n)
  let hhome := e.toAffineEquiv.toHomeomorphOfFiniteDimensional
  ext p
  have hmem_closure :
      p ∈ closure (convexConeGeneratedEpigraph f) ↔
        e p ∈ closure (e '' convexConeGeneratedEpigraph f) := by
    constructor
    · intro hp
      have hp' : hhome p ∈ hhome '' closure (convexConeGeneratedEpigraph f) := ⟨p, hp, rfl⟩
      have himage :
          hhome '' closure (convexConeGeneratedEpigraph f) =
            closure (hhome '' convexConeGeneratedEpigraph f) :=
        hhome.image_closure (convexConeGeneratedEpigraph f)
      have hp'' :
          hhome p ∈ closure (hhome '' convexConeGeneratedEpigraph f) := by
        simpa [himage] using hp'
      simpa [hhome, AffineEquiv.coe_toHomeomorphOfFiniteDimensional] using hp''
    · intro hp
      have himage_symm :
          hhome.symm '' closure (hhome '' convexConeGeneratedEpigraph f) =
            closure (convexConeGeneratedEpigraph f) := by
        simpa [Set.image_image] using
          (hhome.symm.image_closure (hhome '' convexConeGeneratedEpigraph f))
      have hp' :
          p ∈ hhome.symm '' closure (hhome '' convexConeGeneratedEpigraph f) := by
        refine ⟨hhome p, ?_, by simp⟩
        simpa [hhome, AffineEquiv.coe_toHomeomorphOfFiniteDimensional] using hp
      simpa [himage_symm] using hp'
  have hmem_union :
      e p ∈
          (⋃ (lam : Real) (_ : 0 < lam),
            e '' epigraph (Set.univ : Set (Fin n → Real)) (rightScalarMultiple f lam)) ∪
            e '' epigraph (Set.univ : Set (Fin n → Real)) f0_plus ↔
        p ∈
          (⋃ (lam : Real) (_ : 0 < lam),
            epigraph (Set.univ : Set (Fin n → Real)) (rightScalarMultiple f lam)) ∪
            epigraph (Set.univ : Set (Fin n → Real)) f0_plus := by
    constructor
    · intro hp
      rcases hp with hp | hp
      · rcases (Set.mem_iUnion).1 hp with ⟨lam, hp⟩
        rcases (Set.mem_iUnion).1 hp with ⟨hlam, hp⟩
        rcases hp with ⟨q, hq, hqeq⟩
        have hqp : q = p := by
          apply e.injective
          simpa using hqeq
        have hp' :
            p ∈ epigraph (Set.univ : Set (Fin n → Real)) (rightScalarMultiple f lam) := by
          simpa [hqp] using hq
        refine Or.inl ?_
        refine Set.mem_iUnion.2 ⟨lam, ?_⟩
        refine Set.mem_iUnion.2 ⟨hlam, ?_⟩
        exact hp'
      · rcases hp with ⟨q, hq, hqeq⟩
        have hqp : q = p := by
          apply e.injective
          simpa using hqeq
        have hp' : p ∈ epigraph (Set.univ : Set (Fin n → Real)) f0_plus := by
          simpa [hqp] using hq
        exact Or.inr hp'
    · intro hp
      rcases hp with hp | hp
      · rcases (Set.mem_iUnion).1 hp with ⟨lam, hp⟩
        rcases (Set.mem_iUnion).1 hp with ⟨hlam, hp⟩
        have hp' :
            e p ∈ e '' epigraph (Set.univ : Set (Fin n → Real)) (rightScalarMultiple f lam) :=
          ⟨p, hp, rfl⟩
        refine Or.inl ?_
        refine Set.mem_iUnion.2 ⟨lam, ?_⟩
        refine Set.mem_iUnion.2 ⟨hlam, ?_⟩
        exact hp'
      · exact Or.inr ⟨p, hp, rfl⟩
  have hclosure_union'_e :
      closure (e '' convexConeGeneratedEpigraph f) =
        (⋃ (lam : Real) (_ : 0 < lam),
          e '' epigraph (Set.univ : Set (Fin n → Real)) (rightScalarMultiple f lam)) ∪
          e '' epigraph (Set.univ : Set (Fin n → Real)) f0_plus := by
    simpa [e] using hclosure_union'
  have hclosure_union'' :
      e p ∈ closure (e '' convexConeGeneratedEpigraph f) ↔
        e p ∈
          (⋃ (lam : Real) (_ : 0 < lam),
            e '' epigraph (Set.univ : Set (Fin n → Real)) (rightScalarMultiple f lam)) ∪
            e '' epigraph (Set.univ : Set (Fin n → Real)) f0_plus := by
    constructor
    · intro hp
      simpa [hclosure_union'_e] using hp
    · intro hp
      simpa [hclosure_union'_e] using hp
  calc
    p ∈ closure (convexConeGeneratedEpigraph f) ↔
        e p ∈ closure (e '' convexConeGeneratedEpigraph f) := hmem_closure
    _ ↔
        e p ∈
          (⋃ (lam : Real) (_ : 0 < lam),
            e '' epigraph (Set.univ : Set (Fin n → Real)) (rightScalarMultiple f lam)) ∪
            e '' epigraph (Set.univ : Set (Fin n → Real)) f0_plus := hclosure_union''
    _ ↔
        p ∈
          (⋃ (lam : Real) (_ : 0 < lam),
            epigraph (Set.univ : Set (Fin n → Real)) (rightScalarMultiple f lam)) ∪
            epigraph (Set.univ : Set (Fin n → Real)) f0_plus := hmem_union

/-- The positively homogeneous hull is convex and has a nonempty epigraph. -/
lemma posHomGenerated_convex_and_nonempty {n : Nat} {f : (Fin n → Real) → EReal}
    (hfconv : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    let k := positivelyHomogeneousConvexFunctionGenerated f
    ConvexFunctionOn (Set.univ : Set (Fin n → Real)) k ∧
      Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) k) := by
  classical
  intro k
  have hmax :
      (∃ C : ConvexCone ℝ ((Fin n → Real) × Real),
        (C : Set ((Fin n → Real) × Real)) =
          epigraph (Set.univ : Set (Fin n → Real)) k ∧
        (0 : (Fin n → Real) × Real) ∈
          epigraph (Set.univ : Set (Fin n → Real)) k) ∧
      (ConvexFunctionOn (Set.univ : Set (Fin n → Real)) k ∧
        PositivelyHomogeneous k ∧
        k 0 ≤ 0 ∧
        k ≤ f) ∧
      (∀ u : (Fin n → Real) → EReal,
        PositivelyHomogeneous u →
        ConvexFunctionOn (Set.univ : Set (Fin n → Real)) u →
        u 0 ≤ 0 → u ≤ f → u ≤ k) := by
    simpa [k] using
      (maximality_posHomogeneousHull (n := n) (h := f) hfconv)
  have hk_conv : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) k := hmax.2.1.1
  have hk_nonempty : Set.Nonempty (epigraph (Set.univ : Set (Fin n → Real)) k) := by
    rcases hmax.1 with ⟨C, hCeq, hmem⟩
    exact ⟨0, by simpa [hCeq] using hmem⟩
  exact ⟨hk_conv, hk_nonempty⟩

/-- If `0` lies in the effective domain, the positive-scaling infimum formula holds. -/
lemma posHomGenerated_formula_pos {n : Nat} {f : (Fin n → Real) → EReal}
    (hfconv : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (hfinite : ∃ x, f x ≠ (⊤ : EReal))
    (hdom0 : (0 : Fin n → Real) ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f) :
    let k := positivelyHomogeneousConvexFunctionGenerated f
    ∀ x : Fin n → Real,
      k x = sInf { z : EReal | ∃ lam : Real, 0 < lam ∧ z = rightScalarMultiple f lam x } := by
  classical
  intro k x
  have h0ne : f 0 ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (x := (0 : Fin n → Real)) hdom0
  have h0lt : f 0 < (⊤ : EReal) := (lt_top_iff_ne_top).2 h0ne
  have hpos :=
    (infimumRepresentation_posHomogeneousHull (h := f) hfconv hfinite).2
  have hpos' := hpos x (Or.inr h0lt)
  simpa [k] using hpos'

/-- A proper epigraph has no negative vertical recession direction. -/
lemma no_neg_vertical_recession_epigraph {n : Nat} {f : (Fin n → Real) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) {μ : Real}
    (hμ : μ < 0) :
    (0, μ) ∉ Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) f) := by
  classical
  intro hmem
  rcases hproper.2.1 with ⟨p, hp⟩
  have hle : f p.1 ≤ (p.2 : EReal) := (mem_epigraph_univ_iff (f := f)).1 hp
  have hnotbot : f p.1 ≠ (⊥ : EReal) := hproper.2.2 p.1 (by simp)
  cases hfx : f p.1 using EReal.rec with
  | bot =>
      exact (hnotbot hfx)
  | top =>
      refine (not_top_le_coe (r := p.2) ?_)
      rw [← hfx]
      exact hle
  | coe r =>
      have hp' : (p.1, r) ∈ epigraph (Set.univ : Set (Fin n → Real)) f := by
        exact (mem_epigraph_univ_iff (f := f)).2 (by simp [hfx])
      have hmem' :=
        hmem (x := (p.1, r)) hp' (t := (1 : Real)) (by exact zero_le_one)
      have hmem'' :
          (p.1, r + μ) ∈ epigraph (Set.univ : Set (Fin n → Real)) f := by
        simpa using hmem'
      have hle' : f p.1 ≤ ((r + μ : Real) : EReal) :=
        (mem_epigraph_univ_iff (f := f)).1 hmem''
      have hlt : (r + μ : Real) < r := by linarith
      have hlt' : ((r + μ : Real) : EReal) < (r : EReal) :=
        (EReal.coe_lt_coe_iff).2 hlt
      have hnotle : ¬ (r : EReal) ≤ ((r + μ : Real) : EReal) := not_le_of_gt hlt'
      exact hnotle (by simpa [hfx] using hle')

end Section09
end Chap02
