/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Guangxuan Pan, Siyuan Shao, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section10_part7

noncomputable section

section Chap02
section Section10

open scoped BigOperators

/-- If `C` is open and `x₀ ∈ C`, then some closed ball around `x₀` is contained in `C`. -/
lemma Section10.exists_closedBall_subset_of_isOpen {n : ℕ}
    {C : Set (EuclideanSpace Real (Fin n))} (hCopen : IsOpen C) {x0 : EuclideanSpace Real (Fin n)}
    (hx0 : x0 ∈ C) : ∃ r : ℝ, 0 < r ∧ Metric.closedBall x0 r ⊆ C := by
  rcases Metric.mem_nhds_iff.1 (hCopen.mem_nhds hx0) with ⟨r, hrpos, hrsub⟩
  refine ⟨r / 2, by linarith [hrpos], ?_⟩
  intro x hx
  have hx' : x ∈ Metric.ball x0 r := by
    have hlt : r / 2 < r := by linarith [hrpos]
    exact (Metric.closedBall_subset_ball hlt) hx
  exact hrsub hx'

/-- In a locally compact space, every point admits a compact neighborhood. -/
lemma Section10.exists_compact_mem_nhds_of_locallyCompact {T : Type*} [TopologicalSpace T]
    [LocallyCompactSpace T] (t0 : T) : ∃ K : Set T, IsCompact K ∧ K ∈ nhds t0 := by
  simpa using (exists_compact_mem_nhds t0)

/-- A continuous real-valued function is bounded on a compact set (rephrased over a subtype). -/
lemma Section10.isBounded_range_subtype_of_continuous_compact {T : Type*} [TopologicalSpace T]
    {K : Set T} (hK : IsCompact K) {g : T → ℝ} (hg : Continuous g) :
    Bornology.IsBounded (Set.range fun t : {t // t ∈ K} => g t.1) := by
  have hEq : (Set.range fun t : {t // t ∈ K} => g t.1) = g '' K := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t.1, t.2, rfl⟩
    · rintro ⟨t, htK, rfl⟩
      exact ⟨⟨t, htK⟩, rfl⟩
  have himage : IsCompact (g '' K) := hK.image hg
  simpa [hEq] using himage.isBounded

/-- Theorem 10.7. Let `C` be a relatively open convex set in `ℝ^n`, and let `T` be a locally
compact topological space. Let `f : ℝ^n × T → ℝ` be such that:

- for each `t ∈ T`, the function `x ↦ f (x,t)` is convex on `C`;
- for each `x ∈ C`, the function `t ↦ f (x,t)` is continuous on `T`.

Then `f` is continuous on `C × T` (i.e. jointly continuous in `x` and `t`). -/
theorem convexOn_continuousOn_prod_of_locallyCompact {n : ℕ} {T : Type*} [TopologicalSpace T]
    [LocallyCompactSpace T] {C : Set (EuclideanSpace Real (Fin n))} (hCopen : IsOpen C)
    (hCconv : Convex ℝ C) (f : EuclideanSpace Real (Fin n) × T → Real)
    (hfconv : ∀ t, ConvexOn ℝ C (fun x => f (x, t)))
    (hfcont : ∀ x ∈ C, Continuous fun t => f (x, t)) :
    ContinuousOn f (C ×ˢ (Set.univ : Set T)) := by
  classical
  intro p hp
  rcases p with ⟨x0, t0⟩
  have hx0 : x0 ∈ C := hp.1
  -- We show continuity within `C ×ˢ univ` at the point `(x0,t0)`.
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  -- Choose a compact neighborhood `K` of `t0`.
  rcases Section10.exists_compact_mem_nhds_of_locallyCompact (t0 := t0) with ⟨K, hKcomp, hKnhds⟩
  -- Choose a closed ball around `x0` contained in `C`.
  rcases Section10.exists_closedBall_subset_of_isOpen (n := n) (C := C) hCopen hx0 with
    ⟨r, hrpos, hballsub⟩
  let S : Set (EuclideanSpace Real (Fin n)) := Metric.closedBall x0 r
  -- Index the family by the subtype of `K`.
  let I : Type _ := {t : T // t ∈ K}
  let g : I → EuclideanSpace Real (Fin n) → ℝ := fun t x => f (x, t.1)
  have hgconv : ∀ t : I, ConvexOn ℝ C (fun x => g t x) := by
    intro t
    simpa [g] using hfconv t.1
  -- Pointwise boundedness of the family on `C` comes from continuity in `t` on the compact set `K`.
  have hgpt : Function.PointwiseBoundedOn g C := by
    intro x hx
    -- Use compactness of `K` and continuity of `t ↦ f(x,t)`.
    have : Bornology.IsBounded (Set.range fun t : I => (fun t : T => f (x, t)) t.1) :=
      Section10.isBounded_range_subtype_of_continuous_compact (T := T) (K := K) hKcomp
        (g := fun t : T => f (x, t)) (hfcont x hx)
    simpa [g] using this
  -- Apply Theorem 10.6 to obtain an equi-Lipschitz bound on the closed ball `S`.
  have hSclosed : IsClosed S := Metric.isClosed_closedBall
  have hSbdd : Bornology.IsBounded S := Metric.isBounded_closedBall
  have hSsub : S ⊆ C := hballsub
  have hEquiLip : Function.EquiLipschitzRelativeTo g S := by
    exact
      (convexOn_family_uniformlyBoundedOn_and_equiLipschitzRelativeTo_of_pointwiseBoundedOn
            (n := n) (I := I) (C := C) hCopen hCconv g hgconv hgpt (S := S) hSclosed hSbdd hSsub).2
  rcases hEquiLip with ⟨L, hL⟩
  have hL1pos : 0 < ((L : ℝ) + 1) := by
    have hLnonneg : 0 ≤ (L : ℝ) := by exact_mod_cast L.2
    linarith
  have hL1ne : ((L : ℝ) + 1) ≠ 0 := ne_of_gt hL1pos
  -- Control the `t`-variation at `x0` using continuity.
  have hcont_t : Filter.Tendsto (fun t : T => f (x0, t)) (nhds t0) (nhds (f (x0, t0))) :=
    (hfcont x0 hx0).tendsto t0
  have hV' : ∀ᶠ t in nhds t0, dist (f (x0, t)) (f (x0, t0)) < ε / 2 :=
    (Metric.tendsto_nhds.1 hcont_t) (ε / 2) (by linarith)
  let V : Set T := {t : T | dist (f (x0, t)) (f (x0, t0)) < ε / 2} ∩ K
  have hV : V ∈ nhds t0 := Filter.inter_mem hV' hKnhds
  -- Control the `x`-variation uniformly for `t ∈ K` using the equi-Lipschitz estimate.
  let δx : ℝ := (ε / 2) / ((L : ℝ) + 1)
  have hδxpos : 0 < δx := div_pos (by linarith) hL1pos
  let U : Set (EuclideanSpace Real (Fin n)) := Metric.ball x0 (min r δx)
  have hU : U ∈ nhdsWithin x0 C :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x0 (lt_min hrpos hδxpos))
  -- Build a neighborhood in the product filter and use the triangle inequality.
  have hEq :
      nhdsWithin (x0, t0) (C ×ˢ (Set.univ : Set T)) = (nhdsWithin x0 C) ×ˢ (nhds t0) := by
    simpa [nhdsWithin_univ] using (nhdsWithin_prod_eq x0 t0 C (Set.univ : Set T))
  have hUV' : U ×ˢ V ∈ (nhdsWithin x0 C) ×ˢ (nhds t0) :=
    Filter.prod_mem_prod hU hV
  have hUV : U ×ˢ V ∈ nhdsWithin (x0, t0) (C ×ˢ (Set.univ : Set T)) := by
    simpa [hEq] using hUV'
  refine Filter.mem_of_superset hUV ?_
  rintro ⟨x, t⟩ hxt
  rcases hxt with ⟨hxU, htV⟩
  have htK : t ∈ K := htV.2
  have htcont : dist (f (x0, t)) (f (x0, t0)) < ε / 2 := htV.1
  have hxlt_min : dist x x0 < min r δx := by simpa [U, Metric.mem_ball] using hxU
  have hxlt_r : dist x x0 < r := lt_of_lt_of_le hxlt_min (min_le_left _ _)
  have hxlt_δx : dist x x0 < δx := lt_of_lt_of_le hxlt_min (min_le_right _ _)
  have hxS : x ∈ S := by
    have hxle : dist x x0 ≤ r := le_of_lt hxlt_r
    simpa [S, Metric.mem_closedBall] using hxle
  have hx0S : x0 ∈ S := by
    simpa [S] using
      (Metric.mem_closedBall_self (α := EuclideanSpace Real (Fin n)) (x := x0) (ε := r)
        (le_of_lt hrpos))
  let i : I := ⟨t, htK⟩
  have hdist_le : dist (f (x, t)) (f (x0, t)) ≤ (L : ℝ) * dist x x0 := by
    -- `dist x x0` is symmetric, so it does not matter which order we use.
    simpa [g, dist_comm] using (hL i).dist_le_mul x hxS x0 hx0S
  have hmul_lt : ((L : ℝ) + 1) * dist x x0 < ε / 2 := by
    have hxlt_δx' : dist x x0 < δx := by simpa [dist_comm] using hxlt_δx
    have : ((L : ℝ) + 1) * dist x x0 < ((L : ℝ) + 1) * δx :=
      mul_lt_mul_of_pos_left hxlt_δx' hL1pos
    have hmul : ((L : ℝ) + 1) * δx = ε / 2 := by
      simpa [δx] using (mul_div_cancel₀ (a := ε / 2) (b := (L : ℝ) + 1) hL1ne)
    simpa [hmul] using this
  have hle_mul :
      (L : ℝ) * dist x x0 ≤ ((L : ℝ) + 1) * dist x x0 := by
    have hLle : (L : ℝ) ≤ (L : ℝ) + 1 := by linarith
    exact mul_le_mul_of_nonneg_right hLle dist_nonneg
  have hxcont : dist (f (x, t)) (f (x0, t)) < ε / 2 :=
    lt_of_le_of_lt (le_trans hdist_le hle_mul) hmul_lt
  have htri :
      dist (f (x, t)) (f (x0, t0)) ≤
        dist (f (x, t)) (f (x0, t)) + dist (f (x0, t)) (f (x0, t0)) :=
    dist_triangle (f (x, t)) (f (x0, t)) (f (x0, t0))
  have :
      dist (f (x, t)) (f (x0, t0)) < ε / 2 + ε / 2 :=
    lt_of_le_of_lt htri (add_lt_add hxcont htcont)
  simpa [add_halves] using this

/-- Theorem 10.7 (variant). The same conclusion holds if the continuity-in-`t` assumption is
weakened as follows: there exists `C' ⊆ C` with `closure C' ⊇ C` such that `t ↦ f (x,t)` is
continuous for each `x ∈ C'`. -/
theorem convexOn_continuousOn_prod_of_locallyCompact_of_exists_subset_closure {n : ℕ} {T : Type*}
    [TopologicalSpace T] [LocallyCompactSpace T] {C : Set (EuclideanSpace Real (Fin n))}
    (hCopen : IsOpen C) (hCconv : Convex ℝ C) (f : EuclideanSpace Real (Fin n) × T → Real)
    (hfconv : ∀ t, ConvexOn ℝ C (fun x => f (x, t))) {C' : Set (EuclideanSpace Real (Fin n))}
    (hC'sub : C' ⊆ C) (hCclosure : C ⊆ closure C')
    (hfcont : ∀ x ∈ C', Continuous fun t => f (x, t)) :
    ContinuousOn f (C ×ˢ (Set.univ : Set T)) := by
  classical
  intro p hp
  rcases p with ⟨x0, t0⟩
  have hx0 : x0 ∈ C := hp.1
  -- We show continuity within `C ×ˢ univ` at the point `(x0,t0)`.
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  -- Choose a compact neighborhood `K` of `t0`.
  rcases Section10.exists_compact_mem_nhds_of_locallyCompact (t0 := t0) with ⟨K, hKcomp, hKnhds⟩
  have ht0K : t0 ∈ K := mem_of_mem_nhds hKnhds
  -- Choose a closed ball around `x0` contained in `C`.
  rcases Section10.exists_closedBall_subset_of_isOpen (n := n) (C := C) hCopen hx0 with
    ⟨r, hrpos, hballsub⟩
  let S : Set (EuclideanSpace Real (Fin n)) := Metric.closedBall x0 r
  -- Index the family by the subtype of `K`.
  let I : Type _ := {t : T // t ∈ K}
  let g : I → EuclideanSpace Real (Fin n) → ℝ := fun t x => f (x, t.1)
  have hgconv : ∀ t : I, ConvexOn ℝ C (fun x => g t x) := by
    intro t
    simpa [g] using hfconv t.1
  -- The convex-hull hypothesis required for Theorem 10.6 (variant).
  have hC'hull : C ⊆ convexHull ℝ (closure C') :=
    hCclosure.trans (subset_convexHull ℝ (closure C'))
  -- Pointwise upper bounds on `C'` come from continuity in `t` on the compact set `K`.
  have hC'bdAbove : ∀ x ∈ C', BddAbove (Set.range fun t : I => g t x) := by
    intro x hxC'
    have hbdd :
        Bornology.IsBounded (Set.range fun t : I => (fun t : T => f (x, t)) t.1) :=
      Section10.isBounded_range_subtype_of_continuous_compact (T := T) (K := K) hKcomp
        (g := fun t : T => f (x, t)) (hfcont x hxC')
    rcases hbdd.subset_closedBall (0 : ℝ) with ⟨R, hR⟩
    refine ⟨R, ?_⟩
    intro y hy
    have hy' : y ∈ Metric.closedBall (0 : ℝ) R := hR hy
    have hyR : |y| ≤ R := by
      simpa [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hy'
    exact (abs_le.mp hyR).2
  -- Hypothesis (b) of Theorem 10.6 (variant): a single `x ∈ C` with a lower bound.
  have hx0C'cl : x0 ∈ closure C' := hCclosure hx0
  have hexists_bddBelow : ∃ x ∈ C, BddBelow (Set.range fun t : I => g t x) := by
    rcases (Metric.mem_closure_iff.1 hx0C'cl) 1 (by linarith) with ⟨xw, hxwC', -⟩
    have hbdd :
        Bornology.IsBounded (Set.range fun t : I => (fun t : T => f (xw, t)) t.1) :=
      Section10.isBounded_range_subtype_of_continuous_compact (T := T) (K := K) hKcomp
        (g := fun t : T => f (xw, t)) (hfcont xw hxwC')
    rcases hbdd.subset_closedBall (0 : ℝ) with ⟨R, hR⟩
    refine ⟨xw, hC'sub hxwC', ?_⟩
    refine ⟨-R, ?_⟩
    intro y hy
    have hy' : y ∈ Metric.closedBall (0 : ℝ) R := hR hy
    have hyR : |y| ≤ R := by
      simpa [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hy'
    exact (abs_le.mp hyR).1
  -- Apply Theorem 10.6 (variant) to obtain an equi-Lipschitz bound on the closed ball `S`.
  have hSclosed : IsClosed S := Metric.isClosed_closedBall
  have hSbdd : Bornology.IsBounded S := Metric.isBounded_closedBall
  have hSsub : S ⊆ C := hballsub
  have hEquiLip : Function.EquiLipschitzRelativeTo g S := by
    exact
      (convexOn_family_uniformlyBoundedOn_and_equiLipschitzRelativeTo_of_exists_subset
            (n := n) (I := I) (C := C) hCopen hCconv g hgconv (C' := C') hC'sub hC'hull
            hC'bdAbove hexists_bddBelow (S := S) hSclosed hSbdd hSsub).2
  rcases hEquiLip with ⟨L, hL⟩
  have hL1pos : 0 < ((L : ℝ) + 1) := by
    have hLnonneg : 0 ≤ (L : ℝ) := by exact_mod_cast L.2
    linarith
  have hL1ne : ((L : ℝ) + 1) ≠ 0 := ne_of_gt hL1pos
  -- Pick a nearby `x1 ∈ C' ∩ S` and use continuity in `t` at `x1`
  -- to control the `t`-variation at `x0`.
  have hε8 : 0 < ε / 8 := by linarith
  let δ1 : ℝ := min r ((ε / 8) / ((L : ℝ) + 1))
  have hδ1pos : 0 < δ1 := lt_min hrpos (div_pos hε8 hL1pos)
  rcases (Metric.mem_closure_iff.1 hx0C'cl) δ1 hδ1pos with ⟨x1, hx1C', hx1dist⟩
  have hx1dist_x0x1 : dist x0 x1 < δ1 := by simpa using hx1dist
  have hx1dist_x1x0 : dist x1 x0 < δ1 := by simpa [dist_comm] using hx1dist
  have hx1S : x1 ∈ S := by
    have hx1le : dist x1 x0 ≤ r := le_of_lt (lt_of_lt_of_le hx1dist_x1x0 (min_le_left _ _))
    simpa [S, Metric.mem_closedBall, dist_comm] using hx1le
  have hx0S : x0 ∈ S := by
    simpa [S] using
      (Metric.mem_closedBall_self (α := EuclideanSpace Real (Fin n)) (x := x0) (ε := r)
        (le_of_lt hrpos))
  have hcont_t1 :
      Filter.Tendsto (fun t : T => f (x1, t)) (nhds t0) (nhds (f (x1, t0))) :=
    (hfcont x1 hx1C').tendsto t0
  have hV' : ∀ᶠ t in nhds t0, dist (f (x1, t)) (f (x1, t0)) < ε / 4 :=
    (Metric.tendsto_nhds.1 hcont_t1) (ε / 4) (by linarith)
  let V : Set T := {t : T | dist (f (x1, t)) (f (x1, t0)) < ε / 4} ∩ K
  have hV : V ∈ nhds t0 := Filter.inter_mem hV' hKnhds
  -- Control the `x`-variation uniformly for `t ∈ K` using the equi-Lipschitz estimate.
  let δx : ℝ := (ε / 2) / ((L : ℝ) + 1)
  have hδxpos : 0 < δx := div_pos (by linarith) hL1pos
  let U : Set (EuclideanSpace Real (Fin n)) := Metric.ball x0 (min r δx)
  have hU : U ∈ nhdsWithin x0 C :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x0 (lt_min hrpos hδxpos))
  -- Build a neighborhood in the product filter.
  have hEq :
      nhdsWithin (x0, t0) (C ×ˢ (Set.univ : Set T)) = (nhdsWithin x0 C) ×ˢ (nhds t0) := by
    simpa [nhdsWithin_univ] using (nhdsWithin_prod_eq x0 t0 C (Set.univ : Set T))
  have hUV' : U ×ˢ V ∈ (nhdsWithin x0 C) ×ˢ (nhds t0) :=
    Filter.prod_mem_prod hU hV
  have hUV : U ×ˢ V ∈ nhdsWithin (x0, t0) (C ×ˢ (Set.univ : Set T)) := by
    simpa [hEq] using hUV'
  refine Filter.mem_of_superset hUV ?_
  rintro ⟨x, t⟩ hxt
  rcases hxt with ⟨hxU, htV⟩
  have htK : t ∈ K := htV.2
  have htcont1 : dist (f (x1, t)) (f (x1, t0)) < ε / 4 := htV.1
  have hxlt_min : dist x x0 < min r δx := by simpa [U, Metric.mem_ball] using hxU
  have hxlt_r : dist x x0 < r := lt_of_lt_of_le hxlt_min (min_le_left _ _)
  have hxlt_δx : dist x x0 < δx := lt_of_lt_of_le hxlt_min (min_le_right _ _)
  have hxS : x ∈ S := by
    have hxle : dist x x0 ≤ r := le_of_lt hxlt_r
    simpa [S, Metric.mem_closedBall] using hxle
  let i : I := ⟨t, htK⟩
  have hdist_le : dist (f (x, t)) (f (x0, t)) ≤ (L : ℝ) * dist x x0 := by
    -- `dist x x0` is symmetric, so it does not matter which order we use.
    simpa [g, dist_comm] using (hL i).dist_le_mul x hxS x0 hx0S
  have hmul_lt : ((L : ℝ) + 1) * dist x x0 < ε / 2 := by
    have hxlt_δx' : dist x x0 < δx := by simpa [dist_comm] using hxlt_δx
    have : ((L : ℝ) + 1) * dist x x0 < ((L : ℝ) + 1) * δx :=
      mul_lt_mul_of_pos_left hxlt_δx' hL1pos
    have hmul : ((L : ℝ) + 1) * δx = ε / 2 := by
      simpa [δx] using (mul_div_cancel₀ (a := ε / 2) (b := (L : ℝ) + 1) hL1ne)
    simpa [hmul] using this
  have hle_mul :
      (L : ℝ) * dist x x0 ≤ ((L : ℝ) + 1) * dist x x0 := by
    have hLle : (L : ℝ) ≤ (L : ℝ) + 1 := by linarith
    exact mul_le_mul_of_nonneg_right hLle dist_nonneg
  have hxcont : dist (f (x, t)) (f (x0, t)) < ε / 2 :=
    lt_of_le_of_lt (le_trans hdist_le hle_mul) hmul_lt
  have hx1lt_δ1' : dist x0 x1 < (ε / 8) / ((L : ℝ) + 1) := by
    exact lt_of_lt_of_le hx1dist_x0x1 (min_le_right _ _)
  have hmul_x1 :
      ((L : ℝ) + 1) * dist x0 x1 < ε / 8 := by
    have :
        ((L : ℝ) + 1) * dist x0 x1 <
          ((L : ℝ) + 1) * ((ε / 8) / ((L : ℝ) + 1)) :=
      mul_lt_mul_of_pos_left hx1lt_δ1' hL1pos
    have hmul :
        ((L : ℝ) + 1) * ((ε / 8) / ((L : ℝ) + 1)) = ε / 8 := by
      simp [mul_div_cancel₀, hL1ne]
    simpa [hmul] using this
  have hLx0x1 : (L : ℝ) * dist x0 x1 < ε / 8 := by
    have hle :
        (L : ℝ) * dist x0 x1 ≤ ((L : ℝ) + 1) * dist x0 x1 := by
      have hLle : (L : ℝ) ≤ (L : ℝ) + 1 := by linarith
      exact mul_le_mul_of_nonneg_right hLle dist_nonneg
    exact lt_of_le_of_lt hle hmul_x1
  have htcont0 : dist (f (x0, t)) (f (x0, t0)) < ε / 2 := by
    let i0 : I := ⟨t0, ht0K⟩
    have hdist_xt : dist (f (x0, t)) (f (x1, t)) ≤ (L : ℝ) * dist x0 x1 := by
      simpa [g] using (hL i).dist_le_mul x0 hx0S x1 hx1S
    have hdist_x0t0 :
        dist (f (x1, t0)) (f (x0, t0)) ≤ (L : ℝ) * dist x0 x1 := by
      have :
          dist (f (x0, t0)) (f (x1, t0)) ≤ (L : ℝ) * dist x0 x1 := by
        simpa [g] using (hL i0).dist_le_mul x0 hx0S x1 hx1S
      simpa [dist_comm] using this
    have htri1 :
        dist (f (x0, t)) (f (x0, t0)) ≤
          dist (f (x0, t)) (f (x1, t)) +
            dist (f (x1, t)) (f (x1, t0)) +
              dist (f (x1, t0)) (f (x0, t0)) := by
      calc
        dist (f (x0, t)) (f (x0, t0)) ≤
            dist (f (x0, t)) (f (x1, t)) + dist (f (x1, t)) (f (x0, t0)) :=
          dist_triangle (f (x0, t)) (f (x1, t)) (f (x0, t0))
        _ ≤ dist (f (x0, t)) (f (x1, t)) +
              (dist (f (x1, t)) (f (x1, t0)) + dist (f (x1, t0)) (f (x0, t0))) := by
          gcongr
          exact dist_triangle (f (x1, t)) (f (x1, t0)) (f (x0, t0))
        _ = _ := by simp [add_assoc]
    have hle' :
        dist (f (x0, t)) (f (x0, t0)) ≤
          (L : ℝ) * dist x0 x1 + ε / 4 + (L : ℝ) * dist x0 x1 := by
      refine le_trans htri1 ?_
      have hbc : dist (f (x1, t)) (f (x1, t0)) ≤ ε / 4 := le_of_lt htcont1
      have hleft :
          dist (f (x0, t)) (f (x1, t)) + dist (f (x1, t)) (f (x1, t0)) ≤
            (L : ℝ) * dist x0 x1 + ε / 4 :=
        add_le_add hdist_xt hbc
      have htotal :
          (dist (f (x0, t)) (f (x1, t)) + dist (f (x1, t)) (f (x1, t0))) +
              dist (f (x1, t0)) (f (x0, t0)) ≤
            ((L : ℝ) * dist x0 x1 + ε / 4) + (L : ℝ) * dist x0 x1 :=
        add_le_add hleft hdist_x0t0
      simpa [add_assoc] using htotal
    have hfinal :
        (L : ℝ) * dist x0 x1 + ε / 4 + (L : ℝ) * dist x0 x1 < ε / 2 := by
      linarith [hLx0x1]
    exact lt_of_le_of_lt hle' hfinal
  have htri :
      dist (f (x, t)) (f (x0, t0)) ≤
        dist (f (x, t)) (f (x0, t)) + dist (f (x0, t)) (f (x0, t0)) :=
    dist_triangle (f (x, t)) (f (x0, t)) (f (x0, t0))
  have :
      dist (f (x, t)) (f (x0, t0)) < ε / 2 + ε / 2 :=
    lt_of_le_of_lt htri (add_lt_add hxcont htcont0)
  simpa [add_halves] using this

/-- If `x ∈ interior S'` and `x ∈ closure C'`, then for every `δ > 0` there exists a point
`z ∈ C' ∩ S'` within distance `δ` of `x`. -/
lemma Section10.exists_point_mem_C'_mem_S'_dist_lt_of_mem_interior_of_mem_closure {n : ℕ}
    {C' S' : Set (EuclideanSpace Real (Fin n))} {x : EuclideanSpace Real (Fin n)}
    (hxS' : x ∈ interior S') (hxC' : x ∈ closure C') :
    ∀ δ : ℝ, 0 < δ → ∃ z, z ∈ C' ∧ z ∈ S' ∧ dist z x < δ := by
  intro δ hδ
  have hnhds : S' ∈ nhds x := mem_interior_iff_mem_nhds.1 hxS'
  rcases Metric.mem_nhds_iff.1 hnhds with ⟨r, hrpos, hrsub⟩
  have hminpos : 0 < min δ r := lt_min hδ hrpos
  rcases (Metric.mem_closure_iff.1 hxC') (min δ r) hminpos with ⟨z, hzC', hzx⟩
  have hzx' : dist z x < min δ r := by simpa [dist_comm] using hzx
  have hzS' : z ∈ S' := by
    apply hrsub
    simpa [Metric.mem_ball, dist_comm] using (lt_of_lt_of_le hzx' (min_le_right _ _))
  refine ⟨z, hzC', hzS', ?_⟩
  exact lt_of_lt_of_le hzx' (min_le_left _ _)

/-- A compact set admits a finite `δ`-net with points in `C' ∩ S'`, provided `C'` is dense
around points of `S` and `S` sits inside `interior S'`. -/
lemma Section10.exists_finset_net_in_C'_inter_S'_cover {n : ℕ}
    {C' S S' : Set (EuclideanSpace Real (Fin n))} (hScomp : IsCompact S)
    (hSint : S ⊆ interior S') (hSclosure : S ⊆ closure C') :
    ∀ δ : ℝ, 0 < δ →
      ∃ t : Finset (EuclideanSpace Real (Fin n)),
        (∀ z ∈ t, z ∈ C' ∧ z ∈ S') ∧ ∀ x ∈ S, ∃ z ∈ t, dist x z < δ := by
  classical
  intro δ hδ
  let r : ℝ := δ / 2
  have hrpos : 0 < r := by
    simpa [r] using (half_pos hδ)
  -- First, cover `S` by finitely many balls of radius `r` centered at points of `S`.
  rcases hScomp.elim_nhds_subcover (U := fun x => Metric.ball x r)
      (hU := by
        intro x hx
        exact Metric.ball_mem_nhds x hrpos) with ⟨t0, ht0S, hcover0⟩
  -- For each chosen center `x0 ∈ t0`, pick `z0 ∈ C' ∩ S'` within distance `r` of `x0`.
  have hzExists :
      ∀ x0 : {x // x ∈ t0}, ∃ z, z ∈ C' ∧ z ∈ S' ∧ dist x0.1 z < r := by
    intro x0
    have hx0S : x0.1 ∈ S := ht0S x0.1 x0.2
    have hx0Int : x0.1 ∈ interior S' := hSint hx0S
    have hx0Cl : x0.1 ∈ closure C' := hSclosure hx0S
    rcases
        Section10.exists_point_mem_C'_mem_S'_dist_lt_of_mem_interior_of_mem_closure
          (n := n) (C' := C') (S' := S') (x := x0.1) hx0Int hx0Cl r hrpos with
      ⟨z, hzC', hzS', hzx⟩
    refine ⟨z, hzC', hzS', ?_⟩
    simpa [dist_comm] using hzx
  classical
  choose zOf hzOfC hzOfS hzOfdist using hzExists
  let t : Finset (EuclideanSpace Real (Fin n)) := (t0.attach).image fun x0 => zOf x0
  refine ⟨t, ?_, ?_⟩
  · intro z hz
    rcases Finset.mem_image.1 hz with ⟨x0, hx0, rfl⟩
    exact ⟨hzOfC x0, hzOfS x0⟩
  · intro x hxS
    have hxcover : x ∈ ⋃ x0 ∈ t0, Metric.ball x0 r := hcover0 hxS
    rcases (by simpa using hxcover) with ⟨x0, hx0t0, hxball⟩
    let x0' : {x // x ∈ t0} := ⟨x0, hx0t0⟩
    refine ⟨zOf x0', ?_, ?_⟩
    · -- Membership in `t`.
      have : x0' ∈ t0.attach := by simp [x0']
      exact (Finset.mem_image.2 ⟨x0', this, rfl⟩)
    · -- Distance estimate.
      have hxx0 : dist x x0 < r := by
        simpa [Metric.mem_ball] using hxball
      have hx0z : dist x0 (zOf x0') < r := hzOfdist x0'
      have htri : dist x (zOf x0') ≤ dist x x0 + dist x0 (zOf x0') :=
        dist_triangle x x0 (zOf x0')
      have hlt : dist x (zOf x0') < r + r :=
        lt_of_le_of_lt htri (add_lt_add hxx0 hx0z)
      have : r + r = δ := by
        simp [r, add_halves]
      simpa [this] using hlt

/-- A finite family of convergent real sequences is uniformly Cauchy on the index set. -/
lemma Section10.exists_tail_cauchy_on_finset_of_pointwise_tendsto {n : ℕ}
    {f : ℕ → EuclideanSpace Real (Fin n) → Real} (t : Finset (EuclideanSpace Real (Fin n)))
    (hpoint :
      ∀ z ∈ t, ∃ l : Real, Filter.Tendsto (fun i => f i z) Filter.atTop (nhds l)) :
    ∀ ε : Real, 0 < ε → ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N, ∀ z ∈ t, ‖f i z - f j z‖ < ε := by
  classical
  revert hpoint
  refine Finset.induction_on t ?base ?step
  · intro hpoint ε hε
    refine ⟨0, ?_⟩
    intro i hi j hj z hz
    simp at hz
  · intro a0 t ha0_notMem htIH hpoint ε hε
    have hpoint_t :
        ∀ z ∈ t, ∃ l : Real, Filter.Tendsto (fun i => f i z) Filter.atTop (nhds l) := by
      intro z hz
      exact hpoint z (by simp [hz])
    rcases htIH hpoint_t ε hε with ⟨N₁, hN₁⟩
    rcases hpoint a0 (by simp [ha0_notMem]) with ⟨l, hl⟩
    have ha0Cauchy : CauchySeq fun i => f i a0 := hl.cauchySeq
    rcases (Metric.cauchySeq_iff.1 ha0Cauchy) ε hε with ⟨N₂, hN₂⟩
    refine ⟨max N₁ N₂, ?_⟩
    intro i hi j hj w hw
    rcases Finset.mem_insert.1 hw with hw0 | hw'
    · have hi' : N₂ ≤ i := le_of_max_le_right hi
      have hj' : N₂ ≤ j := le_of_max_le_right hj
      subst hw0
      have : dist (f i w) (f j w) < ε := hN₂ i hi' j hj'
      simpa [dist_eq_norm, norm_sub_rev] using this
    · have hi' : N₁ ≤ i := le_of_max_le_left hi
      have hj' : N₁ ≤ j := le_of_max_le_left hj
      exact hN₁ i hi' j hj' w hw'

/-- Triangle inequality estimate upgrading control on a finite `δ`-net to control on all of `S`
under an equi-Lipschitz hypothesis. -/
lemma Section10.uniformCauchyOn_of_equiLipschitz_and_finset_net {n : ℕ}
    {f : ℕ → EuclideanSpace Real (Fin n) → Real} {S S' : Set (EuclideanSpace Real (Fin n))}
    {t : Finset (EuclideanSpace Real (Fin n))} {L : NNReal} (hL : ∀ i, LipschitzOnWith L (f i) S')
    (hSsub : S ⊆ S') (htsub : ∀ z ∈ t, z ∈ S') {ε δ : Real}
    (hδbound : (((L : Real) + 1) * δ) ≤ ε / 3) {N : ℕ}
    (hfin : ∀ i ≥ N, ∀ j ≥ N, ∀ z ∈ t, dist (f i z) (f j z) < ε / 3)
    (hcover : ∀ x ∈ S, ∃ z ∈ t, dist x z < δ) :
    ∀ i ≥ N, ∀ j ≥ N, ∀ x ∈ S, dist (f i x) (f j x) < ε := by
  classical
  intro i hi j hj x hx
  rcases hcover x hx with ⟨z, hzT, hxzlt⟩
  have hxS' : x ∈ S' := hSsub hx
  have hzS' : z ∈ S' := htsub z hzT
  have hL1pos : 0 < ((L : Real) + 1) := by
    have hLnonneg : 0 ≤ (L : Real) := by exact_mod_cast L.2
    linarith
  have hixz : dist (f i x) (f i z) < ε / 3 := by
    have hle : dist (f i x) (f i z) ≤ (L : Real) * dist x z :=
      (hL i).dist_le_mul x hxS' z hzS'
    have hle' : dist (f i x) (f i z) ≤ ((L : Real) + 1) * dist x z := by
      have hLle : (L : Real) ≤ (L : Real) + 1 := by linarith
      exact le_trans hle (mul_le_mul_of_nonneg_right hLle dist_nonneg)
    have hlt'' : ((L : Real) + 1) * dist x z < ((L : Real) + 1) * δ :=
      mul_lt_mul_of_pos_left hxzlt hL1pos
    have hlt' : ((L : Real) + 1) * dist x z < ε / 3 :=
      lt_of_lt_of_le hlt'' hδbound
    exact lt_of_le_of_lt hle' hlt'
  have hjzx : dist (f j z) (f j x) < ε / 3 := by
    have hle : dist (f j z) (f j x) ≤ (L : Real) * dist z x :=
      (hL j).dist_le_mul z hzS' x hxS'
    have hle' : dist (f j z) (f j x) ≤ ((L : Real) + 1) * dist z x := by
      have hLle : (L : Real) ≤ (L : Real) + 1 := by linarith
      exact le_trans hle (mul_le_mul_of_nonneg_right hLle dist_nonneg)
    have hlt'' : ((L : Real) + 1) * dist z x < ((L : Real) + 1) * δ := by
      simpa [dist_comm] using mul_lt_mul_of_pos_left hxzlt hL1pos
    have hlt' : ((L : Real) + 1) * dist z x < ε / 3 :=
      lt_of_lt_of_le hlt'' hδbound
    exact lt_of_le_of_lt hle' hlt'
  have hizjz : dist (f i z) (f j z) < ε / 3 := hfin i hi j hj z hzT
  have htri : dist (f i x) (f j x) ≤
      dist (f i x) (f i z) + dist (f i z) (f j z) + dist (f j z) (f j x) :=
    dist_triangle4 (f i x) (f i z) (f j z) (f j x)
  have hlt : dist (f i x) (f j x) < ε / 3 + ε / 3 + ε / 3 :=
    lt_of_le_of_lt htri (add_lt_add (add_lt_add hixz hizjz) hjzx)
  have hsum : ε / 3 + ε / 3 + ε / 3 = ε := by nlinarith
  simpa [hsum] using hlt

/-- If convex functions converge pointwise on a convex set, the pointwise limit is convex. -/
lemma Section10.convexOn_lim_of_pointwise_tendsto {n : ℕ}
    {C : Set (EuclideanSpace Real (Fin n))} (hCconv : Convex ℝ C)
    {f : ℕ → EuclideanSpace Real (Fin n) → Real} {g : EuclideanSpace Real (Fin n) → Real}
    (hg : ∀ x ∈ C, Filter.Tendsto (fun i => f i x) Filter.atTop (nhds (g x)))
    (hfconv : ∀ i, ConvexOn ℝ C (f i)) : ConvexOn ℝ C g := by
  refine ⟨hCconv, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy : a • x + b • y ∈ C := hCconv hx hy ha hb hab
  have htL :
      Filter.Tendsto (fun i => f i (a • x + b • y)) Filter.atTop
        (nhds (g (a • x + b • y))) :=
    hg _ hxy
  have htx : Filter.Tendsto (fun i => f i x) Filter.atTop (nhds (g x)) := hg x hx
  have hty : Filter.Tendsto (fun i => f i y) Filter.atTop (nhds (g y)) := hg y hy
  have htR :
      Filter.Tendsto (fun i => a * f i x + b * f i y) Filter.atTop (nhds (a * g x + b * g y)) := by
    have h1 : Filter.Tendsto (fun i => a * f i x) Filter.atTop (nhds (a * g x)) :=
      tendsto_const_nhds.mul htx
    have h2 : Filter.Tendsto (fun i => b * f i y) Filter.atTop (nhds (b * g y)) :=
      tendsto_const_nhds.mul hty
    simpa [mul_add] using h1.add h2
  have hEv :
      (∀ᶠ i in Filter.atTop, f i (a • x + b • y) ≤ a * f i x + b * f i y) := by
    refine Filter.eventually_atTop.2 ⟨0, ?_⟩
    intro i hi
    simpa [smul_eq_mul] using (hfconv i).2 hx hy ha hb hab
  have hle :
      g (a • x + b • y) ≤ a * g x + b * g y :=
    tendsto_le_of_eventuallyLE htL htR hEv
  simpa [smul_eq_mul] using hle

/-- Theorem 10.8. Let `C` be a relatively open convex set, and let `f 0, f 1, …` be a sequence of
finite convex functions on `C`. Suppose that there exists `C' ⊆ C` with `closure C' ⊇ C` such
that for each `x ∈ C'` the limit `lim_{i → ∞} f i x` exists (as a finite real number). Then the
limit exists for every `x ∈ C`, the resulting pointwise limit function `f` is finite and convex
on `C`, and the sequence `f 0, f 1, …` converges to `f` uniformly on each closed bounded subset
of `C`. -/
theorem convexOn_seq_exists_convex_limit_of_tendstoOn_dense {n : ℕ}
    {C : Set (EuclideanSpace Real (Fin n))} (hCopen : IsOpen C) (hCconv : Convex ℝ C)
    (f : ℕ → EuclideanSpace Real (Fin n) → Real) (hfconv : ∀ i, ConvexOn ℝ C (f i))
    {C' : Set (EuclideanSpace Real (Fin n))} (hC'sub : C' ⊆ C) (hCclosure : C ⊆ closure C')
    (hpoint :
      ∀ x ∈ C', ∃ l : Real, Filter.Tendsto (fun i => f i x) Filter.atTop (nhds l)) :
    ∃ f_lim : EuclideanSpace Real (Fin n) → Real,
      (∀ x ∈ C, Filter.Tendsto (fun i => f i x) Filter.atTop (nhds (f_lim x))) ∧
        ConvexOn ℝ C f_lim ∧
          ∀ S : Set (EuclideanSpace Real (Fin n)),
            IsClosed S → Bornology.IsBounded S → S ⊆ C →
              ∀ ε : Real, 0 < ε → ∃ N : ℕ, ∀ i ≥ N, ∀ x ∈ S, ‖f i x - f_lim x‖ < ε := by
  classical
  by_cases hCempty : C = ∅
  · refine ⟨fun _ => 0, ?_, ?_, ?_⟩
    · intro x hx
      simp [hCempty] at hx
    · subst hCempty
      refine ⟨convex_empty, ?_⟩
      intro x hx
      exact hx.elim
    · intro S hSclosed hSbdd hSsub ε hε
      have hSem : S = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.2
        intro x hx
        have : False := by
          simpa [hCempty] using (hSsub hx)
        exact this.elim
      subst hSem
      refine ⟨0, ?_⟩
      intro i hi x hx
      simpa using hx.elim
  have hCne : C.Nonempty := Set.nonempty_iff_ne_empty.2 hCempty
  have hC'hull : C ⊆ convexHull ℝ (closure C') :=
    hCclosure.trans (subset_convexHull ℝ (closure C'))
  have hC'bdAbove : ∀ x ∈ C', BddAbove (Set.range fun i : ℕ => f i x) := by
    intro x hx
    rcases hpoint x hx with ⟨l, hl⟩
    exact hl.bddAbove_range
  have hC'ne : C'.Nonempty := by
    by_contra hC'ne'
    have hC'empty : C' = (∅ : Set (EuclideanSpace Real (Fin n))) := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro x hx
      exact hC'ne' ⟨x, hx⟩
    rcases hCne with ⟨x, hxC⟩
    have : False := by
      have hxcl : x ∈ closure C' := hCclosure hxC
      simp [hC'empty] at hxcl
    exact this.elim
  have hexists_bddBelow : ∃ x ∈ C, BddBelow (Set.range fun i : ℕ => f i x) := by
    rcases hC'ne with ⟨x0, hx0C'⟩
    have hx0C : x0 ∈ C := hC'sub hx0C'
    rcases hpoint x0 hx0C' with ⟨l, hl⟩
    exact ⟨x0, hx0C, hl.bddBelow_range⟩

  -- Uniform Cauchy property on any closed bounded subset of `C`.
  have hCauchyOn :
      ∀ S : Set (EuclideanSpace Real (Fin n)),
        IsClosed S → Bornology.IsBounded S → S ⊆ C →
          ∀ ε : Real, 0 < ε →
            ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N, ∀ x ∈ S, ‖f i x - f j x‖ < ε := by
    intro S hSclosed hSbdd hSsub ε hε
    have hScomp : IsCompact S := Section10.isCompact_of_isClosed_isBounded (n := n) hSclosed hSbdd
    rcases (hScomp.exists_cthickening_subset_open hCopen hSsub) with ⟨δ0, hδ0pos, hS'thick_subC⟩
    let S' : Set (EuclideanSpace Real (Fin n)) := Metric.cthickening δ0 S
    have hSsubsetS' : S ⊆ S' := by
      simpa [S'] using (Metric.self_subset_cthickening (δ := δ0) (E := S))
    have hSint : S ⊆ interior S' := by
      have : S ⊆ Metric.thickening δ0 S :=
        Metric.self_subset_thickening hδ0pos S
      have : S ⊆ interior S' := by
        refine this.trans ?_
        simpa [S'] using (Metric.thickening_subset_interior_cthickening δ0 S)
      exact this
    have hSclosure : S ⊆ closure C' := hSsub.trans hCclosure
    have hS'closed : IsClosed S' := by
      simpa [S'] using (Metric.isClosed_cthickening (δ := δ0) (E := S))
    have hS'bdd : Bornology.IsBounded S' := by
      simpa [S'] using hSbdd.cthickening
    have hS'subC : S' ⊆ C := by
      simpa [S'] using hS'thick_subC
    have hEquiLip : Function.EquiLipschitzRelativeTo f S' := by
      exact
        (convexOn_family_uniformlyBoundedOn_and_equiLipschitzRelativeTo_of_exists_subset
              (n := n) (I := ℕ) (C := C) hCopen hCconv f hfconv (C' := C') hC'sub hC'hull
              hC'bdAbove hexists_bddBelow (S := S') hS'closed hS'bdd hS'subC).2
    rcases hEquiLip with ⟨L, hL⟩
    have hL1pos : 0 < ((L : Real) + 1) := by
      have hLnonneg : 0 ≤ (L : Real) := by exact_mod_cast L.2
      linarith
    have hL1ne : ((L : Real) + 1) ≠ 0 := ne_of_gt hL1pos
    let δ : Real := (ε / 3) / ((L : Real) + 1)
    have hδpos : 0 < δ := by
      have : 0 < ε / 3 := by nlinarith
      exact div_pos this hL1pos
    have hδbound : ((L : Real) + 1) * δ ≤ ε / 3 := by
      have : ((L : Real) + 1) * δ = ε / 3 := by
        simpa [δ] using (mul_div_cancel₀ (a := ε / 3) (b := (L : Real) + 1) hL1ne)
      exact le_of_eq this
    rcases
        Section10.exists_finset_net_in_C'_inter_S'_cover (n := n) (C' := C') (S := S) (S' := S')
          hScomp hSint hSclosure δ hδpos with
      ⟨t, htmem, htcover⟩
    have hpoint_t :
        ∀ z ∈ t, ∃ l : Real, Filter.Tendsto (fun i => f i z) Filter.atTop (nhds l) := by
      intro z hz
      have hzC' : z ∈ C' := (htmem z hz).1
      exact hpoint z hzC'
    rcases
        Section10.exists_tail_cauchy_on_finset_of_pointwise_tendsto (n := n) (f := f) t hpoint_t
          (ε / 3) (by nlinarith) with
      ⟨N, hN⟩
    have htS' : ∀ z ∈ t, z ∈ S' := by
      intro z hz
      exact (htmem z hz).2
    have hfin :
        ∀ i ≥ N, ∀ j ≥ N, ∀ z ∈ t, dist (f i z) (f j z) < ε / 3 := by
      intro i hi j hj z hz
      have : ‖f i z - f j z‖ < ε / 3 := hN i hi j hj z hz
      simpa [dist_eq_norm] using this
    refine ⟨N, ?_⟩
    intro i hi j hj x hxS
    have hdist :
        dist (f i x) (f j x) < ε :=
      Section10.uniformCauchyOn_of_equiLipschitz_and_finset_net (n := n) (f := f) (S := S)
        (S' := S') (t := t) (L := L) hL hSsubsetS' htS' hδbound hfin htcover i hi j hj x
        hxS
    simpa [dist_eq_norm] using hdist

  -- Define the pointwise limit function by choosing the limit at each `x ∈ C`.
  have hlim_exists :
      ∀ x ∈ C, ∃ l : Real, Filter.Tendsto (fun i => f i x) Filter.atTop (nhds l) := by
    intro x hxC
    have hxCauchy : CauchySeq fun i => f i x := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      rcases Section10.exists_closedBall_subset_of_isOpen (n := n) (C := C) hCopen hxC with
        ⟨r, hrpos, hballsub⟩
      have hSclosed : IsClosed (Metric.closedBall x r) := Metric.isClosed_closedBall
      have hSbdd : Bornology.IsBounded (Metric.closedBall x r) := Metric.isBounded_closedBall
      have hSsub : Metric.closedBall x r ⊆ C := hballsub
      rcases hCauchyOn (S := Metric.closedBall x r) hSclosed hSbdd hSsub ε hε with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      intro i hi j hj
      have hxmem : x ∈ Metric.closedBall x r := by
        simpa using
          (Metric.mem_closedBall_self (x := x) (ε := r) (le_of_lt hrpos))
      have : ‖f i x - f j x‖ < ε := hN i hi j hj x hxmem
      simpa [dist_eq_norm] using this
    exact cauchySeq_tendsto_of_complete hxCauchy
  let fLimC : {x // x ∈ C} → Real := fun x => Classical.choose (hlim_exists x.1 x.2)
  have hfLimC :
      ∀ x : {x // x ∈ C},
        Filter.Tendsto (fun i => f i x.1) Filter.atTop (nhds (fLimC x)) := fun x =>
    Classical.choose_spec (hlim_exists x.1 x.2)
  let f_lim : EuclideanSpace Real (Fin n) → Real := fun x =>
    if hx : x ∈ C then fLimC ⟨x, hx⟩ else 0
  have hf_lim_tendsto :
      ∀ x ∈ C, Filter.Tendsto (fun i => f i x) Filter.atTop (nhds (f_lim x)) := by
    intro x hxC
    simpa [f_lim, hxC] using (hfLimC ⟨x, hxC⟩)
  have hf_lim_conv : ConvexOn ℝ C f_lim :=
    Section10.convexOn_lim_of_pointwise_tendsto (n := n) (C := C) hCconv
      (f := f) (g := f_lim) hf_lim_tendsto hfconv
  refine ⟨f_lim, hf_lim_tendsto, hf_lim_conv, ?_⟩
  intro S hSclosed hSbdd hSsub ε hε
  have hε2 : 0 < ε / 2 := by nlinarith
  rcases hCauchyOn (S := S) hSclosed hSbdd hSsub (ε / 2) hε2 with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro i hi x hxS
  have hxC : x ∈ C := hSsub hxS
  have ht : Filter.Tendsto (fun j => f j x) Filter.atTop (nhds (f_lim x)) := hf_lim_tendsto x hxC
  have hEv :
      ∀ᶠ j in Filter.atTop, ‖f i x - f j x‖ < ε / 2 := by
    refine (Filter.eventually_atTop.2 ?_)
    refine ⟨N, ?_⟩
    intro j hj
    exact hN i hi j hj x hxS
  have hEv' :
      ∀ᶠ j in Filter.atTop, f j x ∈ Metric.closedBall (f i x) (ε / 2) := by
    filter_upwards [hEv] with j hj
    have : dist (f j x) (f i x) ≤ ε / 2 := by
      have : dist (f i x) (f j x) < ε / 2 := by simpa [dist_eq_norm] using hj
      simpa [dist_comm] using (le_of_lt this)
    simpa [Metric.mem_closedBall] using this
  have hmem : f_lim x ∈ Metric.closedBall (f i x) (ε / 2) :=
    (Metric.isClosed_closedBall).mem_of_tendsto ht hEv'
  have hdist : dist (f i x) (f_lim x) ≤ ε / 2 := by
    have : dist (f_lim x) (f i x) ≤ ε / 2 := by
      simpa [Metric.mem_closedBall] using hmem
    simpa [dist_comm] using this
  have hlt : dist (f i x) (f_lim x) < ε := lt_of_le_of_lt hdist (by nlinarith)
  simpa [dist_eq_norm] using hlt

/-- The pointwise maximum of two convex functions is convex. -/
lemma Section10.convexOn_max {n : ℕ} {C : Set (EuclideanSpace Real (Fin n))}
    {f g : EuclideanSpace Real (Fin n) → Real} (hf : ConvexOn ℝ C f) (hg : ConvexOn ℝ C g) :
    ConvexOn ℝ C (fun x => max (f x) (g x)) := by
  simpa using hf.sup hg

/-- If `limsup (u i) ≤ a`, then `max (u i) a` tends to `a`. -/
lemma Section10.tendsto_max_of_limsup_le {u : ℕ → Real} {a : Real}
    (h : Filter.limsup (fun i : ℕ => (u i : EReal)) Filter.atTop ≤ (a : EReal)) :
    Filter.Tendsto (fun i => max (u i) a) Filter.atTop (nhds a) := by
  -- Use the `ε`-definition of convergence in a metric space.
  rw [Metric.tendsto_nhds]
  intro ε hε
  have ha_lt : (a : EReal) < ((a + ε : Real) : EReal) := by
    exact EReal.coe_lt_coe_iff.2 (lt_add_of_pos_right a hε)
  have hEvE :
      ∀ᶠ i in Filter.atTop, (u i : EReal) < ((a + ε : Real) : EReal) :=
    (Filter.limsup_le_iff).1 h _ ha_lt
  have hEv : ∀ᶠ i in Filter.atTop, u i < a + ε := by
    filter_upwards [hEvE] with i hi
    exact EReal.coe_lt_coe_iff.1 hi
  filter_upwards [hEv] with i hi
  have hmaxlt : max (u i) a < a + ε :=
    max_lt_iff.2 ⟨hi, lt_add_of_pos_right a hε⟩
  have hsub : max (u i) a - a < ε := by linarith
  have hnonneg : 0 ≤ max (u i) a - a := sub_nonneg.2 (le_max_right _ _)
  have habs : |max (u i) a - a| < ε := by
    simpa [abs_of_nonneg hnonneg] using hsub
  simpa [Real.dist_eq] using habs

/-- If `g` is uniformly within `ε` of `f` on `S`, and `f ≤ g`, then `g ≤ f + ε` on `S`. -/
lemma Section10.le_add_of_uniform_norm_sub_lt_of_le {X : Type*}
    {g : ℕ → X → Real} {f : X → Real} {S : Set X} {ε : Real} {N : ℕ}
    (hU : ∀ i ≥ N, ∀ x ∈ S, ‖g i x - f x‖ < ε) (hle : ∀ i x, f x ≤ g i x) :
    ∀ i ≥ N, ∀ x ∈ S, g i x ≤ f x + ε := by
  intro i hi x hxS
  have hnorm : ‖g i x - f x‖ < ε := hU i hi x hxS
  have hnonneg : 0 ≤ g i x - f x := sub_nonneg.2 (hle i x)
  have habs : |g i x - f x| < ε := by
    simpa [Real.norm_eq_abs] using hnorm
  have hsub : g i x - f x < ε := by
    simpa [abs_of_nonneg hnonneg] using habs
  have : g i x < f x + ε := by linarith
  exact le_of_lt this

/-- Corollary 10.8.1. Let `f` be a finite convex function on a relatively open convex set `C`.
Let `f₁, f₂, …` be a sequence of finite convex functions on `C` such that
`limsup_{i → ∞} fᵢ(x) ≤ f(x)` for all `x ∈ C`.
Then for each closed bounded subset `S` of `C` and each `ε > 0`, there exists `i₀` such that
`fᵢ(x) ≤ f(x) + ε` for all `i ≥ i₀` and all `x ∈ S`. -/
theorem convexOn_eventually_le_add_of_limsup_le {n : ℕ}
    {C : Set (EuclideanSpace Real (Fin n))} (hCopen : IsOpen C) (hCconv : Convex ℝ C)
    {f : EuclideanSpace Real (Fin n) → Real} (hfconv : ConvexOn ℝ C f)
    (fseq : ℕ → EuclideanSpace Real (Fin n) → Real) (hfseqconv : ∀ i, ConvexOn ℝ C (fseq i))
    (hlimsup :
      ∀ x ∈ C, Filter.limsup (fun i : ℕ => (fseq i x : EReal)) Filter.atTop ≤ (f x : EReal)) :
    ∀ S : Set (EuclideanSpace Real (Fin n)),
      IsClosed S → Bornology.IsBounded S → S ⊆ C →
        ∀ ε : Real, 0 < ε → ∃ i0 : ℕ, ∀ i ≥ i0, ∀ x ∈ S, fseq i x ≤ f x + ε := by
  classical
  intro S hSclosed hSbdd hSsub ε hε
  -- Modify the sequence by taking the pointwise maximum with the target function.
  let gseq : ℕ → EuclideanSpace Real (Fin n) → Real := fun i x => max (fseq i x) (f x)
  have hgseqconv : ∀ i, ConvexOn ℝ C (gseq i) := by
    intro i
    simpa [gseq] using Section10.convexOn_max (hfseqconv i) hfconv
  have hgpoint :
      ∀ x ∈ C, ∃ l : Real, Filter.Tendsto (fun i => gseq i x) Filter.atTop (nhds l) := by
    intro x hxC
    refine ⟨f x, ?_⟩
    have : Filter.Tendsto (fun i => max (fseq i x) (f x)) Filter.atTop (nhds (f x)) :=
      Section10.tendsto_max_of_limsup_le (u := fun i => fseq i x) (a := f x) (hlimsup x hxC)
    simpa [gseq] using this
  rcases
      convexOn_seq_exists_convex_limit_of_tendstoOn_dense (n := n) (C := C) hCopen hCconv
        (f := gseq) hgseqconv (C' := C) (hC'sub := subset_rfl) (hCclosure := subset_closure)
        (hpoint := hgpoint) with
    ⟨f_lim, hf_lim_tendsto, hf_lim_conv, hU⟩
  -- Identify the limit function with `f` using pointwise uniqueness of limits.
  have hf_lim_eq : ∀ x ∈ C, f_lim x = f x := by
    intro x hxC
    have ht1 : Filter.Tendsto (fun i => gseq i x) Filter.atTop (nhds (f_lim x)) :=
      hf_lim_tendsto x hxC
    have ht2 : Filter.Tendsto (fun i => gseq i x) Filter.atTop (nhds (f x)) := by
      have :
          Filter.Tendsto (fun i => max (fseq i x) (f x)) Filter.atTop (nhds (f x)) :=
        Section10.tendsto_max_of_limsup_le (u := fun i => fseq i x) (a := f x) (hlimsup x hxC)
      simpa [gseq] using this
    exact tendsto_nhds_unique ht1 ht2
  -- Apply uniform convergence of `gseq` to `f_lim` and rewrite the limit as `f`.
  rcases hU S hSclosed hSbdd hSsub ε hε with ⟨N, hN⟩
  have hN' : ∀ i ≥ N, ∀ x ∈ S, ‖gseq i x - f x‖ < ε := by
    intro i hi x hxS
    have hxC : x ∈ C := hSsub hxS
    simpa [hf_lim_eq x hxC] using (hN i hi x hxS)
  have hle : ∀ i x, f x ≤ gseq i x := by
    intro i x
    simp [gseq]
  have hmaxle : ∀ i ≥ N, ∀ x ∈ S, gseq i x ≤ f x + ε :=
    Section10.le_add_of_uniform_norm_sub_lt_of_le (g := gseq) (f := f) (S := S) (ε := ε)
      (N := N) hN' hle
  refine ⟨N, ?_⟩
  intro i hi x hxS
  have h1 : gseq i x ≤ f x + ε := hmaxle i hi x hxS
  have h2 : fseq i x ≤ gseq i x := by
    simp [gseq]
  exact le_trans h2 h1

/-- Any subset of a separable space contains a countable subset with closure containing the set. -/
lemma Section10.exists_countable_subset_closure_superset {n : ℕ}
    (C' : Set (EuclideanSpace Real (Fin n))) :
    ∃ C'' : Set (EuclideanSpace Real (Fin n)),
      C'' ⊆ C' ∧ C''.Countable ∧ C' ⊆ closure C'' := by
  classical
  -- Work in the subtype `C'`.
  obtain ⟨t : Set (↑C'), htcount, htdense⟩ :=
    TopologicalSpace.exists_countable_dense (α := (↑C'))
  refine ⟨Subtype.val '' t, ?_, ?_, (Subtype.dense_iff (s := C') (t := t)).1 htdense⟩
  · intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact y.2
  · simpa using htcount.image (fun y : (↑C') => (y : EuclideanSpace Real (Fin n)))

/-- A diagonal compactness argument: if each coordinate sequence `i ↦ f i (x j)` is bounded in `ℝ`,
then some subsequence converges at every point in the countable range `{x j}`. -/
lemma Section10.exists_strictMono_subseq_pointwise_tendsto_on_countable_range {α : Type*}
    (x : ℕ → α) (f : ℕ → α → ℝ)
    (hbounded : ∀ j, Bornology.IsBounded (Set.range fun i : ℕ => f i (x j))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j, ∃ l : ℝ,
      Filter.Tendsto (fun i => f (φ i) (x j)) Filter.atTop (nhds l) := by
  classical
  -- Package the evaluations into a sequence in the product space `ℕ → ℝ`.
  let u : ℕ → (ℕ → ℝ) := fun i j => f i (x j)
  -- For each coordinate choose a closed ball containing the range.
  have hR : ∀ j, ∃ r : ℝ, Set.range (fun i : ℕ => u i j) ⊆ Metric.closedBall (0 : ℝ) r := by
    intro j
    simpa [u] using (hbounded j).subset_closedBall (c := (0 : ℝ))
  choose r hr using hR
  let K : Set (ℕ → ℝ) := {g | ∀ j, g j ∈ Metric.closedBall (0 : ℝ) (r j)}
  have hKcomp : IsCompact K := by
    -- Compactness of the product of compact sets.
    simpa [K] using
      (isCompact_pi_infinite (s := fun j : ℕ => Metric.closedBall (0 : ℝ) (r j))
        (fun j => by simpa using (ProperSpace.isCompact_closedBall (x := (0 : ℝ)) (r := r j))))
  have huK : ∀ i, u i ∈ K := by
    intro i j
    have : u i j ∈ Set.range (fun i : ℕ => u i j) := ⟨i, rfl⟩
    exact hr j this
  rcases hKcomp.tendsto_subseq (x := u) huK with ⟨a, haK, φ, hφ, haφ⟩
  refine ⟨φ, hφ, ?_⟩
  intro j
  refine ⟨a j, ?_⟩
  -- Evaluate the convergence in the product topology.
  have hcont : Continuous fun g : (ℕ → ℝ) => g j := continuous_apply j
  have : Filter.Tendsto (fun i => (u (φ i)) j) Filter.atTop (nhds (a j)) := by
    simpa [Function.comp] using (hcont.tendsto a).comp haφ
  simpa [u] using this

/-- Turn convergence along an enumeration `x : ℕ → α` into convergence on `Set.range x`. -/
lemma Section10.pointwise_tendsto_on_countable_subset_from_range {α : Type*} {f : ℕ → α → ℝ}
    {x : ℕ → α} {φ : ℕ → ℕ}
    (hpoint : ∀ j, ∃ l : ℝ, Filter.Tendsto (fun i => f (φ i) (x j)) Filter.atTop (nhds l)) :
    ∀ z ∈ Set.range x, ∃ l : ℝ, Filter.Tendsto (fun i => f (φ i) z) Filter.atTop (nhds l) := by
  intro z hz
  rcases hz with ⟨j, rfl⟩
  simpa using hpoint j

/-- Theorem 10.9. Let `C` be a relatively open convex set, and let `f₁, f₂, …` be a sequence of
 finite convex functions on `C`. Suppose that for each `x ∈ C` the real sequence `f₁ x, f₂ x, …`
 is bounded (or merely for each `x` in some dense subset `C'` of `C`). Then there exists a
 subsequence of `f₁, f₂, …` which converges uniformly on each closed bounded subset of `C` to a
finite convex function `f`. -/
theorem convexOn_seq_exists_subseq_uniformlyConvergentOn_of_boundedOn_dense {n : ℕ}
    {C : Set (EuclideanSpace Real (Fin n))} (hCopen : IsOpen C) (hCconv : Convex ℝ C)
    (f : ℕ → EuclideanSpace Real (Fin n) → Real) (hfconv : ∀ i, ConvexOn ℝ C (f i))
    (hbounded :
      ∃ C' : Set (EuclideanSpace Real (Fin n)),
        C' ⊆ C ∧ C ⊆ closure C' ∧
          ∀ x ∈ C', Bornology.IsBounded (Set.range fun i : ℕ => f i x)) :
    ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
        ∃ f_lim : EuclideanSpace Real (Fin n) → Real,
          ConvexOn ℝ C f_lim ∧
            ∀ S : Set (EuclideanSpace Real (Fin n)),
              IsClosed S → Bornology.IsBounded S → S ⊆ C →
                ∀ ε : Real, 0 < ε →
                  ∃ N : ℕ, ∀ i ≥ N, ∀ x ∈ S, ‖f (φ i) x - f_lim x‖ < ε := by
  classical
  rcases hbounded with ⟨C', hC'sub, hCclosure, hptbdd⟩
  by_cases hCempty : C = ∅
  · refine ⟨id, strictMono_id, ?_⟩
    refine ⟨fun _ => 0, ?_, ?_⟩
    · simpa using (convexOn_const (s := C) (c := (0 : Real)) hCconv)
    · intro S hSclosed hSbdd hSsub ε hε
      refine ⟨0, ?_⟩
      intro i hi x hxS
      have : x ∈ (∅ : Set (EuclideanSpace Real (Fin n))) := by
        simpa [hCempty] using hSsub hxS
      simp at this
  -- Reduce the dense set `C'` to a countable dense subset `C''`.
  rcases Section10.exists_countable_subset_closure_superset (n := n) C' with
    ⟨C'', hC''sub, hC''count, hC'closure⟩
  have hC''subC : C'' ⊆ C := fun x hx => hC'sub (hC''sub hx)
  have hCclosure'' : C ⊆ closure C'' := by
    intro x hxC
    have hxcl : x ∈ closure C' := hCclosure hxC
    have hcl : closure C' ⊆ closure C'' := by
      have : closure C' ⊆ closure (closure C'') := closure_mono hC'closure
      simpa [closure_closure] using this
    exact hcl hxcl
  -- Enumerate `C''` and extract a subsequence converging pointwise on it.
  have hC''ne : C'' ≠ ∅ := by
    rcases (Set.nonempty_iff_ne_empty.2 hCempty) with ⟨x0, hx0C⟩
    have : x0 ∈ closure C'' := hCclosure'' hx0C
    intro hC''empty
    simp [hC''empty] at this
  have hC''nonempty : C''.Nonempty := Set.nonempty_iff_ne_empty.2 hC''ne
  rcases hC''count.exists_eq_range hC''nonempty with ⟨x, hx⟩
  -- Pointwise boundedness on `C''`.
  have hbounded_x : ∀ j, Bornology.IsBounded (Set.range fun i : ℕ => f i (x j)) := by
    intro j
    have hxjC'' : x j ∈ C'' := by simp [hx]
    exact hptbdd (x j) (hC''sub hxjC'')
  rcases
      Section10.exists_strictMono_subseq_pointwise_tendsto_on_countable_range (x := x) (f := f)
        hbounded_x with
    ⟨φ, hφ, hpoint_x⟩
  have hpoint :
      ∀ z ∈ C'', ∃ l : Real,
        Filter.Tendsto (fun i => f (φ i) z) Filter.atTop (nhds l) := by
    -- Rewrite `C''` as `range x` and use convergence at each enumerated point.
    have hpointR :
        ∀ z ∈ Set.range x, ∃ l : ℝ, Filter.Tendsto (fun i => f (φ i) z) Filter.atTop (nhds l) :=
      Section10.pointwise_tendsto_on_countable_subset_from_range (f := f) (x := x) (φ := φ)
        (by
          intro j
          simpa using hpoint_x j)
    simpa [hx] using hpointR
  -- Apply Theorem 10.8 to the extracted subsequence.
  let fsub : ℕ → EuclideanSpace Real (Fin n) → Real := fun i x => f (φ i) x
  have hfsubconv : ∀ i, ConvexOn ℝ C (fsub i) := by
    intro i
    simpa [fsub] using hfconv (φ i)
  rcases
      convexOn_seq_exists_convex_limit_of_tendstoOn_dense (n := n) (C := C) hCopen hCconv
        (f := fsub) hfsubconv (C' := C'') (hC'sub := hC''subC) (hCclosure := hCclosure'')
        (hpoint := hpoint) with
    ⟨f_lim, hf_lim_tendsto, hf_lim_conv, hU⟩
  refine ⟨φ, hφ, ⟨f_lim, hf_lim_conv, ?_⟩⟩
  intro S hSclosed hSbdd hSsub ε hε
  rcases hU S hSclosed hSbdd hSsub ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro i hi x hxS
  simpa [fsub] using hN i hi x hxS

end Section10
end Chap02
