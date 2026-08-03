import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap25.Definition_25_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 25.8: a maximally monotone operator has nonempty range. -/
private lemma rangeNonemptyOfMaximal
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) :
    A.range.Nonempty := by
  classical
  by_cases hRangeEmpty : A.range = ∅
  · let B : SetValuedOperator H H := fun x ↦ if x = 0 then ({0} : Set H) else ∅
    -- If `range A` were empty, the singleton graph at the origin would be a monotone extension.
    have hAB : A ≤ B := by
      intro x u hu
      have huRange : u ∈ A.range := (SetValuedOperator.mem_range_iff A u).2 ⟨x, hu⟩
      have : False := by
        have huRangeEmpty : u ∈ (∅ : Set H) := by
          rwa [hRangeEmpty] at huRange
        have hEmpty : u ∉ (∅ : Set H) := by
          simp
        exact hEmpty huRangeEmpty
      exact False.elim this
    have hBmono : B.IsMonotone := by
      -- The auxiliary operator has the single graph point `(0, 0)`.
      rw [isMonotone_iff]
      intro x u y v hxu hyv
      have hx0 : x = 0 := by
        by_cases hx : x = 0
        · exact hx
        · have : False := by
            have hxB : B x = (∅ : Set H) := by
              simp [B, hx]
            have huEmpty : u ∈ (∅ : Set H) := by
              rw [hxB] at hxu
              exact hxu
            have hEmpty : u ∉ (∅ : Set H) := by
              simp
            exact hEmpty huEmpty
          exact False.elim this
      have hy0 : y = 0 := by
        by_cases hy : y = 0
        · exact hy
        · have : False := by
            have hyB : B y = (∅ : Set H) := by
              simp [B, hy]
            have hvEmpty : v ∈ (∅ : Set H) := by
              rw [hyB] at hyv
              exact hyv
            have hEmpty : v ∉ (∅ : Set H) := by
              simp
            exact hEmpty hvEmpty
          exact False.elim this
      subst x y
      have hu0 : u = 0 := by
        simpa [B] using hxu
      have hv0 : v = 0 := by
        simpa [B] using hyv
      subst u v
      simp
    have hBzero : (0 : H) ∈ B 0 := by
      simp [B]
    have hAzero : (0 : H) ∈ A 0 :=
      (hA.2 hBmono hAB 0) hBzero
    exact ⟨0, (SetValuedOperator.mem_range_iff A 0).2 ⟨0, hAzero⟩⟩
  · exact Set.nonempty_iff_ne_empty.mpr hRangeEmpty

/-- Helper for Proposition 25.8: a thickened segment is bounded, closed, and convex. -/
private lemma boundedClosedConvexSegmentAddClosedBall
    (u w : H) {ε : ℝ} (_hε : 0 ≤ ε) :
    Bornology.IsBounded (segment ℝ u w + Metric.closedBall (0 : H) ε : Set H) ∧
      IsClosed (segment ℝ u w + Metric.closedBall (0 : H) ε : Set H) ∧
      Convex ℝ (segment ℝ u w + Metric.closedBall (0 : H) ε : Set H) := by
  let C : Set H := segment ℝ u w + Metric.closedBall (0 : H) ε
  have hC_bounded :
      Bornology.IsBounded C := by
    refine
      (Metric.isBounded_closedBall :
        Bornology.IsBounded (Metric.closedBall u (dist u w + ε))).subset ?_
    intro z hz
    rcases Set.mem_add.1 hz with ⟨s, hs, b, hb, rfl⟩
    have hs' : s ∈ Metric.closedBall u (dist u w) :=
      segment_subset_closedBall_left u w hs
    have hsDist : dist s u ≤ dist u w := by
      simpa [Metric.mem_closedBall] using hs'
    have hbNorm : ‖b‖ ≤ ε := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hb
    -- Bounding the thickened segment reduces to the triangle inequality around `u`.
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc
      ‖s + b - u‖ = ‖(s - u) + b‖ := by
        abel_nf
      _ ≤ ‖s - u‖ + ‖b‖ := norm_add_le _ _
      _ = dist s u + ‖b‖ := by
        rw [dist_eq_norm]
      _ ≤ dist u w + ε := by
        gcongr
  have hSegmentCompact : IsCompact (segment ℝ u w : Set H) := by
    -- A segment is the continuous image of the compact interval `[0, 1]`.
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  have hC_closed : IsClosed C := by
    -- Closedness comes from the compact-plus-closed pointwise-sum theorem.
    simpa [C, add_comm] using
      (Metric.isClosed_closedBall.add_right_of_isCompact hSegmentCompact)
  have hC_convex : Convex ℝ C := by
    -- Convexity is preserved by pointwise addition.
    simpa [C] using (convex_segment (𝕜 := ℝ) u w).add (convex_closedBall (0 : H) ε)
  exact ⟨hC_bounded, hC_closed, hC_convex⟩

/-- Helper for Proposition 25.8: an open convex set contains a bounded closed convex thickening of
the segment joining any two of its points. -/
private lemma segmentClosedBallSubsetOfOpenConvex
    {U : Set H} (hU_open : IsOpen U) (hU_convex : Convex ℝ U)
    {u w : H} (huU : u ∈ U) (hwU : w ∈ U) :
    ∃ ε > 0,
      let C : Set H := segment ℝ u w + Metric.closedBall (0 : H) ε
      C ⊆ U ∧ u ∈ interior C ∧ w ∈ interior C := by
  rcases Metric.mem_nhds_iff.mp (hU_open.mem_nhds huU) with ⟨δu, hδu_pos, hδu_sub⟩
  rcases Metric.mem_nhds_iff.mp (hU_open.mem_nhds hwU) with ⟨δw, hδw_pos, hδw_sub⟩
  let ε : ℝ := min δu δw / 2
  have hε_pos : 0 < ε := by
    have hmin_pos : 0 < min δu δw := lt_min hδu_pos hδw_pos
    positivity
  have hε_lt_u : ε < δu := by
    have hε_le : ε ≤ δu / 2 := by
      dsimp [ε]
      gcongr
      exact min_le_left _ _
    have hhalf_lt : δu / 2 < δu := by
      linarith
    exact lt_of_le_of_lt hε_le hhalf_lt
  have hε_lt_w : ε < δw := by
    have hε_le : ε ≤ δw / 2 := by
      dsimp [ε]
      gcongr
      exact min_le_right _ _
    have hhalf_lt : δw / 2 < δw := by
      linarith
    exact lt_of_le_of_lt hε_le hhalf_lt
  refine ⟨ε, hε_pos, ?_⟩
  let C : Set H := segment ℝ u w + Metric.closedBall (0 : H) ε
  have hC_subset : C ⊆ U := by
    intro z hz
    rcases Set.mem_add.1 hz with ⟨s, hs, b, hb, rfl⟩
    have hubClosed : u + b ∈ Metric.closedBall u ε := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hb
    have hwbClosed : w + b ∈ Metric.closedBall w ε := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hb
    have hubU : u + b ∈ U :=
      hδu_sub (Metric.closedBall_subset_ball hε_lt_u hubClosed)
    have hwbU : w + b ∈ U :=
      hδw_sub (Metric.closedBall_subset_ball hε_lt_w hwbClosed)
    rw [segment_eq_image_lineMap] at hs
    rcases hs with ⟨t, ht, rfl⟩
    -- Translating the segment endpoints by the same vector keeps the whole segment in `U`.
    have hTranslate :
        AffineMap.lineMap u w t + b = AffineMap.lineMap (u + b) (w + b) t := by
      rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module']
      abel_nf
    have hLineU : AffineMap.lineMap (u + b) (w + b) t ∈ U := by
      have hLineMem : AffineMap.lineMap (u + b) (w + b) t ∈ segment ℝ (u + b) (w + b) := by
        rw [segment_eq_image_lineMap]
        exact ⟨t, ht, rfl⟩
      exact hU_convex.segment_subset hubU hwbU hLineMem
    exact hTranslate ▸ hLineU
  have huInt : u ∈ interior C := by
    rw [mem_interior_iff_mem_nhds]
    refine Filter.mem_of_superset (Metric.ball_mem_nhds u hε_pos) ?_
    intro z hz
    have hzClosed : z - u ∈ Metric.closedBall (0 : H) ε := by
      rw [Metric.mem_closedBall]
      exact le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
    exact Set.mem_add.2 ⟨u, left_mem_segment ℝ u w, z - u, hzClosed, by abel_nf⟩
  have hwInt : w ∈ interior C := by
    rw [mem_interior_iff_mem_nhds]
    refine Filter.mem_of_superset (Metric.ball_mem_nhds w hε_pos) ?_
    intro z hz
    have hzClosed : z - w ∈ Metric.closedBall (0 : H) ε := by
      rw [Metric.mem_closedBall]
      exact le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
    exact Set.mem_add.2 ⟨w, right_mem_segment ℝ u w, z - w, hzClosed, by abel_nf⟩
  exact ⟨hC_subset, huInt, hwInt⟩

-- Source/core/bridge triage:
-- `source-facing`: Proposition 25.8 relates the Chapter 25 local-maximal-monotonicity owners to
--   maximal monotonicity and to the bounded closed convex test from the textbook.
-- `core/canonical`: the owner abstractions are `A.IsLocallyMaximallyMonotoneOn U`,
--   `A.IsLocallyMaximallyMonotone`, and the Chapter 20 owner `Maximal IsMonotone A`.
-- `bridge/view`: graph membership is derived pointwise API, so the proposition should use the
--   operator owners directly rather than reintroducing parallel local wrappers.

/-- First part of Proposition 25.8: local maximal monotonicity on the whole Hilbert space is
equivalent to
maximal monotonicity. -/
theorem isLocallyMaximallyMonotoneOn_univ_iff_maximal
    {A : SetValuedOperator H H} :
    A.IsLocallyMaximallyMonotoneOn (Set.univ : Set H) ↔ Maximal IsMonotone A := by
  constructor
  · intro hA
    rw [maximal_iff_mem_iff]
    intro x u
    constructor
    · -- Graph points satisfy the Minty inequalities by monotonicity.
      intro hu y v hv
      exact (isMonotone_iff A).1 hA.monotone hu hv
    · intro hMinty
      by_contra hxu
      -- A local separator on `univ` contradicts the assumed Minty inequalities.
      rcases hA.exists_mem_and_inner_lt_zero (by simp) hxu with ⟨y, v, _, hv, hlt⟩
      exact not_lt_of_ge (hMinty hv) hlt
  · intro hA
    refine ⟨hA.1, isOpen_univ, convex_univ, ?_, ?_⟩
    · -- Maximality forces the graph to be nonempty, hence the range meets `univ`.
      simpa using rangeNonemptyOfMaximal hA
    · intro x u _ hxu
      by_contra hNoWitness
      have hMinty : ∀ ⦃y v : H⦄, v ∈ A y → 0 ≤ ⟪x - y, u - v⟫_ℝ := by
        intro y v hv
        by_contra hlt
        exact hNoWitness ⟨y, v, by simp, hv, lt_of_not_ge hlt⟩
      exact hxu ((SetValuedOperator.Maximal.mem_iff hA x u).2 fun {y v} hv ↦ hMinty hv)

/-- Proposition 25.8. For a monotone operator, local maximal monotonicity is equivalent to the
bounded closed convex localization criterion. -/
theorem isLocallyMaximallyMonotone_iff_forall_bounded_closed_convex
    {A : SetValuedOperator H H} (hA_mono : A.IsMonotone) :
    A.IsLocallyMaximallyMonotone ↔
      ∀ C : Set H, Bornology.IsBounded C → IsClosed C → Convex ℝ C →
        (interior C ∩ A.range).Nonempty →
        ∀ ⦃x u : H⦄, u ∈ interior C → u ∉ A x →
          ∃ y v : H, v ∈ C ∧ v ∈ A y ∧ ⟪x - y, u - v⟫_ℝ < 0 := by
  constructor
  · intro hA C _ _ hC_convex hC_range x u huC hxu
    have hAInterior : A.IsLocallyMaximallyMonotoneOn (interior C) :=
      hA.on_set isOpen_interior hC_convex.interior hC_range
    -- The forward direction is the defining local property applied to `interior C`.
    rcases hAInterior.exists_mem_and_inner_lt_zero huC hxu with ⟨y, v, hvInt, hvA, hlt⟩
    exact ⟨y, v, interior_subset hvInt, hvA, hlt⟩
  · intro hCriterion
    rw [isLocallyMaximallyMonotone_iff]
    refine ⟨hA_mono, ?_⟩
    intro U hU_open hU_convex hU_range
    refine ⟨hA_mono, hU_open, hU_convex, hU_range, ?_⟩
    intro x u huU hxu
    rcases hU_range with ⟨w, hwU, hwRange⟩
    rcases segmentClosedBallSubsetOfOpenConvex hU_open hU_convex huU hwU with
      ⟨ε, hε_pos, hC_subset, huInt, hwInt⟩
    let C : Set H := segment ℝ u w + Metric.closedBall (0 : H) ε
    have hC_props :
        Bornology.IsBounded C ∧ IsClosed C ∧ Convex ℝ C :=
      boundedClosedConvexSegmentAddClosedBall u w (le_of_lt hε_pos)
    rcases hC_props with ⟨hC_bounded, hC_closed, hC_convex⟩
    have hC_range : (interior C ∩ A.range).Nonempty := by
      exact ⟨w, hwInt, hwRange⟩
    -- The backward direction applies the bounded closed convex criterion to the localizer `C`.
    rcases hCriterion C hC_bounded hC_closed hC_convex hC_range huInt hxu with
      ⟨y, v, hvC, hvA, hlt⟩
    exact ⟨y, v, hC_subset hvC, hvA, hlt⟩

end SetValuedOperator
