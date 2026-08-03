module

public import Topology_Munkres_2000.Book.Definition_36_6
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.ChartedSpace

public section

open Set

namespace LineWithTwoOrigins

namespace Origin

/-- The other distinguished origin. -/
def other : Origin → Origin
  | .p => .q
  | .q => .p

/-- The other origin is distinct from the selected origin. -/
theorem other_ne (o : Origin) : o.other ≠ o := by
  cases o <;> simp [other]

/-- Helper for Exercise 36.5: the selected origin differs from the other origin. -/
theorem ne_other (o : Origin) : o ≠ o.other := by
  exact o.other_ne.symm

end Origin

/-- Helper for Exercise 36.5: the other distinguished origin survives deletion of the selected
origin. -/
theorem originOther_ne_origin (o : Origin) : origin o.other ≠ origin o := by
  intro h
  exact o.other_ne (LineWithTwoOrigins.origin.inj h)

/-- Helper for Exercise 36.5: every ordinary point differs from each distinguished origin. -/
theorem point_ne_origin (x : ℝ) (hx : x ≠ 0) (o : Origin) : point x hx ≠ origin o := by
  intro h
  cases h

/-- Helper for Exercise 36.5: the inverse coordinate map avoids the deleted origin. -/
theorem removeOriginInvFun_ne_origin (o : Origin) (x : ℝ) :
    (if hx : x = 0 then origin o.other else point x hx) ≠ origin o := by
  split
  · exact originOther_ne_origin o
  · exact point_ne_origin x ‹x ≠ 0› o

/-- Helper for Exercise 36.5: the inverse coordinate map on the punctured line. -/
noncomputable def removeOriginInvFun (o : Origin) (x : ℝ) :
    {z : LineWithTwoOrigins | z ≠ origin o} :=
  ⟨if hx : x = 0 then origin o.other else point x hx, removeOriginInvFun_ne_origin o x⟩

/-- Helper for Exercise 36.5: the coordinate map is inverted on the punctured line. -/
theorem removeOriginLeftInv (o : Origin) (z : {z : LineWithTwoOrigins | z ≠ origin o}) :
    removeOriginInvFun o (toReal z) = z := by
  apply Subtype.ext
  rcases z with ⟨z, hz⟩
  cases z with
  | point x hx =>
      simp only [removeOriginInvFun, toReal_point, dif_neg hx]
  | origin o' =>
      have hne : o' ≠ o := by
        intro h
        exact hz (congrArg origin h)
      have hother : o.other = o' := by
        cases o <;> cases o' <;> simp_all [Origin.other]
      simp only [removeOriginInvFun, toReal_origin]
      exact congrArg origin hother

/-- Helper for Exercise 36.5: the punctured-line inverse preserves real coordinates. -/
theorem removeOriginRightInv (o : Origin) (x : ℝ) :
    toReal (removeOriginInvFun o x) = x := by
  by_cases hx : x = 0
  · simp only [removeOriginInvFun, dif_pos hx, toReal_origin]
    exact hx.symm
  · simp only [removeOriginInvFun, dif_neg hx, toReal_point]


/-- Helper for Exercise 36.5: transported intervals avoiding zero are open. -/
theorem isOpen_interval {l r : ℝ} (hlr : l < r) (hzero : 0 ∉ Ioo l r) :
    IsOpen (interval l r) := by
  exact basis_isTopologicalBasis.isOpen (mem_basis_iff.mpr (.inl ⟨l, r, hlr, hzero, rfl⟩))

/-- Helper for Exercise 36.5: positive-radius neighborhoods of an origin are open. -/
theorem isOpen_originNeighborhood (o : Origin) {a : ℝ} (ha : 0 < a) :
    IsOpen (originNeighborhood o a) := by
  exact basis_isTopologicalBasis.isOpen (mem_basis_iff.mpr (.inr ⟨o, a, ha, rfl⟩))

/-- Helper for Exercise 36.5: the inverse map sends zero to the surviving origin. -/
theorem removeOriginInvFun_zero (o : Origin) :
    (removeOriginInvFun o 0 : LineWithTwoOrigins) = origin o.other := by
  simp [removeOriginInvFun]

/-- Helper for Exercise 36.5: the inverse map sends a nonzero coordinate to its ordinary point. -/
theorem removeOriginInvFun_of_ne (o : Origin) {x : ℝ} (hx : x ≠ 0) :
    (removeOriginInvFun o x : LineWithTwoOrigins) = point x hx := by
  simp only [removeOriginInvFun, dif_neg hx]

/-- Helper for Exercise 36.5: the real coordinate is continuous. -/
theorem continuous_toReal : Continuous toReal := by
  rw [continuous_def]
  intro s hs
  refine basis_isTopologicalBasis.isOpen_iff.mpr ?_
  intro z hz
  cases z with
  | point x hx =>
      obtain ⟨l, r, ⟨hlx, hxr⟩, hlrs⟩ := mem_nhds_iff_exists_Ioo_subset.mp
        (hs.mem_nhds (show x ∈ s from toReal_point x hx ▸ hz))
      by_cases xpos : 0 < x
      · refine ⟨interval (max l 0) r, ?_, ?_, ?_⟩
        · exact mem_basis_iff.mpr (.inl ⟨max l 0, r,
            max_lt (hlx.trans hxr) (xpos.trans hxr), by simp, rfl⟩)
        · exact point_mem_interval_iff hx |>.mpr ⟨max_lt_iff.mpr ⟨hlx, xpos⟩, hxr⟩
        · intro w hw
          cases w with
          | point y hy =>
              change toReal (point y hy) ∈ s
              rw [toReal_point]
              exact hlrs ⟨lt_of_le_of_lt (le_max_left l 0)
                ((point_mem_interval_iff hy).mp hw).1, ((point_mem_interval_iff hy).mp hw).2⟩
          | origin o => exact (origin_not_mem_interval o _ _ hw).elim
      · have xneg : x < 0 := lt_of_le_of_ne (le_of_not_gt xpos) hx
        refine ⟨interval l (min r 0), ?_, ?_, ?_⟩
        · exact mem_basis_iff.mpr (.inl ⟨l, min r 0,
            lt_min (hlx.trans hxr) (hlx.trans xneg), by simp, rfl⟩)
        · exact point_mem_interval_iff hx |>.mpr ⟨hlx, lt_min hxr xneg⟩
        · intro w hw
          cases w with
          | point y hy =>
              change toReal (point y hy) ∈ s
              rw [toReal_point]
              exact hlrs ⟨((point_mem_interval_iff hy).mp hw).1,
                lt_of_lt_of_le ((point_mem_interval_iff hy).mp hw).2 (min_le_left r 0)⟩
          | origin o => exact (origin_not_mem_interval o _ _ hw).elim
  | origin o =>
      obtain ⟨l, r, ⟨hl0, h0r⟩, hlrs⟩ := mem_nhds_iff_exists_Ioo_subset.mp
        (hs.mem_nhds (show (0 : ℝ) ∈ s from toReal_origin o ▸ hz))
      let a := min (-l) r
      have ha : 0 < a := lt_min (neg_pos.mpr hl0) h0r
      refine ⟨originNeighborhood o a, mem_basis_iff.mpr (.inr ⟨o, a, ha, rfl⟩), ?_, ?_⟩
      · exact mem_originNeighborhood_iff.mpr (.inr rfl)
      · intro w hw
        rcases mem_originNeighborhood_iff.mp hw with hw | rfl
        · cases w with
          | point y hy =>
              change toReal (point y hy) ∈ s
              rw [toReal_point]
              have hyIoo := (point_mem_interval_iff hy).mp hw
              have hly : l < y := by
                linarith [hyIoo.1, min_le_left (-l) r]
              exact hlrs ⟨hly, lt_of_lt_of_le hyIoo.2 (min_le_right (-l) r)⟩
          | origin o' => exact (origin_not_mem_interval o' _ _ hw).elim
        · change toReal (origin o) ∈ s
          rw [toReal_origin]
          exact hlrs ⟨hl0, h0r⟩

/-- Helper for Exercise 36.5: the punctured-line inverse is continuous. -/
theorem continuous_removeOriginInvFun (o : Origin) : Continuous (removeOriginInvFun o) := by
  rw [Topology.IsInducing.subtypeVal.continuous_iff, continuous_def]
  intro s hs
  refine isOpen_iff_mem_nhds.mpr ?_
  intro x hx
  by_cases hzero : x = 0
  · subst x
    have hx' : origin o.other ∈ s := removeOriginInvFun_zero o ▸ hx
    obtain ⟨t, ht, hot, hts⟩ := basis_isTopologicalBasis.isOpen_iff.mp hs
      (origin o.other) hx'
    rcases mem_basis_iff.mp ht with ⟨l, r, hlr, hnot, rfl⟩ | ⟨o', a, ha, rfl⟩
    · exact (origin_not_mem_interval o.other l r hot).elim
    · have hoo : o' = o.other := by
        rcases mem_originNeighborhood_iff.mp hot with hot | hot
        · exact (origin_not_mem_interval o.other (-a) a hot).elim
        · exact origin.inj hot.symm
      refine Filter.mem_of_superset (isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr ha, ha⟩) ?_
      intro y hy
      apply hts
      rw [hoo]
      rcases eq_or_ne y 0 with rfl | hyzero
      · change (removeOriginInvFun o 0 : LineWithTwoOrigins) ∈ originNeighborhood o.other a
        rw [removeOriginInvFun_zero]
        exact mem_originNeighborhood_iff.mpr (.inr rfl)
      · change (removeOriginInvFun o y : LineWithTwoOrigins) ∈ originNeighborhood o.other a
        rw [removeOriginInvFun_of_ne o hyzero]
        exact mem_originNeighborhood_iff.mpr (.inl ((point_mem_interval_iff hyzero).mpr hy))
  · have hx' : point x hzero ∈ s := removeOriginInvFun_of_ne o hzero ▸ hx
    obtain ⟨t, ht, hxt, hts⟩ := basis_isTopologicalBasis.isOpen_iff.mp hs
      (point x hzero) hx'
    rcases mem_basis_iff.mp ht with ⟨l, r, hlr, hnot, rfl⟩ | ⟨o', a, ha, rfl⟩
    · have hxIoo := (point_mem_interval_iff hzero).mp hxt
      refine Filter.mem_of_superset (isOpen_Ioo.mem_nhds hxIoo) ?_
      intro y hy
      have hyzero : y ≠ 0 := by
        intro hy0
        subst y
        exact hnot hy
      change (removeOriginInvFun o y : LineWithTwoOrigins) ∈ s
      rw [removeOriginInvFun_of_ne o hyzero]
      exact hts ((point_mem_interval_iff hyzero).mpr hy)
    · rcases mem_originNeighborhood_iff.mp hxt with hxt | hxt
      · have hxIoo := (point_mem_interval_iff hzero).mp hxt
        have hside : x < 0 ∨ 0 < x := lt_or_gt_of_ne hzero
        rcases hside with xneg | xpos
        · refine Filter.mem_of_superset (isOpen_Ioo.mem_nhds ⟨hxIoo.1, xneg⟩) ?_
          intro y hy
          have hyzero : y ≠ 0 := ne_of_lt hy.2
          change (removeOriginInvFun o y : LineWithTwoOrigins) ∈ s
          rw [removeOriginInvFun_of_ne o hyzero]
          exact hts (mem_originNeighborhood_iff.mpr (.inl
            ((point_mem_interval_iff hyzero).mpr ⟨hy.1, hy.2.trans ha⟩)))
        · refine Filter.mem_of_superset (isOpen_Ioo.mem_nhds ⟨xpos, hxIoo.2⟩) ?_
          intro y hy
          have hyzero : y ≠ 0 := ne_of_gt hy.1
          change (removeOriginInvFun o y : LineWithTwoOrigins) ∈ s
          rw [removeOriginInvFun_of_ne o hyzero]
          exact hts (mem_originNeighborhood_iff.mpr (.inl
            ((point_mem_interval_iff hyzero).mpr ⟨(neg_lt_zero.mpr ha).trans hy.1, hy.2⟩)))
      · exact (point_ne_origin x hzero o' hxt).elim

/-- Deleting either origin from the line with two origins gives a copy of `ℝ`. -/
noncomputable def removeOriginHomeomorphReal (o : Origin) :
    {z : LineWithTwoOrigins | z ≠ origin o} ≃ₜ ℝ where
  toFun z := toReal z
  invFun := removeOriginInvFun o
  left_inv := removeOriginLeftInv o
  right_inv := removeOriginRightInv o
  continuous_toFun := continuous_toReal.comp continuous_subtype_val
  continuous_invFun := continuous_removeOriginInvFun o

/-- The standard homeomorphism from `ℝ` to one-dimensional Euclidean space. -/
noncomputable def realHomeomorphEuclideanOne : ℝ ≃ₜ EuclideanSpace ℝ (Fin 1) :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr.toHomeomorph

/-- Helper for Exercise 36.5: the chart coordinate and inverse cancel on its source. -/
theorem chartLeftInv (o : Origin) (z : LineWithTwoOrigins) (hz : z ≠ origin o) :
    (removeOriginHomeomorphReal o).symm
      (realHomeomorphEuclideanOne.symm (realHomeomorphEuclideanOne (toReal z))) = z := by
  rw [realHomeomorphEuclideanOne.symm_apply_apply]
  exact congrArg Subtype.val ((removeOriginHomeomorphReal o).symm_apply_apply ⟨z, hz⟩)

/-- Helper for Exercise 36.5: the chart inverse and coordinate cancel on the model space. -/
theorem chartRightInv (o : Origin) (x : EuclideanSpace ℝ (Fin 1)) :
    realHomeomorphEuclideanOne
      (toReal ((removeOriginHomeomorphReal o).symm (realHomeomorphEuclideanOne.symm x))) = x := by
  rw [show ((removeOriginHomeomorphReal o).symm (realHomeomorphEuclideanOne.symm x) :
    LineWithTwoOrigins) = removeOriginInvFun o (realHomeomorphEuclideanOne.symm x) from rfl]
  rw [removeOriginRightInv, realHomeomorphEuclideanOne.apply_symm_apply]

/-- Helper for Exercise 36.5: deleting either origin gives an open subset. -/
theorem isOpen_ne_origin (o : Origin) : IsOpen {z : LineWithTwoOrigins | z ≠ origin o} := by
  refine basis_isTopologicalBasis.isOpen_iff.mpr ?_
  intro z hz
  cases z with
  | point x hx =>
      by_cases xpos : 0 < x
      · refine ⟨interval (x / 2) (x * 2),
          mem_basis_iff.mpr (.inl ⟨x / 2, x * 2, ?_, ?_, rfl⟩), ?_, ?_⟩
        · linarith
        · intro h
          exact (not_lt_of_ge (div_nonneg xpos.le (by norm_num))) h.1
        · exact (point_mem_interval_iff hx).mpr (by constructor <;> linarith)
        · intro w hw hwo
          cases hwo
          exact (origin_not_mem_interval o _ _) hw
      · have xneg : x < 0 := lt_of_le_of_ne (le_of_not_gt xpos) hx
        refine ⟨interval (x * 2) (x / 2),
          mem_basis_iff.mpr (.inl ⟨x * 2, x / 2, ?_, ?_, rfl⟩), ?_, ?_⟩
        · linarith
        · simp [not_lt, xneg.le]
        · exact (point_mem_interval_iff hx).mpr (by constructor <;> linarith)
        · intro w hw hwo
          cases hwo
          exact (origin_not_mem_interval o _ _) hw
  | origin o' =>
      have hoo : o' = o.other := by
        cases o <;> cases o' <;> simp_all [Origin.other]
      refine ⟨originNeighborhood o.other 1,
        mem_basis_iff.mpr (.inr ⟨o.other, 1, by norm_num, rfl⟩), ?_, ?_⟩
      · exact mem_originNeighborhood_iff.mpr (.inr (congrArg origin hoo))
      · intro w hw hwo
        cases hwo
        rcases mem_originNeighborhood_iff.mp hw with hw | hw
        · exact (origin_not_mem_interval o _ _ hw).elim
        · exact o.other_ne (origin.inj hw.symm)

/-- Helper for Exercise 36.5: the chart inverse lands in the deleted-origin source. -/
theorem chartMapTarget (o : Origin) (x : EuclideanSpace ℝ (Fin 1)) :
    x ∈ univ →
      ((removeOriginHomeomorphReal o).symm (realHomeomorphEuclideanOne.symm x) :
        LineWithTwoOrigins) ≠ origin o := by
  intro _
  exact ((removeOriginHomeomorphReal o).symm (realHomeomorphEuclideanOne.symm x)).property

/-- The chart obtained by deleting one origin and using the real coordinate. -/
noncomputable def chart (o : Origin) :
    OpenPartialHomeomorph LineWithTwoOrigins (EuclideanSpace ℝ (Fin 1)) where
  toPartialEquiv :=
    { toFun := fun z ↦ realHomeomorphEuclideanOne (toReal z)
      invFun := fun x ↦ (removeOriginHomeomorphReal o).symm
        (realHomeomorphEuclideanOne.symm x)
      source := {z | z ≠ origin o}
      target := univ
      map_source' := fun _ _ ↦ mem_univ _
      map_target' := chartMapTarget o
      left_inv' := chartLeftInv o
      right_inv' := fun x _ ↦ chartRightInv o x }
  open_source := isOpen_ne_origin o
  open_target := isOpen_univ
  continuousOn_toFun :=
    (realHomeomorphEuclideanOne.continuous.comp continuous_toReal).continuousOn
  continuousOn_invFun :=
    (continuous_subtype_val.comp ((removeOriginHomeomorphReal o).symm.continuous.comp
      realHomeomorphEuclideanOne.symm.continuous)).continuousOn

/-- Helper for Exercise 36.5: each point belongs to the source of its selected chart. -/
theorem mem_selectedChartSource (x : LineWithTwoOrigins) :
    x ∈ (match x with
      | point _ _ => chart .p
      | origin .p => chart .q
      | origin .q => chart .p).source := by
  cases x with
  | point x hx => exact point_ne_origin x hx .p
  | origin o => cases o <;> simp [chart]

/-- Helper for Exercise 36.5: each selected chart belongs to the two-chart atlas. -/
theorem selectedChart_mem_atlas (x : LineWithTwoOrigins) :
    (match x with
      | point _ _ => chart .p
      | origin .p => chart .q
      | origin .q => chart .p) ∈ range chart := by
  cases x with
  | point x hx => exact ⟨Origin.p, rfl⟩
  | origin o => cases o <;> exact ⟨_, rfl⟩

/-- The line with two origins is locally modelled on one-dimensional Euclidean space. -/
noncomputable instance instChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 1)) LineWithTwoOrigins where
  atlas := range chart
  chartAt
    | point _ _ => chart .p
    | origin .p => chart .q
    | origin .q => chart .p
  mem_chart_source := mem_selectedChartSource
  chart_mem_atlas := selectedChart_mem_atlas

end LineWithTwoOrigins
