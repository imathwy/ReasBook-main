module

public import Topology_Munkres_2000.Book.Definition_25_4.Neighborhoods
public import Mathlib.Analysis.Convex.«PathConnected»
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Instances.RatLemmas

public section

open Filter Set Topology
open scoped Convex

/-- The apex `(0, 1)` of the rational fan. -/
def rationalFanApex : ℝ × ℝ := (0, 1)

/-- The rational points of the horizontal interval `[0, 1] × {0}`. -/
def rationalFanBase : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Icc (0 : ℝ) 1 ∧ x.2 = 0 ∧ x.1 ∈ Set.range fun q : ℚ ↦ (q : ℝ)}

/-- A point lies in the rational fan base exactly when it lies on the horizontal
unit interval and its first coordinate is rational. -/
theorem mem_rationalFanBase_iff (x : ℝ × ℝ) :
    x ∈ rationalFanBase ↔
      x.1 ∈ Icc (0 : ℝ) 1 ∧ x.2 = 0 ∧ ∃ q : ℚ, (q : ℝ) = x.1 := by
  simp [rationalFanBase]

/-- The union of the line segments from `(0, 1)` to the rational points of
`[0, 1] × {0}`. -/
def rationalFan : Set (ℝ × ℝ) :=
  ⋃ x ∈ rationalFanBase, [rationalFanApex -[ℝ] x]

/-- A point lies in the rational fan exactly when it lies on a segment from the
apex to a rational point of the horizontal unit interval. -/
theorem mem_rationalFan_iff (y : ℝ × ℝ) :
    y ∈ rationalFan ↔ ∃ x ∈ rationalFanBase, y ∈ [rationalFanApex -[ℝ] x] := by
  simp [rationalFan]

/-- Helper for Exercise 25.5: points of the rational fan have the standard
radial parametrization by a height parameter and a rational slope. -/
lemma mem_rationalFan_iff_exists_rat_slice (z : ℝ × ℝ) :
    z ∈ rationalFan ↔ ∃ t ∈ Icc (0 : ℝ) 1, ∃ q : ℚ,
      (q : ℝ) ∈ Icc (0 : ℝ) 1 ∧ z = (t * (q : ℝ), 1 - t) := by
  -- Expand a spoke with the canonical line-map parametrization.
  rw [mem_rationalFan_iff]
  constructor
  · rintro ⟨x, hx, hz⟩
    rw [mem_rationalFanBase_iff] at hx
    obtain ⟨hxIcc, hx2, q, hq⟩ := hx
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    refine ⟨t, ht, q, ?_, ?_⟩
    · simpa only [hq] using hxIcc
    · apply Prod.ext
      · simp [rationalFanApex, AffineMap.lineMap_apply, ← hq]
      · simp [rationalFanApex, AffineMap.lineMap_apply, hx2]
        ring
  · rintro ⟨t, ht, q, hq, rfl⟩
    refine ⟨((q : ℝ), 0), ?_, ?_⟩
    · rw [mem_rationalFanBase_iff]
      exact ⟨hq, rfl, q, rfl⟩
    · rw [segment_eq_image_lineMap]
      refine ⟨t, ht, ?_⟩
      apply Prod.ext
      · simp [rationalFanApex, AffineMap.lineMap_apply]
      · simp [rationalFanApex, AffineMap.lineMap_apply]
        ring

/-- Helper for Exercise 25.5: the rational fan is star-convex at its apex. -/
lemma rationalFanStarConvex : StarConvex ℝ rationalFanApex rationalFan := by
  -- Each spoke is convex and contains the common apex; unions preserve this
  -- star-convexity.
  unfold rationalFan
  refine starConvex_iUnion₂ fun x hx ↦ ?_
  exact (convex_segment rationalFanApex x) (left_mem_segment ℝ rationalFanApex x)

/-- The apex belongs to the rational fan. -/
theorem rationalFanApex_mem : rationalFanApex ∈ rationalFan := by
  -- Use the zero rational spoke, whose left endpoint is the apex.
  rw [mem_rationalFan_iff]
  refine ⟨(0, 0), ?_, left_mem_segment ℝ rationalFanApex (0, 0)⟩
  rw [mem_rationalFanBase_iff]
  have hzeroIcc : (0 : ℝ) ∈ Icc 0 1 := by
    norm_num
  have hzeroCast : ((0 : ℚ) : ℝ) = 0 := by
    norm_num
  exact ⟨hzeroIcc, rfl, 0, hzeroCast⟩

/-- Helper for Exercise 25.5: the rational fan `T` is path connected. -/
theorem rationalFan_isPathConnected : IsPathConnected rationalFan := by
  -- Star-convexity joins every point to the apex by its spoke.
  exact rationalFanStarConvex.isPathConnected rationalFanApex_mem

/-- Helper for Exercise 25.5: the apex regarded as a point of the rational fan. -/
def rationalFanApexPoint : rationalFan := ⟨rationalFanApex, rationalFanApex_mem⟩

/-- Helper for Exercise 25.5: the rational fan is locally connected at its apex. -/
lemma rationalFanApex_isLocallyConnectedAt :
    IsLocallyConnectedAt rationalFanApexPoint := by
  -- Intersections with sufficiently small apex-centered balls are still
  -- star-convex, and hence give connected subtype neighborhoods.
  rw [isLocallyConnectedAt_iff_connected_neighborhoods]
  intro U hU
  obtain ⟨r, hr, hballU⟩ := Metric.nhds_basis_ball.mem_iff.mp hU
  let W : Set (ℝ × ℝ) := rationalFan ∩ Metric.ball rationalFanApex r
  have hcenter : rationalFanApex ∈ W := by
    exact ⟨rationalFanApex_mem, Metric.mem_ball_self hr⟩
  have hWstar : StarConvex ℝ rationalFanApex W := by
    exact rationalFanStarConvex.inter ((convex_ball rationalFanApex r) hcenter.2)
  have hWpath : IsPathConnected W := by
    exact hWstar.isPathConnected hcenter
  refine ⟨(fun z : rationalFan ↦ (z : ℝ × ℝ)) ⁻¹' W, ?_, ?_, ?_, ?_⟩
  · intro z hz
    apply hballU
    simpa only [W, mem_preimage, mem_inter_iff, Metric.mem_ball, Subtype.dist_eq,
      rationalFanApexPoint] using hz.2
  · have hopen : IsOpen ((fun z : rationalFan ↦ (z : ℝ × ℝ)) ⁻¹'
        Metric.ball rationalFanApex r) := by
      exact Metric.isOpen_ball.preimage continuous_subtype_val
    simpa only [W, preimage_inter, Subtype.coe_preimage_self, univ_inter] using hopen
  · exact hcenter
  · exact (hWpath.preimage_coe inter_subset_left).isConnected

/-- Helper for Exercise 25.5: no rational point of the closed unit interval is
isolated relative to that interval. -/
lemma existsNearbyRatInUnitInterval (q : ℚ)
    (hq : (q : ℝ) ∈ Icc (0 : ℝ) 1) (W : Set ℚ) (hW : W ∈ 𝓝 q) :
    ∃ q' ∈ W, (q' : ℝ) ∈ Icc (0 : ℝ) 1 ∧ q' ≠ q := by
  -- Take a smaller rational point at the right endpoint and a larger one
  -- everywhere else, keeping it inside a metric ball contained in `W`.
  obtain ⟨ε, hε, hballW⟩ := Metric.mem_nhds_iff.mp hW
  by_cases hqtop : (q : ℝ) < 1
  · have hqmin : (q : ℝ) < min 1 ((q : ℝ) + ε) := by
      exact lt_min hqtop (lt_add_of_pos_right _ hε)
    obtain ⟨q', hqq', hq'upper⟩ := exists_rat_btwn hqmin
    have hq'ball : q' ∈ Metric.ball q ε := by
      rw [Metric.mem_ball, Rat.dist_eq, abs_of_nonneg]
      · linarith [hq'upper, min_le_right (1 : ℝ) ((q : ℝ) + ε)]
      · exact sub_nonneg.mpr hqq'.le
    refine ⟨q', hballW hq'ball, ?_, ?_⟩
    · exact ⟨hq.1.trans hqq'.le,
        hq'upper.le.trans (min_le_left (1 : ℝ) ((q : ℝ) + ε))⟩
    · intro h
      subst q'
      exact (lt_irrefl (q : ℝ)) hqq'
  · have hqeq : (q : ℝ) = 1 := by
      exact le_antisymm hq.2 (not_lt.mp hqtop)
    have hmaxq : max 0 ((q : ℝ) - ε) < (q : ℝ) := by
      rw [hqeq]
      exact max_lt zero_lt_one (sub_lt_self 1 hε)
    obtain ⟨q', hq'lower, hq'q⟩ := exists_rat_btwn hmaxq
    have hq'ball : q' ∈ Metric.ball q ε := by
      rw [Metric.mem_ball, Rat.dist_eq, abs_of_nonpos]
      · have hlower : (q : ℝ) - ε < (q' : ℝ) :=
          (le_max_right 0 ((q : ℝ) - ε)).trans_lt hq'lower
        linarith
      · exact sub_nonpos.mpr hq'q.le
    refine ⟨q', hballW hq'ball, ?_, ?_⟩
    · exact ⟨(le_max_left 0 ((q : ℝ) - ε)).trans hq'lower.le,
        hq'q.le.trans hq.2⟩
    · intro h
      subst q'
      exact (lt_irrefl (q : ℝ)) hq'q

/-- Helper for Exercise 25.5: every nonempty connected open subset of the
rational fan contains its apex. -/
lemma rationalFanApexPoint_mem_of_isOpen_isConnected (V : Set rationalFan)
    (hVopen : IsOpen V) (hVconnected : IsConnected V) :
    rationalFanApexPoint ∈ V := by
  -- Away from the apex, the continuous slope `x / (1-y)` is rational-valued.
  -- Connectedness makes it constant, whereas openness permits varying the
  -- rational endpoint of any one spoke.
  by_contra hapex
  let slope : rationalFan → ℝ := fun z ↦ (z : ℝ × ℝ).1 / (1 - (z : ℝ × ℝ).2)
  have hdenom : ∀ z ∈ V, 1 - (z : ℝ × ℝ).2 ≠ 0 := by
    intro z hzV hzero
    obtain ⟨t, ht, q, hq, hz⟩ := mem_rationalFan_iff_exists_rat_slice z
      |>.mp z.property
    have htzero : t = 0 := by
      rw [hz] at hzero
      simpa only [Prod.snd, sub_sub_cancel] using hzero
    have hzapex : z = rationalFanApexPoint := by
      apply Subtype.ext
      rw [hz, htzero]
      simp [rationalFanApexPoint, rationalFanApex]
    exact hapex (hzapex ▸ hzV)
  have hslopeContinuous : ContinuousOn slope V := by
    apply ContinuousOn.div
    · exact (continuous_fst.comp continuous_subtype_val).continuousOn
    · exact (continuous_const.sub
        (continuous_snd.comp continuous_subtype_val)).continuousOn
    · exact hdenom
  have hslopeRange : slope '' V ⊆ Set.range fun q : ℚ ↦ (q : ℝ) := by
    rintro _ ⟨z, hzV, rfl⟩
    obtain ⟨t, ht, q, hq, hz⟩ := mem_rationalFan_iff_exists_rat_slice z
      |>.mp z.property
    refine ⟨q, ?_⟩
    have htne : t ≠ 0 := by
      intro htzero
      apply hdenom z hzV
      rw [hz, htzero]
      norm_num
    dsimp [slope]
    rw [hz]
    simp only [sub_sub_cancel]
    field_simp
  have hslopeSubsingleton : (slope '' V).Subsingleton := by
    have hpreconnected := hVconnected.isPreconnected.image slope hslopeContinuous
    exact (Rat.isEmbedding_coe_real.isTotallyDisconnected_range.mpr inferInstance)
      (slope '' V) hslopeRange hpreconnected
  obtain ⟨z, hzV⟩ := hVconnected.nonempty
  obtain ⟨t, ht, q, hq, hz⟩ := mem_rationalFan_iff_exists_rat_slice z
    |>.mp z.property
  have htne : t ≠ 0 := by
    intro htzero
    apply hdenom z hzV
    rw [hz, htzero]
    norm_num
  obtain ⟨O, hOopen, hOV⟩ := isOpen_induced_iff.mp hVopen
  let spoke : ℚ → ℝ × ℝ := fun r ↦ (t * (r : ℝ), 1 - t)
  have hspokeContinuous : Continuous spoke := by
    fun_prop
  have hzO : (z : ℝ × ℝ) ∈ O := by
    have hzpre : z ∈ (fun w : rationalFan ↦ (w : ℝ × ℝ)) ⁻¹' O := by
      rwa [hOV]
    exact hzpre
  have hspokeq : spoke q = (z : ℝ × ℝ) := by
    exact hz.symm
  have hpreimageNhds : spoke ⁻¹' O ∈ 𝓝 q := by
    apply hspokeContinuous.continuousAt
    rw [hspokeq]
    exact hOopen.mem_nhds hzO
  obtain ⟨q', hq'O, hq'Icc, hq'ne⟩ :=
    existsNearbyRatInUnitInterval q hq (spoke ⁻¹' O) hpreimageNhds
  have hyFan : spoke q' ∈ rationalFan := by
    rw [mem_rationalFan_iff_exists_rat_slice]
    exact ⟨t, ht, q', hq'Icc, rfl⟩
  let y : rationalFan := ⟨spoke q', hyFan⟩
  have hyV : y ∈ V := by
    rw [← hOV]
    exact hq'O
  have hslopeEq : slope z = slope y := by
    exact hslopeSubsingleton ⟨z, hzV, rfl⟩ ⟨y, hyV, rfl⟩
  have hcastEq : (q : ℝ) = (q' : ℝ) := by
    dsimp [slope] at hslopeEq
    rw [hz] at hslopeEq
    simp only [sub_sub_cancel] at hslopeEq
    dsimp [y, spoke] at hslopeEq
    simp only [sub_sub_cancel] at hslopeEq
    field_simp [htne] at hslopeEq
    exact hslopeEq
  exact hq'ne (Rat.cast_injective hcastEq.symm)

/-- Helper for Exercise 25.5: the rational fan `T` is locally connected precisely at
its apex `p = (0, 1)`. -/
theorem rationalFan_isLocallyConnectedAt_iff (x : rationalFan) :
    IsLocallyConnectedAt x ↔ (x : ℝ × ℝ) = rationalFanApex := by
  constructor
  · intro hlocal
    -- Exclude the apex from a neighborhood of a putative second locally
    -- connected point, then use the connected-open apex obstruction.
    by_contra hxapex
    have hxne : x ≠ rationalFanApexPoint := by
      intro h
      apply hxapex
      exact congrArg Subtype.val h
    have hcompl : {rationalFanApexPoint}ᶜ ∈ 𝓝 x :=
      isOpen_compl_singleton.mem_nhds hxne
    rw [isLocallyConnectedAt_iff_connected_neighborhoods] at hlocal
    obtain ⟨V, hVsub, hVopen, hxV, hVconnected⟩ := hlocal _ hcompl
    have hapexV := rationalFanApexPoint_mem_of_isOpen_isConnected V hVopen hVconnected
    exact (hVsub hapexV) (mem_singleton rationalFanApexPoint)
  · intro hxapex
    -- Equality in the ambient plane identifies the subtype point with the
    -- apex, where star-convex ball neighborhoods apply.
    have hx : x = rationalFanApexPoint := by
      exact Subtype.ext hxapex
    rw [hx]
    exact rationalFanApex_isLocallyConnectedAt

/-- Helper for Exercise 25.5: the origin belongs to the rational fan. -/
lemma rationalFanOrigin_mem : ((0, 0) : ℝ × ℝ) ∈ rationalFan := by
  -- It is the endpoint of the zero-slope spoke.
  rw [mem_rationalFan_iff_exists_rat_slice]
  have honeIcc : (1 : ℝ) ∈ Icc 0 1 := by
    norm_num
  have hzeroIcc : ((0 : ℚ) : ℝ) ∈ Icc 0 1 := by
    norm_num
  refine ⟨1, honeIcc, 0, hzeroIcc, ?_⟩
  norm_num

/-- The double rational fan, obtained by adjoining to `rationalFan` its image
under the half-turn about `(0, 1 / 2)`. -/
def doubleRationalFan : Set (ℝ × ℝ) :=
  rationalFan ∪ (fun z : ℝ × ℝ ↦ (-z.1, 1 - z.2)) '' rationalFan

/-- Membership in the double rational fan is membership in the original fan or
in its reflected copy. -/
theorem mem_doubleRationalFan_iff (z : ℝ × ℝ) :
    z ∈ doubleRationalFan ↔ z ∈ rationalFan ∨
      ∃ w ∈ rationalFan, (-w.1, 1 - w.2) = z := by
  -- This is the defining union and the explicit image-membership condition.
  simp only [doubleRationalFan, mem_union, mem_image]

/-- Helper for Exercise 25.5: the upper rational-ray invariant on the double fan. -/
noncomputable def doubleRationalFanUpperSlope (z : ℝ × ℝ) : ℝ :=
  max z.1 0 / (1 - z.2 + max (-z.1) 0)

/-- Helper for Exercise 25.5: the lower rational-ray invariant on the double fan. -/
noncomputable def doubleRationalFanLowerSlope (z : ℝ × ℝ) : ℝ :=
  min z.1 0 / (z.2 + max z.1 0)

/-- Helper for Exercise 25.5: the upper slope denominator vanishes in the
double fan only at `(0, 1)`. -/
lemma doubleRationalFanUpperDenominator_ne_zero {z : ℝ × ℝ}
    (hz : z ∈ doubleRationalFan) (hzne : z ≠ rationalFanApex) :
    1 - z.2 + max (-z.1) 0 ≠ 0 := by
  -- Normalize separately on an original spoke and a reflected spoke.
  intro hzero
  rcases (mem_doubleRationalFan_iff z).mp hz with hzright | ⟨w, hw, hwz⟩
  · obtain ⟨t, ht, q, hq, hzt⟩ :=
      (mem_rationalFan_iff_exists_rat_slice z).mp hzright
    have htq : 0 ≤ t * (q : ℝ) := mul_nonneg ht.1 hq.1
    have htzero : t = 0 := by
      rw [hzt] at hzero
      simp only [sub_sub_cancel] at hzero
      rw [max_eq_right (neg_nonpos.mpr htq)] at hzero
      linarith
    apply hzne
    rw [hzt, htzero]
    simp [rationalFanApex]
  · obtain ⟨t, ht, q, hq, hwt⟩ :=
      (mem_rationalFan_iff_exists_rat_slice w).mp hw
    have htq : 0 ≤ t * (q : ℝ) := mul_nonneg ht.1 hq.1
    rw [← hwz, hwt] at hzero
    simp only [neg_neg, sub_sub_cancel] at hzero
    rw [max_eq_left htq] at hzero
    have htone : t = 1 := by
      nlinarith [ht.2]
    have htqzero : t * (q : ℝ) = 0 := by
      nlinarith
    have hqzero : q = 0 := by
      have hqcastzero : (q : ℝ) = 0 := by
        nlinarith [htqzero]
      exact Rat.cast_eq_zero.mp hqcastzero
    apply hzne
    rw [← hwz, hwt, htone]
    simp [rationalFanApex, hqzero]

/-- Helper for Exercise 25.5: the lower slope denominator vanishes in the
double fan only at `(0, 0)`. -/
lemma doubleRationalFanLowerDenominator_ne_zero {z : ℝ × ℝ}
    (hz : z ∈ doubleRationalFan) (hzne : z ≠ (0, 0)) :
    z.2 + max z.1 0 ≠ 0 := by
  -- The same spoke normalization now singles out the lower endpoint.
  intro hzero
  rcases (mem_doubleRationalFan_iff z).mp hz with hzright | ⟨w, hw, hwz⟩
  · obtain ⟨t, ht, q, hq, hzt⟩ :=
      (mem_rationalFan_iff_exists_rat_slice z).mp hzright
    have htq : 0 ≤ t * (q : ℝ) := mul_nonneg ht.1 hq.1
    rw [hzt] at hzero
    dsimp at hzero
    rw [max_eq_left htq] at hzero
    have htone : t = 1 := by
      nlinarith [ht.2]
    have htqzero : t * (q : ℝ) = 0 := by
      nlinarith
    have hqzero : q = 0 := by
      have hqcastzero : (q : ℝ) = 0 := by
        nlinarith [htqzero]
      exact Rat.cast_eq_zero.mp hqcastzero
    apply hzne
    rw [hzt, htone]
    simp [hqzero]
  · obtain ⟨t, ht, q, hq, hwt⟩ :=
      (mem_rationalFan_iff_exists_rat_slice w).mp hw
    have htq : 0 ≤ t * (q : ℝ) := mul_nonneg ht.1 hq.1
    have htzero : t = 0 := by
      rw [← hwz, hwt] at hzero
      simp only [sub_sub_cancel] at hzero
      rw [max_eq_right (neg_nonpos.mpr htq)] at hzero
      simpa only [add_zero] using hzero
    apply hzne
    rw [← hwz, hwt, htzero]
    norm_num

/-- Helper for Exercise 25.5: the upper endpoint belongs to the double fan. -/
lemma doubleRationalFanTop_mem : rationalFanApex ∈ doubleRationalFan := by
  exact (mem_doubleRationalFan_iff rationalFanApex).mpr (Or.inl rationalFanApex_mem)

/-- Helper for Exercise 25.5: the lower endpoint belongs to the double fan. -/
lemma doubleRationalFanBottom_mem : ((0, 0) : ℝ × ℝ) ∈ doubleRationalFan := by
  exact (mem_doubleRationalFan_iff (0, 0)).mpr (Or.inl rationalFanOrigin_mem)

/-- Helper for Exercise 25.5: the upper endpoint as a point of the double fan. -/
def doubleRationalFanTopPoint : doubleRationalFan :=
  ⟨rationalFanApex, doubleRationalFanTop_mem⟩

/-- Helper for Exercise 25.5: the lower endpoint as a point of the double fan. -/
def doubleRationalFanBottomPoint : doubleRationalFan :=
  ⟨(0, 0), doubleRationalFanBottom_mem⟩

/-- Helper for Exercise 25.5: on a connected subset avoiding the upper
endpoint, the upper rational-ray invariant is constant. -/
lemma doubleRationalFanUpperSlope_eq_of_isConnected {V : Set doubleRationalFan}
    (hVconnected : IsConnected V) (htop : doubleRationalFanTopPoint ∉ V)
    {x y : doubleRationalFan} (hx : x ∈ V) (hy : y ∈ V) :
    doubleRationalFanUpperSlope x = doubleRationalFanUpperSlope y := by
  -- Map the connected set continuously into the embedded rational numbers.
  let slope : doubleRationalFan → ℝ :=
    fun z ↦ doubleRationalFanUpperSlope (z : ℝ × ℝ)
  have hne : ∀ z ∈ V, (z : ℝ × ℝ) ≠ rationalFanApex := by
    intro z hz hzeq
    apply htop
    have hzpoint : z = doubleRationalFanTopPoint := by
      exact Subtype.ext hzeq
    rwa [← hzpoint]
  have hcontinuous : ContinuousOn slope V := by
    dsimp [slope, doubleRationalFanUpperSlope]
    have hnum : Continuous (fun z : doubleRationalFan ↦ max (z : ℝ × ℝ).1 0) := by
      fun_prop
    have hden : Continuous (fun z : doubleRationalFan ↦
        1 - (z : ℝ × ℝ).2 + max (-(z : ℝ × ℝ).1) 0) := by
      fun_prop
    exact hnum.continuousOn.div hden.continuousOn fun z hz ↦
      doubleRationalFanUpperDenominator_ne_zero z.property (hne z hz)
  have hrange : slope '' V ⊆ Set.range fun q : ℚ ↦ (q : ℝ) := by
    rintro _ ⟨z, hzV, rfl⟩
    rcases (mem_doubleRationalFan_iff z).mp z.property with hzright | ⟨w, hw, hwz⟩
    · obtain ⟨t, ht, q, hq, hzt⟩ :=
        (mem_rationalFan_iff_exists_rat_slice z).mp hzright
      have htq : 0 ≤ t * (q : ℝ) := mul_nonneg ht.1 hq.1
      have htne : t ≠ 0 := by
        intro htzero
        apply hne z hzV
        rw [hzt, htzero]
        simp [rationalFanApex]
      refine ⟨q, ?_⟩
      dsimp [slope, doubleRationalFanUpperSlope]
      rw [hzt]
      simp only [sub_sub_cancel]
      rw [max_eq_left htq, max_eq_right (neg_nonpos.mpr htq)]
      field_simp [htne]
      ring
    · obtain ⟨t, ht, q, hq, hwt⟩ :=
        (mem_rationalFan_iff_exists_rat_slice w).mp hw
      have htq : 0 ≤ t * (q : ℝ) := mul_nonneg ht.1 hq.1
      refine ⟨0, ?_⟩
      dsimp [slope, doubleRationalFanUpperSlope]
      rw [← hwz, hwt]
      simp only [neg_neg, sub_sub_cancel]
      rw [max_eq_right (neg_nonpos.mpr htq), max_eq_left htq]
      norm_num
  have himagePreconnected := hVconnected.isPreconnected.image slope hcontinuous
  have himageSubsingleton : (slope '' V).Subsingleton :=
    (Rat.isEmbedding_coe_real.isTotallyDisconnected_range.mpr inferInstance)
      (slope '' V) hrange himagePreconnected
  exact himageSubsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩

/-- Helper for Exercise 25.5: on a connected subset avoiding the lower
endpoint, the lower rational-ray invariant is constant. -/
lemma doubleRationalFanLowerSlope_eq_of_isConnected {V : Set doubleRationalFan}
    (hVconnected : IsConnected V) (hbottom : doubleRationalFanBottomPoint ∉ V)
    {x y : doubleRationalFan} (hx : x ∈ V) (hy : y ∈ V) :
    doubleRationalFanLowerSlope x = doubleRationalFanLowerSlope y := by
  -- This is the reflected companion of the upper-slope argument.
  let slope : doubleRationalFan → ℝ :=
    fun z ↦ doubleRationalFanLowerSlope (z : ℝ × ℝ)
  have hne : ∀ z ∈ V, (z : ℝ × ℝ) ≠ (0, 0) := by
    intro z hz hzeq
    apply hbottom
    have hzpoint : z = doubleRationalFanBottomPoint := by
      exact Subtype.ext hzeq
    rwa [← hzpoint]
  have hcontinuous : ContinuousOn slope V := by
    dsimp [slope, doubleRationalFanLowerSlope]
    have hnum : Continuous (fun z : doubleRationalFan ↦ min (z : ℝ × ℝ).1 0) := by
      fun_prop
    have hden : Continuous (fun z : doubleRationalFan ↦
        (z : ℝ × ℝ).2 + max (z : ℝ × ℝ).1 0) := by
      fun_prop
    exact hnum.continuousOn.div hden.continuousOn fun z hz ↦
      doubleRationalFanLowerDenominator_ne_zero z.property (hne z hz)
  have hrange : slope '' V ⊆ Set.range fun q : ℚ ↦ (q : ℝ) := by
    rintro _ ⟨z, hzV, rfl⟩
    rcases (mem_doubleRationalFan_iff z).mp z.property with hzright | ⟨w, hw, hwz⟩
    · obtain ⟨t, ht, q, hq, hzt⟩ :=
        (mem_rationalFan_iff_exists_rat_slice z).mp hzright
      have htq : 0 ≤ t * (q : ℝ) := mul_nonneg ht.1 hq.1
      refine ⟨0, ?_⟩
      dsimp [slope, doubleRationalFanLowerSlope]
      rw [hzt]
      rw [min_eq_right htq]
      norm_num
    · obtain ⟨t, ht, q, hq, hwt⟩ :=
        (mem_rationalFan_iff_exists_rat_slice w).mp hw
      have htq : 0 ≤ t * (q : ℝ) := mul_nonneg ht.1 hq.1
      have htne : t ≠ 0 := by
        intro htzero
        apply hne z hzV
        rw [← hwz, hwt, htzero]
        norm_num
      refine ⟨-q, ?_⟩
      dsimp [slope, doubleRationalFanLowerSlope]
      rw [← hwz, hwt]
      simp only [sub_sub_cancel]
      rw [min_eq_left (neg_nonpos.mpr htq), max_eq_right (neg_nonpos.mpr htq)]
      simp only [add_zero, Rat.cast_neg]
      field_simp [htne]
  have himagePreconnected := hVconnected.isPreconnected.image slope hcontinuous
  have himageSubsingleton : (slope '' V).Subsingleton :=
    (Rat.isEmbedding_coe_real.isTotallyDisconnected_range.mpr inferInstance)
      (slope '' V) hrange himagePreconnected
  exact himageSubsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩

/-- Helper for Exercise 25.5: openness lets the upper slope vary at every
non-apex point of the original fan inside the double fan. -/
lemma exists_doubleRationalFanUpperSlope_ne_of_isOpen
    {V : Set doubleRationalFan} (hVopen : IsOpen V) {x : doubleRationalFan}
    (hxV : x ∈ V) (hxright : (x : ℝ × ℝ) ∈ rationalFan)
    (hxne : (x : ℝ × ℝ) ≠ rationalFanApex) :
    ∃ y ∈ V, doubleRationalFanUpperSlope y ≠ doubleRationalFanUpperSlope x := by
  -- Keep the radial parameter fixed and perturb only its rational endpoint.
  obtain ⟨t, ht, q, hq, hxt⟩ :=
    (mem_rationalFan_iff_exists_rat_slice x).mp hxright
  have htq : 0 ≤ t * (q : ℝ) := mul_nonneg ht.1 hq.1
  have htne : t ≠ 0 := by
    intro htzero
    apply hxne
    rw [hxt, htzero]
    simp [rationalFanApex]
  obtain ⟨O, hOopen, hOV⟩ := isOpen_induced_iff.mp hVopen
  let spoke : ℚ → ℝ × ℝ := fun r ↦ (t * (r : ℝ), 1 - t)
  have hspokeContinuous : Continuous spoke := by
    fun_prop
  have hxO : (x : ℝ × ℝ) ∈ O := by
    have hxpre : x ∈ (fun z : doubleRationalFan ↦ (z : ℝ × ℝ)) ⁻¹' O := by
      rwa [hOV]
    exact hxpre
  have hspokeq : spoke q = (x : ℝ × ℝ) := hxt.symm
  have hpreimageNhds : spoke ⁻¹' O ∈ 𝓝 q := by
    apply hspokeContinuous.continuousAt
    rw [hspokeq]
    exact hOopen.mem_nhds hxO
  obtain ⟨q', hq'O, hq'Icc, hq'ne⟩ :=
    existsNearbyRatInUnitInterval q hq (spoke ⁻¹' O) hpreimageNhds
  have hyFan : spoke q' ∈ rationalFan := by
    rw [mem_rationalFan_iff_exists_rat_slice]
    exact ⟨t, ht, q', hq'Icc, rfl⟩
  have hyDouble : spoke q' ∈ doubleRationalFan :=
    (mem_doubleRationalFan_iff (spoke q')).mpr (Or.inl hyFan)
  let y : doubleRationalFan := ⟨spoke q', hyDouble⟩
  have hyV : y ∈ V := by
    rw [← hOV]
    exact hq'O
  refine ⟨y, hyV, ?_⟩
  intro hslope
  have htq' : 0 ≤ t * (q' : ℝ) := mul_nonneg ht.1 hq'Icc.1
  have hslopeX : doubleRationalFanUpperSlope x = (q : ℝ) := by
    dsimp [doubleRationalFanUpperSlope]
    rw [hxt]
    simp only [sub_sub_cancel]
    rw [max_eq_left htq, max_eq_right (neg_nonpos.mpr htq)]
    field_simp [htne]
    ring
  have hslopeY : doubleRationalFanUpperSlope y = (q' : ℝ) := by
    dsimp [y, spoke, doubleRationalFanUpperSlope]
    simp only [sub_sub_cancel]
    rw [max_eq_left htq', max_eq_right (neg_nonpos.mpr htq')]
    field_simp [htne]
    ring
  apply hq'ne
  have hcast : (q' : ℝ) = (q : ℝ) := by
    rw [← hslopeY, ← hslopeX]
    exact hslope
  exact Rat.cast_injective hcast

/-- Helper for Exercise 25.5: openness lets the lower slope vary at every
non-apex point of the reflected fan inside the double fan. -/
lemma exists_doubleRationalFanLowerSlope_ne_of_isOpen
    {V : Set doubleRationalFan} (hVopen : IsOpen V) {x : doubleRationalFan}
    (hxV : x ∈ V) {w : ℝ × ℝ} (hw : w ∈ rationalFan)
    (hwx : (-w.1, 1 - w.2) = (x : ℝ × ℝ))
    (hxne : (x : ℝ × ℝ) ≠ (0, 0)) :
    ∃ y ∈ V, doubleRationalFanLowerSlope y ≠ doubleRationalFanLowerSlope x := by
  -- Perturb the rational endpoint before reflecting the spoke.
  obtain ⟨t, ht, q, hq, hwt⟩ :=
    (mem_rationalFan_iff_exists_rat_slice w).mp hw
  have htq : 0 ≤ t * (q : ℝ) := mul_nonneg ht.1 hq.1
  have htne : t ≠ 0 := by
    intro htzero
    apply hxne
    rw [← hwx, hwt, htzero]
    norm_num
  obtain ⟨O, hOopen, hOV⟩ := isOpen_induced_iff.mp hVopen
  let spoke : ℚ → ℝ × ℝ := fun r ↦ (-t * (r : ℝ), t)
  have hspokeContinuous : Continuous spoke := by
    fun_prop
  have hxO : (x : ℝ × ℝ) ∈ O := by
    have hxpre : x ∈ (fun z : doubleRationalFan ↦ (z : ℝ × ℝ)) ⁻¹' O := by
      rwa [hOV]
    exact hxpre
  have hspokeq : spoke q = (x : ℝ × ℝ) := by
    rw [← hwx, hwt]
    apply Prod.ext
    · simp [spoke]
    · simp [spoke]
  have hpreimageNhds : spoke ⁻¹' O ∈ 𝓝 q := by
    apply hspokeContinuous.continuousAt
    rw [hspokeq]
    exact hOopen.mem_nhds hxO
  obtain ⟨q', hq'O, hq'Icc, hq'ne⟩ :=
    existsNearbyRatInUnitInterval q hq (spoke ⁻¹' O) hpreimageNhds
  let basePoint : ℝ × ℝ := (t * (q' : ℝ), 1 - t)
  have hbaseFan : basePoint ∈ rationalFan := by
    rw [mem_rationalFan_iff_exists_rat_slice]
    exact ⟨t, ht, q', hq'Icc, rfl⟩
  have hyDouble : spoke q' ∈ doubleRationalFan := by
    rw [mem_doubleRationalFan_iff]
    refine Or.inr ⟨basePoint, hbaseFan, ?_⟩
    apply Prod.ext
    · simp [basePoint, spoke]
    · simp [basePoint, spoke]
  let y : doubleRationalFan := ⟨spoke q', hyDouble⟩
  have hyV : y ∈ V := by
    rw [← hOV]
    exact hq'O
  refine ⟨y, hyV, ?_⟩
  intro hslope
  have htq' : 0 ≤ t * (q' : ℝ) := mul_nonneg ht.1 hq'Icc.1
  have hslopeX : doubleRationalFanLowerSlope x = -(q : ℝ) := by
    dsimp [doubleRationalFanLowerSlope]
    rw [← hwx, hwt]
    simp only [sub_sub_cancel]
    rw [min_eq_left (neg_nonpos.mpr htq), max_eq_right (neg_nonpos.mpr htq)]
    simp only [add_zero]
    field_simp [htne]
  have hslopeY : doubleRationalFanLowerSlope y = -(q' : ℝ) := by
    dsimp [y, spoke, doubleRationalFanLowerSlope]
    have hneg : -t * (q' : ℝ) = -(t * (q' : ℝ)) := by
      ring
    rw [hneg]
    rw [min_eq_left (neg_nonpos.mpr htq'), max_eq_right (neg_nonpos.mpr htq')]
    simp only [add_zero]
    field_simp [htne]
  apply hq'ne
  have hcast : (q' : ℝ) = (q : ℝ) := by
    have hneg : -(q' : ℝ) = -(q : ℝ) := by
      rw [← hslopeY, ← hslopeX]
      exact hslope
    linarith
  exact Rat.cast_injective hcast

/-- Helper for Exercise 25.5: the double rational fan is path connected. -/
theorem doubleRationalFan_isPathConnected : IsPathConnected doubleRationalFan := by
  -- The reflected fan is a continuous image of the original, and the two
  -- copies meet at the origin.
  let reflect : ℝ × ℝ → ℝ × ℝ := fun z ↦ (-z.1, 1 - z.2)
  have hreflectContinuous : Continuous reflect := by
    fun_prop
  have hreflected : IsPathConnected (reflect '' rationalFan) := by
    exact rationalFan_isPathConnected.image hreflectContinuous
  have horiginImage : ((0, 0) : ℝ × ℝ) ∈ reflect '' rationalFan := by
    refine ⟨rationalFanApex, rationalFanApex_mem, ?_⟩
    norm_num [reflect, rationalFanApex]
  have hinter : (rationalFan ∩ reflect '' rationalFan).Nonempty := by
    exact ⟨(0, 0), rationalFanOrigin_mem, horiginImage⟩
  unfold doubleRationalFan
  exact rationalFan_isPathConnected.union hreflected hinter

/-- Helper for Exercise 25.5: every nonempty connected open subset of the
double rational fan contains both endpoints of its vertical segment. -/
lemma doubleRationalFan_endpoints_mem_of_isOpen_isConnected
    (V : Set doubleRationalFan) (hVopen : IsOpen V) (hVconnected : IsConnected V) :
    doubleRationalFanTopPoint ∈ V ∧ doubleRationalFanBottomPoint ∈ V := by
  -- First force the upper endpoint. If an arbitrary point lies on the
  -- original fan, vary the upper slope. If it lies on the reflected fan,
  -- either the lower endpoint is already present or vary the lower slope;
  -- the lower endpoint then lets us vary the upper slope as well.
  have htopV : doubleRationalFanTopPoint ∈ V := by
    by_contra htop
    have hbottomV : doubleRationalFanBottomPoint ∈ V := by
      by_contra hbottom
      obtain ⟨z, hzV⟩ := hVconnected.nonempty
      rcases (mem_doubleRationalFan_iff z).mp z.property with hzright | ⟨w, hw, hwz⟩
      · have hznetop : (z : ℝ × ℝ) ≠ rationalFanApex := by
          intro hzeq
          apply htop
          have hzpoint : z = doubleRationalFanTopPoint := Subtype.ext hzeq
          rwa [← hzpoint]
        obtain ⟨y, hyV, hslopene⟩ :=
          exists_doubleRationalFanUpperSlope_ne_of_isOpen hVopen hzV hzright hznetop
        have hslopeeq :=
          doubleRationalFanUpperSlope_eq_of_isConnected hVconnected htop hzV hyV
        exact hslopene hslopeeq.symm
      · have hzbottom : (z : ℝ × ℝ) ≠ (0, 0) := by
          intro hzeq
          apply hbottom
          have hzpoint : z = doubleRationalFanBottomPoint := Subtype.ext hzeq
          rwa [← hzpoint]
        obtain ⟨y, hyV, hslopene⟩ :=
          exists_doubleRationalFanLowerSlope_ne_of_isOpen
            hVopen hzV hw hwz hzbottom
        have hslopeeq :=
          doubleRationalFanLowerSlope_eq_of_isConnected hVconnected hbottom hzV hyV
        exact hslopene hslopeeq.symm
    have hbottomne :
        (doubleRationalFanBottomPoint : ℝ × ℝ) ≠ rationalFanApex := by
      norm_num [doubleRationalFanBottomPoint, rationalFanApex]
    obtain ⟨y, hyV, hslopene⟩ :=
      exists_doubleRationalFanUpperSlope_ne_of_isOpen hVopen hbottomV
        rationalFanOrigin_mem hbottomne
    have hslopeeq :=
      doubleRationalFanUpperSlope_eq_of_isConnected hVconnected htop hbottomV hyV
    exact hslopene hslopeeq.symm
  -- With the upper endpoint present, view it as the reflection of the origin;
  -- varying the lower slope forces the lower endpoint.
  have hbottomV : doubleRationalFanBottomPoint ∈ V := by
    by_contra hbottom
    have hreflectOrigin :
        (-((0, 0) : ℝ × ℝ).1, 1 - ((0, 0) : ℝ × ℝ).2) =
          (doubleRationalFanTopPoint : ℝ × ℝ) := by
      norm_num [doubleRationalFanTopPoint, rationalFanApex]
    have htopne : (doubleRationalFanTopPoint : ℝ × ℝ) ≠ (0, 0) := by
      norm_num [doubleRationalFanTopPoint, rationalFanApex]
    obtain ⟨y, hyV, hslopene⟩ :=
      exists_doubleRationalFanLowerSlope_ne_of_isOpen hVopen htopV
        rationalFanOrigin_mem hreflectOrigin htopne
    have hslopeeq :=
      doubleRationalFanLowerSlope_eq_of_isConnected hVconnected hbottom htopV hyV
    exact hslopene hslopeeq.symm
  exact ⟨htopV, hbottomV⟩

/-- Helper for Exercise 25.5: the double rational fan is not locally connected at any
of its points. -/
theorem doubleRationalFan_notLocallyConnectedAt (x : doubleRationalFan) :
    ¬ IsLocallyConnectedAt x := by
  -- Exclude an endpoint different from `x`. Any connected open neighborhood
  -- supplied by local connectedness must nevertheless contain that endpoint.
  intro hlocal
  rw [isLocallyConnectedAt_iff_connected_neighborhoods] at hlocal
  by_cases hxtop : x = doubleRationalFanTopPoint
  · have htopbottom : doubleRationalFanTopPoint ≠ doubleRationalFanBottomPoint := by
      intro h
      have hval := congrArg Subtype.val h
      norm_num [doubleRationalFanTopPoint, doubleRationalFanBottomPoint,
        rationalFanApex] at hval
    have hxbottom : x ≠ doubleRationalFanBottomPoint := by
      rwa [hxtop]
    have hcompl : {doubleRationalFanBottomPoint}ᶜ ∈ 𝓝 x :=
      isOpen_compl_singleton.mem_nhds hxbottom
    obtain ⟨V, hVsub, hVopen, hxV, hVconnected⟩ := hlocal _ hcompl
    have hbottomV :=
      (doubleRationalFan_endpoints_mem_of_isOpen_isConnected V hVopen hVconnected).2
    exact (hVsub hbottomV) (mem_singleton doubleRationalFanBottomPoint)
  · have hcompl : {doubleRationalFanTopPoint}ᶜ ∈ 𝓝 x :=
      isOpen_compl_singleton.mem_nhds hxtop
    obtain ⟨V, hVsub, hVopen, hxV, hVconnected⟩ := hlocal _ hcompl
    have htopV :=
      (doubleRationalFan_endpoints_mem_of_isOpen_isConnected V hVopen hVconnected).1
    exact (hVsub htopV) (mem_singleton doubleRationalFanTopPoint)

/-- Exercise 25.5: The double rational fan supplies a path-connected subset of the plane that
is locally connected at none of its points. -/
theorem exists_pathConnected_nowhereLocallyConnected :
    ∃ S : Set (ℝ × ℝ), IsPathConnected S ∧ ∀ x : S, ¬ IsLocallyConnectedAt x := by
  -- The double rational fan has exactly the two required global properties.
  exact ⟨doubleRationalFan, doubleRationalFan_isPathConnected,
    doubleRationalFan_notLocallyConnectedAt⟩
