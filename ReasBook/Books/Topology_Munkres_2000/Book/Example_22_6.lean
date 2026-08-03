module

public import Topology_Munkres_2000.Book.Corollary_22_3
public import Topology_Munkres_2000.Book.Definition_22_2.Saturation
public import Mathlib.Data.PNat.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Real.Lemmas

public section

namespace SegmentFan

/-- The horizontal line segment at height `n`. -/
def horizontalSegment (n : ℕ+) : Set (ℝ × ℝ) :=
  {point | point.1 ∈ Set.Icc (0 : ℝ) 1 ∧ point.2 = (n : ℝ)}

/-- The line segment from the origin to `(1, 1 / n)`. -/
def fanSegment (n : ℕ+) : Set (ℝ × ℝ) :=
  {point | point.1 ∈ Set.Icc (0 : ℝ) 1 ∧ point.2 = point.1 / (n : ℝ)}

/-- The union of the horizontal segments indexed by positive integers. -/
def horizontalSegments : Set (ℝ × ℝ) :=
  ⋃ n : ℕ+, horizontalSegment n

/-- The union of the fan segments indexed by positive integers. -/
def fanSegments : Set (ℝ × ℝ) :=
  ⋃ n : ℕ+, fanSegment n

/-- The subspace formed by the horizontal segments. -/
abbrev HorizontalSegments := horizontalSegments

/-- The subspace formed by the fan segments. -/
abbrev FanSegments := fanSegments

/-- The coordinate formula defining `segmentFanMap` lands in `fanSegments`. -/
theorem segmentFanMap_mem (point : HorizontalSegments) :
    (point.1.1, point.1.1 / point.1.2) ∈ fanSegments := by
  -- Keep the horizontal-segment index and reuse it for the corresponding fan segment.
  rcases Set.mem_iUnion.mp point.property with ⟨n, hn⟩
  refine Set.mem_iUnion.mpr ⟨n, ?_⟩
  exact ⟨hn.1, by rw [hn.2]⟩

/-- The map sending `(x, n)` on a horizontal segment to `(x, x / n)` on the
corresponding fan segment. -/
noncomputable def segmentFanMap (point : HorizontalSegments) : FanSegments :=
  ⟨(point.1.1, point.1.1 / point.1.2), segmentFanMap_mem point⟩

/-- Evaluation of `segmentFanMap` on an explicitly parameterized horizontal segment. -/
theorem segmentFanMap_apply (x : Set.Icc (0 : ℝ) 1) (n : ℕ+)
    (hpoint : ((x : ℝ), (n : ℝ)) ∈ horizontalSegments) :
    (segmentFanMap ⟨((x : ℝ), (n : ℝ)), hpoint⟩ : ℝ × ℝ) =
      ((x : ℝ), (x : ℝ) / (n : ℝ)) := by
  -- The defining coordinate formula is already in the required normal form.
  rfl

/-- The point `(1 / n, n)` in the horizontal-segment space. -/
theorem closedSequencePoint_mem (n : ℕ+) :
    (((n : ℝ)⁻¹, (n : ℝ)) : ℝ × ℝ) ∈ horizontalSegments := by
  -- Insert the point into the horizontal segment indexed by `n`.
  refine Set.mem_iUnion.mpr ⟨n, ?_⟩
  constructor
  · constructor
    · positivity
    · exact inv_le_one_of_one_le₀ (by exact_mod_cast n.property)
  · rfl

/-- The `n`th point `(1 / n, n)` of the closed saturated sequence. -/
noncomputable def closedSequencePoint (n : ℕ+) : HorizontalSegments :=
  ⟨((n : ℝ)⁻¹, (n : ℝ)), closedSequencePoint_mem n⟩

/-- The set of points `(1 / n, n)` in `HorizontalSegments`. -/
def closedSequence : Set HorizontalSegments :=
  Set.range closedSequencePoint

/-- The image of `closedSequencePoint n` is `(1 / n, 1 / n²)`. -/
theorem segmentFanMap_closedSequencePoint (n : ℕ+) :
    (segmentFanMap (closedSequencePoint n) : ℝ × ℝ) =
      ((n : ℝ)⁻¹, ((n : ℝ) ^ 2)⁻¹) := by
  -- Normalize the second coordinate using the inverse-of-a-product identity.
  unfold closedSequencePoint
  ext
  · rfl
  · simp [segmentFanMap, div_eq_mul_inv, pow_two]

/-- Helper for Example 22.6: distinct horizontal segments in `HorizontalSegments` are disjoint. -/
theorem horizontalSegments_pairwiseDisjoint :
    Pairwise fun m n : ℕ+ ↦ Disjoint (horizontalSegment m) (horizontalSegment n) := by
  intro m n hmn
  -- A point in both segments would force their distinct heights to coincide.
  rw [Set.disjoint_left]
  intro point hm hn
  have hcast : (m : ℝ) = (n : ℝ) := hm.2.symm.trans hn.2
  have hval : (m : ℕ) = n := by exact_mod_cast hcast
  exact hmn (Subtype.ext hval)

/-- Helper for Example 22.6: every fan segment contains the common endpoint `(0, 0)`. -/
theorem origin_mem_fanSegment (n : ℕ+) :
    ((0, 0) : ℝ × ℝ) ∈ fanSegment n := by
  -- Both the interval condition and the fan equation hold at the origin.
  exact ⟨by norm_num, by simp⟩

/-- Helper for Example 22.6: the map `segmentFanMap` is surjective. -/
theorem segmentFanMap_surjective :
    Function.Surjective segmentFanMap := by
  intro point
  -- Choose the horizontal point with the same first coordinate and segment index.
  rcases Set.mem_iUnion.mp point.property with ⟨n, hn⟩
  have hmem : (point.1.1, (n : ℝ)) ∈ horizontalSegments :=
    Set.mem_iUnion.mpr ⟨n, hn.1, rfl⟩
  refine ⟨⟨(point.1.1, (n : ℝ)), hmem⟩, ?_⟩
  apply Subtype.ext
  exact Prod.ext rfl hn.2.symm

/-- Helper for Example 22.6: every horizontal segment has nonzero height. -/
lemma horizontalHeight_ne_zero (point : HorizontalSegments) : point.1.2 ≠ 0 := by
  -- Read the positive integer height from the indexed-union membership witness.
  rcases Set.mem_iUnion.mp point.property with ⟨n, hn⟩
  rw [hn.2]
  positivity

/-- Helper for Example 22.6: the map `segmentFanMap` is continuous. -/
theorem segmentFanMap_continuous :
    Continuous segmentFanMap := by
  -- Continuity follows from the coordinate formula and nonvanishing height.
  apply Continuous.subtype_mk
  exact (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_fst.comp continuous_subtype_val).div
      (continuous_snd.comp continuous_subtype_val) horizontalHeight_ne_zero)

/-- Helper for Example 22.6: the only nontrivial fiber of `segmentFanMap` identifies all
points whose first coordinate is zero. -/
theorem segmentFanMap_eq_iff (point point' : HorizontalSegments) :
    segmentFanMap point = segmentFanMap point' ↔
      point = point' ∨ (point.1.1 = 0 ∧ point'.1.1 = 0) := by
  constructor
  · intro heq
    have hcoordinates := congrArg (fun z : FanSegments ↦ (z : ℝ × ℝ)) heq
    have hfirst : point.1.1 = point'.1.1 := by
      simpa [segmentFanMap] using congrArg Prod.fst hcoordinates
    by_cases hzero : point.1.1 = 0
    · exact Or.inr ⟨hzero, hfirst.symm.trans hzero⟩
    · left
      apply Subtype.ext
      apply Prod.ext hfirst
      have hsecond : point.1.1 / point.1.2 = point'.1.1 / point'.1.2 :=
        by simpa [segmentFanMap] using congrArg Prod.snd hcoordinates
      rw [← hfirst] at hsecond
      have hmul := (div_eq_div_iff (horizontalHeight_ne_zero point)
        (horizontalHeight_ne_zero point')).mp hsecond
      exact (mul_left_cancel₀ hzero hmul.symm)
  · rintro (heq | ⟨hzero, hzero'⟩)
    · exact congrArg segmentFanMap heq
    · apply Subtype.ext
      apply Prod.ext
      · exact hzero.trans hzero'.symm
      · simp [segmentFanMap, hzero, hzero']

/-- Helper for Example 22.6: the equivalence induced from the fiber quotient is bijective. -/
theorem quotientEquivFan_bijective :
    Function.Bijective
      (Setoid.quotientKerEquivOfSurjective segmentFanMap segmentFanMap_surjective) := by
  -- The induced map is an equivalence, hence bijective.
  exact Equiv.bijective _

/-- Helper for Example 22.6: the equivalence induced from the fiber quotient is continuous. -/
theorem quotientEquivFan_continuous :
    Continuous
      (Setoid.quotientKerEquivOfSurjective segmentFanMap segmentFanMap_surjective) := by
  -- Apply the general continuity theorem for a surjective continuous map.
  exact Setoid.quotientKerEquivOfSurjective_continuous _ _ segmentFanMap_continuous

/-- Helper for Example 22.6: membership in the closed sequence is equivalent to
the coordinate equation `x * y = 1`. -/
lemma mem_closedSequence_iff_mul_coordinates_eq_one (point : HorizontalSegments) :
    point ∈ closedSequence ↔ point.1.1 * point.1.2 = 1 := by
  constructor
  · rintro ⟨n, rfl⟩
    -- Each chosen point satisfies the defining reciprocal equation.
    simp [closedSequencePoint, PNat.ne_zero]
  · intro hproduct
    -- The horizontal height selects the unique reciprocal point in the range.
    rcases Set.mem_iUnion.mp point.property with ⟨n, hn⟩
    rw [hn.2] at hproduct
    have hfirst : point.1.1 = (n : ℝ)⁻¹ := eq_inv_of_mul_eq_one_left hproduct
    refine ⟨n, ?_⟩
    unfold closedSequencePoint
    apply Subtype.ext
    apply Prod.ext
    · exact hfirst.symm
    · exact hn.2.symm

/-- Helper for Example 22.6: the sequence set `closedSequence` is closed in
`HorizontalSegments`. -/
theorem closedSequence_isClosed :
    IsClosed closedSequence := by
  -- Identify the sequence with a closed level set of coordinate multiplication.
  have hlevel : closedSequence =
      {point : HorizontalSegments | point.1.1 * point.1.2 = 1} := by
    ext point
    exact mem_closedSequence_iff_mul_coordinates_eq_one point
  rw [hlevel]
  exact isClosed_eq (continuous_subtype_val.fst.mul continuous_subtype_val.snd) continuous_const

/-- Helper for Example 22.6: every point of the closed sequence has nonzero first
coordinate. -/
lemma closedSequence_first_ne_zero {point : HorizontalSegments}
    (hpoint : point ∈ closedSequence) : point.1.1 ≠ 0 := by
  -- A zero first coordinate contradicts the intrinsic product equation.
  intro hzero
  have hproduct := (mem_closedSequence_iff_mul_coordinates_eq_one point).mp hpoint
  rw [hzero, zero_mul] at hproduct
  exact zero_ne_one hproduct

/-- Helper for Example 22.6: the sequence set is saturated with respect to
`segmentFanMap`. -/
theorem closedSequence_saturated :
    Set.IsSaturated segmentFanMap closedSequence := by
  rw [Set.isSaturated_iff_mem_of_eq]
  intro point point' hpoint heq
  -- The zero-fiber alternative is impossible for a sequence point.
  rcases (segmentFanMap_eq_iff point' point).mp heq with hsame | hzero
  · rwa [hsame]
  · exact False.elim (closedSequence_first_ne_zero hpoint hzero.2)

/-- Helper for Example 22.6: the origin belongs to the union of fan segments. -/
lemma origin_mem_fanSegments : ((0, 0) : ℝ × ℝ) ∈ fanSegments := by
  -- Any fan segment supplies the required indexed-union witness.
  exact Set.mem_iUnion.mpr ⟨1, origin_mem_fanSegment 1⟩

/-- The common origin of all fan segments. -/
noncomputable def fanOrigin : FanSegments :=
  ⟨(0, 0), origin_mem_fanSegments⟩

/-- Helper for Example 22.6: the images of the reciprocal sequence converge to
the common fan origin. -/
lemma closedSequenceImage_tendsto_origin :
    Filter.Tendsto (fun n : ℕ+ ↦ segmentFanMap (closedSequencePoint n))
      Filter.atTop (nhds fanOrigin) := by
  -- First prove convergence of the inverse casts in the ambient real line.
  have hinv : Filter.Tendsto (fun n : ℕ+ ↦ (n : ℝ)⁻¹)
      Filter.atTop (nhds 0) := by
    exact tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop)
  -- Combine the two coordinate limits, then transport once into the subtype.
  rw [tendsto_subtype_rng]
  simpa only [segmentFanMap_closedSequencePoint, fanOrigin, pow_two, mul_inv_rev,
    mul_comm, zero_mul, nhds_prod_eq]
    using hinv.prodMk (hinv.mul hinv)

/-- Helper for Example 22.6: the common fan origin is not an image point of the
closed reciprocal sequence. -/
lemma fanOrigin_not_mem_image_closedSequence :
    fanOrigin ∉ segmentFanMap '' closedSequence := by
  rintro ⟨point, ⟨n, rfl⟩, heq⟩
  -- Equality with the origin would make a nonzero reciprocal first coordinate vanish.
  have hfirst := congrArg (fun z : FanSegments ↦ (z : ℝ × ℝ).1) heq
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast PNat.ne_zero n
  simp [fanOrigin, segmentFanMap_closedSequencePoint, hn] at hfirst

/-- Helper for Example 22.6: the image of the closed saturated sequence is not closed in
`FanSegments`. -/
theorem image_closedSequence_not_isClosed :
    ¬ IsClosed (segmentFanMap '' closedSequence) := by
  intro hclosed
  -- Closedness would force the limit of image points to remain in the image.
  apply fanOrigin_not_mem_image_closedSequence
  exact hclosed.mem_of_tendsto closedSequenceImage_tendsto_origin
    (Filter.Eventually.of_forall fun n ↦ ⟨closedSequencePoint n, ⟨n, rfl⟩, rfl⟩)

/-- Helper for Example 22.6: the continuous surjection `segmentFanMap` is not a quotient map. -/
theorem segmentFanMap_not_isQuotientMap :
    ¬ Topology.IsQuotientMap segmentFanMap := by
  intro hquotient
  -- A quotient map reflects closedness from the saturated preimage to the image.
  have himageClosed : IsClosed (segmentFanMap '' closedSequence) :=
    hquotient.isCoinducing.isClosed_preimage.mp (by
      rw [Set.isSaturated_iff_preimage_image.mp closedSequence_saturated]
      exact closedSequence_isClosed)
  exact image_closedSequence_not_isClosed himageClosed

/-- Example 22.6: The induced continuous equivalence from the fiber quotient
to `FanSegments` is not a homeomorphism. -/
theorem quotientEquivFan_not_isHomeomorph :
    ¬ IsHomeomorph
      (Setoid.quotientKerEquivOfSurjective segmentFanMap segmentFanMap_surjective) := by
  -- The induced equivalence is a homeomorphism exactly when the original map is quotient.
  rw [Setoid.quotientKerEquivOfSurjective_isHomeomorph_iff]
  exact segmentFanMap_not_isQuotientMap


end SegmentFan

end
