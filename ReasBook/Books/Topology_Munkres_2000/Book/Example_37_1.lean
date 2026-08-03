module

public import Topology_Munkres_2000.Book.Definition_26_5.FiniteIntersection
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.StrictConvexBetween
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

public section

open Set

namespace FixedFociEllipse

/-- Support for Example 37.1: the Euclidean plane containing the fixed-foci
elliptical regions. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Support for Example 37.1: projection to the first coordinate of the Euclidean
plane. -/
def firstCoordinate (x : Plane) : ℝ :=
  x 0

/-- Support for Example 37.1: projection to the second coordinate of the Euclidean
plane. -/
def secondCoordinate (x : Plane) : ℝ :=
  x 1

/-- Support for Example 37.1: the first focus `p = (1 / 3, 1 / 3)`. -/
noncomputable def p : Plane :=
  WithLp.toLp 2 ![(1 / 3 : ℝ), (1 / 3 : ℝ)]

/-- Support for Example 37.1: the second focus `q = (1 / 2, 2 / 3)`. -/
noncomputable def q : Plane :=
  WithLp.toLp 2 ![(1 / 2 : ℝ), (2 / 3 : ℝ)]

/-- Support for Example 37.1: the unit square `[0, 1] × [0, 1]` in the Euclidean
plane. -/
def unitSquare : Set Plane :=
  {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}

/-- Support for Example 37.1: the filled ellipse with foci `p`, `q` and
focal-distance bound `c`. -/
def region (c : ℝ) : Set Plane :=
  {x | dist x p + dist x q ≤ c}

/-- Support for Example 37.1: the family of fixed-foci filled ellipses contained in
the unit square. -/
def family : Set (Set Plane) :=
  {D | ∃ c, dist p q < c ∧ region c ⊆ unitSquare ∧ D = region c}

/-- Helper for Example 37.1: membership in a fixed-foci region is exactly its
focal-distance inequality. -/
theorem mem_region (x : Plane) (c : ℝ) :
    x ∈ region c ↔ dist x p + dist x q ≤ c := by
  -- The region is defined by this inequality.
  rfl

/-- Helper for Example 37.1: membership in the ellipse family exposes its distance
parameter and containment in the unit square. -/
theorem mem_family (D : Set Plane) :
    D ∈ family ↔ ∃ c,
      dist p q < c ∧ region c ⊆ unitSquare ∧ D = region c := by
  -- The family is defined by the displayed witnesses and conditions.
  rfl

/-- Helper for Example 37.1: every fixed-foci region is closed. -/
theorem isClosed_region (c : ℝ) : IsClosed (region c) := by
  -- The focal-distance sum is continuous, so its closed sublevel set is closed.
  exact isClosed_le
    ((continuous_id.dist continuous_const).add (continuous_id.dist continuous_const))
    continuous_const

/-- Helper for Example 37.1: every member of the fixed-foci family is closed. -/
theorem isClosed_of_mem_family {D : Set Plane} (hD : D ∈ family) :
    IsClosed D := by
  -- Expose the region representing the family member.
  obtain ⟨c, -, -, rfl⟩ := (mem_family D).mp hD
  exact isClosed_region c

/-- Helper for Example 37.1: the focal-distance minimizers are exactly the points of
the segment joining the two foci. -/
private lemma focalDistance_eq_iff_mem_segment (x : Plane) :
    dist x p + dist x q = dist p q ↔ x ∈ segment ℝ p q := by
  -- Put the triangle equality into the orientation used by `Wbtw`.
  rw [dist_comm x p, dist_add_dist_eq_iff, mem_segment_iff_wbtw]

/-- Helper for Example 37.1: projecting the focal segment onto either coordinate gives
the interval between the corresponding focal coordinates. -/
private lemma coordinate_image_segment (i : Fin 2) :
    (fun x : Plane ↦ x i) '' segment ℝ p q =
      Icc (min (p i) (q i)) (max (p i) (q i)) := by
  -- Affine maps preserve segments, after which real segments are closed intervals.
  change (EuclideanSpace.projₗ i).toAffineMap '' segment ℝ p q = _
  rw [image_segment, segment_eq_Icc']
  rfl

/-- Helper for Example 37.1: the focal segment lies in the open unit square. -/
private lemma segment_subset_openUnitSquare :
    segment ℝ p q ⊆ {x : Plane | ∀ i, x i ∈ Ioo (0 : ℝ) 1} := by
  intro x hx i
  -- Read each coordinate through the projected-segment normal form.
  have hxi : x i ∈ Icc (min (p i) (q i)) (max (p i) (q i)) := by
    rw [← coordinate_image_segment i]
    exact ⟨x, hx, rfl⟩
  fin_cases i
  · norm_num [p, q] at hxi
    constructor
    · linarith [hxi.1]
    · linarith [hxi.2]
  · norm_num [p, q] at hxi
    constructor
    · linarith [hxi.1]
    · linarith [hxi.2]

/-- Helper for Example 37.1: every open neighborhood of the focal segment contains a
fixed-foci region whose parameter is strictly larger than the distance between the foci. -/
private lemma exists_region_subset_of_segment_subset {U : Set Plane} (hU : IsOpen U)
    (hsegment : segment ℝ p q ⊆ U) :
    ∃ c, dist p q < c ∧ region c ⊆ U := by
  -- First compactify the part of the complement on which a thin region could lie.
  have hregionCompact : IsCompact (region (dist p q + 1)) := by
    refine (isCompact_closedBall p (dist p q + 1)).of_isClosed_subset
      (isClosed_region (dist p q + 1)) ?_
    intro x hx
    rw [Metric.mem_closedBall]
    exact (le_add_of_nonneg_right dist_nonneg).trans ((mem_region x _).mp hx)
  have hbadCompact : IsCompact (region (dist p q + 1) \ U) :=
    hregionCompact.diff hU
  have hfocalContinuous : Continuous (fun x : Plane ↦ dist x p + dist x q) :=
    (continuous_id.dist continuous_const).add (continuous_id.dist continuous_const)
  have hstrict : ∀ x ∈ region (dist p q + 1) \ U,
      dist p q < dist x p + dist x q := by
    intro x hx
    have hxNotSegment : x ∉ segment ℝ p q := fun hxSegment ↦ hx.2 (hsegment hxSegment)
    have hne : dist x p + dist x q ≠ dist p q := by
      exact fun heq ↦ hxNotSegment ((focalDistance_eq_iff_mem_segment x).mp heq)
    have htriangle : dist p q ≤ dist x p + dist x q := by
      simpa only [dist_comm p x] using dist_triangle p x q
    exact lt_of_le_of_ne htriangle hne.symm
  obtain ⟨m, hdm, hm⟩ :=
    hbadCompact.exists_forall_le' hfocalContinuous.continuousOn hstrict
  have hdUpper : dist p q < min m (dist p q + 1) := by
    have hdistSucc : dist p q < dist p q + 1 := by
      linarith
    exact lt_min hdm hdistSucc
  obtain ⟨c, hdc, hcUpper⟩ := exists_between hdUpper
  refine ⟨c, hdc, ?_⟩
  intro x hx
  -- Outside `U`, the compact lower bound contradicts the chosen intermediate level.
  by_contra hxU
  have hxLargeRegion : x ∈ region (dist p q + 1) := by
    rw [mem_region] at hx ⊢
    exact hx.trans (hcUpper.le.trans (min_le_right _ _))
  have hxBad : x ∈ region (dist p q + 1) \ U := ⟨hxLargeRegion, hxU⟩
  have hxc : dist x p + dist x q ≤ c := (mem_region x c).mp hx
  have hcm : c < m := hcUpper.trans_le (min_le_left _ _)
  exact (not_lt_of_ge (hm x hxBad)) (hxc.trans_lt hcm)

/-- Helper for Example 37.1: every member of the ellipse family contains the focal
segment. -/
private lemma segment_subset_of_mem_family {D : Set Plane} (hD : D ∈ family) :
    segment ℝ p q ⊆ D := by
  obtain ⟨c, hc, -, rfl⟩ := (mem_family D).mp hD
  intro x hx
  -- On the focal segment the focal-distance sum has its minimum value.
  rw [mem_region, (focalDistance_eq_iff_mem_segment x).mpr hx]
  exact hc.le

/-- Helper for Example 37.1: a coordinate band containing the projected focal segment
contains the closure of that coordinate image for some member of the ellipse family. -/
private lemma exists_family_member_coordinate_closure_subset (i : Fin 2) {a b : ℝ}
    (ha : a < min (p i) (q i)) (hb : max (p i) (q i) < b) :
    ∃ D ∈ family, closure ((fun x : Plane ↦ x i) '' D) ⊆ Icc a b := by
  let U : Set Plane :=
    (fun x : Plane ↦ x i) ⁻¹' Ioo a b ∩
      (fun x : Plane ↦ x 0) ⁻¹' Ioo 0 1 ∩
        (fun x : Plane ↦ x 1) ⁻¹' Ioo 0 1
  have hUOpen : IsOpen U := by
    exact ((isOpen_Ioo.preimage (PiLp.continuous_apply 2 _ i)).inter
      (isOpen_Ioo.preimage (PiLp.continuous_apply 2 _ 0))).inter
        (isOpen_Ioo.preimage (PiLp.continuous_apply 2 _ 1))
  have hsegmentU : segment ℝ p q ⊆ U := by
    intro x hx
    have hcoordinate : x i ∈ Icc (min (p i) (q i)) (max (p i) (q i)) := by
      rw [← coordinate_image_segment i]
      exact ⟨x, hx, rfl⟩
    have hopenSquare := segment_subset_openUnitSquare hx
    exact ⟨⟨⟨ha.trans_le hcoordinate.1, hcoordinate.2.trans_lt hb⟩,
      hopenSquare 0⟩, hopenSquare 1⟩
  obtain ⟨c, hc, hregionU⟩ :=
    exists_region_subset_of_segment_subset hUOpen hsegmentU
  have hregionSquare : region c ⊆ unitSquare := by
    intro x hx
    rw [unitSquare]
    intro j
    have hxU := hregionU hx
    fin_cases j
    · exact ⟨hxU.1.2.1.le, hxU.1.2.2.le⟩
    · exact ⟨hxU.2.1.le, hxU.2.2.le⟩
  have hregionFamily : region c ∈ family := by
    exact (mem_family (region c)).mpr ⟨c, hc, hregionSquare, rfl⟩
  refine ⟨region c, hregionFamily, ?_⟩
  -- The open coordinate containment persists after taking closure as a closed band.
  have himage : (fun x : Plane ↦ x i) '' region c ⊆ Ioo a b := by
    rintro y ⟨x, hx, rfl⟩
    exact (hregionU hx).1.1
  calc
    closure ((fun x : Plane ↦ x i) '' region c) ⊆ closure (Ioo a b) :=
      closure_mono himage
    _ = Icc a b := closure_Ioo (ne_of_lt ((ha.trans_le min_le_max).trans hb))

/-- Helper for Example 37.1: the common coordinate-closure intersection is the interval
between the two focal coordinates. -/
private lemma iInter_closure_coordinate (i : Fin 2) :
    (⋂ D ∈ family, closure ((fun x : Plane ↦ x i) '' D)) =
      Icc (min (p i) (q i)) (max (p i) (q i)) := by
  ext x
  constructor
  · intro hx
    -- Separate a point below the lower endpoint by a smaller closed coordinate band.
    have hlower : min (p i) (q i) ≤ x := by
      by_contra hnot
      have hxLower : x < min (p i) (q i) := lt_of_not_ge hnot
      obtain ⟨a, hxa, ha⟩ := exists_between hxLower
      obtain ⟨D, hD, hclosure⟩ :=
        exists_family_member_coordinate_closure_subset i ha (lt_add_one _)
      have hxClosure : x ∈ closure ((fun y : Plane ↦ y i) '' D) :=
        Set.mem_iInter₂.mp hx D hD
      exact (not_le_of_gt hxa) (hclosure hxClosure).1
    -- The symmetric separating band rules out points above the upper endpoint.
    have hupper : x ≤ max (p i) (q i) := by
      by_contra hnot
      have hUpperX : max (p i) (q i) < x := lt_of_not_ge hnot
      obtain ⟨b, hb, hbx⟩ := exists_between hUpperX
      obtain ⟨D, hD, hclosure⟩ :=
        exists_family_member_coordinate_closure_subset i (sub_one_lt _) hb
      have hxClosure : x ∈ closure ((fun y : Plane ↦ y i) '' D) :=
        Set.mem_iInter₂.mp hx D hD
      exact (not_le_of_gt hbx) (hclosure hxClosure).2
    exact ⟨hlower, hupper⟩
  · intro hx
    -- Lift the coordinate value to the focal segment, which lies in every family member.
    rw [← coordinate_image_segment i] at hx
    obtain ⟨y, hySegment, rfl⟩ := hx
    rw [Set.mem_iInter₂]
    intro D hD
    exact subset_closure ⟨y, segment_subset_of_mem_family hD hySegment, rfl⟩

/-- Helper for Example 37.1: every point outside the focal segment is omitted by some
member of the fixed-foci ellipse family. -/
private lemma exists_family_member_not_mem_of_not_mem_segment {x : Plane}
    (hx : x ∉ segment ℝ p q) : ∃ D ∈ family, x ∉ D := by
  let U : Set Plane :=
    {x}ᶜ ∩ (fun y : Plane ↦ y 0) ⁻¹' Ioo 0 1 ∩
      (fun y : Plane ↦ y 1) ⁻¹' Ioo 0 1
  have hUOpen : IsOpen U := by
    exact (isClosed_singleton.isOpen_compl.inter
      (isOpen_Ioo.preimage (PiLp.continuous_apply 2 _ 0))).inter
        (isOpen_Ioo.preimage (PiLp.continuous_apply 2 _ 1))
  have hsegmentU : segment ℝ p q ⊆ U := by
    intro y hy
    have hyOpenSquare := segment_subset_openUnitSquare hy
    have hyNe : y ≠ x := by
      intro hyx
      exact hx (hyx ▸ hy)
    exact ⟨⟨hyNe, hyOpenSquare 0⟩, hyOpenSquare 1⟩
  obtain ⟨c, hc, hregionU⟩ :=
    exists_region_subset_of_segment_subset hUOpen hsegmentU
  have hregionSquare : region c ⊆ unitSquare := by
    intro y hy
    rw [unitSquare]
    intro j
    have hyU := hregionU hy
    fin_cases j
    · exact ⟨hyU.1.2.1.le, hyU.1.2.2.le⟩
    · exact ⟨hyU.2.1.le, hyU.2.2.le⟩
  have hregionFamily : region c ∈ family := by
    exact (mem_family (region c)).mpr ⟨c, hc, hregionSquare, rfl⟩
  refine ⟨region c, hregionFamily, ?_⟩
  -- Membership would put `x` in the complement of its own singleton.
  intro hxRegion
  exact (hregionU hxRegion).1.1 rfl

/-- Helper for Example 37.1: the point with both coordinates `1 / 2` is not on the
segment joining `p` and `q`. -/
private lemma halfPoint_not_mem_segment :
    WithLp.toLp 2 ![(1 / 2 : ℝ), (1 / 2 : ℝ)] ∉ segment ℝ p q := by
  intro hx
  -- A segment point has one common affine parameter in both coordinates.
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, -, ht⟩ := hx
  have hfirst := congrArg (fun x : Plane ↦ x 0) ht
  have hsecond := congrArg (fun x : Plane ↦ x 1) ht
  norm_num [AffineMap.lineMap_apply, p, q] at hfirst hsecond
  linarith

/-- Example 37.1 (1). The family of fixed-foci elliptical regions has the finite
intersection property. -/
theorem finiteIntersectionProperty : family.FiniteIntersectionProperty := by
  rw [Set.FiniteIntersectionProperty.finset_iff]
  intro s hs
  refine ⟨p, ?_⟩
  rw [Set.mem_iInter₂]
  intro D hD
  -- The common focus `p` belongs to the focal segment and hence to every chosen region.
  exact segment_subset_of_mem_family (hs D hD) (left_mem_segment ℝ p q)

/-- Companion to Example 37.1 (2). The common intersection of the closures of the first-coordinate
images is `[1 / 3, 1 / 2]`. -/
theorem iInter_closure_firstCoordinate :
    (⋂ D ∈ family, closure (firstCoordinate '' D)) = Icc (1 / 3 : ℝ) (1 / 2 : ℝ) := by
  -- Specialize the coordinate-indexed intersection formula to the first coordinate.
  change (⋂ D ∈ family, closure ((fun x : Plane ↦ x 0) '' D)) = _
  rw [iInter_closure_coordinate]
  norm_num [p, q]

/-- Companion to Example 37.1 (3). The common intersection of the closures of the second-coordinate
images is `[1 / 3, 2 / 3]`. -/
theorem iInter_closure_secondCoordinate :
    (⋂ D ∈ family, closure (secondCoordinate '' D)) = Icc (1 / 3 : ℝ) (2 / 3 : ℝ) := by
  -- Specialize the same formula to the second coordinate.
  change (⋂ D ∈ family, closure ((fun x : Plane ↦ x 1) '' D)) = _
  rw [iInter_closure_coordinate]
  norm_num [p, q]

/-- Companion to Example 37.1 (4). The selected point `(1 / 2, 1 / 2)` does not belong to every
member of the elliptical family. -/
theorem halfPoint_not_mem_iInter :
    WithLp.toLp 2 ![(1 / 2 : ℝ), (1 / 2 : ℝ)] ∉
      ⋂ D ∈ family, D := by
  obtain ⟨D, hD, hhalfD⟩ :=
    exists_family_member_not_mem_of_not_mem_segment halfPoint_not_mem_segment
  -- The selected family member witnesses failure of membership in the total intersection.
  intro hhalf
  exact hhalfD (Set.mem_iInter₂.mp hhalf D hD)

end FixedFociEllipse
