module

public import Topology_Munkres_2000.Book.Example_25_2
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Topology.Subpath

public section

open Set

namespace TopologistsSineCurve

/-- The points of the vertical part whose second coordinate is rational. -/
def rationalVerticalPoints : Set Space :=
  verticalPart ∩ (fun p : Space ↦ p.1.2) ⁻¹' Set.range Rat.cast

/-- Membership in `rationalVerticalPoints` means lying in the vertical part at rational height. -/
theorem mem_rationalVerticalPoints_iff (p : Space) :
    p ∈ rationalVerticalPoints ↔
      p ∈ verticalPart ∧ p.1.2 ∈ Set.range Rat.cast := Iff.rfl

/-- The topologist's sine curve with its rational-height vertical points deleted. -/
abbrev RationalVerticalDeletion := rationalVerticalPointsᶜ

namespace RationalVerticalDeletion

/-- Helper for Example 25.4: coercing the oscillating part to the plane recovers `curve`. -/
private lemma image_val_curvePart : Subtype.val '' curvePart = curve := by
  -- The forward inclusion is definitional; the reverse inclusion uses `curve ⊆ closure curve`.
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (mem_curvePart_iff q).mp hq
  · intro hp
    have hpCarrier : p ∈ carrier := subset_closure hp
    let q : Space := ⟨p, hpCarrier⟩
    have hqCurve : q ∈ curvePart := (mem_curvePart_iff q).mpr hp
    have hqVal : q.1 = p := rfl
    exact ⟨q, hqCurve, hqVal⟩

/-- Helper for Example 25.4: the oscillating part is connected in the sine-curve space. -/
private lemma curvePart_isConnected : IsConnected curvePart := by
  -- Transport both nonemptiness and preconnectedness through the subtype coercion.
  constructor
  · obtain ⟨p, hp⟩ := curve_isConnected.nonempty
    have hpCarrier : p ∈ carrier := subset_closure hp
    let q : Space := ⟨p, hpCarrier⟩
    have hqCurve : q ∈ curvePart := (mem_curvePart_iff q).mpr hp
    exact ⟨q, hqCurve⟩
  · rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, image_val_curvePart]
    exact curve_isConnected.isPreconnected

/-- Helper for Example 25.4: the oscillating part is dense in the sine-curve space. -/
private lemma curvePart_dense : Dense curvePart := by
  -- Subtype closure reduces to the defining ambient closure of `curve`.
  rw [dense_iff_closure_eq]
  ext p
  rw [closure_subtype, image_val_curvePart]
  exact iff_of_true p.property (mem_univ p)

/-- Helper for Example 25.4: every oscillating-graph point survives the rational deletion. -/
private lemma curvePart_subset_deletion : curvePart ⊆ rationalVerticalPointsᶜ := by
  -- Graph points have positive first coordinate; deleted points have first coordinate zero.
  intro p hpCurve hpRational
  have hpGraph : p.1 ∈ curve := (mem_curvePart_iff p).mp hpCurve
  have hpVertical : p ∈ verticalPart :=
    (mem_rationalVerticalPoints_iff p).mp hpRational |>.1
  have hpZero : p.1.1 = 0 :=
    (mem_vertical_iff p.1).mp ((mem_verticalPart_iff p).mp hpVertical) |>.1
  rcases hpGraph with ⟨x, hx, hxp⟩
  rw [← hxp] at hpZero
  exact (ne_of_gt hx.1) hpZero

/-- Example 25.4 (1): Deleting rational-height vertical points leaves a connected space. -/
instance instConnectedSpace : ConnectedSpace RationalVerticalDeletion := by
  -- The dense connected graph lies in the deletion, so the bark-and-tree theorem applies.
  apply Subtype.connectedSpace
  apply curvePart_isConnected.subset_closure curvePart_subset_deletion
  intro p hp
  rw [curvePart_dense.closure_eq]
  exact mem_univ p

/-- Helper for Example 25.4: the allowed vertical heights are the irrational points of `[-1, 1]`. -/
private def IrrationalVerticalHeight : Set ℝ :=
  Icc (-1 : ℝ) 1 \ Set.range Rat.cast

/-- Helper for Example 25.4: there are uncountably many allowed vertical heights. -/
private instance instUncountableIrrationalVerticalHeight :
    Uncountable IrrationalVerticalHeight := by
  -- Countability of the difference and of the rationals would make the whole interval countable.
  constructor
  intro hcountable
  have hinterval : (Icc (-1 : ℝ) 1).Countable :=
    Set.Countable.of_sdiff hcountable (Set.countable_range Rat.cast)
  have hcollapsed : (1 : ℝ) ≤ -1 := (Cardinal.Real.Icc_countable_iff).mp hinterval
  norm_num at hcollapsed

/-- Helper for Example 25.4: an allowed height gives a point of the sine-curve carrier. -/
private lemma zeroHeightPoint_mem_carrier (y : IrrationalVerticalHeight) :
    (0, (y : ℝ)) ∈ carrier := by
  -- The point belongs to the limiting vertical interval, hence to the carrier union.
  rw [carrier_eq_curve_union_vertical]
  right
  rw [mem_vertical_iff]
  have hzero : (0 : ℝ) = 0 := rfl
  exact ⟨hzero, y.property.1⟩

/-- Helper for Example 25.4: the carrier point at an allowed height. -/
private def zeroHeightPoint (y : IrrationalVerticalHeight) : Space :=
  ⟨(0, (y : ℝ)), zeroHeightPoint_mem_carrier y⟩

/-- Helper for Example 25.4: an allowed-height carrier point is not rational vertical. -/
private lemma zeroHeightPoint_mem_deletion (y : IrrationalVerticalHeight) :
    zeroHeightPoint y ∈ rationalVerticalPointsᶜ := by
  -- Rational membership would contradict the defining exclusion on the height.
  intro hyRational
  have hyRange := (mem_rationalVerticalPoints_iff (zeroHeightPoint y)).mp hyRational |>.2
  exact y.property.2 hyRange

/-- Helper for Example 25.4: the deleted-space point at an allowed vertical height. -/
private def verticalPointOfIrrationalHeight
    (y : IrrationalVerticalHeight) : RationalVerticalDeletion :=
  ⟨zeroHeightPoint y, zeroHeightPoint_mem_deletion y⟩

/-- Helper for Example 25.4: an allowed-height point lies in the vertical part. -/
private lemma verticalPointOfIrrationalHeight_mem_verticalPart
    (y : IrrationalVerticalHeight) :
    (verticalPointOfIrrationalHeight y : Space) ∈ verticalPart := by
  -- Unfold only the point interface and use coordinatewise vertical membership.
  rw [mem_verticalPart_iff, mem_vertical_iff]
  have hzero : (0 : ℝ) = 0 := rfl
  exact ⟨hzero, y.property.1⟩

/-- Helper for Example 25.4: the second coordinate of the allowed-height point is its height. -/
private lemma verticalPointOfIrrationalHeight_second
    (y : IrrationalVerticalHeight) :
    (verticalPointOfIrrationalHeight y : Space).1.2 = (y : ℝ) := by
  -- The coordinate is exposed directly by the point construction.
  rfl

/-- Helper for Example 25.4: a deleted-space path starting vertically stays in the vertical part. -/
private lemma path_mem_verticalPart_of_source_mem {p q : RationalVerticalDeletion}
    (path : Path p q) (hp : (p : Space) ∈ verticalPart) (t : unitInterval) :
    (path t : Space) ∈ verticalPart := by
  -- Map the path into `Space` and classify its path-connected range using Example 25.2.
  let ambientPath : Path (p : Space) (q : Space) := path.map continuous_subtype_val
  have hsource : (p : Space) = ambientPath 0 := ambientPath.source.symm
  have htarget : ambientPath t = ambientPath t := Eq.refl _
  let pathPrefix : Path (p : Space) (ambientPath t) :=
    (ambientPath.subpath 0 t).cast hsource htarget
  have htJoined : Joined (p : Space) (ambientPath t) := ⟨pathPrefix⟩
  have htComponent : ambientPath t ∈ pathComponent (p : Space) :=
    mem_pathComponent_iff.mpr htJoined
  rw [pathComponent_vertical (p : Space) hp] at htComponent
  exact htComponent

/-- Helper for Example 25.4: a deleted-space path starting vertically has equal endpoint heights. -/
private lemma path_second_eq_of_source_mem_vertical {p q : RationalVerticalDeletion}
    (path : Path p q) (hp : (p : Space) ∈ verticalPart) :
    (p : Space).1.2 = (q : Space).1.2 := by
  -- A change of height would force the path through a deleted rational-height point.
  by_contra hpq
  let height : unitInterval → ℝ := fun t ↦ (path t : Space).1.2
  have height_continuous : Continuous height :=
    continuous_snd.comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp path.continuous))
  have height_source : height 0 = (p : Space).1.2 := by
    dsimp [height]
    rw [path.source]
  have height_target : height 1 = (q : Space).1.2 := by
    dsimp [height]
    rw [path.target]
  obtain ⟨r, hr⟩ := exists_rat_mem_uIoo hpq
  have hrClosed : (r : ℝ) ∈ uIcc (height 0) (height 1) := by
    rw [height_source, height_target]
    exact uIoo_subset_uIcc_self hr
  obtain ⟨t, ht, hheight⟩ :=
    intermediate_value_uIcc height_continuous.continuousOn hrClosed
  have htVertical : (path t : Space) ∈ verticalPart :=
    path_mem_verticalPart_of_source_mem path hp t
  have htRational : (path t : Space) ∈ rationalVerticalPoints := by
    rw [mem_rationalVerticalPoints_iff]
    refine ⟨htVertical, ?_⟩
    exact ⟨r, hheight.symm⟩
  exact (path t).property htRational

/-- Helper for Example 25.4: joined vertical deleted points have equal second coordinates. -/
private lemma joined_verticalPoints_second_eq {p q : RationalVerticalDeletion}
    (hp : (p : Space) ∈ verticalPart) (hpq : Joined p q) :
    (p : Space).1.2 = (q : Space).1.2 := by
  -- Choose the joining path and apply the endpoint-height obstruction.
  exact path_second_eq_of_source_mem_vertical hpq.somePath hp

/-- Helper for Example 25.4: send each allowed height to its path-component class. -/
private def verticalComponentMap
    (y : IrrationalVerticalHeight) : ZerothHomotopy RationalVerticalDeletion :=
  ZerothHomotopy.mk (verticalPointOfIrrationalHeight y)

/-- Helper for Example 25.4: distinct allowed heights give distinct path-component classes. -/
private lemma verticalComponentMap_injective : Function.Injective verticalComponentMap := by
  -- Quotient equality supplies a path; constancy of its vertical coordinate recovers the height.
  intro y z hyz
  have hjoined : Joined (verticalPointOfIrrationalHeight y)
      (verticalPointOfIrrationalHeight z) := Quotient.exact hyz
  have hsecond := joined_verticalPoints_second_eq
    (verticalPointOfIrrationalHeight_mem_verticalPart y) hjoined
  apply Subtype.ext
  simpa only [verticalPointOfIrrationalHeight_second] using hsecond

/-- Companion to Example 25.4: The resulting space has uncountably many path components. -/
instance instUncountableZerothHomotopy :
    Uncountable (ZerothHomotopy RationalVerticalDeletion) := by
  -- The injective component map transfers uncountability from the allowed heights.
  exact verticalComponentMap_injective.uncountable

end RationalVerticalDeletion

end TopologistsSineCurve
