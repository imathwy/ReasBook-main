module

public import Topology_Munkres_2000.Book.Corollary_55_4
public import Topology_Munkres_2000.Book.Definition_55_2.VectorField
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.ContinuousMap.Algebra

import all Topology_Munkres_2000.Book.Definition_21_3.ClosedUnitDisk
import all Topology_Munkres_2000.Book.Exercise_35_4.RadialRetraction

public section

namespace DiskVectorField

/-- Helper for Theorem 55.5: a point of `EuclideanPlane.unitCircle` lies in the closed unit
disk after forgetting its two nested subtype structures. -/
private lemma unitCirclePointMemClosedUnitDisk (x : EuclideanPlane.unitCircle) :
    ((x : EuclideanPlane.punctured) : EuclideanPlane) ∈ B² := by
  -- The circle equation gives the defining weak norm inequality for the closed disk.
  simpa only [Metric.mem_closedBall, dist_zero_right] using x.property.le

/-- Helper for Theorem 55.5: forgetting the circle and punctured-plane subtypes continuously
maps the unit circle into the closed unit disk. -/
private lemma continuous_unitCircleToClosedUnitDisk :
    Continuous (fun x : EuclideanPlane.unitCircle ↦
      (⟨((x : EuclideanPlane.punctured) : EuclideanPlane),
        unitCirclePointMemClosedUnitDisk x⟩ : B²)) := by
  -- Compose the two subtype projections, then lift through the disk subtype.
  exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- Helper for Theorem 55.5: the canonical continuous map from the nested unit circle into
the closed unit disk. -/
private def unitCircleToClosedUnitDisk : C(EuclideanPlane.unitCircle, B²) :=
  ⟨fun x ↦ ⟨((x : EuclideanPlane.punctured) : EuclideanPlane),
    unitCirclePointMemClosedUnitDisk x⟩, continuous_unitCircleToClosedUnitDisk⟩

/-- Helper for Theorem 55.5: the circle-to-disk map preserves the underlying Euclidean vector. -/
private lemma unitCircleToClosedUnitDisk_apply (x : EuclideanPlane.unitCircle) :
    ((unitCircleToClosedUnitDisk x : B²) : EuclideanPlane) =
      ((x : EuclideanPlane.punctured) : EuclideanPlane) := by
  -- Both sides are the same ambient vector by construction.
  rfl

/-- Helper for Theorem 55.5: every image of the circle-to-disk map is a boundary point. -/
private lemma unitCircleToClosedUnitDisk_isBoundary (x : EuclideanPlane.unitCircle) :
    ClosedUnitDisk.IsBoundary (unitCircleToClosedUnitDisk x) := by
  -- Reduce the disk boundary predicate to the unit-circle norm equation.
  exact x.property

/-- Helper for Theorem 55.5: an affine segment between two nonzero vectors cannot meet zero
when its first endpoint avoids the negative ray through its second endpoint. -/
private lemma positiveSegmentNeZeroOfAvoidsNegativeRay
    {E : Type*} [AddCommGroup E] [Module ℝ E] {a b : E}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (havoid : ∀ r : ℝ, 0 < r → a ≠ -(r • b)) (t : unitInterval) :
    (1 - (t : ℝ)) • a + (t : ℝ) • b ≠ 0 := by
  -- If the segment vanished, neither endpoint coefficient could vanish.
  intro hzero
  have ht_ne_zero : (t : ℝ) ≠ 0 := by
    intro ht
    apply ha
    simpa only [ht, sub_zero, one_smul, zero_smul, add_zero] using hzero
  have ht_ne_one : (t : ℝ) ≠ 1 := by
    intro ht
    apply hb
    simpa only [ht, sub_self, zero_smul, one_smul, zero_add] using hzero
  have ht_pos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht_ne_zero)
  have hone_sub_pos : 0 < 1 - (t : ℝ) := sub_pos.mpr (lt_of_le_of_ne t.property.2 ht_ne_one)
  have hone_sub_ne : 1 - (t : ℝ) ≠ 0 := ne_of_gt hone_sub_pos
  -- Solving the vanishing equation expresses `a` on the forbidden negative ray.
  have hrelation : (1 - (t : ℝ)) • a = -((t : ℝ) • b) :=
    eq_neg_of_add_eq_zero_left hzero
  let r : ℝ := (1 - (t : ℝ))⁻¹ * (t : ℝ)
  have hr : 0 < r := mul_pos (inv_pos.mpr hone_sub_pos) ht_pos
  apply havoid r hr
  calc
    a = (1 - (t : ℝ))⁻¹ • ((1 - (t : ℝ)) • a) := by
      rw [smul_smul, inv_mul_cancel₀ hone_sub_ne, one_smul]
    _ = (1 - (t : ℝ))⁻¹ • (-((t : ℝ) • b)) := congrArg _ hrelation
    _ = -(r • b) := by
      simp only [smul_neg, smul_smul, r]

/-- Helper for Theorem 55.5: the ambient affine interpolation between the boundary restriction
of a vector field and the unit-circle inclusion. -/
private def boundaryStraightLineAmbientValue (v : DiskVectorField)
    (p : unitInterval × EuclideanPlane.unitCircle) : EuclideanPlane :=
  (1 - (p.1 : ℝ)) • v (unitCircleToClosedUnitDisk p.2) +
    (p.1 : ℝ) • ((p.2 : EuclideanPlane.punctured) : EuclideanPlane)

/-- Helper for Theorem 55.5: the boundary affine interpolation of a nonvanishing field that
avoids inward rays never equals the zero vector. -/
private lemma boundaryStraightLineAmbientValue_ne_zero (v : DiskVectorField)
    (h_nonvanishing : v.IsNonvanishing)
    (h_avoids : ∀ x : EuclideanPlane.unitCircle, ∀ r : ℝ, 0 < r →
      v (unitCircleToClosedUnitDisk x) ≠
        -(r • ((x : EuclideanPlane.punctured) : EuclideanPlane)))
    (p : unitInterval × EuclideanPlane.unitCircle) :
    boundaryStraightLineAmbientValue v p ≠ 0 := by
  -- Apply the abstract segment lemma to the field value and the radial boundary vector.
  apply positiveSegmentNeZeroOfAvoidsNegativeRay
  · exact h_nonvanishing (unitCircleToClosedUnitDisk p.2)
  · intro hpzero
    have hnorm : ‖((p.2 : EuclideanPlane.punctured) : EuclideanPlane)‖ = 1 := p.2.property
    rw [hpzero, norm_zero] at hnorm
    exact zero_ne_one hnorm
  · exact h_avoids p.2

/-- Helper for Theorem 55.5: the ambient boundary straight-line interpolation is continuous. -/
private lemma continuous_boundaryStraightLineAmbientValue (v : DiskVectorField) :
    Continuous (boundaryStraightLineAmbientValue v) := by
  -- Continuity follows from the coordinate projection, field continuity, and vector operations.
  unfold boundaryStraightLineAmbientValue
  fun_prop

/-- Helper for Theorem 55.5: the boundary affine interpolation lies in the punctured plane. -/
private lemma boundaryStraightLineAmbientValue_mem_punctured (v : DiskVectorField)
    (h_nonvanishing : v.IsNonvanishing)
    (h_avoids : ∀ x : EuclideanPlane.unitCircle, ∀ r : ℝ, 0 < r →
      v (unitCircleToClosedUnitDisk x) ≠
        -(r • ((x : EuclideanPlane.punctured) : EuclideanPlane)))
    (p : unitInterval × EuclideanPlane.unitCircle) :
    boundaryStraightLineAmbientValue v p ∈ EuclideanPlane.punctured := by
  -- Convert the named nonvanishing result to membership in the singleton complement.
  exact (EuclideanPlane.mem_punctured_iff _).mpr
    (boundaryStraightLineAmbientValue_ne_zero v h_nonvanishing h_avoids p)

/-- Helper for Theorem 55.5: the boundary straight-line interpolation as a punctured-plane
valued function. -/
private def boundaryStraightLineValue (v : DiskVectorField)
    (h_nonvanishing : v.IsNonvanishing)
    (h_avoids : ∀ x : EuclideanPlane.unitCircle, ∀ r : ℝ, 0 < r →
      v (unitCircleToClosedUnitDisk x) ≠
        -(r • ((x : EuclideanPlane.punctured) : EuclideanPlane)))
    (p : unitInterval × EuclideanPlane.unitCircle) : EuclideanPlane.punctured :=
  ⟨boundaryStraightLineAmbientValue v p,
    boundaryStraightLineAmbientValue_mem_punctured v h_nonvanishing h_avoids p⟩

/-- Helper for Theorem 55.5: the punctured-plane boundary straight-line interpolation is
continuous. -/
private lemma continuous_boundaryStraightLineValue (v : DiskVectorField)
    (h_nonvanishing : v.IsNonvanishing)
    (h_avoids : ∀ x : EuclideanPlane.unitCircle, ∀ r : ℝ, 0 < r →
      v (unitCircleToClosedUnitDisk x) ≠
        -(r • ((x : EuclideanPlane.punctured) : EuclideanPlane))) :
    Continuous (boundaryStraightLineValue v h_nonvanishing h_avoids) := by
  -- Lift the already continuous ambient segment through the punctured subtype.
  exact (continuous_boundaryStraightLineAmbientValue v).subtype_mk _

/-- Helper for Theorem 55.5: at time zero the straight-line interpolation is the boundary
restriction of the vector field. -/
private lemma boundaryStraightLineValue_zero (v : DiskVectorField)
    (h_nonvanishing : v.IsNonvanishing)
    (h_avoids : ∀ x : EuclideanPlane.unitCircle, ∀ r : ℝ, 0 < r →
      v (unitCircleToClosedUnitDisk x) ≠
        -(r • ((x : EuclideanPlane.punctured) : EuclideanPlane)))
    (x : EuclideanPlane.unitCircle) :
    boundaryStraightLineValue v h_nonvanishing h_avoids (0, x) =
      (v.toPuncturedPlane h_nonvanishing).comp unitCircleToClosedUnitDisk x := by
  -- Compare punctured-plane points through their ambient vectors and simplify the zero endpoint.
  apply Subtype.ext
  simp only [boundaryStraightLineValue, boundaryStraightLineAmbientValue,
    ContinuousMap.comp_apply, toPuncturedPlane_apply, Set.Icc.coe_zero, sub_zero,
    one_smul, zero_smul, add_zero]

/-- Helper for Theorem 55.5: at time one the straight-line interpolation is the canonical
unit-circle inclusion. -/
private lemma boundaryStraightLineValue_one (v : DiskVectorField)
    (h_nonvanishing : v.IsNonvanishing)
    (h_avoids : ∀ x : EuclideanPlane.unitCircle, ∀ r : ℝ, 0 < r →
      v (unitCircleToClosedUnitDisk x) ≠
        -(r • ((x : EuclideanPlane.punctured) : EuclideanPlane)))
    (x : EuclideanPlane.unitCircle) :
    boundaryStraightLineValue v h_nonvanishing h_avoids (1, x) =
      EuclideanPlane.unitCircleInclusion x := by
  -- Compare ambient vectors and simplify the affine segment at its one endpoint.
  apply Subtype.ext
  simp only [boundaryStraightLineValue, boundaryStraightLineAmbientValue,
    EuclideanPlane.unitCircleInclusion_apply, Set.Icc.coe_one, sub_self, zero_smul,
    one_smul, zero_add]

/-- Helper for Theorem 55.5: inward-ray avoidance yields a straight-line homotopy from the
boundary field to the canonical unit-circle inclusion. -/
private def boundaryStraightLineHomotopy (v : DiskVectorField)
    (h_nonvanishing : v.IsNonvanishing)
    (h_avoids : ∀ x : EuclideanPlane.unitCircle, ∀ r : ℝ, 0 < r →
      v (unitCircleToClosedUnitDisk x) ≠
        -(r • ((x : EuclideanPlane.punctured) : EuclideanPlane))) :
    ContinuousMap.Homotopy
      ((v.toPuncturedPlane h_nonvanishing).comp unitCircleToClosedUnitDisk)
      EuclideanPlane.unitCircleInclusion :=
  { toFun := boundaryStraightLineValue v h_nonvanishing h_avoids
    continuous_toFun := continuous_boundaryStraightLineValue v h_nonvanishing h_avoids
    map_zero_left := boundaryStraightLineValue_zero v h_nonvanishing h_avoids
    map_one_left := boundaryStraightLineValue_one v h_nonvanishing h_avoids }

/-- Helper for Theorem 55.5: inward-ray avoidance makes the boundary restriction homotopic to
the canonical inclusion into the punctured plane. -/
private lemma boundaryRestrictionHomotopicUnitCircleInclusion (v : DiskVectorField)
    (h_nonvanishing : v.IsNonvanishing)
    (h_avoids : ∀ x : EuclideanPlane.unitCircle, ∀ r : ℝ, 0 < r →
      v (unitCircleToClosedUnitDisk x) ≠
        -(r • ((x : EuclideanPlane.punctured) : EuclideanPlane))) :
    ((v.toPuncturedPlane h_nonvanishing).comp unitCircleToClosedUnitDisk).Homotopic
      EuclideanPlane.unitCircleInclusion := by
  -- Package the straight-line homotopy interface as a homotopy witness.
  exact ⟨boundaryStraightLineHomotopy v h_nonvanishing h_avoids⟩

/-- Helper for Theorem 55.5: a nonvanishing disk field cannot avoid every inward radial
direction along the boundary. -/
private lemma nonvanishingFieldCannotAvoidInwardBoundary (v : DiskVectorField)
    (h_nonvanishing : v.IsNonvanishing)
    (h_avoids : ∀ x : EuclideanPlane.unitCircle, ∀ r : ℝ, 0 < r →
      v (unitCircleToClosedUnitDisk x) ≠
        -(r • ((x : EuclideanPlane.punctured) : EuclideanPlane))) : False := by
  -- Contractibility of the disk makes the field and then its boundary restriction nullhomotopic.
  letI : ContractibleSpace B² := Metric.contractibleSpace_closedBall zero_le_one
  have hfieldNull : (v.toPuncturedPlane h_nonvanishing).Nullhomotopic := by
    simpa only [ContinuousMap.comp_id] using
      (id_nullhomotopic B²).comp_right (v.toPuncturedPlane h_nonvanishing)
  have hboundaryNull :
      ((v.toPuncturedPlane h_nonvanishing).comp unitCircleToClosedUnitDisk).Nullhomotopic :=
    hfieldNull.comp_left unitCircleToClosedUnitDisk
  -- Transport that nullhomotopy across the affine homotopy to contradict Corollary 55.4.
  obtain ⟨y, hconstant⟩ := hboundaryNull
  have hinclusionNull : EuclideanPlane.unitCircleInclusion.Nullhomotopic := by
    refine ⟨y, ?_⟩
    exact (boundaryRestrictionHomotopicUnitCircleInclusion
      v h_nonvanishing h_avoids).symm.trans hconstant
  exact EuclideanPlane.unitCircleInclusion_not_nullhomotopic hinclusionNull

/-- Theorem 55.5. Every nonvanishing vector field on the closed unit disk points directly inward
at some point of the boundary circle and directly outward at some boundary point. -/
theorem exists_pointingInwardAndOutwardOnBoundary (v : DiskVectorField)
    (h_nonvanishing : v.IsNonvanishing) :
    (∃ x : B², ClosedUnitDisk.IsBoundary x ∧
      ∃ r : ℝ, 0 < r ∧ v x = -(r • (x : EuclideanPlane))) ∧
    ∃ x : B², ClosedUnitDisk.IsBoundary x ∧
      ∃ r : ℝ, 0 < r ∧ v x = r • (x : EuclideanPlane) := by
  classical
  -- The topological contradiction first supplies an inward-pointing boundary value.
  have hinward : ∃ x : B², ClosedUnitDisk.IsBoundary x ∧
      ∃ r : ℝ, 0 < r ∧ v x = -(r • (x : EuclideanPlane)) := by
    by_contra hnone
    apply nonvanishingFieldCannotAvoidInwardBoundary v h_nonvanishing
    intro x r hr heq
    apply hnone
    exact ⟨unitCircleToClosedUnitDisk x, unitCircleToClosedUnitDisk_isBoundary x,
      r, hr, heq⟩
  -- Apply the same inward-pointing argument to the negated field to obtain an outward value.
  have hneg_nonvanishing : (-v).IsNonvanishing := by
    intro x
    simpa only [ContinuousMap.neg_apply, neg_ne_zero] using h_nonvanishing x
  have hneg_inward : ∃ x : B², ClosedUnitDisk.IsBoundary x ∧
      ∃ r : ℝ, 0 < r ∧ (-v) x = -(r • (x : EuclideanPlane)) := by
    by_contra hnone
    apply nonvanishingFieldCannotAvoidInwardBoundary (-v) hneg_nonvanishing
    intro x r hr heq
    apply hnone
    exact ⟨unitCircleToClosedUnitDisk x, unitCircleToClosedUnitDisk_isBoundary x,
      r, hr, heq⟩
  obtain ⟨x, hxBoundary, r, hr, hneg⟩ := hneg_inward
  have houtward : v x = r • (x : EuclideanPlane) := by
    have hnegated := congrArg Neg.neg hneg
    simpa only [ContinuousMap.neg_apply, neg_neg] using hnegated
  exact ⟨hinward, x, hxBoundary, r, hr, houtward⟩

/-- The inward-pointing conclusion of Theorem 55.5. -/
theorem exists_pointingInwardOnBoundary (v : DiskVectorField)
    (h_nonvanishing : v.IsNonvanishing) :
    ∃ x : B², ClosedUnitDisk.IsBoundary x ∧
      ∃ r : ℝ, 0 < r ∧ v x = -(r • (x : EuclideanPlane)) :=
  (v.exists_pointingInwardAndOutwardOnBoundary h_nonvanishing).1

/-- The outward-pointing conclusion of Theorem 55.5. -/
theorem exists_pointingOutwardOnBoundary (v : DiskVectorField)
    (h_nonvanishing : v.IsNonvanishing) :
    ∃ x : B², ClosedUnitDisk.IsBoundary x ∧
      ∃ r : ℝ, 0 < r ∧ v x = r • (x : EuclideanPlane) :=
  (v.exists_pointingInwardAndOutwardOnBoundary h_nonvanishing).2

end DiskVectorField
