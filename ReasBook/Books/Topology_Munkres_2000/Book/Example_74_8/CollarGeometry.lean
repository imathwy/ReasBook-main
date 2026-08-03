module

public import Topology_Munkres_2000.Book.Example_74_8.CutPresentation
import all Topology_Munkres_2000.Book.Definition_21_3.ClosedUnitDisk

public section

open Set ClosedUnitDisk

namespace ProjectivePlaneTorus

noncomputable section

/-- Helper for Example 74.8: closed-disk boundary membership is ambient unit norm. -/
lemma closedUnitDisk_isBoundary_iff_norm (point : B²) :
    ClosedUnitDisk.IsBoundary point ↔ ‖(point : ModelPlane)‖ = 1 := by
  -- This is the stable item-level interface to the closed-disk boundary predicate.
  rfl

/-- Helper for Example 74.8: negation of a closed-disk point negates its ambient vector. -/
lemma closedUnitDisk_neg_coe (point : B²) :
    ((-point : B²) : ModelPlane) = -(point : ModelPlane) := by
  -- Negation on the invariant closed ball is inherited from the ambient plane.
  rfl

/-- Helper for Example 74.8: negation on the attaching circle negates its ambient vector. -/
lemma boundaryCircle_neg_coe (point : DiscBoundaryGluing.BoundaryCircle) :
    ((-point : DiscBoundaryGluing.BoundaryCircle) : ModelPlane) =
      -(point : ModelPlane) := by
  -- Negation on the invariant metric sphere is inherited from the ambient plane.
  rfl

/-- Helper for Example 74.8: one coordinate-bearing collar square. -/
abbrev CollarSquare := unitInterval × unitInterval

/-- Helper for Example 74.8: the common source retaining separate projective and torus
collars. -/
abbrev CollarSource := CollarSquare ⊕ CollarSquare

/-- Helper for Example 74.8: the physical radius corresponding to the deleted coordinate
disc of radius one half. -/
noncomputable def projectiveInnerRadius : ℝ :=
  1 / Real.sqrt 5

/-- Helper for Example 74.8: the projective collar radius interpolates affinely from the
deleted-disc boundary to the unit-circle boundary. -/
noncomputable def projectiveCollarRadius (t : unitInterval) : ℝ :=
  projectiveInnerRadius + (t : ℝ) * (1 - projectiveInnerRadius)

/-- Helper for Example 74.8: expose the affine projective collar radius without unfolding its
construction across the support-module boundary. -/
lemma projectiveCollarRadius_apply (t : unitInterval) :
    projectiveCollarRadius t =
      projectiveInnerRadius + (t : ℝ) * (1 - projectiveInnerRadius) := by
  -- This owner-level equation is the stable rewrite interface for the opaque definition.
  rfl

/-- Helper for Example 74.8: the projective collar follows the standard attaching-circle
direction while varying its physical radius. -/
noncomputable def projectiveCollarVector (point : CollarSquare) : ModelPlane :=
  (2 * projectiveCollarRadius point.2) • (boundaryCircleParam point.1 : ModelPlane)

/-- Helper for Example 74.8: expose the projective collar vector's radial formula without
unfolding its construction downstream. -/
lemma projectiveCollarVector_apply (point : CollarSquare) :
    projectiveCollarVector point =
      (2 * projectiveCollarRadius point.2) •
        (boundaryCircleParam point.1 : ModelPlane) := by
  -- This is the defining radial formula.
  rfl

/-- Helper for Example 74.8: global projective coordinates have the explicit radial image
under the plane-to-open-disk homeomorphism. -/
lemma projectiveInteriorPoint_coe (point : ModelPlane) :
    (projectiveInteriorPoint point : ModelPlane) =
      (Real.sqrt (1 + ‖point‖ ^ 2))⁻¹ • point := by
  -- Unfold the owner-level bridge once; the remaining two subtype maps preserve values.
  calc
    (projectiveInteriorPoint point : ModelPlane) =
        (Homeomorph.unitBall point : ModelPlane) :=
      projectiveInteriorPoint_coe_unitBall point
    _ = (Real.sqrt (1 + ‖point‖ ^ 2))⁻¹ • point := by
      rw [Homeomorph.unitBall_apply_coe,
        OpenPartialHomeomorph.univUnitBall_apply]

/-- Helper for Example 74.8: the physical inner radius is strictly positive. -/
lemma projectiveInnerRadius_pos : 0 < projectiveInnerRadius := by
  -- Positivity follows from positivity of the square root of five.
  rw [projectiveInnerRadius]
  positivity

/-- Helper for Example 74.8: the physical inner radius lies strictly below the unit radius. -/
lemma projectiveInnerRadius_lt_one : projectiveInnerRadius < 1 := by
  -- Squaring shows that `sqrt 5` is larger than one, so its reciprocal is smaller.
  have hsqrt_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsqrt_gt_one : 1 < Real.sqrt 5 := by
    nlinarith [Real.sqrt_nonneg 5]
  rw [projectiveInnerRadius, div_lt_one hsqrt_pos]
  exact hsqrt_gt_one

/-- Helper for Example 74.8: the affine projective collar radius is bounded below by its
inner endpoint. -/
lemma projectiveInnerRadius_le_collarRadius (t : unitInterval) :
    projectiveInnerRadius ≤ projectiveCollarRadius t := by
  -- The interpolation increment is a product of two nonnegative factors.
  rw [projectiveCollarRadius]
  have ht : 0 ≤ (t : ℝ) := unitInterval.nonneg t
  have hr : 0 ≤ 1 - projectiveInnerRadius :=
    sub_nonneg.mpr projectiveInnerRadius_lt_one.le
  exact le_add_of_nonneg_right (mul_nonneg ht hr)

/-- Helper for Example 74.8: the affine projective collar radius never exceeds one. -/
lemma projectiveCollarRadius_le_one (t : unitInterval) :
    projectiveCollarRadius t ≤ 1 := by
  -- Rewrite the distance from the outer endpoint as a nonnegative product.
  rw [projectiveCollarRadius]
  have ht : (t : ℝ) ≤ 1 := unitInterval.le_one t
  have hr : 0 ≤ 1 - projectiveInnerRadius :=
    sub_nonneg.mpr projectiveInnerRadius_lt_one.le
  nlinarith [mul_nonneg (sub_nonneg.mpr ht) hr]

/-- Helper for Example 74.8: the norm of an interior projective point is the standard radial
unit-ball formula. -/
lemma projectiveInteriorPoint_norm (point : ModelPlane) :
    ‖(projectiveInteriorPoint point : ModelPlane)‖ =
      ‖point‖ / Real.sqrt (1 + ‖point‖ ^ 2) := by
  -- Take norms in the owner-level vector formula and normalize the positive square root.
  rw [projectiveInteriorPoint_coe, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_mul_eq_div]

/-- Helper for Example 74.8: coordinates in the radius-one-half ball map strictly inside the
physical collar's inner radius. -/
lemma projectiveInteriorPoint_norm_lt_innerRadius {point : ModelPlane}
    (hpoint : point ∈ Metric.ball (0 : ModelPlane) (1 / 2 : ℝ)) :
    ‖(projectiveInteriorPoint point : ModelPlane)‖ < projectiveInnerRadius := by
  -- Compare the positive fractions after squaring their positive numerators and denominators.
  have hnorm_nonneg : 0 ≤ ‖point‖ := norm_nonneg point
  have hnorm_lt_half : ‖point‖ < (1 / 2 : ℝ) := by
    simpa only [mem_ball_zero_iff] using hpoint
  have hsqrt_five_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_five_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hdenom_pos : 0 < Real.sqrt (1 + ‖point‖ ^ 2) := by
    apply Real.sqrt_pos.2
    positivity
  have hdenom_sq : Real.sqrt (1 + ‖point‖ ^ 2) ^ 2 = 1 + ‖point‖ ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hcross : ‖point‖ * Real.sqrt 5 < Real.sqrt (1 + ‖point‖ ^ 2) := by
    have hleft_nonneg : 0 ≤ ‖point‖ * Real.sqrt 5 :=
      mul_nonneg hnorm_nonneg (Real.sqrt_nonneg 5)
    nlinarith
  rw [projectiveInteriorPoint_norm, projectiveInnerRadius,
    div_lt_div_iff₀ hdenom_pos hsqrt_five_pos]
  simpa only [one_mul] using hcross

/-- Helper for Example 74.8: every closed-disk point of norm strictly below one has a
global projective coordinate. -/
lemma exists_projectiveInteriorPoint_of_norm_lt_one (point : B²)
    (hpoint : ‖(point : ModelPlane)‖ < 1) :
    ∃ coordinate : ModelPlane, projectiveInteriorPoint coordinate = point := by
  -- Regard the disk point as an interior point and invert the coordinate homeomorphism.
  have hinterior : point ∈ DiskAntipodalQuotient.interior := by
    apply (DiskAntipodalQuotient.mem_interior_iff_mem_ball point).mpr
    simpa only [Metric.mem_ball, dist_zero_right]
  let interiorPoint : DiskAntipodalQuotient.interior := ⟨point, hinterior⟩
  refine ⟨DiskAntipodalQuotient.planeHomeomorphInterior.symm interiorPoint, ?_⟩
  exact projectiveInteriorPoint_symm_apply interiorPoint

/-- Helper for Example 74.8: a projective coordinate whose physical image lies below the
inner collar radius has coordinate norm below one half. -/
lemma projectiveInteriorPoint_coordinate_norm_lt_half {point : ModelPlane}
    (hpoint : ‖(projectiveInteriorPoint point : ModelPlane)‖ < projectiveInnerRadius) :
    ‖point‖ < 1 / 2 := by
  -- Cross-multiply the radial formula, then compare the squares of its nonnegative sides.
  have hnorm_nonneg : 0 ≤ ‖point‖ := norm_nonneg point
  have hsqrt_five_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_five_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hdenom_pos : 0 < Real.sqrt (1 + ‖point‖ ^ 2) := by
    apply Real.sqrt_pos.2
    positivity
  have hdenom_sq : Real.sqrt (1 + ‖point‖ ^ 2) ^ 2 = 1 + ‖point‖ ^ 2 :=
    Real.sq_sqrt (by positivity)
  rw [projectiveInteriorPoint_norm, projectiveInnerRadius,
    div_lt_div_iff₀ hdenom_pos hsqrt_five_pos] at hpoint
  have hleft_nonneg : 0 ≤ ‖point‖ * Real.sqrt 5 :=
    mul_nonneg hnorm_nonneg (Real.sqrt_nonneg 5)
  nlinarith

/-- Helper for Example 74.8: a closed-disk representative belongs to the chosen projective
complement exactly when its physical norm is at least the inner collar radius. -/
lemma projectiveModelComplement_iff_norm (point : B²) :
    projectiveModelMap point ∈ standardGluing.leftDeletedDiscᶜ ↔
      projectiveInnerRadius ≤ ‖(point : ModelPlane)‖ := by
  constructor
  · intro hcomplement
    -- If the norm were smaller, invert the interior chart and recover a deleted coordinate.
    by_contra hnot
    have hnorm_lt : ‖(point : ModelPlane)‖ < projectiveInnerRadius :=
      lt_of_not_ge hnot
    have hnorm_lt_one : ‖(point : ModelPlane)‖ < 1 :=
      hnorm_lt.trans projectiveInnerRadius_lt_one
    obtain ⟨coordinate, hcoordinate⟩ :=
      exists_projectiveInteriorPoint_of_norm_lt_one point hnorm_lt_one
    have hcoordinate_norm : ‖coordinate‖ < 1 / 2 :=
      projectiveInteriorPoint_coordinate_norm_lt_half (by
        rw [hcoordinate]
        exact hnorm_lt)
    have hpreimage : point ∈
        projectiveModelMap ⁻¹' standardGluing.leftDeletedDisc := by
      rw [projectiveModelMap_preimage_leftDeletedDisc]
      exact ⟨coordinate, by simpa only [Metric.mem_ball, dist_zero_right], hcoordinate⟩
    exact hcomplement hpreimage
  · intro hnorm
    -- Any deleted representative comes from a coordinate with physical norm below the inner
    -- radius, contradicting the assumed lower bound.
    rw [Set.mem_compl_iff]
    intro hdeleted
    have hpreimage : point ∈
        projectiveModelMap ⁻¹' standardGluing.leftDeletedDisc := hdeleted
    rw [projectiveModelMap_preimage_leftDeletedDisc] at hpreimage
    rcases hpreimage with ⟨coordinate, hcoordinate, hcoordinate_eq⟩
    have hcoordinate_norm := projectiveInteriorPoint_norm_lt_innerRadius hcoordinate
    have hambient_eq : (projectiveInteriorPoint coordinate : ModelPlane) =
        (point : ModelPlane) := congrArg Subtype.val hcoordinate_eq
    rw [hambient_eq] at hcoordinate_norm
    exact (not_lt_of_ge hnorm) hcoordinate_norm

/-- Helper for Example 74.8: the standard boundary-circle parameter always has norm one
half. -/
lemma boundaryCircleParam_norm (s : unitInterval) :
    ‖(boundaryCircleParam s : ModelPlane)‖ = 1 / 2 := by
  -- The codomain of the parameterization is precisely the radius-one-half sphere.
  simpa only [Metric.mem_sphere, dist_zero_right] using
    (boundaryCircleParam s).property

/-- Helper for Example 74.8: the collar vector has exactly its prescribed affine radius. -/
lemma projectiveCollarVector_norm (point : CollarSquare) :
    ‖projectiveCollarVector point‖ = projectiveCollarRadius point.2 := by
  -- The direction has norm one half, cancelling the explicit factor two.
  have hradius_nonneg : 0 ≤ projectiveCollarRadius point.2 :=
    (projectiveInnerRadius_pos.le.trans
      (projectiveInnerRadius_le_collarRadius point.2))
  rw [projectiveCollarVector, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by norm_num) hradius_nonneg),
    boundaryCircleParam_norm]
  ring

/-- Helper for Example 74.8: every collar vector belongs to the closed unit disk. -/
lemma projectiveCollarVector_mem_closedUnitDisk (point : CollarSquare) :
    projectiveCollarVector point ∈
      Metric.closedBall (0 : ModelPlane) 1 := by
  -- The norm formula reduces disk membership to the upper affine-radius bound.
  rw [mem_closedBall_zero_iff, projectiveCollarVector_norm]
  exact projectiveCollarRadius_le_one point.2

/-- Helper for Example 74.8: regard a projective collar vector as a point of the canonical
closed-disk model. -/
noncomputable def projectiveCollarDiskPoint (point : CollarSquare) : B² :=
  ⟨projectiveCollarVector point, projectiveCollarVector_mem_closedUnitDisk point⟩

/-- Helper for Example 74.8: coercing a collar disk point recovers its ambient collar vector. -/
lemma projectiveCollarDiskPoint_coe (point : CollarSquare) :
    (projectiveCollarDiskPoint point : ModelPlane) = projectiveCollarVector point := by
  -- The disk point packages this vector with its closed-ball membership proof.
  rfl

/-- Helper for Example 74.8: every projective collar disk point avoids the deleted coordinate
disc. -/
lemma projectiveCollarDiskPoint_mem_complement (point : CollarSquare) :
    projectiveModelMap (projectiveCollarDiskPoint point) ∈
      standardGluing.leftDeletedDiscᶜ := by
  -- Apply the annulus normal form to the collar's exact radial norm.
  rw [projectiveModelComplement_iff_norm, projectiveCollarDiskPoint,
    projectiveCollarVector_norm]
  exact projectiveInnerRadius_le_collarRadius point.2

/-- Helper for Example 74.8: the affine projective collar radius varies continuously. -/
lemma continuous_projectiveCollarRadius : Continuous projectiveCollarRadius := by
  -- The radius is an affine expression in the interval coordinate.
  exact continuous_const.add (continuous_subtype_val.mul continuous_const)

/-- Helper for Example 74.8: the explicit projective collar vector varies continuously in
both collar coordinates. -/
lemma continuous_projectiveCollarVector : Continuous projectiveCollarVector := by
  -- Multiply the continuous radial factor by the continuous boundary direction.
  exact (continuous_const.mul
      (continuous_projectiveCollarRadius.comp continuous_snd)).smul
    (continuous_subtype_val.comp
      (boundaryCircleParam_isQuotientMap.continuous.comp continuous_fst))

/-- Helper for Example 74.8: the projective collar point varies continuously in the closed
disk model. -/
lemma continuous_projectiveCollarDiskPoint : Continuous projectiveCollarDiskPoint := by
  -- Package continuous ambient vectors with their already proved disk-membership certificate.
  exact Continuous.subtype_mk continuous_projectiveCollarVector _

/-- Helper for Example 74.8: the underlying projective collar function lands in the chosen
deleted-disc complement. -/
noncomputable def projectiveCollarFunction :
    CollarSquare → standardGluing.LeftComplement :=
  fun point ↦ ⟨projectiveModelMap (projectiveCollarDiskPoint point),
    projectiveCollarDiskPoint_mem_complement point⟩

/-- Helper for Example 74.8: the projective collar function is continuous. -/
lemma continuous_projectiveCollarFunction : Continuous projectiveCollarFunction := by
  -- Compose the continuous disk collar with the canonical quotient model, then corestrict.
  exact Continuous.subtype_mk
    (projectiveModelMap_isQuotientMap.continuous.comp
      continuous_projectiveCollarDiskPoint) _

/-- Helper for Example 74.8: the explicit radial collar maps onto the projective-plane
deleted-disc complement. -/
noncomputable def projectiveCollarMap :
    C(CollarSquare, standardGluing.LeftComplement) :=
  ⟨projectiveCollarFunction, continuous_projectiveCollarFunction⟩

/-- Helper for Example 74.8: coercing the projective collar map to the projective plane
recovers the canonical disk-model quotient value. -/
lemma projectiveCollarMap_coe (point : CollarSquare) :
    (projectiveCollarMap point : RealProjectivePlane) =
      projectiveModelMap (projectiveCollarDiskPoint point) := by
  -- Both continuous-map and complement subtype packages preserve the underlying value.
  rfl

/-- Helper for Example 74.8: at its inner edge, the collar disk point is the canonical image
of the standard attaching-circle coordinate. -/
lemma projectiveCollarDiskPoint_inner (s : unitInterval) :
    projectiveCollarDiskPoint (s, 0) = projectiveInteriorPoint (boundaryCircleParam s) := by
  -- Both sides are the same boundary direction scaled by the physical radius `1 / sqrt 5`.
  apply Subtype.ext
  rw [projectiveCollarDiskPoint_coe, projectiveCollarVector_apply, projectiveCollarRadius,
    projectiveInteriorPoint_coe, boundaryCircleParam_norm]
  have hzero : ((0 : unitInterval) : ℝ) = 0 := rfl
  rw [hzero, zero_mul, add_zero, projectiveInnerRadius]
  have hsqrt_five_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_five_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsmall_sqrt_sq : Real.sqrt (1 + (1 / 2 : ℝ) ^ 2) ^ 2 = 5 / 4 := by
    rw [Real.sq_sqrt (by positivity)]
    norm_num
  have hsmall_sqrt : Real.sqrt (1 + (1 / 2 : ℝ) ^ 2) = Real.sqrt 5 / 2 := by
    nlinarith [Real.sqrt_nonneg (1 + (1 / 2 : ℝ) ^ 2), Real.sqrt_nonneg 5]
  rw [hsmall_sqrt]
  have hcoeff : 2 * (1 / Real.sqrt 5) = (Real.sqrt 5 / 2)⁻¹ := by
    field_simp
  rw [hcoeff]

/-- Helper for Example 74.8: the inner projective collar edge agrees with the attaching map
used by the standard deleted-disc gluing. -/
lemma projectiveCollarMap_inner (s : unitInterval) :
    projectiveCollarMap (s, 0) = standardGluing.leftBoundary (boundaryCircleParam s) := by
  -- Compare ambient projective points through the owner-level chart computation.
  apply Subtype.ext
  rw [projectiveCollarMap_coe, standardGluing.leftBoundary_coe,
    standardGluing_leftChart_apply,
    projectiveCollarDiskPoint_inner]

end

end ProjectivePlaneTorus
