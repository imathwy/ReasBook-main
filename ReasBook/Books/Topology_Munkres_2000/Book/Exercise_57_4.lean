module

import all Topology_Munkres_2000.Book.Definition_55_2.Sphere

public import Topology_Munkres_2000.Book.Definition_35_1.Retraction
public import Topology_Munkres_2000.Book.Definition_57_2.Antipodal
public import Topology_Munkres_2000.Book.Exercise_55_5.Inclusion
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.Homotopy.Contractible

noncomputable section

public section

open MeasureTheory
open scoped symmDiff

/-- No continuous antipode-preserving self-map of `Sⁿ` is nullhomotopic. -/
def StandardSphere.OddSelfMapsNotNullhomotopic (n : ℕ) : Prop :=
  ∀ h : C(StandardSphere n, StandardSphere n), Function.Odd h → ¬ h.Nullhomotopic

/-- Construct `OddSelfMapsNotNullhomotopic n` from its pointwise formulation. -/
theorem StandardSphere.OddSelfMapsNotNullhomotopic.of_forall (n : ℕ)
    (h_odd_not_nullhomotopic :
      ∀ h : C(StandardSphere n, StandardSphere n), Function.Odd h → ¬ h.Nullhomotopic) :
    StandardSphere.OddSelfMapsNotNullhomotopic n :=
  h_odd_not_nullhomotopic

/-- Apply `OddSelfMapsNotNullhomotopic n` to an odd self-map of `Sⁿ`. -/
theorem StandardSphere.OddSelfMapsNotNullhomotopic.apply {n : ℕ}
    (h_odd_not_nullhomotopic : StandardSphere.OddSelfMapsNotNullhomotopic n)
    (h : C(StandardSphere n, StandardSphere n)) (h_odd : Function.Odd h) :
    ¬ h.Nullhomotopic :=
  h_odd_not_nullhomotopic h h_odd

namespace StandardSphere

/-- Helper for Exercise 57.4: a standard sphere point lies on the boundary of the
closed unit ball. -/
private theorem spherePoint_mem_ballBoundary (n : ℕ) (x : StandardSphere n) :
    toBall n x ∈ boundary n := by
  -- Rewrite both sphere presentations as the same ambient norm-one equation.
  rw [boundary, Set.mem_setOf_eq]
  calc
    ‖(toBall n x : EuclideanSpace ℝ (Fin (n + 1)))‖ =
        ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ := congrArg norm (toBall_apply n x)
    _ = 1 := mem_sphere_zero_iff_norm.mp x.property

/-- Helper for Exercise 57.4: the standard sphere inclusion into the ball boundary
is continuous. -/
private theorem continuous_sphereToBallBoundary (n : ℕ) :
    Continuous (fun x : StandardSphere n ↦
      (⟨toBall n x, spherePoint_mem_ballBoundary n x⟩ : boundary n)) := by
  -- The map is the canonical sphere-to-ball inclusion with a restricted codomain.
  fun_prop

/-- Helper for Exercise 57.4: the canonical map from the standard sphere to the
boundary presentation of the same sphere. -/
private def sphereToBallBoundary (n : ℕ) : C(StandardSphere n, boundary n) :=
  ⟨fun x ↦ ⟨toBall n x, spherePoint_mem_ballBoundary n x⟩,
    continuous_sphereToBallBoundary n⟩

/-- Helper for Exercise 57.4: the sphere-to-boundary map preserves the underlying
closed-ball point. -/
private theorem sphereToBallBoundary_coe (n : ℕ) (x : StandardSphere n) :
    (sphereToBallBoundary n x : ClosedUnitBall n) = toBall n x := by
  -- Restricting the codomain changes only the membership certificate.
  rfl

/-- Helper for Exercise 57.4: a point of the ball boundary determines a point of
the standard sphere. -/
private theorem ballBoundaryPoint_mem_sphere (n : ℕ) (x : boundary n) :
    (x : EuclideanSpace ℝ (Fin (n + 1))) ∈ StandardSphere n := by
  -- The boundary certificate is exactly the norm-one sphere certificate.
  exact mem_sphere_zero_iff_norm.mpr x.property

/-- Helper for Exercise 57.4: the boundary-to-standard-sphere conversion is
continuous. -/
private theorem continuous_ballBoundaryToSphere (n : ℕ) :
    Continuous (fun x : boundary n ↦
      (⟨(x : EuclideanSpace ℝ (Fin (n + 1))), ballBoundaryPoint_mem_sphere n x⟩ :
        StandardSphere n)) := by
  -- Continuity follows from the nested subtype projections.
  fun_prop

/-- Helper for Exercise 57.4: the canonical map from the ball-boundary sphere to
the standard sphere. -/
private def ballBoundaryToSphere (n : ℕ) : C(boundary n, StandardSphere n) :=
  ⟨fun x ↦ ⟨x, ballBoundaryPoint_mem_sphere n x⟩, continuous_ballBoundaryToSphere n⟩

/-- Helper for Exercise 57.4: converting a standard sphere point to the ball
boundary and back is the identity. -/
private theorem ballBoundaryToSphere_sphereToBallBoundary (n : ℕ)
    (x : StandardSphere n) :
    ballBoundaryToSphere n (sphereToBallBoundary n x) = x := by
  -- Both points have the same ambient Euclidean vector.
  apply Subtype.ext
  exact toBall_apply n x

end StandardSphere

/-- Helper for Exercise 57.4: radial projection of a continuous nonvanishing map
to the unit sphere is continuous. -/
private theorem continuous_radialDirection {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : C(X, E))
    (hF : ∀ x, F x ∈ ({0}ᶜ : Set E)) :
    Continuous (fun x ↦ ((homeomorphUnitSphereProd E) ⟨F x, hF x⟩).1) := by
  -- The nonvanishing map lands in the punctured space, where radial projection is continuous.
  fun_prop

/-- Helper for Exercise 57.4: the radial direction of a continuous nonvanishing
map. -/
private def radialDirection {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : C(X, E))
    (hF : ∀ x, F x ∈ ({0}ᶜ : Set E)) :
    C(X, Metric.sphere (0 : E) 1) :=
  ⟨fun x ↦ ((homeomorphUnitSphereProd E) ⟨F x, hF x⟩).1,
    continuous_radialDirection F hF⟩

/-- Helper for Exercise 57.4: the radial direction has the expected normalized
ambient vector. -/
private theorem radialDirection_coe {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : C(X, E))
    (hF : ∀ x, F x ∈ ({0}ᶜ : Set E)) (x : X) :
    (radialDirection F hF x : E) = ‖F x‖⁻¹ • F x := by
  -- This is the first-coordinate computation rule for polar coordinates.
  exact homeomorphUnitSphereProd_apply_fst_coe E ⟨F x, hF x⟩

/-- Helper for Exercise 57.4: radial projection preserves oddness. -/
private theorem radialDirection_odd {X E : Type*} [TopologicalSpace X] [Neg X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : C(X, E))
    (hF : ∀ x, F x ∈ ({0}ᶜ : Set E))
    (hF_odd : Function.Odd F) : Function.Odd (radialDirection F hF) := by
  -- Negation preserves the norm, so normalization commutes with antipodes.
  intro x
  apply Subtype.ext
  calc
    (radialDirection F hF (-x) : E) = ‖F (-x)‖⁻¹ • F (-x) :=
      radialDirection_coe F hF (-x)
    _ = -(‖F x‖⁻¹ • F x) := by
      rw [hF_odd, norm_neg, smul_neg]
    _ = -(radialDirection F hF x : E) :=
      congrArg Neg.neg (radialDirection_coe F hF x).symm
    _ = ((-(radialDirection F hF x) : Metric.sphere (0 : E) 1) : E) := rfl

/-- Helper for Exercise 57.4: the antipodal difference of a continuous map is
continuous. -/
private theorem continuous_antipodalDifference {n : ℕ}
    (f : C(StandardSphere (n + 1), EuclideanSpace ℝ (Fin (n + 1)))) :
    Continuous (fun x ↦ f x - f (-x)) := by
  -- Both evaluation and antipodal evaluation are continuous, hence so is their difference.
  fun_prop

/-- Helper for Exercise 57.4: the antipodal difference as a continuous map. -/
private def antipodalDifference {n : ℕ}
    (f : C(StandardSphere (n + 1), EuclideanSpace ℝ (Fin (n + 1)))) :
    C(StandardSphere (n + 1), EuclideanSpace ℝ (Fin (n + 1))) :=
  ⟨fun x ↦ f x - f (-x), continuous_antipodalDifference f⟩

/-- Helper for Exercise 57.4: evaluation of the antipodal difference is the
corresponding vector subtraction. -/
private theorem antipodalDifference_apply {n : ℕ}
    (f : C(StandardSphere (n + 1), EuclideanSpace ℝ (Fin (n + 1))))
    (x : StandardSphere (n + 1)) :
    antipodalDifference f x = f x - f (-x) := by
  -- This is the defining computation rule.
  rfl

/-- Helper for Exercise 57.4: the antipodal difference is odd. -/
private theorem antipodalDifference_odd {n : ℕ}
    (f : C(StandardSphere (n + 1), EuclideanSpace ℝ (Fin (n + 1)))) :
    Function.Odd (antipodalDifference f) := by
  -- Swapping an antipodal pair reverses the subtraction.
  intro x
  rw [antipodalDifference_apply, antipodalDifference_apply, neg_neg, neg_sub]

/-- Helper for Exercise 57.4: if a map separates every antipodal pair, radial
normalization of its difference gives an odd sphere map. -/
private theorem existsOddSphereMap_of_antipodal_ne {n : ℕ}
    (f : C(StandardSphere (n + 1), EuclideanSpace ℝ (Fin (n + 1))))
    (h_ne : ∀ x, f x ≠ f (-x)) :
    ∃ g : C(StandardSphere (n + 1), StandardSphere n), Function.Odd g := by
  -- Normalize the nowhere-zero antipodal difference to the unit sphere.
  have difference_mem_compl : ∀ x, antipodalDifference f x ∈
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    intro x
    rw [Set.mem_compl_iff, Set.mem_singleton_iff, antipodalDifference_apply]
    exact sub_ne_zero.mpr (h_ne x)
  exact ⟨radialDirection (antipodalDifference f) difference_mem_compl,
    radialDirection_odd (antipodalDifference f) difference_mem_compl
      (antipodalDifference_odd f)⟩

/-- Helper for Exercise 57.4: adjoining a leading real coordinate to a Euclidean
vector through the canonical `L²` coordinate equivalence. -/
private def prependCoordinate {n : ℕ} (c : ℝ)
    (v : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin (n + 2)) :=
  (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm
    (Fin.cons c (EuclideanSpace.equiv (Fin (n + 1)) ℝ v))

/-- Helper for Exercise 57.4: the squared norm after adjoining a leading
coordinate is the sum of the two squared norms. -/
private theorem prependCoordinate_norm_sq {n : ℕ} (c : ℝ)
    (v : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖prependCoordinate c v‖ ^ 2 = c ^ 2 + ‖v‖ ^ 2 := by
  -- Pass to ordinary coordinates, where the finite sum splits at its first term.
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_succ]
  simp [prependCoordinate]

/-- Helper for Exercise 57.4: adjoining a leading coordinate commutes with
negation. -/
private theorem prependCoordinate_neg {n : ℕ} (c : ℝ)
    (v : EuclideanSpace ℝ (Fin (n + 1))) :
    prependCoordinate (-c) (-v) = -prependCoordinate c v := by
  -- Compare ordinary coordinates, where `Fin.cons` commutes pointwise with negation.
  apply (EuclideanSpace.equiv (Fin (n + 2)) ℝ).injective
  simp only [prependCoordinate, ContinuousLinearEquiv.apply_symm_apply, map_neg]
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simp

/-- Helper for Exercise 57.4: adjoining a varying leading coordinate to a
varying Euclidean vector is continuous. -/
private theorem continuous_prependCoordinate {n : ℕ} :
    Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin (n + 1)) ↦
      prependCoordinate p.1 p.2) := by
  -- Check continuity after the Euclidean coordinate homeomorphism, coordinate by coordinate.
  apply (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact continuous_fst
  · exact (continuous_apply j).comp
      ((EuclideanSpace.equiv (Fin (n + 1)) ℝ).continuous.comp continuous_snd)

/-- Helper for Exercise 57.4: the first sphere coordinate is the offset of the
corresponding oriented affine halfspace. -/
private def halfspaceOffset {n : ℕ} (p : StandardSphere (n + 1)) : ℝ :=
  EuclideanSpace.equiv (Fin (n + 2)) ℝ p 0

/-- Helper for Exercise 57.4: the remaining sphere coordinates form the normal
of the corresponding oriented affine halfspace. -/
private def halfspaceNormal {n : ℕ} (p : StandardSphere (n + 1)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
    (Fin.tail (EuclideanSpace.equiv (Fin (n + 2)) ℝ p))

/-- Helper for Exercise 57.4: an oriented sphere parameter determines its lower
closed affine halfspace. -/
private def orientedHalfspace {n : ℕ} (p : StandardSphere (n + 1)) :
    Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {x | inner ℝ (halfspaceNormal p) x ≤ halfspaceOffset p}

/-- Helper for Exercise 57.4: the offset and normal reconstruct the original
sphere parameter. -/
private theorem prependCoordinate_halfspaceCoordinates {n : ℕ}
    (p : StandardSphere (n + 1)) :
    prependCoordinate (halfspaceOffset p) (halfspaceNormal p) = p := by
  -- Compare ordinary coordinates, splitting off the leading coordinate.
  apply (EuclideanSpace.equiv (Fin (n + 2)) ℝ).injective
  rw [prependCoordinate, ContinuousLinearEquiv.apply_symm_apply]
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rfl
  · change (EuclideanSpace.equiv (Fin (n + 2)) ℝ p) j.succ = _
    rfl

/-- Helper for Exercise 57.4: antipodes negate the halfspace offset. -/
private theorem halfspaceOffset_neg {n : ℕ} (p : StandardSphere (n + 1)) :
    halfspaceOffset (-p) = -halfspaceOffset p := by
  -- The Euclidean coordinate equivalence is linear.
  simp [halfspaceOffset]

/-- Helper for Exercise 57.4: antipodes negate the halfspace normal. -/
private theorem halfspaceNormal_neg {n : ℕ} (p : StandardSphere (n + 1)) :
    halfspaceNormal (-p) = -halfspaceNormal p := by
  -- Compare the tail coordinates after applying the Euclidean equivalence.
  apply (EuclideanSpace.equiv (Fin (n + 1)) ℝ).injective
  rw [halfspaceNormal, halfspaceNormal, ContinuousLinearEquiv.apply_symm_apply, map_neg,
    ContinuousLinearEquiv.apply_symm_apply]
  funext i
  rfl

/-- Helper for Exercise 57.4: the halfspace offset varies continuously on the
parameter sphere. -/
private theorem continuous_halfspaceOffset {n : ℕ} :
    Continuous (halfspaceOffset : StandardSphere (n + 1) → ℝ) := by
  -- It is the leading coordinate of a continuous linear coordinate map.
  unfold halfspaceOffset
  fun_prop

/-- Helper for Exercise 57.4: the halfspace normal varies continuously on the
parameter sphere. -/
private theorem continuous_halfspaceNormal {n : ℕ} :
    Continuous (halfspaceNormal : StandardSphere (n + 1) →
      EuclideanSpace ℝ (Fin (n + 1))) := by
  -- Each normal coordinate is a tail coordinate of the ambient sphere point.
  apply (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  exact (continuous_apply i.succ).comp
    ((EuclideanSpace.equiv (Fin (n + 2)) ℝ).continuous.comp continuous_subtype_val)

/-- Helper for Exercise 57.4: the offset and normal satisfy the unit-sphere
equation. -/
private theorem halfspaceOffset_sq_add_normal_sq {n : ℕ}
    (p : StandardSphere (n + 1)) :
    halfspaceOffset p ^ 2 + ‖halfspaceNormal p‖ ^ 2 = 1 := by
  -- Transfer the sphere norm equation through the reconstruction formula.
  have hnorm := congrArg (fun x : EuclideanSpace ℝ (Fin (n + 2)) ↦ ‖x‖ ^ 2)
    (prependCoordinate_halfspaceCoordinates p)
  rw [show ‖(p : EuclideanSpace ℝ (Fin (n + 2)))‖ = 1 from
    mem_sphere_zero_iff_norm.mp p.property] at hnorm
  simpa [prependCoordinate, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ] using hnorm

/-- Helper for Exercise 57.4: a nonconstant real inner-product level set has
Lebesgue measure zero. -/
private theorem volume_inner_levelSet_eq_zero {m : ℕ}
    (v : EuclideanSpace ℝ (Fin m)) (c : ℝ) (hv : v ≠ 0) :
    volume {x | inner ℝ v x = c} = 0 := by
  -- Realize the level set as a strict affine subspace with normal `v`.
  let p : EuclideanSpace ℝ (Fin m) := (c / ‖v‖ ^ 2) • v
  let s : AffineSubspace ℝ (EuclideanSpace ℝ (Fin m)) :=
    AffineSubspace.mk' p (LinearMap.ker (innerSL ℝ v).toLinearMap)
  have hvnorm : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
  have hp : inner ℝ v p = c := by
    -- The chosen base point lies on the desired level set.
    rw [show p = _ from rfl, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hs_coe : (s : Set (EuclideanSpace ℝ (Fin m))) = {x | inner ℝ v x = c} := by
    -- Membership in the translated kernel is exactly the level-set equation.
    ext x
    change x ∈ s ↔ inner ℝ v x = c
    rw [show s = _ from rfl, AffineSubspace.mem_mk']
    simp only [LinearMap.mem_ker]
    change inner ℝ v (x - p) = 0 ↔ inner ℝ v x = c
    rw [inner_sub_right, hp]
    constructor <;> intro h <;> linarith
  have hs_ne_top : s ≠ ⊤ := by
    -- Translating the base point by `v` leaves the affine subspace only if `v = 0`.
    intro hs
    have hv_mem : p + v ∈ s := by
      rw [hs]
      trivial
    rw [show s = _ from rfl, AffineSubspace.mem_mk'] at hv_mem
    simp only [LinearMap.mem_ker] at hv_mem
    change inner ℝ v ((p + v) - p) = 0 at hv_mem
    rw [add_sub_cancel_left, real_inner_self_eq_norm_sq] at hv_mem
    exact hvnorm hv_mem
  rw [← hs_coe]
  exact Measure.addHaar_affineSubspace volume s hs_ne_top

namespace StandardSphere

/-- Helper for Exercise 57.4: the square-root radicand defining the upper
hemisphere is nonnegative on the closed unit ball. -/
private theorem upperHemisphere_radicand_nonneg {n : ℕ} (y : ClosedUnitBall n) :
    0 ≤ 1 - ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 := by
  -- Closed-ball membership gives `‖y‖ ≤ 1`, which controls the square.
  have hy_norm : ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ ≤ 1 := by
    simpa [Real.norm_eq_abs] using Metric.mem_closedBall.mp y.property
  nlinarith [norm_nonneg (y : EuclideanSpace ℝ (Fin (n + 1)))]

/-- Helper for Exercise 57.4: the upper-hemisphere formula has unit norm. -/
private theorem upperHemispherePoint_mem_sphere {n : ℕ} (y : ClosedUnitBall n) :
    prependCoordinate (Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2)) y ∈
      StandardSphere (n + 1) := by
  -- The new coordinate supplies exactly the missing squared norm.
  rw [mem_sphere_zero_iff_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [prependCoordinate_norm_sq, Real.sq_sqrt (upperHemisphere_radicand_nonneg y)]
  ring

/-- Helper for Exercise 57.4: the upper-hemisphere extension is continuous. -/
private theorem continuous_upperHemispherePoint (n : ℕ) :
    Continuous (fun y : ClosedUnitBall n ↦
      (⟨prependCoordinate
          (Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2)) y,
        upperHemispherePoint_mem_sphere y⟩ : StandardSphere (n + 1))) := by
  -- Compose the continuous coordinate-adjoining map with the height and projection pair.
  have height_continuous : Continuous (fun y : ClosedUnitBall n ↦
      Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2)) := by
    fun_prop
  have vector_continuous : Continuous (fun y : ClosedUnitBall n ↦
      (y : EuclideanSpace ℝ (Fin (n + 1)))) := continuous_subtype_val
  exact Continuous.subtype_mk
    (continuous_prependCoordinate.comp (height_continuous.prodMk vector_continuous)) _

/-- Helper for Exercise 57.4: the upper hemisphere extends the equator over the
closed unit ball. -/
private def upperHemisphere (n : ℕ) : C(ClosedUnitBall n, StandardSphere (n + 1)) :=
  ⟨fun y ↦ ⟨prependCoordinate
      (Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2)) y,
    upperHemispherePoint_mem_sphere y⟩, continuous_upperHemispherePoint n⟩

/-- Helper for Exercise 57.4: the standard equator is the boundary restriction
of the upper-hemisphere extension. -/
private def equator (n : ℕ) : C(StandardSphere n, StandardSphere (n + 1)) :=
  (upperHemisphere n).comp (toBall n)

/-- Helper for Exercise 57.4: the equator has zero leading coordinate and the
original sphere point as its remaining coordinates. -/
private theorem equator_coe (n : ℕ) (x : StandardSphere n) :
    (equator n x : EuclideanSpace ℝ (Fin (n + 2))) = prependCoordinate 0 x := by
  -- On the boundary `‖x‖ = 1`, so the upper-hemisphere height is zero.
  rw [equator, ContinuousMap.comp_apply]
  simp only [upperHemisphere, ContinuousMap.coe_mk, toBall_apply]
  congr 1
  rw [mem_sphere_zero_iff_norm.mp x.property, one_pow, sub_self, Real.sqrt_zero]

/-- Helper for Exercise 57.4: the standard equator preserves antipodes. -/
private theorem equator_odd (n : ℕ) : Function.Odd (equator n) := by
  -- The ambient zero-leading-coordinate formula commutes with negation.
  intro x
  apply Subtype.ext
  calc
    (equator n (-x) : EuclideanSpace ℝ (Fin (n + 2))) = prependCoordinate 0 (-x) :=
      equator_coe n (-x)
    _ = prependCoordinate 0 (-(x : EuclideanSpace ℝ (Fin (n + 1)))) := by
      congr 1
    _ = -prependCoordinate 0 x := by
      rw [← prependCoordinate_neg, neg_zero]
    _ = -(equator n x : EuclideanSpace ℝ (Fin (n + 2))) :=
      congrArg Neg.neg (equator_coe n x).symm
    _ = ((-(equator n x) : StandardSphere (n + 1)) :
        EuclideanSpace ℝ (Fin (n + 2))) := rfl

/-- Helper for Exercise 57.4: the standard equator is nullhomotopic because it
extends over the contractible closed unit ball. -/
private theorem equator_nullhomotopic (n : ℕ) : (equator n).Nullhomotopic := by
  -- Restrict a nullhomotopic ball identity and then postcompose with the extension.
  have unit_radius_nonnegative : (0 : ℝ) ≤ 1 := by
    positivity
  letI : ContractibleSpace (ClosedUnitBall n) :=
    Metric.contractibleSpace_closedBall unit_radius_nonnegative
  have inclusion_null : (toBall n).Nullhomotopic :=
    (id_nullhomotopic (ClosedUnitBall n)).comp_left (toBall n)
  exact inclusion_null.comp_right (upperHemisphere n)

end StandardSphere

/-- Helper for Exercise 57.4 (1): if every continuous odd self-map of `Sⁿ` is not nullhomotopic,
then the unit sphere is not a retract of the unit closed ball. -/
theorem sphereNotRetractOfBall (n : ℕ)
    (h_odd_not_nullhomotopic : StandardSphere.OddSelfMapsNotNullhomotopic n) :
    ¬ Set.IsRetract (StandardSphere.boundary n) := by
  -- A retraction would make the sphere identity factor through the contractible ball.
  intro h_retract
  rw [Set.isRetract_iff] at h_retract
  obtain ⟨retractionMap, leftInverse⟩ := h_retract
  let retraction := Set.Retraction.ofContinuousMap retractionMap leftInverse
  have unit_radius_nonnegative : (0 : ℝ) ≤ 1 := by
    -- The unit closed ball has nonnegative radius.
    positivity
  letI : ContractibleSpace (ClosedUnitBall n) :=
    Metric.contractibleSpace_closedBall unit_radius_nonnegative
  have inclusion_null : (StandardSphere.toBall n).Nullhomotopic :=
    (id_nullhomotopic (ClosedUnitBall n)).comp_left (StandardSphere.toBall n)
  have composite_null :
      ((StandardSphere.ballBoundaryToSphere n).comp
        (retraction.toContinuousMap.comp (StandardSphere.toBall n))).Nullhomotopic :=
    (inclusion_null.comp_right retraction.toContinuousMap).comp_right
      (StandardSphere.ballBoundaryToSphere n)
  have composite_eq :
      (StandardSphere.ballBoundaryToSphere n).comp
          (retraction.toContinuousMap.comp (StandardSphere.toBall n)) =
        ContinuousMap.id (StandardSphere n) := by
    -- The retraction fixes boundary points, and the two sphere presentations agree there.
    apply ContinuousMap.ext
    intro x
    rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply]
    rw [← StandardSphere.sphereToBallBoundary_coe n x]
    rw [← Set.Retraction.apply_eq, retraction.apply_coe]
    exact StandardSphere.ballBoundaryToSphere_sphereToBallBoundary n x
  rw [composite_eq] at composite_null
  have identity_odd : Function.Odd (ContinuousMap.id (StandardSphere n)) := by
    -- The identity commutes with negation pointwise.
    intro x
    rfl
  exact h_odd_not_nullhomotopic.apply (ContinuousMap.id (StandardSphere n)) identity_odd
    composite_null

/-- Helper for Exercise 57.4 (2): if every continuous odd self-map of `Sⁿ` is not nullhomotopic,
then there is no continuous odd map from `Sⁿ⁺¹` to `Sⁿ`. -/
theorem notExistsOddMapSphereSucc (n : ℕ)
    (h_odd_not_nullhomotopic : StandardSphere.OddSelfMapsNotNullhomotopic n) :
    ¬ ∃ g : C(StandardSphere (n + 1), StandardSphere n), Function.Odd g := by
  -- Route correction: factor the equator through the contractible ball instead
  -- of constructing a time-parameterized sphere homotopy.
  rintro ⟨g, g_odd⟩
  have composite_odd : Function.Odd (g.comp (StandardSphere.equator n)) := by
    -- The composite of the two antipode-preserving maps is antipode-preserving.
    intro x
    rw [ContinuousMap.comp_apply, StandardSphere.equator_odd n x,
      ContinuousMap.comp_apply, g_odd]
  have composite_null : (g.comp (StandardSphere.equator n)).Nullhomotopic :=
    (StandardSphere.equator_nullhomotopic n).comp_right g
  exact h_odd_not_nullhomotopic.apply (g.comp (StandardSphere.equator n)) composite_odd
    composite_null

/-- Helper for Exercise 57.4 (3): Borsuk–Ulam states that odd self-maps of `Sⁿ`
being non-nullhomotopic forces every map from `Sⁿ⁺¹` to `ℝⁿ⁺¹` to identify an
antipodal pair. -/
theorem existsAntipodalEq (n : ℕ)
    (h_odd_not_nullhomotopic : StandardSphere.OddSelfMapsNotNullhomotopic n)
    (f : C(StandardSphere (n + 1), EuclideanSpace ℝ (Fin (n + 1)))) :
    ∃ x, f x = f (-x) := by
  -- Otherwise radial normalization produces the odd dimension-lowering map ruled out above.
  by_contra h_no_pair
  push Not at h_no_pair
  obtain ⟨g, g_odd⟩ := existsOddSphereMap_of_antipodal_ne f h_no_pair
  exact notExistsOddMapSphereSucc n h_odd_not_nullhomotopic ⟨g, g_odd⟩

/-- Helper for Exercise 57.4: on bounded support, disagreement between two
affine lower halfspaces lies in a slab around the first boundary. -/
private theorem inter_halfspaceDiff_subset_slab {m : ℕ}
    (A : Set (EuclideanSpace ℝ (Fin m))) (R ε c d : ℝ)
    (v w : EuclideanSpace ℝ (Fin m)) (hA_ball : A ⊆ Metric.closedBall 0 R)
    (hclose : ‖w - v‖ * R + |d - c| ≤ ε) :
    A ∩ ({x | inner ℝ w x ≤ d} \ {x | inner ℝ v x ≤ c}) ⊆
        {x | |inner ℝ v x - c| ≤ ε} ∧
      A ∩ ({x | inner ℝ v x ≤ c} \ {x | inner ℝ w x ≤ d}) ⊆
        {x | |inner ℝ v x - c| ≤ ε} := by
  -- Each direction uses the same uniform bound on the change of affine functional.
  have hinner_change (x : EuclideanSpace ℝ (Fin m)) (hxA : x ∈ A) :
      |inner ℝ (w - v) x| ≤ ‖w - v‖ * R := by
    have hxnorm : ‖x‖ ≤ R := by
      have hxball := hA_ball hxA
      simpa [Metric.mem_closedBall] using hxball
    exact (abs_real_inner_le_norm (w - v) x).trans
      (mul_le_mul_of_nonneg_left hxnorm (norm_nonneg _))
  constructor
  · -- If only the moving halfspace contains the point, it lies just above the fixed boundary.
    rintro x ⟨hxA, hxw, hxv⟩
    change inner ℝ w x ≤ d at hxw
    change ¬inner ℝ v x ≤ c at hxv
    change |inner ℝ v x - c| ≤ ε
    have hxv_strict : c < inner ℝ v x := lt_of_not_ge hxv
    have hchange := hinner_change x hxA
    have hlinear : inner ℝ w x = inner ℝ v x + inner ℝ (w - v) x := by
      rw [inner_sub_left]
      ring
    rw [abs_of_pos (sub_pos.mpr hxv_strict)]
    have hchange_lower : -(‖w - v‖ * R) ≤ inner ℝ (w - v) x :=
      neg_le_of_abs_le hchange
    have hoffset : d - c ≤ |d - c| := le_abs_self _
    linarith
  · -- If only the fixed halfspace contains the point, it lies just below its boundary.
    rintro x ⟨hxA, hxv, hxw⟩
    change inner ℝ v x ≤ c at hxv
    change ¬inner ℝ w x ≤ d at hxw
    change |inner ℝ v x - c| ≤ ε
    have hxw_strict : d < inner ℝ w x := lt_of_not_ge hxw
    have hchange := hinner_change x hxA
    have hlinear : inner ℝ w x = inner ℝ v x + inner ℝ (w - v) x := by
      rw [inner_sub_left]
      ring
    rw [abs_of_nonpos (sub_nonpos.mpr hxv)]
    have hchange_upper : inner ℝ (w - v) x ≤ ‖w - v‖ * R :=
      le_trans (le_abs_self _) hchange
    have hoffset : c - d ≤ |d - c| := by
      have : c - d ≤ |c - d| := le_abs_self (c - d)
      simpa [abs_sub_comm] using this
    linarith

/-- Helper for Exercise 57.4: bounded-support disagreement of two affine
halfspaces is contained in the same boundary slab. -/
private theorem inter_halfspaceSymmDiff_subset_slab {m : ℕ}
    (A : Set (EuclideanSpace ℝ (Fin m))) (R ε c d : ℝ)
    (v w : EuclideanSpace ℝ (Fin m)) (hA_ball : A ⊆ Metric.closedBall 0 R)
    (hclose : ‖w - v‖ * R + |d - c| ≤ ε) :
    A ∩ ({x | inner ℝ w x ≤ d} ∆ {x | inner ℝ v x ≤ c}) ⊆
      {x | |inner ℝ v x - c| ≤ ε} := by
  -- Split the symmetric difference into its two directional disagreements.
  obtain ⟨hforward, hbackward⟩ :=
    inter_halfspaceDiff_subset_slab A R ε c d v w hA_ball hclose
  rintro x ⟨hxA, hx⟩
  rw [Set.mem_symmDiff] at hx
  rcases hx with ⟨hxw, hxv⟩ | ⟨hxv, hxw⟩
  · exact hforward ⟨hxA, hxw, hxv⟩
  · exact hbackward ⟨hxA, hxv, hxw⟩

/-- Helper for Exercise 57.4: restricted volume of shrinking slabs around a
nonconstant affine level set tends to zero. -/
private theorem restrictedVolume_slab_tendsto_zero {m : ℕ}
    (A : Set (EuclideanSpace ℝ (Fin m))) (hA_bounded : Bornology.IsBounded A)
    (v : EuclideanSpace ℝ (Fin m))
    (c : ℝ) (hv : v ≠ 0) :
    Filter.Tendsto (fun k : ℕ ↦
      (volume.restrict A) {x | |inner ℝ v x - c| ≤ ((k + 1 : ℝ)⁻¹)})
      Filter.atTop (nhds 0) := by
  -- Work with one finite restricted measure throughout the decreasing limit.
  let μ : Measure (EuclideanSpace ℝ (Fin m)) := volume.restrict A
  let slabs : ℕ → Set (EuclideanSpace ℝ (Fin m)) :=
    fun k ↦ {x | |inner ℝ v x - c| ≤ ((k + 1 : ℝ)⁻¹)}
  letI : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.2 hA_bounded.measure_lt_top.ne
  have hslabs_measurable : ∀ k, MeasurableSet (slabs k) := by
    -- Each slab is a closed sublevel set of a continuous affine functional.
    intro k
    dsimp [slabs]
    exact measurableSet_le
      ((continuous_const.inner continuous_id).sub continuous_const).abs.measurable
      measurable_const
  have hslabs_antitone : Antitone slabs := by
    -- The reciprocal widths decrease with the natural index.
    intro k l hkl x hx
    dsimp [slabs] at hx ⊢
    exact hx.trans (inv_anti₀ (by positivity) (by
      exact_mod_cast Nat.add_le_add_right hkl 1))
  have hslabs_iInter : ⋂ k, slabs k = {x | inner ℝ v x = c} := by
    -- A real number lying in every reciprocal-width interval must be zero.
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro hx
      by_contra hne
      have hpos : 0 < |inner ℝ v x - c| := abs_pos.mpr (sub_ne_zero.mpr hne)
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
      have hxk := hx k
      dsimp [slabs] at hxk
      have : ((k + 1 : ℝ)⁻¹) < |inner ℝ v x - c| := by
        simpa [one_div] using hk
      exact (not_lt_of_ge hxk) this
    · intro hx k
      dsimp [slabs]
      rw [hx, sub_self, abs_zero]
      positivity
  have hboundary_zero : μ {x | inner ℝ v x = c} = 0 := by
    -- Restriction cannot give positive mass to the ambient null level set.
    have hlevel : MeasurableSet {x | inner ℝ v x = c} := by
      exact (isClosed_eq (continuous_const.inner continuous_id) continuous_const).measurableSet
    change (volume.restrict A) {x | inner ℝ v x = c} = 0
    rw [Measure.restrict_apply hlevel]
    exact measure_mono_null Set.inter_subset_left (volume_inner_levelSet_eq_zero v c hv)
  have hlimit := tendsto_measure_iInter_atTop
    (μ := μ) (fun k ↦ (hslabs_measurable k).nullMeasurableSet)
    hslabs_antitone ⟨0, measure_ne_top μ (slabs 0)⟩
  -- Rewrite the intersection to the null boundary and unfold the local names.
  rw [hslabs_iInter, hboundary_zero] at hlimit
  simpa [μ, slabs, Function.comp_def] using hlimit

/-- Helper for Exercise 57.4: restricted halfspace volume is continuous at a
parameter with nonzero normal. -/
private theorem restrictedVolume_halfspace_continuousAt_of_normal_ne_zero (n : ℕ)
    (A : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hA_bounded : Bornology.IsBounded A) (v : EuclideanSpace ℝ (Fin (n + 1)))
    (c : ℝ) (hv : v ≠ 0) :
    ContinuousAt (fun q : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦
      ((volume.restrict A) {x | inner ℝ q.1 x ≤ q.2}).toReal) (v, c) := by
  -- Route correction: control the real-volume difference by symmetric difference,
  -- then contain that disagreement in one shrinking slab.
  let μ : Measure (EuclideanSpace ℝ (Fin (n + 1))) := volume.restrict A
  letI : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.2 hA_bounded.measure_lt_top.ne
  obtain ⟨R, hR_pos, hA_ball⟩ := hA_bounded.subset_closedBall_lt 0 0
  have hslabs_real : Filter.Tendsto (fun k : ℕ ↦
      (μ {x | |inner ℝ v x - c| ≤ ((k + 1 : ℝ)⁻¹)}).toReal)
      Filter.atTop (nhds 0) := by
    rw [ENNReal.tendsto_toReal_zero_iff]
    simpa [μ] using restrictedVolume_slab_tendsto_zero A hA_bounded v c hv
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hsmall_eventually : ∀ᶠ k : ℕ in Filter.atTop,
      (μ {x | |inner ℝ v x - c| ≤ ((k + 1 : ℝ)⁻¹)}).toReal < ε :=
    hslabs_real (eventually_lt_nhds hε)
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 hsmall_eventually
  have hwidth_pos : 0 < ((k + 1 : ℝ)⁻¹) := by positivity
  have hnear : ∀ᶠ q : EuclideanSpace ℝ (Fin (n + 1)) × ℝ in nhds (v, c),
      ‖q.1 - v‖ * R + |q.2 - c| < ((k + 1 : ℝ)⁻¹) := by
    have hcontinuous : ContinuousAt
        (fun q : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦
          ‖q.1 - v‖ * R + |q.2 - c|) (v, c) := by
      fun_prop
    exact hcontinuous (eventually_lt_nhds (by simpa using hwidth_pos))
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.mem_nhds_iff.1 hnear
  refine ⟨δ, hδ_pos, ?_⟩
  intro q hq
  have hq_close := hδ (Metric.mem_ball.2 hq)
  let moving : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    {x | inner ℝ q.1 x ≤ q.2}
  let fixed : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    {x | inner ℝ v x ≤ c}
  let slab : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    {x | |inner ℝ v x - c| ≤ ((k + 1 : ℝ)⁻¹)}
  have hmoving : MeasurableSet moving := by
    exact measurableSet_le (continuous_const.inner continuous_id).measurable measurable_const
  have hfixed : MeasurableSet fixed := by
    exact measurableSet_le (continuous_const.inner continuous_id).measurable measurable_const
  have hslab : MeasurableSet slab := by
    exact measurableSet_le
      ((continuous_const.inner continuous_id).sub continuous_const).abs.measurable
      measurable_const
  have hdisagreement : A ∩ (moving ∆ fixed) ⊆ slab := by
    simpa [moving, fixed, slab] using inter_halfspaceSymmDiff_subset_slab
      A R ((k + 1 : ℝ)⁻¹) c q.2 v q.1 hA_ball hq_close.le
  have hsymm_bound : μ.real (moving ∆ fixed) ≤ μ.real slab := by
    change ((volume.restrict A) (moving ∆ fixed)).toReal ≤
      ((volume.restrict A) slab).toReal
    rw [Measure.restrict_apply (hmoving.symmDiff hfixed), Measure.restrict_apply hslab]
    have hsubset : moving ∆ fixed ∩ A ⊆ slab ∩ A := by
      intro x hx
      have hxslab := hdisagreement ⟨hx.2, hx.1⟩
      exact ⟨hxslab, hx.2⟩
    exact ENNReal.toReal_mono
      ((measure_mono Set.inter_subset_right).trans_lt hA_bounded.measure_lt_top).ne
      (measure_mono hsubset)
  have habs_bound : |μ.real moving - μ.real fixed| ≤ μ.real slab :=
    (abs_measureReal_sub_le_measureReal_symmDiff hmoving.nullMeasurableSet
      hfixed.nullMeasurableSet).trans hsymm_bound
  have hsmall : μ.real slab < ε := by
    exact hk k le_rfl
  change dist (μ.real moving) (μ.real fixed) < ε
  rw [Real.dist_eq]
  exact habs_bound.trans_lt hsmall

/-- Helper for Exercise 57.4: bounded support makes restricted halfspace volume
continuous at a zero-normal parameter with nonzero offset. -/
private theorem restrictedVolume_halfspace_continuousAt_zero_normal (n : ℕ)
    (A : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hA_bounded : Bornology.IsBounded A) (c : ℝ) (hc : c ≠ 0) :
    ContinuousAt (fun q : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦
      ((volume.restrict A) {x | inner ℝ q.1 x ≤ q.2}).toReal) (0, c) := by
  -- Bound the support in a positive-radius ball, then keep the moving linear
  -- term and moving offset error smaller than half the fixed offset.
  obtain ⟨R, hR_pos, hA_ball⟩ := hA_bounded.subset_closedBall_lt 0 0
  have hc_abs_pos : 0 < |c| := abs_pos.mpr hc
  have hnormal : ∀ᶠ q : EuclideanSpace ℝ (Fin (n + 1)) × ℝ in nhds (0, c),
      ‖q.1‖ * R < |c| / 2 := by
    have hcontinuous : ContinuousAt
        (fun q : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦ ‖q.1‖ * R) (0, c) :=
      continuousAt_fst.norm.mul_const R
    exact hcontinuous (eventually_lt_nhds (by simpa using half_pos hc_abs_pos))
  have hoffset : ∀ᶠ q : EuclideanSpace ℝ (Fin (n + 1)) × ℝ in nhds (0, c),
      |q.2 - c| < |c| / 2 := by
    have hcontinuous : ContinuousAt
        (fun q : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦ |q.2 - c|) (0, c) :=
      (continuousAt_snd.sub_const c).abs
    exact hcontinuous (eventually_lt_nhds (by simpa using half_pos hc_abs_pos))
  rcases lt_or_gt_of_ne hc with hc_neg | hc_pos
  · -- For a negative offset, nearby halfspaces miss the bounded support.
    apply Filter.EventuallyEq.continuousAt (y := 0)
    filter_upwards [hnormal, hoffset] with q hq_normal hq_offset
    have hdisjoint : A ∩ {x | inner ℝ q.1 x ≤ q.2} = ∅ := by
      ext x
      constructor
      · rintro ⟨hxA, hxhalf⟩
        change inner ℝ q.1 x ≤ q.2 at hxhalf
        have hxnorm : ‖x‖ ≤ R := by
          have hxball := hA_ball hxA
          simpa [Metric.mem_closedBall] using hxball
        have hinner_abs : |inner ℝ q.1 x| ≤ ‖q.1‖ * R :=
          (abs_real_inner_le_norm q.1 x).trans
            (mul_le_mul_of_nonneg_left hxnorm (norm_nonneg _))
        have hq2 : q.2 < c + |c| / 2 := by
          have := (le_abs_self (q.2 - c)).trans_lt hq_offset
          linarith
        have hc_half : c + |c| / 2 = c / 2 := by rw [abs_of_neg hc_neg]; ring
        have hinner_lower : -(‖q.1‖ * R) ≤ inner ℝ q.1 x := by
          exact (neg_le_of_abs_le hinner_abs)
        rw [hc_half] at hq2
        have hnormal_half : ‖q.1‖ * R < -c / 2 := by
          simpa [abs_of_neg hc_neg] using hq_normal
        linarith
      · intro hx
        exact hx.elim
    have hhalf_measurable : MeasurableSet {x | inner ℝ q.1 x ≤ q.2} := by
      exact measurableSet_le ((continuous_const.inner continuous_id).measurable) measurable_const
    rw [Measure.restrict_apply hhalf_measurable, Set.inter_comm, hdisjoint]
    simp
  · -- For a positive offset, nearby halfspaces contain the bounded support.
    apply Filter.EventuallyEq.continuousAt (y := (volume A).toReal)
    filter_upwards [hnormal, hoffset] with q hq_normal hq_offset
    have hcontain : A ∩ {x | inner ℝ q.1 x ≤ q.2} = A := by
      ext x
      constructor
      · exact And.left
      · intro hxA
        refine ⟨hxA, ?_⟩
        change inner ℝ q.1 x ≤ q.2
        have hxnorm : ‖x‖ ≤ R := by
          have hxball := hA_ball hxA
          simpa [Metric.mem_closedBall] using hxball
        have hinner_abs : |inner ℝ q.1 x| ≤ ‖q.1‖ * R :=
          (abs_real_inner_le_norm q.1 x).trans
            (mul_le_mul_of_nonneg_left hxnorm (norm_nonneg _))
        have hq2 : c - |c| / 2 < q.2 := by
          have := (abs_lt.mp hq_offset).1
          linarith
        have hc_half : c - |c| / 2 = c / 2 := by rw [abs_of_pos hc_pos]; ring
        have hinner_upper : inner ℝ q.1 x ≤ ‖q.1‖ * R := le_trans (le_abs_self _) hinner_abs
        rw [hc_half] at hq2
        have hnormal_half : ‖q.1‖ * R < c / 2 := by
          simpa [abs_of_pos hc_pos] using hq_normal
        linarith
    have hhalf_measurable : MeasurableSet {x | inner ℝ q.1 x ≤ q.2} := by
      exact measurableSet_le ((continuous_const.inner continuous_id).measurable) measurable_const
    rw [Measure.restrict_apply hhalf_measurable, Set.inter_comm, hcontain]

/-- Helper for Exercise 57.4: restricted volume of the oriented lower halfspace
is continuous on the compactified halfspace parameter sphere. -/
private theorem restrictedVolume_orientedHalfspace_continuous (n : ℕ)
    (A : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hA_bounded : Bornology.IsBounded A) :
    Continuous (fun p : StandardSphere (n + 1) ↦
      ((volume.restrict A) (orientedHalfspace p)).toReal) := by
  -- Compose the two product-space continuity regimes with the sphere coordinates.
  rw [continuous_iff_continuousAt]
  intro p
  have hcoordinates : ContinuousAt
      (fun q : StandardSphere (n + 1) ↦ (halfspaceNormal q, halfspaceOffset q)) p :=
    continuous_halfspaceNormal.continuousAt.prodMk continuous_halfspaceOffset.continuousAt
  by_cases hp : halfspaceNormal p = 0
  · have hc : halfspaceOffset p ≠ 0 := by
      intro hc
      have hsphere := halfspaceOffset_sq_add_normal_sq p
      rw [hp, hc, norm_zero] at hsphere
      norm_num at hsphere
    have hpole : ContinuousAt
        (fun q : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦
          ((volume.restrict A) {x | inner ℝ q.1 x ≤ q.2}).toReal)
        (halfspaceNormal p, halfspaceOffset p) := by
      simpa [hp] using restrictedVolume_halfspace_continuousAt_zero_normal n A
        hA_bounded (halfspaceOffset p) hc
    have hcomp : ContinuousAt
        ((fun q : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦
            ((volume.restrict A) {x | inner ℝ q.1 x ≤ q.2}).toReal) ∘
          fun q : StandardSphere (n + 1) ↦ (halfspaceNormal q, halfspaceOffset q)) p :=
      ContinuousAt.comp (f := fun q : StandardSphere (n + 1) ↦
        (halfspaceNormal q, halfspaceOffset q)) hpole hcoordinates
    simpa [Function.comp_def, orientedHalfspace, hp] using hcomp
  · have hregular := restrictedVolume_halfspace_continuousAt_of_normal_ne_zero n A
      hA_bounded (halfspaceNormal p) (halfspaceOffset p) hp
    have hcomp : ContinuousAt
        ((fun q : EuclideanSpace ℝ (Fin (n + 1)) × ℝ ↦
            ((volume.restrict A) {x | inner ℝ q.1 x ≤ q.2}).toReal) ∘
          fun q : StandardSphere (n + 1) ↦ (halfspaceNormal q, halfspaceOffset q)) p :=
      ContinuousAt.comp (f := fun q : StandardSphere (n + 1) ↦
        (halfspaceNormal q, halfspaceOffset q)) hregular hcoordinates
    simpa [Function.comp_def, orientedHalfspace] using hcomp

/-- Helper for Exercise 57.4: two equal finite complementary cuts with null
overlap each have half the total measure. -/
private theorem finiteMeasure_eq_half_of_oppositeCuts {α : Type*}
    [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (s t : Set α) (ht : MeasurableSet t) (hunion : s ∪ t = Set.univ)
    (hinter : μ (s ∩ t) = 0) (heq : μ s = μ t) :
    μ s = μ Set.univ / 2 := by
  -- Inclusion-exclusion reduces the claim to `2 * μ s = μ univ`.
  have hsum := measure_union_add_inter (μ := μ) s ht
  rw [hunion, hinter, add_zero, ← heq] at hsum
  apply (ENNReal.eq_div_iff (by norm_num) (by norm_num)).2
  simpa [two_mul] using hsum.symm

/-- Helper for Exercise 57.4: antipodally equal restricted halfspace volumes
produce a common unit-normal bisecting hyperplane. -/
private theorem antipodalRestrictedVolumes_imp_bisects (n : ℕ)
    (A : Fin (n + 1) → Set (EuclideanSpace ℝ (Fin (n + 1))))
    (_hA_measurable : ∀ i, MeasurableSet (A i))
    (hA_bounded : ∀ i, Bornology.IsBounded (A i)) (p : StandardSphere (n + 1))
    (h_balanced : ∀ i,
      ((volume.restrict (A i)) (orientedHalfspace p)).toReal =
        ((volume.restrict (A i)) (orientedHalfspace (-p))).toReal) :
    ∃ v : EuclideanSpace ℝ (Fin (n + 1)), ∃ c : ℝ,
      ‖v‖ = 1 ∧
        ∀ i, volume (A i ∩ {x | inner ℝ v x ≤ c}) = volume (A i) / 2 := by
  -- Split between genuine affine hyperplanes and the two pole parameters.
  let v₀ := halfspaceNormal p
  let c₀ := halfspaceOffset p
  by_cases hv₀ : v₀ = 0
  · -- At a pole, the balanced constant cuts force every set to have zero volume.
    have hc₀ : c₀ ≠ 0 := by
      intro hc₀
      have hsphere := halfspaceOffset_sq_add_normal_sq p
      rw [show halfspaceNormal p = v₀ from rfl, hv₀,
        show halfspaceOffset p = c₀ from rfl, hc₀, norm_zero] at hsphere
      norm_num at hsphere
    have hvolume_zero : ∀ i, volume (A i) = 0 := by
      intro i
      let μ : Measure (EuclideanSpace ℝ (Fin (n + 1))) := volume.restrict (A i)
      have hμ_finite : μ Set.univ ≠ ⊤ := by
        dsimp [μ]
        rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        exact (hA_bounded i).measure_lt_top.ne
      have hbalanced := h_balanced i
      rcases lt_or_gt_of_ne hc₀ with hc₀_neg | hc₀_pos
      · have hp_empty : orientedHalfspace p = ∅ := by
          ext x
          change inner ℝ v₀ x ≤ c₀ ↔ x ∈ ∅
          rw [hv₀, inner_zero_left]
          simp [not_le_of_gt hc₀_neg]
        have hneg_univ : orientedHalfspace (-p) = Set.univ := by
          ext x
          simp [orientedHalfspace, halfspaceNormal_neg, halfspaceOffset_neg,
            v₀, c₀, hv₀, hc₀_neg.le]
        rw [hp_empty, hneg_univ, measure_empty] at hbalanced
        have hμ_zero : μ Set.univ = 0 :=
          (ENNReal.toReal_eq_zero_iff (μ Set.univ)).mp hbalanced.symm |>.resolve_right hμ_finite
        simpa [μ, Measure.restrict_apply (_hA_measurable i)] using hμ_zero
      · have hp_univ : orientedHalfspace p = Set.univ := by
          ext x
          change inner ℝ v₀ x ≤ c₀ ↔ x ∈ Set.univ
          rw [hv₀, inner_zero_left]
          simp [hc₀_pos.le]
        have hneg_empty : orientedHalfspace (-p) = ∅ := by
          ext x
          change inner ℝ (-v₀) x ≤ -c₀ ↔ x ∈ ∅
          rw [hv₀, neg_zero, inner_zero_left]
          simp [hc₀_pos]
        rw [hp_univ, hneg_empty, measure_empty] at hbalanced
        have hμ_zero : μ Set.univ = 0 :=
          (ENNReal.toReal_eq_zero_iff (μ Set.univ)).mp hbalanced |>.resolve_right hμ_finite
        simpa [μ, Measure.restrict_apply (_hA_measurable i)] using hμ_zero
    let e : EuclideanSpace ℝ (Fin (n + 1)) :=
      (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (Pi.single 0 1)
    refine ⟨e, 0, ?_, ?_⟩
    · -- A coordinate unit vector supplies an arbitrary unit normal.
      simp [e]
    · intro i
      rw [hvolume_zero i]
      simpa using measure_mono_null Set.inter_subset_left (hvolume_zero i)
  · -- For a genuine normal, opposite cuts cover space and meet on a null boundary.
    have hv₀_norm : 0 < ‖v₀‖ := norm_pos_iff.mpr hv₀
    let scale : ℝ := ‖v₀‖⁻¹
    let v : EuclideanSpace ℝ (Fin (n + 1)) := scale • v₀
    let c : ℝ := scale * c₀
    have hscale_pos : 0 < scale := inv_pos.mpr hv₀_norm
    have hv_norm : ‖v‖ = 1 := by
      change ‖scale • v₀‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hscale_pos]
      change ‖v₀‖⁻¹ * ‖v₀‖ = 1
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv₀)
    have hnormalized_cut : {x | inner ℝ v x ≤ c} = {x | inner ℝ v₀ x ≤ c₀} := by
      ext x
      simp only [Set.mem_setOf_eq, v, c, real_inner_smul_left]
      simpa [mul_comm] using (mul_le_mul_iff_left₀ hscale_pos :
        inner ℝ v₀ x * scale ≤ c₀ * scale ↔ inner ℝ v₀ x ≤ c₀)
    refine ⟨v, c, hv_norm, ?_⟩
    intro i
    let μ : Measure (EuclideanSpace ℝ (Fin (n + 1))) := volume.restrict (A i)
    let lower : Set (EuclideanSpace ℝ (Fin (n + 1))) := {x | inner ℝ v₀ x ≤ c₀}
    let upper : Set (EuclideanSpace ℝ (Fin (n + 1))) := {x | c₀ ≤ inner ℝ v₀ x}
    letI : IsFiniteMeasure μ :=
      isFiniteMeasure_restrict.2 (hA_bounded i).measure_lt_top.ne
    have hlower_measurable : MeasurableSet lower := by
      exact measurableSet_le (continuous_const.inner continuous_id).measurable measurable_const
    have hupper_measurable : MeasurableSet upper := by
      exact measurableSet_le measurable_const (continuous_const.inner continuous_id).measurable
    have hp_lower : orientedHalfspace p = lower := by
      rfl
    have hneg_upper : orientedHalfspace (-p) = upper := by
      ext x
      simp [orientedHalfspace, halfspaceNormal_neg, halfspaceOffset_neg,
        upper, v₀, c₀]
    have hcuts_equal : μ lower = μ upper := by
      have hreal := h_balanced i
      rw [hp_lower, hneg_upper] at hreal
      exact (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp hreal
    have hunion : lower ∪ upper = Set.univ := by
      ext x
      simp [lower, upper, le_total]
    have hinter : μ (lower ∩ upper) = 0 := by
      have hboundary : lower ∩ upper = {x | inner ℝ v₀ x = c₀} := by
        ext x
        simp [lower, upper, le_antisymm_iff]
      rw [hboundary]
      have hlevel : MeasurableSet {x | inner ℝ v₀ x = c₀} :=
        (isClosed_eq (continuous_const.inner continuous_id) continuous_const).measurableSet
      change (volume.restrict (A i)) {x | inner ℝ v₀ x = c₀} = 0
      rw [Measure.restrict_apply hlevel]
      exact measure_mono_null Set.inter_subset_left
        (volume_inner_levelSet_eq_zero v₀ c₀ hv₀)
    have hhalf : μ lower = μ Set.univ / 2 :=
      finiteMeasure_eq_half_of_oppositeCuts μ lower upper hupper_measurable
        hunion hinter hcuts_equal
    rw [hnormalized_cut]
    change volume (A i ∩ lower) = volume (A i) / 2
    have hlower_restrict : μ lower = volume (A i ∩ lower) := by
      change (volume.restrict (A i)) lower = volume (A i ∩ lower)
      rw [Measure.restrict_apply hlower_measurable, Set.inter_comm]
    have huniv_restrict : μ Set.univ = volume (A i) := by
      simp [μ]
    simpa [hlower_restrict, huniv_restrict] using hhalf

/-- Exercise 57.4 (4). If every continuous odd self-map of `Sⁿ` is not nullhomotopic,
then any `n + 1` bounded measurable subsets of `ℝⁿ⁺¹` have a common bisecting affine
hyperplane, represented by a unit normal and an offset. -/
theorem existsHyperplaneBisects (n : ℕ)
    (h_odd_not_nullhomotopic : StandardSphere.OddSelfMapsNotNullhomotopic n)
    (A : Fin (n + 1) → Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hA_measurable : ∀ i, MeasurableSet (A i))
    (hA_bounded : ∀ i, Bornology.IsBounded (A i)) :
    ∃ v : EuclideanSpace ℝ (Fin (n + 1)), ∃ c : ℝ,
      ‖v‖ = 1 ∧
        ∀ i, volume (A i ∩ {x | inner ℝ v x ≤ c}) = volume (A i) / 2 := by
  -- Assemble the scalar restricted volumes into one Euclidean-valued map.
  let volumeVector : C(StandardSphere (n + 1), EuclideanSpace ℝ (Fin (n + 1))) :=
    ⟨fun p ↦ (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
        (fun i ↦ ((volume.restrict (A i)) (orientedHalfspace p)).toReal), by
      apply (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.continuous.comp
      apply continuous_pi
      intro i
      exact restrictedVolume_orientedHalfspace_continuous n (A i)
        (hA_bounded i)⟩
  -- Borsuk--Ulam supplies one parameter with all restricted volumes balanced.
  obtain ⟨p, hp⟩ := existsAntipodalEq n h_odd_not_nullhomotopic volumeVector
  apply antipodalRestrictedVolumes_imp_bisects n A hA_measurable hA_bounded p
  intro i
  have hi := congrArg
    (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦
      EuclideanSpace.equiv (Fin (n + 1)) ℝ z i) hp
  simpa [volumeVector] using hi
