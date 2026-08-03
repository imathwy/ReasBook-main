module

public import Topology_Munkres_2000.Book.Definition_60_3.Quotient
public import Topology_Munkres_2000.Book.Exercise_60_2.Quotient
import all Topology_Munkres_2000.Book.Definition_21_3.ClosedUnitDisk
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Topology.Separation.Hausdorff

public section

noncomputable section

namespace DiskAntipodalQuotient

open ClosedUnitDisk

/-- Helper for Exercise 60.2: adjoining a leading real coordinate to a vector in
`EuclideanSpace ℝ (Fin 2)`. -/
private def prependCoordinate (c : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm
    (Fin.cons c (EuclideanSpace.equiv (Fin 2) ℝ v))

/-- Helper for Exercise 60.2: the first coordinate of a vector in
`EuclideanSpace ℝ (Fin 3)`. -/
private def leadingCoordinate (z : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  EuclideanSpace.equiv (Fin 3) ℝ z 0

/-- Helper for Exercise 60.2: the two coordinates following the first coordinate. -/
private def tailCoordinates (z : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm
    (Fin.tail (EuclideanSpace.equiv (Fin 3) ℝ z))

/-- Helper for Exercise 60.2: adjoining a leading coordinate splits the squared norm. -/
private lemma prependCoordinate_norm_sq (c : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    ‖prependCoordinate c v‖ ^ 2 = c ^ 2 + ‖v‖ ^ 2 := by
  -- Ordinary finite coordinates split the sum of squares at the first coordinate.
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_succ]
  simp [prependCoordinate]

/-- Helper for Exercise 60.2: adjoining the extracted leading and tail coordinates
reconstructs a vector. -/
private lemma prependCoordinate_leading_tail (z : EuclideanSpace ℝ (Fin 3)) :
    prependCoordinate (leadingCoordinate z) (tailCoordinates z) = z := by
  -- Apply the coordinate equivalence and check the head and tail separately.
  apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
  rw [prependCoordinate, ContinuousLinearEquiv.apply_symm_apply]
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rfl
  · change (EuclideanSpace.equiv (Fin 3) ℝ z) j.succ = _
    rfl

/-- Helper for Exercise 60.2: extracting the tail after adjoining a coordinate
recovers the original vector. -/
private lemma tailCoordinates_prependCoordinate (c : ℝ)
    (v : EuclideanSpace ℝ (Fin 2)) :
    tailCoordinates (prependCoordinate c v) = v := by
  -- Both coordinate equivalences cancel, leaving `Fin.tail (Fin.cons c v)`.
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  rw [tailCoordinates, prependCoordinate, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- Helper for Exercise 60.2: extracting the leading coordinate after adjoining it
recovers that coordinate. -/
private lemma leadingCoordinate_prependCoordinate (c : ℝ)
    (v : EuclideanSpace ℝ (Fin 2)) :
    leadingCoordinate (prependCoordinate c v) = c := by
  -- The zeroth coordinate of `Fin.cons c v` is `c`.
  simp [leadingCoordinate, prependCoordinate]

/-- Helper for Exercise 60.2: adjoining a coordinate commutes with negation. -/
private lemma prependCoordinate_neg (c : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    prependCoordinate (-c) (-v) = -prependCoordinate c v := by
  -- Compare ordinary coordinates, where head and tail negate pointwise.
  apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
  simp only [prependCoordinate, ContinuousLinearEquiv.apply_symm_apply, map_neg]
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simp

/-- Helper for Exercise 60.2: the leading coordinate changes sign under negation. -/
private lemma leadingCoordinate_neg (z : EuclideanSpace ℝ (Fin 3)) :
    leadingCoordinate (-z) = -leadingCoordinate z := by
  -- The Euclidean coordinate equivalence is linear.
  simp [leadingCoordinate]

/-- Helper for Exercise 60.2: the tail coordinates change sign under negation. -/
private lemma tailCoordinates_neg (z : EuclideanSpace ℝ (Fin 3)) :
    tailCoordinates (-z) = -tailCoordinates z := by
  -- Compare ordinary coordinates; the tail of a pointwise negation is pointwise negated.
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  simp only [tailCoordinates, ContinuousLinearEquiv.apply_symm_apply, map_neg]
  rfl

/-- Helper for Exercise 60.2: adjoining a varying head to a varying tail is continuous. -/
private lemma continuous_prependCoordinate :
    Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin 2) ↦
      prependCoordinate p.1 p.2) := by
  -- Check continuity coordinatewise after applying the Euclidean equivalence.
  apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact continuous_fst
  · exact (continuous_apply j).comp
      ((EuclideanSpace.equiv (Fin 2) ℝ).continuous.comp continuous_snd)

/-- Helper for Exercise 60.2: the square-root radicand for a disk point is nonnegative. -/
private lemma upperHemisphere_radicand_nonneg (x : B²) :
    0 ≤ 1 - ‖(x : EuclideanSpace ℝ (Fin 2))‖ ^ 2 := by
  -- Membership in the closed unit disk bounds the norm by one.
  have hx : ‖(x : EuclideanSpace ℝ (Fin 2))‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
  nlinarith [norm_nonneg (x : EuclideanSpace ℝ (Fin 2))]

/-- Helper for Exercise 60.2: the upper-hemisphere coordinate formula has unit norm. -/
private lemma upperHemispherePoint_mem_sphere (x : B²) :
    prependCoordinate (Real.sqrt (1 - ‖(x : EuclideanSpace ℝ (Fin 2))‖ ^ 2)) x ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  -- The new coordinate supplies the difference between one and the squared disk norm.
  rw [mem_sphere_zero_iff_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [prependCoordinate_norm_sq, Real.sq_sqrt (upperHemisphere_radicand_nonneg x)]
  ring

/-- Helper for Exercise 60.2: a disk point mapped to the closed upper hemisphere of `S²`. -/
private def upperHemispherePoint (x : B²) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨prependCoordinate (Real.sqrt (1 - ‖(x : EuclideanSpace ℝ (Fin 2))‖ ^ 2)) x,
    upperHemispherePoint_mem_sphere x⟩

/-- Helper for Exercise 60.2: the upper-hemisphere map is continuous. -/
private lemma continuous_upperHemispherePoint : Continuous upperHemispherePoint := by
  -- Compose the continuous height-and-tail pair with coordinate adjoining.
  have heightContinuous : Continuous (fun x : B² ↦
      Real.sqrt (1 - ‖(x : EuclideanSpace ℝ (Fin 2))‖ ^ 2)) := by
    fun_prop
  have tailContinuous : Continuous (fun x : B² ↦
      (x : EuclideanSpace ℝ (Fin 2))) := continuous_subtype_val
  exact Continuous.subtype_mk
    (continuous_prependCoordinate.comp (heightContinuous.prodMk tailContinuous)) _

/-- Helper for Exercise 60.2: the tail of an upper-hemisphere point is its disk point. -/
private lemma tailCoordinates_upperHemispherePoint (x : B²) :
    tailCoordinates (upperHemispherePoint x : EuclideanSpace ℝ (Fin 3)) = x := by
  -- Unpack only the coordinate interface of the upper-hemisphere construction.
  exact tailCoordinates_prependCoordinate _ _

/-- Helper for Exercise 60.2: the leading and tail coordinates of a point of `S²`
satisfy the unit-sphere equation. -/
private lemma leading_sq_add_tail_norm_sq
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    leadingCoordinate z ^ 2 + ‖tailCoordinates z‖ ^ 2 = 1 := by
  -- Reconstruct the ambient vector, split its norm, and use sphere membership.
  calc
    leadingCoordinate z ^ 2 + ‖tailCoordinates z‖ ^ 2 =
        ‖prependCoordinate (leadingCoordinate z) (tailCoordinates z)‖ ^ 2 :=
      (prependCoordinate_norm_sq _ _).symm
    _ = ‖(z : EuclideanSpace ℝ (Fin 3))‖ ^ 2 := by
      rw [prependCoordinate_leading_tail]
    _ = 1 := by
      rw [mem_sphere_zero_iff_norm.mp z.property]
      norm_num

/-- Helper for Exercise 60.2: the tail coordinates of a unit sphere point lie in `B²`. -/
private lemma tailCoordinates_mem_closedBall
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    tailCoordinates z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  -- The unit-sphere equation bounds the squared tail norm by one.
  rw [Metric.mem_closedBall, dist_zero_right]
  nlinarith [leading_sq_add_tail_norm_sq z, norm_nonneg (tailCoordinates z)]

/-- Helper for Exercise 60.2: the tail of a sphere point, regarded as a disk point. -/
private def sphereTailPoint
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : B² :=
  ⟨tailCoordinates z, tailCoordinates_mem_closedBall z⟩

/-- Helper for Exercise 60.2: a sphere point with nonnegative leading coordinate is
recovered from its tail by the upper-hemisphere map. -/
private lemma upperHemispherePoint_sphereTailPoint
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hz : 0 ≤ leadingCoordinate z) :
    upperHemispherePoint (sphereTailPoint z) = z := by
  -- The sphere equation identifies the square-root height with the nonnegative head.
  have hrad : 1 - ‖tailCoordinates z‖ ^ 2 = leadingCoordinate z ^ 2 := by
    nlinarith [leading_sq_add_tail_norm_sq z]
  have hheight : Real.sqrt (1 - ‖tailCoordinates z‖ ^ 2) = leadingCoordinate z := by
    rw [hrad, Real.sqrt_sq_eq_abs, abs_of_nonneg hz]
  apply Subtype.ext
  calc
    (upperHemispherePoint (sphereTailPoint z) : EuclideanSpace ℝ (Fin 3)) =
        prependCoordinate (Real.sqrt (1 - ‖tailCoordinates z‖ ^ 2))
          (tailCoordinates z) := rfl
    _ = prependCoordinate (leadingCoordinate z) (tailCoordinates z) := by
      rw [hheight]
    _ = z := prependCoordinate_leading_tail z

/-- Helper for Exercise 60.2: every antipodal class on `S²` has an
upper-hemisphere representative coming from `B²`. -/
private lemma exists_upperHemispherePoint_eq_or_eq_neg
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∃ x : B², upperHemispherePoint x = z ∨ upperHemispherePoint x = -z := by
  -- Choose the tail of `z` or of `-z`, according to the sign of the first coordinate.
  by_cases hz : 0 ≤ leadingCoordinate z
  · exact ⟨sphereTailPoint z, Or.inl (upperHemispherePoint_sphereTailPoint z hz)⟩
  · have hneg : 0 ≤ leadingCoordinate (-(z : EuclideanSpace ℝ (Fin 3))) := by
      rw [leadingCoordinate_neg]
      exact neg_nonneg.mpr (le_of_not_ge hz)
    exact ⟨sphereTailPoint (-z),
      Or.inr (upperHemispherePoint_sphereTailPoint (-z) hneg)⟩

/-- Helper for Exercise 60.2: on the boundary, the upper-hemisphere map commutes
with the disk antipode. -/
private lemma upperHemispherePoint_neg_of_isBoundary (x : B²)
    (hx : IsBoundary x) :
    upperHemispherePoint (-x) = -upperHemispherePoint x := by
  -- Boundary points have zero height, so only their tail coordinates are negated.
  have hxNorm : ‖(x : EuclideanSpace ℝ (Fin 2))‖ = 1 := hx
  have hxHeight : Real.sqrt (1 - ‖(x : EuclideanSpace ℝ (Fin 2))‖ ^ 2) = 0 := by
    rw [hxNorm]
    norm_num
  have hnegHeight : Real.sqrt
      (1 - ‖((-x : B²) : EuclideanSpace ℝ (Fin 2))‖ ^ 2) = 0 := by
    simp only [coe_neg_closedBall, norm_neg, hxNorm]
    norm_num
  apply Subtype.ext
  change prependCoordinate
      (Real.sqrt (1 - ‖((-x : B²) : EuclideanSpace ℝ (Fin 2))‖ ^ 2)) (-x) =
    -prependCoordinate (Real.sqrt (1 - ‖(x : EuclideanSpace ℝ (Fin 2))‖ ^ 2)) x
  rw [hnegHeight, hxHeight]
  simpa only [neg_zero] using prependCoordinate_neg 0 (x : EuclideanSpace ℝ (Fin 2))

/-- Helper for Exercise 60.2: the natural map from `B²` to the real projective plane. -/
private def projectiveMap (x : B²) : RealProjectivePlane :=
  RealProjectivePlane.quotientMap (upperHemispherePoint x)

/-- Helper for Exercise 60.2: the fibers of `projectiveMap` are precisely equal
points or antipodal boundary pairs. -/
private lemma projectiveMap_fiber_iff (x y : B²) :
    projectiveMap x = projectiveMap y ↔
      y = x ∨ (IsBoundary x ∧ y = -x) := by
  -- First reduce equality in projective space to equality or antipodality on `S²`.
  rw [projectiveMap, projectiveMap, RealProjectivePlane.quotientMap_eq_iff]
  constructor
  · intro h
    rcases h with h | h
    · left
      apply Subtype.ext
      have htail := congrArg
        (fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦
          tailCoordinates (z : EuclideanSpace ℝ (Fin 3))) h
      simpa only [tailCoordinates_upperHemispherePoint] using htail
    · right
      have hleading := congrArg
        (fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦
          leadingCoordinate (z : EuclideanSpace ℝ (Fin 3))) h
      have hheight : Real.sqrt (1 - ‖(y : EuclideanSpace ℝ (Fin 2))‖ ^ 2) =
          -Real.sqrt (1 - ‖(x : EuclideanSpace ℝ (Fin 2))‖ ^ 2) := by
        simpa only [upperHemispherePoint, leadingCoordinate_prependCoordinate, coe_neg_sphere,
          leadingCoordinate_neg] using hleading
      have hxHeight : Real.sqrt (1 - ‖(x : EuclideanSpace ℝ (Fin 2))‖ ^ 2) = 0 := by
        nlinarith [Real.sqrt_nonneg (1 - ‖(x : EuclideanSpace ℝ (Fin 2))‖ ^ 2),
          Real.sqrt_nonneg (1 - ‖(y : EuclideanSpace ℝ (Fin 2))‖ ^ 2)]
      have hxBoundary : IsBoundary x := by
        have hrad := (Real.sqrt_eq_zero (upperHemisphere_radicand_nonneg x)).mp hxHeight
        rw [IsBoundary]
        nlinarith [norm_nonneg (x : EuclideanSpace ℝ (Fin 2))]
      refine ⟨hxBoundary, ?_⟩
      apply Subtype.ext
      have htail := congrArg
        (fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦
          tailCoordinates (z : EuclideanSpace ℝ (Fin 3))) h
      simpa only [tailCoordinates_upperHemispherePoint, coe_neg_sphere,
        tailCoordinates_neg, coe_neg_closedBall] using htail
  · intro h
    rcases h with rfl | ⟨hx, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (upperHemispherePoint_neg_of_isBoundary x hx)

/-- Helper for Exercise 60.2: the natural disk-to-projective-plane map is continuous. -/
private lemma continuous_projectiveMap : Continuous projectiveMap := by
  -- Compose the upper-hemisphere map with the continuous projective quotient map.
  exact RealProjectivePlane.quotientMap_isQuotientMap.continuous.comp
    continuous_upperHemispherePoint

/-- Helper for Exercise 60.2: the natural disk-to-projective-plane map is surjective. -/
private lemma projectiveMap_surjective : Function.Surjective projectiveMap := by
  -- Choose a sphere representative, then replace it by its upper-hemisphere representative.
  intro q
  obtain ⟨z, rfl⟩ := RealProjectivePlane.quotientMap_isQuotientMap.surjective q
  obtain ⟨x, hx | hx⟩ := exists_upperHemispherePoint_eq_or_eq_neg z
  · refine ⟨x, ?_⟩
    rw [projectiveMap, hx]
  · refine ⟨x, ?_⟩
    rw [projectiveMap, hx, RealProjectivePlane.quotientMap_neg]

/-- Helper for Exercise 60.2: saturating a subset of `S²` under the projective
quotient adds precisely its antipodal preimage. -/
private lemma projectiveQuotientMap_preimage_image (U : Set
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    RealProjectivePlane.quotientMap ⁻¹' (RealProjectivePlane.quotientMap '' U) =
      U ∪ (fun z ↦ -z) ⁻¹' U := by
  -- Expand equality of quotient images and sort the equal and antipodal cases.
  ext z
  constructor
  · rintro ⟨w, hw, hqw⟩
    rcases (RealProjectivePlane.quotientMap_eq_iff w z).mp hqw with h | h
    · left
      rwa [h]
    · right
      simpa only [Set.mem_preimage, h, neg_neg] using hw
  · intro hz
    rcases hz with hz | hz
    · exact ⟨z, hz, rfl⟩
    · exact ⟨-z, hz, RealProjectivePlane.quotientMap_neg z⟩

/-- Helper for Exercise 60.2: the antipodal quotient map from `S²` is open. -/
private lemma projectiveQuotientMap_isOpenMap :
    IsOpenMap RealProjectivePlane.quotientMap := by
  -- Openness is checked after taking the quotient-map preimage, whose saturation is explicit.
  intro U hU
  apply RealProjectivePlane.quotientMap_isQuotientMap.isCoinducing.isOpen_preimage.mp
  rw [projectiveQuotientMap_preimage_image]
  exact hU.union (hU.preimage continuous_neg)

/-- Helper for Exercise 60.2: the projective quotient map from `S²` is an open
quotient map. -/
private lemma projectiveQuotientMap_isOpenQuotientMap :
    IsOpenQuotientMap RealProjectivePlane.quotientMap := by
  -- Combine the owner-provided quotient property with the open-map calculation.
  exact IsOpenQuotientMap.of_isOpenMap_isQuotientMap
    projectiveQuotientMap_isOpenMap RealProjectivePlane.quotientMap_isQuotientMap

/-- Helper for Exercise 60.2: the fiber relation of the antipodal sphere quotient
is closed. -/
private lemma projectiveQuotientMap_fiberRelation_isClosed :
    IsClosed {q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ×
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 |
      RealProjectivePlane.quotientMap q.1 = RealProjectivePlane.quotientMap q.2} := by
  -- The relation is the union of the diagonal and the graph of the antipodal map.
  simpa only [RealProjectivePlane.quotientMap_eq_iff, Set.setOf_or,
    Function.comp_apply] using
    (isClosed_eq continuous_snd continuous_fst).union
      (isClosed_eq continuous_snd (continuous_neg.comp continuous_fst))

/-- Helper for Exercise 60.2: the natural disk-to-projective-plane map is a
quotient map. -/
private lemma projectiveMap_isQuotientMap :
    Topology.IsQuotientMap projectiveMap := by
  -- The closed fiber relation makes the open sphere quotient Hausdorff locally.
  letI : T2Space RealProjectivePlane :=
    (t2Space_iff_of_isOpenQuotientMap projectiveQuotientMap_isOpenQuotientMap).mpr
      projectiveQuotientMap_fiberRelation_isClosed
  -- A continuous surjection from the compact disk to that Hausdorff quotient is quotient.
  exact Topology.IsQuotientMap.of_surjective_continuous
    projectiveMap_surjective continuous_projectiveMap

/-- Helper for Exercise 60.2: the natural comparison map bundled as a continuous map. -/
private def projectiveMapContinuous : C(B², RealProjectivePlane) :=
  ⟨projectiveMap, continuous_projectiveMap⟩

end DiskAntipodalQuotient

/-- Exercise 60.2: the quotient of `B²` identifying antipodal boundary points is
homeomorphic to the real projective plane `P²`. -/
theorem diskAntipodalQuotientHomeomorphicProjectivePlane :
    Nonempty (DiskAntipodalQuotient.Space ≃ₜ RealProjectivePlane) := by
  -- Identify the disk setoid with the kernel of the natural projective comparison map.
  have hkernel : ∀ x y : B², DiskAntipodalQuotient.setoid x y ↔
      Setoid.ker DiskAntipodalQuotient.projectiveMapContinuous x y := by
    intro x y
    change DiskAntipodalQuotient.setoid x y ↔
      DiskAntipodalQuotient.projectiveMap x = DiskAntipodalQuotient.projectiveMap y
    rw [DiskAntipodalQuotient.setoid_rel_iff,
      DiskAntipodalQuotient.projectiveMap_fiber_iff]
  have hquotient : Topology.IsQuotientMap
      DiskAntipodalQuotient.projectiveMapContinuous := by
    -- Bundling the continuous map does not change its underlying quotient property.
    exact DiskAntipodalQuotient.projectiveMap_isQuotientMap
  -- Compose the relation-change homeomorphism with the canonical kernel quotient homeomorphism.
  exact ⟨(Homeomorph.Quotient.congrRight hkernel).trans hquotient.homeomorph⟩
