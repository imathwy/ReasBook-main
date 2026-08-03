module

public import Topology_Munkres_2000.Book.Exercise_60_2
public import Topology_Munkres_2000.Book.Theorem_22_1
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import all Topology_Munkres_2000.Book.Definition_21_3.ClosedUnitDisk

public section

open Set ClosedUnitDisk

namespace DiskAntipodalQuotient

/-- Helper for Example 74.8: the ambient Euclidean plane of the disk model. -/
abbrev DiskPlane := EuclideanSpace ℝ (Fin 2)

/-- Helper for Example 74.8: the open interior of the closed unit disk. -/
def interior : Set B² :=
  {point | ‖(point : DiskPlane)‖ < 1}

/-- Helper for Example 74.8: disk-interior membership is ambient open-ball membership. -/
lemma mem_interior_iff_mem_ball (point : B²) :
    point ∈ interior ↔ (point : DiskPlane) ∈ Metric.ball (0 : DiskPlane) 1 := by
  -- Both predicates assert that the ambient norm is strictly less than one.
  rw [interior, Metric.mem_ball, dist_zero_right]
  rfl

/-- Helper for Example 74.8: the interior is open in the closed disk. -/
lemma isOpen_interior : IsOpen interior := by
  -- Pull the ambient open unit ball back along the closed-disk inclusion.
  have hpreimage :
      ((↑) : B² → DiskPlane) ⁻¹' Metric.ball (0 : DiskPlane) 1 = interior := by
    ext point
    exact (mem_interior_iff_mem_ball point).symm
  rw [← hpreimage]
  exact Metric.isOpen_ball.preimage continuous_subtype_val

/-- Helper for Example 74.8: the disk interior is saturated under the boundary-antipodal
quotient. -/
lemma interior_isSaturated : Set.IsSaturated quotientMap interior := by
  -- A nontrivial quotient fiber starts at a boundary point, which cannot be interior.
  rw [Set.isSaturated_iff_mem_of_eq]
  intro point other hpoint hfiber
  rcases (quotientMap_eq_iff point other).mp hfiber.symm with hsame | ⟨hboundary, _⟩
  · rwa [hsame]
  · rw [interior] at hpoint
    rw [ClosedUnitDisk.IsBoundary] at hboundary
    exact (ne_of_lt hpoint hboundary).elim

/-- Helper for Example 74.8: the quotient map is injective when restricted to the disk
interior. -/
lemma interiorQuotient_injective :
    Function.Injective (interior.restrict quotientMap) := by
  intro point other hfiber
  -- Equality in the quotient has no boundary-antipode branch for an interior point.
  have hpoint : ‖(↑(point : B²) : DiskPlane)‖ < 1 := point.property
  apply Subtype.ext
  rcases (quotientMap_eq_iff point other).mp hfiber with hsame | ⟨hboundary, _⟩
  · exact hsame.symm
  · rw [ClosedUnitDisk.IsBoundary] at hboundary
    exact (ne_of_lt hpoint hboundary).elim

/-- Helper for Example 74.8: corestricting the interior quotient to its range preserves
injectivity. -/
lemma interiorQuotientRangeFactorization_injective :
    Function.Injective
      (Set.rangeFactorization (interior.restrict quotientMap)) := by
  intro point other hfiber
  -- Forgetting range membership reduces the claim to injectivity of the restricted map.
  exact interiorQuotient_injective (congrArg Subtype.val hfiber)

/-- Helper for Example 74.8: the quotient map restricts to an open embedding on the disk
interior. -/
lemma interiorQuotient_isOpenEmbedding :
    Topology.IsOpenEmbedding (interior.restrict quotientMap) := by
  -- The saturated open restriction is a homeomorphism onto its range.
  have hrangeHomeomorph :
      IsHomeomorph
        (Set.rangeFactorization (interior.restrict quotientMap)) := by
    rw [isHomeomorph_iff_isQuotientMap_injective]
    exact ⟨quotientMap_isQuotientMap.restrictImage_of_isOpen_or_isClosed
        interior_isSaturated (Or.inl isOpen_interior),
      interiorQuotientRangeFactorization_injective⟩
  -- Saturation also makes that range an open subset of the quotient.
  have hrangeOpen : IsOpen (Set.range (interior.restrict quotientMap)) := by
    rw [Set.range_restrict, ← quotientMap_isQuotientMap.isOpen_preimage,
      Set.isSaturated_iff_preimage_image.mp interior_isSaturated]
    exact isOpen_interior
  -- Compose the range homeomorphism with the open-subset inclusion.
  exact hrangeOpen.isOpenEmbedding_subtypeVal.comp hrangeHomeomorph.isOpenEmbedding

/-- Helper for Example 74.8: an interior disk point determines a point of the ambient open
unit ball. -/
private def interiorToBall (point : interior) : Metric.ball (0 : DiskPlane) 1 :=
  ⟨point, (mem_interior_iff_mem_ball point).mp point.property⟩

/-- Helper for Example 74.8: an ambient open-unit-ball point determines an interior point of
the closed disk. -/
private def ballToInterior (point : Metric.ball (0 : DiskPlane) 1) : interior :=
  ⟨⟨point, Metric.ball_subset_closedBall point.property⟩,
    (mem_interior_iff_mem_ball ⟨point, Metric.ball_subset_closedBall point.property⟩).mpr
      point.property⟩

/-- Helper for Example 74.8: passing from the disk interior to the ambient ball and back fixes
the point. -/
private lemma ballToInterior_interiorToBall (point : interior) :
    ballToInterior (interiorToBall point) = point := by
  -- Compare first the closed-disk values and then their ambient Euclidean values.
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- Helper for Example 74.8: passing from the ambient ball to the disk interior and back fixes
the point. -/
private lemma interiorToBall_ballToInterior (point : Metric.ball (0 : DiskPlane) 1) :
    interiorToBall (ballToInterior point) = point := by
  -- The two ball points have the same ambient Euclidean value.
  apply Subtype.ext
  rfl

/-- Helper for Example 74.8: the inclusion from the disk interior to the ambient ball is
continuous. -/
private lemma continuous_interiorToBall : Continuous interiorToBall := by
  -- Both layers are subtype inclusions.
  exact Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) _

/-- Helper for Example 74.8: the inclusion from the ambient ball into the disk interior is
continuous. -/
private lemma continuous_ballToInterior : Continuous ballToInterior := by
  -- Build the two nested subtype layers from the continuous ambient inclusion.
  exact Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val _) _

/-- Helper for Example 74.8: the disk interior is canonically homeomorphic to the ambient open
unit ball. -/
def interiorHomeomorphBall : interior ≃ₜ Metric.ball (0 : DiskPlane) 1 where
  toFun := interiorToBall
  invFun := ballToInterior
  left_inv := ballToInterior_interiorToBall
  right_inv := interiorToBall_ballToInterior
  continuous_toFun := continuous_interiorToBall
  continuous_invFun := continuous_ballToInterior

/-- Helper for Example 74.8: global Euclidean coordinates identify the plane with the disk
interior. -/
noncomputable def planeHomeomorphInterior : DiskPlane ≃ₜ interior :=
  Homeomorph.unitBall.trans interiorHomeomorphBall.symm

end DiskAntipodalQuotient

namespace ProjectivePlaneTorus

noncomputable section

/-- Helper for Example 74.8: the Euclidean coordinate plane used for the projective chart. -/
abbrev ModelPlane := EuclideanSpace ℝ (Fin 2)

/-- Helper for Example 74.8: a chosen canonical homeomorphism from the disk-antipodal quotient
to the real projective plane. -/
noncomputable def projectiveQuotientHomeomorph :
    DiskAntipodalQuotient.Space ≃ₜ RealProjectivePlane :=
  Classical.choice diskAntipodalQuotientHomeomorphicProjectivePlane

/-- Helper for Example 74.8: the global plane coordinate regarded as an interior point of the
closed disk. -/
noncomputable def projectiveInteriorPoint (point : ModelPlane) : B² :=
  DiskAntipodalQuotient.planeHomeomorphInterior point

/-- Helper for Example 74.8: inverting the global plane-to-interior homeomorphism and then
forgetting the interior certificate recovers the original closed-disk point. -/
lemma projectiveInteriorPoint_symm_apply (point : DiskAntipodalQuotient.interior) :
    projectiveInteriorPoint
        (DiskAntipodalQuotient.planeHomeomorphInterior.symm point) = (point : B²) := by
  -- Cancel the homeomorphism before forgetting the interior subtype layer.
  exact congrArg Subtype.val
    (DiskAntipodalQuotient.planeHomeomorphInterior.apply_symm_apply point)

/-- Helper for Example 74.8: the ambient value of the chosen projective interior point is
the canonical unit-ball image of its plane coordinate. -/
lemma projectiveInteriorPoint_coe_unitBall (point : ModelPlane) :
    (projectiveInteriorPoint point : ModelPlane) =
      (Homeomorph.unitBall point : ModelPlane) := by
  -- Both intervening subtype equivalences preserve the ambient vector.
  rfl

/-- Helper for Example 74.8: every global plane coordinate lands in the open disk interior. -/
lemma projectiveInteriorPoint_mem_interior (point : ModelPlane) :
    projectiveInteriorPoint point ∈ DiskAntipodalQuotient.interior := by
  -- This is the membership field of the chosen plane-to-interior homeomorphism.
  exact (DiskAntipodalQuotient.planeHomeomorphInterior point).property

/-- Helper for Example 74.8: a point in the global projective coordinate image is not on the
closed disk's boundary. -/
lemma projectiveInteriorPoint_not_boundary (point : ModelPlane) :
    ¬ ClosedUnitDisk.IsBoundary (projectiveInteriorPoint point) := by
  -- Strictly interior norm and unit boundary norm are incompatible.
  intro hboundary
  have hinterior := projectiveInteriorPoint_mem_interior point
  rw [DiskAntipodalQuotient.interior] at hinterior
  rw [ClosedUnitDisk.IsBoundary] at hboundary
  exact (ne_of_lt hinterior hboundary).elim

/-- Helper for Example 74.8: the canonical closed-disk quotient map transported to the real
projective plane. -/
noncomputable def projectiveModelMap : B² → RealProjectivePlane :=
  projectiveQuotientHomeomorph ∘ DiskAntipodalQuotient.quotientMap

/-- Helper for Example 74.8: equality under the projective model map is equality under the
disk-antipodal quotient. -/
lemma projectiveModelMap_eq_iff (x y : B²) :
    projectiveModelMap x = projectiveModelMap y ↔
      DiskAntipodalQuotient.quotientMap x = DiskAntipodalQuotient.quotientMap y := by
  -- Cancel the transported quotient's homeomorphism.
  exact projectiveQuotientHomeomorph.injective.eq_iff

/-- Helper for Example 74.8: the transported closed-disk model remains a quotient map. -/
lemma projectiveModelMap_isQuotientMap :
    Topology.IsQuotientMap projectiveModelMap := by
  -- Postcomposition with a homeomorphism preserves quotientness.
  exact projectiveQuotientHomeomorph.isQuotientMap.comp
    DiskAntipodalQuotient.quotientMap_isQuotientMap

/-- Helper for Example 74.8: global Euclidean coordinates embedded into the projective-plane
quotient model. -/
noncomputable def projectiveModelEmbedding : ModelPlane → RealProjectivePlane :=
  projectiveQuotientHomeomorph ∘
    (DiskAntipodalQuotient.interior.restrict DiskAntipodalQuotient.quotientMap ∘
      DiskAntipodalQuotient.planeHomeomorphInterior)

/-- Helper for Example 74.8: the global quotient-model coordinates form an open embedding. -/
lemma projectiveModelEmbedding_isOpenEmbedding :
    Topology.IsOpenEmbedding projectiveModelEmbedding := by
  -- Compose the plane-to-interior homeomorphism, the open quotient restriction, and the
  -- quotient-to-projective-plane homeomorphism.
  exact projectiveQuotientHomeomorph.isOpenEmbedding.comp
    (DiskAntipodalQuotient.interiorQuotient_isOpenEmbedding.comp
      DiskAntipodalQuotient.planeHomeomorphInterior.isOpenEmbedding)

/-- Helper for Example 74.8: the open embedding is the closed-disk model map evaluated at the
corresponding interior point. -/
lemma projectiveModelEmbedding_eq_modelMap (point : ModelPlane) :
    projectiveModelEmbedding point = projectiveModelMap (projectiveInteriorPoint point) := by
  -- The two sides use the same quotient representative after unfolding their compositions.
  rfl

end

end ProjectivePlaneTorus
