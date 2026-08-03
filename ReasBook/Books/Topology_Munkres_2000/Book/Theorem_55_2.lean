module

public import Topology_Munkres_2000.Book.Definition_35_1.Retraction
public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
import Topology_Munkres_2000.Book.Lemma_55_1
import Topology_Munkres_2000.Book.Theorem_54_5.FundamentalGroup
import Mathlib.Analysis.Normed.Module.Connected

public section

/-- Helper for Theorem 55.2: a point on the boundary of the closed unit disk lies on
the Euclidean unit sphere after forgetting the disk membership proof. -/
private lemma closedUnitDiskBoundaryPoint_mem_sphere
    (x : StandardSphere.boundary 1) :
    x.1.1 ∈ StandardSphere 1 := by
  -- Both boundary and sphere membership reduce to the same unit-norm equation.
  rw [Metric.mem_sphere, dist_zero_right]
  exact (StandardSphere.mem_boundary_iff_norm_eq 1 x.1).mp x.2

/-- Helper for Theorem 55.2: forgetting the disk membership proof maps the closed
unit-disk boundary to the Euclidean unit sphere. -/
private def closedUnitDiskBoundaryToSphere
    (x : StandardSphere.boundary 1) : StandardSphere 1 :=
  -- Package the ambient point using the boundary-to-sphere membership lemma.
  ⟨x.1.1, closedUnitDiskBoundaryPoint_mem_sphere x⟩

/-- Helper for Theorem 55.2: every point of the Euclidean unit sphere lies in the
closed unit disk. -/
private lemma unitSpherePoint_mem_closedUnitDisk (x : StandardSphere 1) :
    x.1 ∈ ClosedUnitBall 1 := by
  -- The sphere equation gives the closed-ball inequality by equality.
  have hNorm := x.2
  rw [Metric.mem_sphere, dist_zero_right] at hNorm
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_of_eq hNorm

/-- Helper for Theorem 55.2: a Euclidean unit-sphere point, regarded as a point of
the closed unit disk, belongs to its boundary. -/
private lemma unitSpherePoint_mem_closedUnitDiskBoundary (x : StandardSphere 1) :
    (⟨x.1, unitSpherePoint_mem_closedUnitDisk x⟩ : ClosedUnitBall 1) ∈
      StandardSphere.boundary 1 := by
  -- Boundary membership is again exactly the unit-norm equation from the sphere.
  have hNorm := x.2
  rw [Metric.mem_sphere, dist_zero_right] at hNorm
  rw [StandardSphere.mem_boundary_iff_norm_eq]
  exact hNorm

/-- Helper for Theorem 55.2: a Euclidean unit-sphere point determines a point of the
closed unit-disk boundary. -/
private def unitSphereToClosedUnitDiskBoundary
    (x : StandardSphere 1) : StandardSphere.boundary 1 :=
  -- Package the sphere point with its disk and boundary membership proofs.
  ⟨⟨x.1, unitSpherePoint_mem_closedUnitDisk x⟩,
    unitSpherePoint_mem_closedUnitDiskBoundary x⟩

/-- Helper for Theorem 55.2: converting a disk-boundary point to the unit sphere and
back returns the original point. -/
private lemma unitSphereToClosedUnitDiskBoundary_leftInverse :
    Function.LeftInverse unitSphereToClosedUnitDiskBoundary
      closedUnitDiskBoundaryToSphere := by
  -- Extensionality removes both subtype proof fields, leaving the same ambient point.
  intro x
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- Helper for Theorem 55.2: converting a unit-sphere point to the disk boundary and
back returns the original point. -/
private lemma unitSphereToClosedUnitDiskBoundary_rightInverse :
    Function.RightInverse unitSphereToClosedUnitDiskBoundary
      closedUnitDiskBoundaryToSphere := by
  -- Extensionality removes the sphere membership proof, leaving the same ambient point.
  intro x
  apply Subtype.ext
  rfl

/-- Helper for Theorem 55.2: the ambient projection from the disk boundary to the
Euclidean unit sphere is continuous. -/
private lemma continuous_closedUnitDiskBoundaryToSphere :
    Continuous closedUnitDiskBoundaryToSphere := by
  -- The map is the composite of two subtype projections, repackaged in the sphere.
  exact continuous_subtype_val.comp continuous_subtype_val |>.subtype_mk _

/-- Helper for Theorem 55.2: the canonical map from the Euclidean unit sphere to the
disk boundary is continuous. -/
private lemma continuous_unitSphereToClosedUnitDiskBoundary :
    Continuous unitSphereToClosedUnitDiskBoundary := by
  -- The inverse preserves the ambient point and only adds two subtype proofs.
  exact (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- Helper for Theorem 55.2: the closed unit-disk boundary is canonically
homeomorphic to the Euclidean unit sphere. -/
private def closedUnitDiskBoundaryHomeomorphSphere :
    StandardSphere.boundary 1 ≃ₜ StandardSphere 1 :=
  -- Assemble the homeomorphism from the inverse and continuity interface lemmas.
  { toFun := closedUnitDiskBoundaryToSphere
    invFun := unitSphereToClosedUnitDiskBoundary
    left_inv := unitSphereToClosedUnitDiskBoundary_leftInverse
    right_inv := unitSphereToClosedUnitDiskBoundary_rightInverse
    continuous_toFun := continuous_closedUnitDiskBoundaryToSphere
    continuous_invFun := continuous_unitSphereToClosedUnitDiskBoundary }

/-- Helper for Theorem 55.2: the canonical Euclidean-plane-to-complex isometry
preserves membership in the unit sphere. -/
private lemma euclideanPlaneComplex_mem_sphere_iff
    (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
      Complex.orthonormalBasisOneI.repr.symm x ∈ Metric.sphere (0 : ℂ) 1 := by
  -- Normalize both predicates to norms and use preservation of norm by the isometry.
  simp only [Metric.mem_sphere, dist_zero_right]
  exact (Complex.orthonormalBasisOneI.repr.symm.norm_map x).symm ▸ Iff.rfl

/-- Helper for Theorem 55.2: complex coordinates identify the Euclidean unit sphere
with the complex unit circle. -/
private noncomputable def euclideanSphereHomeomorphCircle :
    StandardSphere 1 ≃ₜ Circle :=
  -- Restrict the canonical ambient homeomorphism using sphere-membership preservation.
  Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.subtype
    euclideanPlaneComplex_mem_sphere_iff

/-- Helper for Theorem 55.2: the boundary of the closed unit disk is homeomorphic to
the complex unit circle. -/
private noncomputable def closedUnitDiskBoundaryHomeomorphCircle :
    StandardSphere.boundary 1 ≃ₜ Circle :=
  -- Compose the boundary-to-sphere and sphere-to-circle homeomorphisms.
  closedUnitDiskBoundaryHomeomorphSphere.trans euclideanSphereHomeomorphCircle

/-- Helper for Theorem 55.2: the fundamental group of the closed unit-disk boundary
at the point corresponding to `1 : Circle` is not a subsingleton. -/
private lemma closedUnitDiskBoundaryFundamentalGroup_not_subsingleton :
    ¬ Subsingleton (FundamentalGroup (StandardSphere.boundary 1)
      (closedUnitDiskBoundaryHomeomorphCircle.symm 1)) := by
  -- The inverse homeomorphism injects the circle fundamental group into this group.
  intro hBoundary
  letI : Subsingleton (FundamentalGroup (StandardSphere.boundary 1)
      (closedUnitDiskBoundaryHomeomorphCircle.symm 1)) := hBoundary
  have hCircleMapInjective : Function.Injective
      (FundamentalGroup.map
        (closedUnitDiskBoundaryHomeomorphCircle.symm :
          C(Circle, StandardSphere.boundary 1)) 1) :=
    FundamentalGroup.mapInjectiveOfLeftInverse
      (closedUnitDiskBoundaryHomeomorphCircle.symm :
        C(Circle, StandardSphere.boundary 1))
      (closedUnitDiskBoundaryHomeomorphCircle :
        C(StandardSphere.boundary 1, Circle))
      closedUnitDiskBoundaryHomeomorphCircle.apply_symm_apply 1
  have hCircle : Subsingleton (FundamentalGroup Circle 1) :=
    hCircleMapInjective.subsingleton
  -- Integer coordinates for `π₁(S¹)` contradict its resulting subsingleton instance.
  have hIntegers : Subsingleton (Multiplicative ℤ) :=
    Circle.fundamentalGroupEquivInt.toEquiv.subsingleton_congr.mp hCircle
  exact not_subsingleton_iff_nontrivial.mpr inferInstance hIntegers

/-- Theorem 55.2 (No-retraction theorem). There is no retraction of the closed unit
disk `ClosedUnitBall 1` onto its boundary circle `StandardSphere.boundary 1`. -/
theorem unitCircle_not_isRetract_closedUnitDisk :
    ¬ Set.IsRetract (StandardSphere.boundary 1) := by
  -- A hypothetical retraction makes boundary inclusion injective on fundamental groups.
  intro hRetract
  let boundaryPoint := closedUnitDiskBoundaryHomeomorphCircle.symm 1
  have hRadius : 0 ≤ (1 : ℝ) := by
    norm_num
  letI : ContractibleSpace (ClosedUnitBall 1) :=
    Metric.contractibleSpace_closedBall hRadius
  have hBoundaryMapInjective :=
    fundamentalGroupMap_injective_of_isRetract hRetract boundaryPoint
  -- The disk group is trivial, so this injection would make the boundary group trivial.
  have hBoundary : Subsingleton
      (FundamentalGroup (StandardSphere.boundary 1) boundaryPoint) :=
    hBoundaryMapInjective.subsingleton
  exact closedUnitDiskBoundaryFundamentalGroup_not_subsingleton hBoundary
