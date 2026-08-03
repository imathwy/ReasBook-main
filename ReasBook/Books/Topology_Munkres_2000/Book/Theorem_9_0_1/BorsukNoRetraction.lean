module

public import Topology_Munkres_2000.Book.Definition_35_1.Retraction
public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Topology_Munkres_2000.Book.Theorem_54_5.FundamentalGroup
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

public section

open Set

/-- Helper for Theorem 9.0.1: a disk-boundary point determines a point of the
Euclidean unit sphere. -/
private def diskBoundaryToSphere (x : StandardSphere.boundary 1) : StandardSphere 1 :=
  ⟨x.1.1, by
    rw [Metric.mem_sphere, dist_zero_right]
    exact (StandardSphere.mem_boundary_iff_norm_eq 1 x.1).mp x.2⟩

/-- Helper for Theorem 9.0.1: a Euclidean unit-sphere point lies in the closed
unit disk. -/
private lemma spherePointMemClosedUnitBall (x : StandardSphere 1) :
    x.1 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  -- Unit norm implies the required closed-ball inequality.
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_of_eq (by simpa [Metric.mem_sphere, dist_zero_right] using x.2)

/-- Helper for Theorem 9.0.1: a Euclidean unit-sphere point determines a point
of the disk boundary. -/
private def sphereToDiskBoundary (x : StandardSphere 1) : StandardSphere.boundary 1 :=
  ⟨⟨x.1, spherePointMemClosedUnitBall x⟩,
    (StandardSphere.mem_boundary_iff_norm_eq 1 _).mpr
      (by simpa [Metric.mem_sphere, dist_zero_right] using x.2)⟩

/-- Helper for Theorem 9.0.1: the boundary-to-sphere map preserves the ambient
Euclidean point. -/
private lemma diskBoundaryToSphere_coe (x : StandardSphere.boundary 1) :
    (diskBoundaryToSphere x : EuclideanSpace ℝ (Fin 2)) = x.1.1 := rfl

/-- Helper for Theorem 9.0.1: the sphere-to-boundary map preserves the ambient
Euclidean point. -/
private lemma sphereToDiskBoundary_coe (x : StandardSphere 1) :
    ((sphereToDiskBoundary x).1 : EuclideanSpace ℝ (Fin 2)) = x.1 := rfl

/-- Helper for Theorem 9.0.1: the boundary-to-sphere map is continuous. -/
private lemma continuous_diskBoundaryToSphere : Continuous diskBoundaryToSphere := by
  -- Both subtype layers use the same ambient Euclidean coordinate.
  exact continuous_subtype_val.comp continuous_subtype_val |>.subtype_mk _

/-- Helper for Theorem 9.0.1: the sphere-to-boundary map is continuous. -/
private lemma continuous_sphereToDiskBoundary : Continuous sphereToDiskBoundary := by
  -- The inverse likewise preserves the ambient Euclidean coordinate.
  exact (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- Helper for Theorem 9.0.1: the boundary of the closed unit disk is
canonically homeomorphic to the Euclidean unit circle. -/
private def diskBoundaryHomeomorphSphere :
    StandardSphere.boundary 1 ≃ₜ StandardSphere 1 :=
  { toFun := diskBoundaryToSphere
    invFun := sphereToDiskBoundary
    left_inv := fun x ↦ by
      apply Subtype.ext
      apply Subtype.ext
      rw [sphereToDiskBoundary_coe, diskBoundaryToSphere_coe]
    right_inv := fun x ↦ by
      apply Subtype.ext
      rw [diskBoundaryToSphere_coe, sphereToDiskBoundary_coe]
    continuous_toFun := continuous_diskBoundaryToSphere
    continuous_invFun := continuous_sphereToDiskBoundary }

/-- Helper for Theorem 9.0.1: the canonical coordinate isometry identifies
the Euclidean plane with the complex plane. -/
private noncomputable def euclideanPlaneHomeomorphComplex :
    EuclideanSpace ℝ (Fin 2) ≃ₜ ℂ :=
  Complex.orthonormalBasisOneI.repr.symm.toHomeomorph

/-- Helper for Theorem 9.0.1: the Euclidean-complex coordinate map preserves
the unit-sphere predicate. -/
private lemma euclideanPlaneHomeomorphComplexMemSphere
    (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
      euclideanPlaneHomeomorphComplex x ∈ Metric.sphere (0 : ℂ) 1 := by
  -- Reduce both memberships to norm one and use isometry of coordinates.
  simp only [Metric.mem_sphere, dist_zero_right]
  exact (Complex.orthonormalBasisOneI.repr.symm.norm_map x).symm ▸ Iff.rfl

/-- Helper for Theorem 9.0.1: the canonical coordinate isometry identifies
the Euclidean unit circle with `Circle`. -/
private noncomputable def euclideanSphereHomeomorphCircle : StandardSphere 1 ≃ₜ Circle :=
  euclideanPlaneHomeomorphComplex.subtype euclideanPlaneHomeomorphComplexMemSphere

/-- Helper for Theorem 9.0.1: the boundary of the closed unit disk is
homeomorphic to the complex unit circle. -/
noncomputable def closedUnitDiskBoundaryHomeomorphCircle :
    StandardSphere.boundary 1 ≃ₜ Circle :=
  diskBoundaryHomeomorphSphere.trans euclideanSphereHomeomorphCircle

/-- Helper for Theorem 9.0.1: the identity map of `Circle` is not
nullhomotopic. -/
private lemma circleIdentityNotNullhomotopic :
    ¬ (ContinuousMap.id Circle).Nullhomotopic := by
  -- A nullhomotopic identity would make the circle contractible and its π₁ trivial.
  intro hid
  letI : ContractibleSpace Circle := (contractible_iff_id_nullhomotopic Circle).mpr hid
  have hsub : Subsingleton (FundamentalGroup Circle 1) := inferInstance
  have hsubInt : Subsingleton (Multiplicative ℤ) :=
    Circle.fundamentalGroupEquivInt.toEquiv.subsingleton_congr.mp hsub
  exact not_subsingleton_iff_nontrivial.mpr inferInstance hsubInt

/-- Helper for Theorem 9.0.1: a retract of a contractible space is
contractible. -/
private lemma contractibleSpaceOfIsRetract
    {X : Type*} [TopologicalSpace X] [ContractibleSpace X]
    {A : Set X} (hA : A.IsRetract) : ContractibleSpace A := by
  -- Compose a contraction of the ambient space with the retraction and inclusion.
  rw [Set.isRetract_iff] at hA
  obtain ⟨r, hr⟩ := hA
  rw [contractible_iff_id_nullhomotopic]
  let inclusion : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hNull : (r.comp inclusion).Nullhomotopic :=
    (id_nullhomotopic X).comp_right r |>.comp_left inclusion
  have hIdentity : r.comp inclusion = ContinuousMap.id A := by
    apply ContinuousMap.ext
    intro a
    exact Subtype.ext (congrArg Subtype.val (hr a))
  simpa only [hIdentity] using hNull

/-- Helper for Theorem 9.0.1: the boundary circle is not a retract of the
closed unit disk. -/
lemma closedUnitDiskBoundary_not_isRetract :
    ¬ Set.IsRetract (StandardSphere.boundary 1) := by
  -- A retraction would make the boundary contractible, hence also the circle.
  intro hRetract
  letI : ContractibleSpace (ClosedUnitBall 1) :=
    Metric.contractibleSpace_closedBall (by positivity)
  letI : ContractibleSpace (StandardSphere.boundary 1) :=
    contractibleSpaceOfIsRetract hRetract
  letI : ContractibleSpace Circle :=
    closedUnitDiskBoundaryHomeomorphCircle.symm.contractibleSpace
  exact circleIdentityNotNullhomotopic (id_nullhomotopic Circle)

end
