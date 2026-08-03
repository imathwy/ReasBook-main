module

public import Topology_Munkres_2000.Book.Definition_73_1.DunceCap
public import Topology_Munkres_2000.Book.Definition_54_4.Classification
public import Topology_Munkres_2000.Book.Exercise_54_6.Power
public import Topology_Munkres_2000.Book.Theorem_54_5.FundamentalGroup
public import Topology_Munkres_2000.Book.Theorem_58_7
public import Topology_Munkres_2000.Book.Theorem_72_1
public import Topology_Munkres_2000.Book.Remark_73_1
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.RingTheory.RootsOfUnity.Complex

public section

namespace DunceCap

/-- Helper for Theorem 73.4: a member of `Fin n` has value zero when `n ≤ 1`. -/
private theorem finValue_eq_zero_of_natLeOne (n : ℕ) (hn : n ≤ 1) (k : Fin n) :
    (k : ℕ) = 0 := by
  -- The bounds `k < n ≤ 1` force the only possible natural value.
  omega

/-- Helper for Theorem 73.4: every indexed boundary rotation is trivial when
`n ≤ 1`. -/
private theorem rotation_pow_eq_self_of_natLeOne
    (n : ℕ) (hn : n ≤ 1) (k : Fin n) (z : Circle) :
    (rotation n ^ (k : ℕ)) z = z := by
  -- Replace the finite index by zero and use the zeroth power of the homeomorphism.
  rw [finValue_eq_zero_of_natLeOne n hn k]
  rfl

/-- Helper for Theorem 73.4: a setoid containing every indexed boundary rotation
also contains the generated identification relation. -/
private theorem identified_le_of_boundary_rotations {n : ℕ} {s : Setoid Disk}
    (h : ∀ (z : Circle) (k : Fin n),
      s (boundary z) (boundary ((rotation n ^ (k : ℕ)) z))) : Identified n ≤ s := by
  -- Use the owner-level elimination principle for the generated identification.
  exact (identified_le_iff_boundary_rotations n s).2 h

/-- Helper for Theorem 73.4: when `n ≤ 1`, the generated boundary-identification
setoid is equality. -/
private theorem identified_eq_bot_of_natLeOne (n : ℕ) (hn : n ≤ 1) :
    Identified n = (⊥ : Setoid Disk) := by
  -- Every direct rotation is trivial, so the generated setoid is contained in equality.
  apply le_antisymm
  · apply identified_le_of_boundary_rotations
    intro z k
    exact congrArg boundary (rotation_pow_eq_self_of_natLeOne n hn k z).symm
  · exact bot_le

/-- Helper for Theorem 73.4: the standard real-linear isometry from the Euclidean
plane to the complex plane. -/
private noncomputable def planeComplexIsometry : EuclideanSpace ℝ (Fin 2) ≃ᵢ ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

/-- Helper for Theorem 73.4: the standard plane-complex isometry carries the real
closed unit disk onto the complex closed unit disk. -/
private theorem planeComplexIsometry_image_closedUnitDisk :
    planeComplexIsometry '' (Metric.closedBall 0 1 : Set (EuclideanSpace ℝ (Fin 2))) = Disk := by
  -- Apply the closed-ball image formula and normalize the image of the origin.
  rw [planeComplexIsometry.image_closedBall]
  simp [Disk, planeComplexIsometry]

/-- Helper for Theorem 73.4: the standard plane-complex isometry carries the real
unit circle onto the complex unit circle. -/
private theorem planeComplexIsometry_image_unitSphere :
    planeComplexIsometry '' (Metric.sphere 0 1 : Set (EuclideanSpace ℝ (Fin 2))) =
      (Submonoid.unitSphere ℂ : Set ℂ) := by
  -- Apply the sphere image formula and normalize the image of the origin.
  rw [planeComplexIsometry.image_sphere]
  simp [Submonoid.unitSphere, planeComplexIsometry]

/-- Helper for Theorem 73.4: the canonical homeomorphism from the Euclidean closed
unit disk to the closed complex unit disk. -/
private noncomputable def closedUnitDiskHomeomorphComplexDisk : B² ≃ₜ Disk :=
  (planeComplexIsometry.toHomeomorph.isEmbedding.homeomorphImage
      (Metric.closedBall 0 1)).trans
    (Homeomorph.setCongr planeComplexIsometry_image_closedUnitDisk)

/-- Helper for Theorem 73.4: the canonical disk homeomorphism is the standard
plane-complex isometry on underlying values. -/
private theorem closedUnitDiskHomeomorphComplexDisk_coe (x : B²) :
    ((closedUnitDiskHomeomorphComplexDisk x : Disk) : ℂ) = planeComplexIsometry x := by
  -- Both subtype restrictions preserve the underlying value.
  rfl

/-- Helper for Theorem 73.4: the canonical disk homeomorphism preserves the
underlying norm. -/
private theorem closedUnitDiskHomeomorphComplexDisk_norm (x : B²) :
    ‖((closedUnitDiskHomeomorphComplexDisk x : Disk) : ℂ)‖ =
      ‖(x : EuclideanSpace ℝ (Fin 2))‖ := by
  -- Compare distances from zero and use that the linear isometry fixes zero.
  rw [closedUnitDiskHomeomorphComplexDisk_coe]
  have hzero : planeComplexIsometry (0 : EuclideanSpace ℝ (Fin 2)) = 0 := by
    simp [planeComplexIsometry]
  calc
    ‖planeComplexIsometry (x : EuclideanSpace ℝ (Fin 2))‖ =
        dist (planeComplexIsometry x) 0 := by rw [dist_zero_right]
    _ = dist (planeComplexIsometry x) (planeComplexIsometry 0) := by rw [hzero]
    _ = dist (x : EuclideanSpace ℝ (Fin 2)) 0 := planeComplexIsometry.dist_eq x 0
    _ = ‖(x : EuclideanSpace ℝ (Fin 2))‖ := dist_zero_right _

/-- Helper for Theorem 73.4: membership in the Euclidean open disk is detected by
the norm of the corresponding complex point. -/
private theorem closedUnitDiskHomeomorphComplexDisk_mem_interior_iff (x : B²) :
    x ∈ ClosedUnitDisk.interior ↔
      ‖((closedUnitDiskHomeomorphComplexDisk x : Disk) : ℂ)‖ < 1 := by
  -- Transfer the owner-level interior characterization across norm preservation.
  rw [closedUnitDiskHomeomorphComplexDisk_norm]
  exact ClosedUnitDisk.mem_interior_iff_norm_lt x

/-- Helper for Theorem 73.4: the canonical homeomorphism from the Euclidean unit
circle to the complex unit circle. -/
private noncomputable def closedUnitDiskBoundaryHomeomorphCircle :
    StandardSphere 1 ≃ₜ Circle :=
  (planeComplexIsometry.toHomeomorph.isEmbedding.homeomorphImage
      (Metric.sphere 0 1)).trans
    (Homeomorph.setCongr planeComplexIsometry_image_unitSphere)

/-- Helper for Theorem 73.4: a point of the boundary of the closed disk lies on
the corresponding Euclidean unit sphere. -/
private theorem diskBoundaryPoint_mem_sphere (q : StandardSphere.boundary 1) :
    (q : EuclideanSpace ℝ (Fin 2)) ∈ Metric.sphere 0 1 := by
  -- Rewrite the sphere predicate using the boundary point's unit norm.
  rw [Metric.mem_sphere, dist_zero_right]
  exact (StandardSphere.mem_boundary_iff_norm_eq 1 q).1 q.property

/-- Helper for Theorem 73.4: forgetting the closed-ball certificate sends a
disk-boundary point to the Euclidean unit sphere. -/
private def diskBoundaryToSphere (q : StandardSphere.boundary 1) : StandardSphere 1 :=
  ⟨q, diskBoundaryPoint_mem_sphere q⟩

/-- Helper for Theorem 73.4: a Euclidean unit-sphere point belongs to the closed
unit disk. -/
private theorem spherePoint_mem_closedUnitDisk (q : StandardSphere 1) :
    (q : EuclideanSpace ℝ (Fin 2)) ∈
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  -- Unit norm implies the weak norm bound defining the closed disk.
  rw [Metric.mem_closedBall, dist_zero_right]
  have hnorm := q.property
  rw [Metric.mem_sphere, dist_zero_right] at hnorm
  exact hnorm.le

/-- Helper for Theorem 73.4: a Euclidean unit-sphere point, viewed in the
closed disk, belongs to its boundary. -/
private theorem spherePoint_mem_diskBoundary (q : StandardSphere 1) :
    (⟨q, spherePoint_mem_closedUnitDisk q⟩ : B²) ∈ StandardSphere.boundary 1 := by
  -- Both boundary models use the same unit-norm equation.
  apply (StandardSphere.mem_boundary_iff_norm_eq 1 _).2
  have hnorm := q.property
  rw [Metric.mem_sphere, dist_zero_right] at hnorm
  exact hnorm

/-- Helper for Theorem 73.4: a Euclidean unit-sphere point determines a point
of the closed disk's boundary. -/
private def sphereToDiskBoundary (q : StandardSphere 1) : StandardSphere.boundary 1 :=
  ⟨⟨q, spherePoint_mem_closedUnitDisk q⟩, spherePoint_mem_diskBoundary q⟩

/-- Helper for Theorem 73.4: conversion from disk-boundary points to sphere
points is continuous. -/
private theorem continuous_diskBoundaryToSphere : Continuous diskBoundaryToSphere := by
  -- The conversion is the composite of the two underlying subtype projections.
  exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- Helper for Theorem 73.4: conversion from sphere points to disk-boundary
points is continuous. -/
private theorem continuous_sphereToDiskBoundary : Continuous sphereToDiskBoundary := by
  -- The inverse conversion only adds the two canonical subtype certificates.
  exact (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- Helper for Theorem 73.4: converting a disk-boundary point to the sphere and
back fixes the point. -/
private theorem sphereToDiskBoundary_leftInverse :
    Function.LeftInverse sphereToDiskBoundary diskBoundaryToSphere := by
  -- Both nested subtype values have the same ambient Euclidean coordinate.
  intro q
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- Helper for Theorem 73.4: converting a sphere point to the disk boundary and
back fixes the point. -/
private theorem sphereToDiskBoundary_rightInverse :
    Function.RightInverse sphereToDiskBoundary diskBoundaryToSphere := by
  -- Equality of sphere points follows from equality of their ambient values.
  intro q
  apply Subtype.ext
  rfl

/-- Helper for Theorem 73.4: the boundary subtype of the closed disk is
canonically homeomorphic to the Euclidean unit sphere. -/
private def diskBoundaryHomeomorphSphere :
    StandardSphere.boundary 1 ≃ₜ StandardSphere 1 :=
  { toFun := diskBoundaryToSphere
    invFun := sphereToDiskBoundary
    left_inv := sphereToDiskBoundary_leftInverse
    right_inv := sphereToDiskBoundary_rightInverse
    continuous_toFun := continuous_diskBoundaryToSphere
    continuous_invFun := continuous_sphereToDiskBoundary }

/-- Helper for Theorem 73.4: the boundary subtype of the closed disk has the
circle coordinate induced by the plane-complex isometry. -/
private noncomputable def diskBoundaryHomeomorphCircle :
    StandardSphere.boundary 1 ≃ₜ Circle :=
  diskBoundaryHomeomorphSphere.trans closedUnitDiskBoundaryHomeomorphCircle

/-- Helper for Theorem 73.4: the disk homeomorphism and its sphere restriction have
the same underlying complex value. -/
private theorem closedUnitDiskHomeomorphComplexDisk_sphere_apply
    (q : StandardSphere 1) :
    closedUnitDiskHomeomorphComplexDisk ⟨q, spherePoint_mem_closedUnitDisk q⟩ =
      boundary (closedUnitDiskBoundaryHomeomorphCircle q) := by
  -- Extensionality reduces compatibility to the shared underlying linear isometry.
  apply Subtype.ext
  rfl

/-- Helper for Theorem 73.4: the disk and boundary circle coordinates have the
same image in the complex closed disk. -/
private theorem closedUnitDiskHomeomorphComplexDisk_boundary_apply
    (q : StandardSphere.boundary 1) :
    closedUnitDiskHomeomorphComplexDisk (q : B²) =
      boundary (diskBoundaryHomeomorphCircle q) := by
  -- Reduce to compatibility of the disk map with its unit-sphere restriction.
  exact closedUnitDiskHomeomorphComplexDisk_sphere_apply (diskBoundaryToSphere q)

/-- Helper for Theorem 73.4: the quotient map transported to the Euclidean closed
unit disk. -/
private noncomputable def transportedQuotientMap (n : ℕ) : C(B², Space n) :=
  (⟨quotientMap n, (quotientMap_isQuotientMap n).continuous⟩ : C(Disk, Space n)).comp
    closedUnitDiskHomeomorphComplexDisk

/-- Helper for Theorem 73.4: the transported quotient map evaluates by first using
the canonical disk homeomorphism. -/
private theorem transportedQuotientMap_apply (n : ℕ) (x : B²) :
    transportedQuotientMap n x = quotientMap n (closedUnitDiskHomeomorphComplexDisk x) := by
  -- This is the computation rule for composition of continuous maps.
  rfl

/-- Helper for Theorem 73.4: the transported quotient map sends the Euclidean
boundary into the canonical boundary image. -/
private theorem transportedQuotientMap_mapsToBoundary (n : ℕ) :
    Set.MapsTo (transportedQuotientMap n) (StandardSphere.boundary 1)
      (Set.range (fun z : Circle ↦ quotientMap n (boundary z))) := by
  -- Convert a disk-boundary point to the unit sphere and use the compatible restriction.
  intro q hq
  have hnorm : ‖(q : EuclideanSpace ℝ (Fin 2))‖ = 1 :=
    (StandardSphere.mem_boundary_iff_norm_eq 1 q).1 hq
  let qSphere : StandardSphere 1 := ⟨q, by simpa [Metric.mem_sphere] using hnorm⟩
  refine ⟨closedUnitDiskBoundaryHomeomorphCircle qSphere, ?_⟩
  exact congrArg (quotientMap n) (closedUnitDiskHomeomorphComplexDisk_sphere_apply qSphere)

/-- Helper for Theorem 73.4: iterated rotations of an exponential circle point
add the corresponding multiple of the basic rotation angle. -/
private theorem rotation_pow_apply_exp (n m : ℕ) (θ : ℝ) :
    (rotation n ^ m) (Circle.exp θ) =
      Circle.exp (θ + m * (2 * Real.pi / n)) := by
  -- Induct on the iterate and use the public computation rule for one rotation.
  induction m generalizing θ with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, Homeomorph.mul_apply, rotation_apply_exp, ih]
      congr 1
      push_cast
      ring

/-- Helper for Theorem 73.4: every indexed rotation preserves the `n`-th power
map on the circle. -/
private theorem rotation_pow_npow (n : ℕ) (hn : 0 < n) (z : Circle) (k : Fin n) :
    ((rotation n ^ (k : ℕ)) z) ^ n = z ^ n := by
  -- Lift the point to an angle and compare the resulting exponents modulo `2π`.
  obtain ⟨θ, rfl⟩ := Circle.exp_surjective z
  rw [rotation_pow_apply_exp, ← Circle.exp_natCast_mul, ← Circle.exp_natCast_mul]
  rw [Circle.exp_inj, AddCommGroup.modEq_iff_zsmul]
  use -((k : ℕ) : ℤ)
  norm_num
  field_simp
  ring

/-- Helper for Theorem 73.4: two circle points with equal `n`-th powers differ by
one of the indexed rotations defining the dunce-cap boundary relation. -/
private theorem eq_rotation_pow_of_npow_eq (n : ℕ) (hn : 0 < n) (z w : Circle)
    (h : z ^ n = w ^ n) : ∃ k : Fin n, z = (rotation n ^ (k : ℕ)) w := by
  -- The covering-map fiber is an orbit under the group of `n`-th roots of unity.
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have horbit := (Circle.isQuotientCoveringMap_npow n).apply_eq_iff_mem_orbit.mp h
  rw [MulAction.mem_orbit_iff] at horbit
  obtain ⟨g, hg⟩ := horbit
  rcases g with ⟨g, hgpow⟩
  dsimp at hg
  have hroot : Circle.toUnits g ∈ rootsOfUnity n ℂ := by
    rw [mem_rootsOfUnity]
    ext
    exact congrArg Subtype.val hgpow
  obtain ⟨i, hi, hgi⟩ := (Complex.mem_rootsOfUnity n (Circle.toUnits g)).mp hroot
  let k : Fin n := ⟨i, hi⟩
  refine ⟨k, ?_⟩
  rw [← hg]
  obtain ⟨θ, rfl⟩ := Circle.exp_surjective w
  rw [rotation_pow_apply_exp]
  apply Circle.coe_injective
  simp only [Circle.coe_mul, Circle.coe_exp]
  have hgcoe : (g : ℂ) = Complex.exp (2 * Real.pi * Complex.I * (i / n)) := by
    simpa [Circle.toUnits_apply] using hgi.symm
  rw [hgcoe, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Helper for Theorem 73.4: boundary points are identified exactly when they
have the same image under the `n`-th power map. -/
private theorem identified_boundary_iff_npow_eq (n : ℕ) (hn : 0 < n) (z w : Circle) :
    Identified n (boundary z) (boundary w) ↔ z ^ n = w ^ n := by
  -- The forward implication extends rotation-invariance through the generated setoid.
  constructor
  · intro hidentified
    let powerFiber : Setoid Disk := Setoid.ker (fun x : Disk ↦ (x : ℂ) ^ n)
    have identified_le : Identified n ≤ powerFiber := by
      apply (identified_le_iff_boundary_rotations n powerFiber).2
      intro u k
      change ((boundary u : Disk) : ℂ) ^ n =
        ((boundary ((rotation n ^ (k : ℕ)) u) : Disk) : ℂ) ^ n
      simpa using congrArg Subtype.val (rotation_pow_npow n hn u k).symm
    have hpower := identified_le hidentified
    exact Circle.coe_injective (by simpa [powerFiber] using hpower)
  · intro hpower
    -- The reverse implication selects the indexed rotation in the common power fiber.
    obtain ⟨k, hk⟩ := eq_rotation_pow_of_npow_eq n hn z w hpower
    rw [← quotientMap_eq_iff]
    calc
      quotientMap n (boundary z) = quotientMap n (boundary ((rotation n ^ (k : ℕ)) w)) := by
        rw [hk]
      _ = quotientMap n (boundary w) := (quotientMap_rotate n w k).symm

/-- Helper for Theorem 73.4: the boundary image is a circle, with the quotient
map represented by the `n`-th power map in the chosen circle coordinate. -/
private theorem boundaryImageHomeomorphCircle (n : ℕ) (hn : 0 < n) :
    ∃ eA : Set.range (fun z : Circle ↦ quotientMap n (boundary z)) ≃ₜ Circle,
      ∀ z : Circle,
        eA ⟨quotientMap n (boundary z), Set.mem_range_self z⟩ = z ^ n := by
  -- Compare the two quotient maps after identifying their kernel setoids.
  let A := Set.range (fun z : Circle ↦ quotientMap n (boundary z))
  let f : C(Circle, A) :=
    ⟨fun z ↦ ⟨quotientMap n (boundary z), Set.mem_range_self z⟩,
      ((quotientMap_isQuotientMap n).continuous.comp
        (continuous_subtype_val.subtype_mk boundary_mem)).subtype_mk _⟩
  have hf_surjective : Function.Surjective f := by
    intro a
    obtain ⟨z, hz⟩ := a.property
    exact ⟨z, Subtype.ext hz⟩
  have hf_quotient : Topology.IsQuotientMap f :=
    Topology.IsQuotientMap.of_surjective_continuous hf_surjective f.continuous
  let g : C(Circle, Circle) := ⟨fun z ↦ z ^ n, continuous_pow n⟩
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hg_quotient : Topology.IsQuotientMap g :=
    (Circle.isQuotientCoveringMap_npow n).toIsQuotientMap
  let eKer : Quotient (Setoid.ker f) ≃ₜ Quotient (Setoid.ker g) :=
    Homeomorph.Quotient.congrRight fun z w ↦ by
      change f z = f w ↔ g z = g w
      constructor
      · intro h
        have hq : quotientMap n (boundary z) = quotientMap n (boundary w) :=
          congrArg Subtype.val h
        exact (identified_boundary_iff_npow_eq n hn z w).1
          ((quotientMap_eq_iff n _ _).1 hq)
      · intro h
        apply Subtype.ext
        exact (quotientMap_eq_iff n _ _).2
          ((identified_boundary_iff_npow_eq n hn z w).2 h)
  let eA := hf_quotient.homeomorph.symm.trans (eKer.trans hg_quotient.homeomorph)
  refine ⟨eA, ?_⟩
  intro z
  change eA (f z) = z ^ n
  have hf_symm : hf_quotient.homeomorph.symm (f z) = Quotient.mk'' z := by
    apply hf_quotient.homeomorph.injective
    simp only [Homeomorph.apply_symm_apply, Topology.IsQuotientMap.homeomorph_apply]
    rfl
  rw [show eA (f z) = hg_quotient.homeomorph
    (eKer (hf_quotient.homeomorph.symm (f z))) by rfl]
  rw [hf_symm]
  rfl

/-- Helper for Theorem 73.4: the canonical boundary image is closed and path connected. -/
private theorem boundaryImage_closed_pathConnected (n : ℕ) :
    IsClosed (Set.range (fun z : Circle ↦ quotientMap n (boundary z))) ∧
      IsPathConnected (Set.range (fun z : Circle ↦ quotientMap n (boundary z))) := by
  -- Compactness gives closedness in the Hausdorff quotient, while circle paths map onto the range.
  let f : Circle → Space n := fun z ↦ quotientMap n (boundary z)
  have hf : Continuous f :=
    (quotientMap_isQuotientMap n).continuous.comp
      (continuous_subtype_val.subtype_mk boundary_mem)
  constructor
  · rw [← Set.image_univ]
    exact (isCompact_univ.image hf).isClosed
  · rw [← Set.image_univ]
    exact isPathConnected_univ.image hf

/-- Helper for Theorem 73.4: an identified point in the open complex disk has no
distinct representative. -/
private theorem identified_eq_of_norm_lt_one_left (n : ℕ) {x y : Disk}
    (hxy : Identified n x y) (hx : ‖(x : ℂ)‖ < 1) : x = y := by
  -- Bound the generated relation by the setoid that only collapses boundary points.
  have boundary_equivalence :
      Equivalence (fun u v : Disk ↦ u = v ∨ (‖(u : ℂ)‖ = 1 ∧ ‖(v : ℂ)‖ = 1)) := by
    constructor
    · intro u
      exact Or.inl rfl
    · intro u v huv
      rcases huv with huv | ⟨hu, hv⟩
      · exact Or.inl huv.symm
      · exact Or.inr ⟨hv, hu⟩
    · intro u v w huv hvw
      rcases huv with huv | ⟨hu, hv⟩
      · simpa [huv] using hvw
      · rcases hvw with hvw | ⟨_, hw⟩
        · exact Or.inr ⟨hu, hvw ▸ hv⟩
        · exact Or.inr ⟨hu, hw⟩
  let boundarySetoid : Setoid Disk :=
    { r := fun u v ↦ u = v ∨ (‖(u : ℂ)‖ = 1 ∧ ‖(v : ℂ)‖ = 1)
      iseqv := boundary_equivalence }
  have identified_le : Identified n ≤ boundarySetoid := by
    apply (identified_le_iff_boundary_rotations n boundarySetoid).2
    intro z k
    exact Or.inr ⟨Circle.norm_coe z, Circle.norm_coe ((rotation n ^ (k : ℕ)) z)⟩
  rcases identified_le hxy with hxy | ⟨hx_boundary, _⟩
  · exact hxy
  · exact (lt_irrefl 1 (hx_boundary ▸ hx)).elim

/-- Helper for Theorem 73.4: the transported quotient map is bijective from the
open disk onto the complement of the canonical boundary image. -/
private theorem transportedQuotientMap_bijOnInterior (n : ℕ) :
    Set.BijOn (transportedQuotientMap n) ClosedUnitDisk.interior
      (Set.range (fun z : Circle ↦ quotientMap n (boundary z)))ᶜ := by
  -- Interior representatives cannot lie in the boundary image.
  constructor
  · intro x hx hxRange
    obtain ⟨z, hz⟩ := hxRange
    have hxNorm : ‖((closedUnitDiskHomeomorphComplexDisk x : Disk) : ℂ)‖ < 1 :=
      (closedUnitDiskHomeomorphComplexDisk_mem_interior_iff x).1 hx
    have hDisk : closedUnitDiskHomeomorphComplexDisk x = boundary z := by
      exact identified_eq_of_norm_lt_one_left n
        ((quotientMap_eq_iff n _ _).1 (by
          rw [← transportedQuotientMap_apply]
          exact hz.symm)) hxNorm
    rw [hDisk] at hxNorm
    change ‖(z : ℂ)‖ < 1 at hxNorm
    rw [Circle.norm_coe] at hxNorm
    exact (lt_irrefl 1 hxNorm).elim
  · constructor
    · intro x hx y hy hxy
      apply closedUnitDiskHomeomorphComplexDisk.injective
      apply identified_eq_of_norm_lt_one_left n
      · exact (quotientMap_eq_iff n _ _).1 hxy
      · exact (closedUnitDiskHomeomorphComplexDisk_mem_interior_iff x).1 hx
    · intro y hy
      obtain ⟨z, rfl⟩ := (quotientMap_isQuotientMap n).surjective y
      let x : B² := closedUnitDiskHomeomorphComplexDisk.symm z
      refine ⟨x, ?_, by simp [transportedQuotientMap, x]⟩
      apply (closedUnitDiskHomeomorphComplexDisk_mem_interior_iff x).2
      by_contra hnot
      have hzLe : ‖(z : ℂ)‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
      have hnotz : ¬ ‖(z : ℂ)‖ < 1 := by
        simpa [x] using hnot
      have hzNorm : ‖(z : ℂ)‖ = 1 := le_antisymm hzLe (le_of_not_gt hnotz)
      let zCircle : Circle := ⟨z, by simpa [Submonoid.unitSphere] using hzNorm⟩
      apply hy
      refine ⟨zCircle, ?_⟩
      apply congrArg (quotientMap n)
      apply Subtype.ext
      rfl

/-- Helper for Theorem 73.4: in a commutative group, the normal closure of a
homomorphism's range is already its range. -/
private theorem normalClosure_range_eq_range_of_commGroup
    {G H : Type*} [Group G] [CommGroup H] (f : G →* H) :
    Subgroup.normalClosure (Set.range f) = f.range := by
  -- The range is a normal subgroup in the commutative codomain, giving one inclusion.
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro x hx
    exact hx
  · -- The generating range is contained in its normal closure, giving the reverse inclusion.
    intro x hx
    exact Subgroup.subset_normalClosure hx

/-- Helper for Theorem 73.4: based fundamental-group maps preserve composition,
including the endpoint equalities used to select the target basepoints. -/
private theorem fundamentalGroupMapOfEq_comp
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) {x : X} {y : Y} {z : Z}
    (hf : f x = y) (hg : g y = z) (hgf : (g.comp f) x = z) :
    (FundamentalGroup.mapOfEq g hg).comp (FundamentalGroup.mapOfEq f hf) =
      FundamentalGroup.mapOfEq (g.comp f) hgf := by
  -- Normalize the chosen endpoints, then use functoriality on loop classes.
  subst y
  subst z
  have hg_rfl : hg = rfl := Subsingleton.elim _ _
  cases hg_rfl
  ext a
  simp only [MonoidHom.coe_comp, Function.comp_apply, FundamentalGroup.mapOfEq_apply,
    Path.Homotopic.Quotient.cast_rfl_rfl, Path.Homotopic.Quotient.map_comp]
  apply eq_of_heq
  exact Path.Homotopic.Quotient.cast_heq _ _

/-- Helper for Theorem 73.4: a reflexive endpoint choice in `mapOfEq` gives the
ordinary induced fundamental-group homomorphism. -/
private theorem fundamentalGroupMapOfEq_refl
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    FundamentalGroup.mapOfEq f (rfl : f x = f x) = FundamentalGroup.map f x := by
  -- Evaluate on a loop class and remove the reflexive endpoint transport.
  ext a
  simp only [FundamentalGroup.mapOfEq_apply,
    Path.Homotopic.Quotient.cast_rfl_rfl, FundamentalGroup.map_apply]

/-- Helper for Theorem 73.4: equal continuous maps induce equal pointed
fundamental-group homomorphisms, independently of the endpoint proofs. -/
private theorem fundamentalGroupMapOfEq_congr
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f g : C(X, Y)) {x : X} {y : Y} (hfg : f = g)
    (hf : f x = y) (hg : g x = y) :
    FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg := by
  -- Substitute the map equality; proof irrelevance identifies the endpoint witnesses.
  subst g
  rfl

/-- Helper for Theorem 73.4: the integer-power endomorphism of multiplicative
integers has range equal to the subgroup of multiples of its exponent. -/
private theorem range_zpowGroupHom_multiplicativeInt (k : ℤ) :
    (zpowGroupHom k : Multiplicative ℤ →* Multiplicative ℤ).range =
      AddSubgroup.toSubgroup (AddSubgroup.zmultiples k) := by
  -- Identify integer exponentiation with the multiplicative form of multiplication by `k`.
  have hhom :
      (zpowGroupHom k : Multiplicative ℤ →* Multiplicative ℤ) =
        AddMonoidHom.toMultiplicative (zmultiplesHom ℤ k) := by
    apply MonoidHom.ext
    intro x
    change Multiplicative.ofAdd (k • x.toAdd) = Multiplicative.ofAdd (x.toAdd * k)
    congr 1
    rw [zsmul_eq_mul, Int.cast_id, mul_comm]
  -- The standard range computation for `zmultiplesHom` now gives `kℤ`.
  rw [hhom, MonoidHom.coe_toMultiplicative_range,
    AddSubgroup.range_zmultiplesHom]

/-- Helper for Theorem 73.4: a commuting square with integer circle coordinates
transports the range of a group homomorphism to the subgroup `nℤ`. -/
private theorem map_range_eq_zmultiples_of_coordinateSquare
    {G H : Type*} [Group G] [Group H] (f : G →* H)
    (sourceCoordinates : G ≃* Multiplicative ℤ)
    (targetCoordinates : H ≃* Multiplicative ℤ) (n : ℕ)
    (hsquare : targetCoordinates.toMonoidHom.comp f =
      (zpowGroupHom (n : ℤ)).comp sourceCoordinates.toMonoidHom) :
    f.range.map targetCoordinates.toMonoidHom =
      AddSubgroup.toSubgroup (AddSubgroup.zmultiples (n : ℤ)) := by
  -- Move the range around the square and use surjectivity of the source coordinate.
  calc
    f.range.map targetCoordinates.toMonoidHom =
        (targetCoordinates.toMonoidHom.comp f).range :=
      MonoidHom.map_range targetCoordinates.toMonoidHom f
    _ = ((zpowGroupHom (n : ℤ)).comp sourceCoordinates.toMonoidHom).range :=
      congrArg MonoidHom.range hsquare
    _ = sourceCoordinates.toMonoidHom.range.map (zpowGroupHom (n : ℤ)) :=
      MonoidHom.range_comp (zpowGroupHom (n : ℤ)) sourceCoordinates.toMonoidHom
    _ = (⊤ : Subgroup (Multiplicative ℤ)).map (zpowGroupHom (n : ℤ)) := by
      rw [MonoidHom.range_eq_top_of_surjective sourceCoordinates.toMonoidHom
        sourceCoordinates.surjective]
    _ = (zpowGroupHom (n : ℤ) : Multiplicative ℤ →* Multiplicative ℤ).range :=
      (MonoidHom.range_eq_map _).symm
    _ = AddSubgroup.toSubgroup (AddSubgroup.zmultiples (n : ℤ)) :=
      range_zpowGroupHom_multiplicativeInt (n : ℤ)

/-- Helper for Theorem 73.4: the multiplicative form of the standard
identification of integers modulo `nℤ` with `ZMod n`. -/
private noncomputable def multiplicativeIntQuotientZMultiplesMulEquivZMod (n : ℕ) :
    Multiplicative ℤ ⧸ AddSubgroup.toSubgroup (AddSubgroup.zmultiples (n : ℤ)) ≃*
      Multiplicative (ZMod n) :=
  AddEquiv.toMultiplicative (Int.quotientZMultiplesNatEquivZMod n)

/-- Helper for Theorem 73.4: integer coordinates identify a group quotient with
`ZMod n` once the normal subgroup is transported to `nℤ`. -/
private noncomputable def quotientMulEquivZModOfMappedSubgroup
    {G : Type*} [Group G] (e : G ≃* Multiplicative ℤ) (N : Subgroup G) [N.Normal]
    (n : ℕ) (hN : N.map e = AddSubgroup.toSubgroup (AddSubgroup.zmultiples (n : ℤ))) :
    G ⧸ N ≃* Multiplicative (ZMod n) :=
  (QuotientGroup.congr N _ e hN).trans
    (multiplicativeIntQuotientZMultiplesMulEquivZMod n)

/-- Helper for Theorem 73.4: for a nondegenerate dunce cap, its fundamental group
is the cyclic group represented by `ZMod n`. -/
private theorem fundamentalGroupMulEquivZModOfOneLt (n : ℕ) (hn : 1 < n) :
    Nonempty
      (FundamentalGroup (Space n) (quotientMap n (boundary (1 : Circle))) ≃*
        Multiplicative (ZMod n)) := by
  -- Route correction: the owner API and the `n`-th-power fiber theorem now control
  -- the quotient relation without unfolding sealed definitions.
  classical
  have hn_pos : 0 < n := Nat.zero_lt_of_lt hn
  let A : Set (Space n) :=
    Set.range (fun z : Circle ↦ quotientMap n (boundary z))
  obtain ⟨boundaryEquiv, boundaryEquiv_apply⟩ :=
    boundaryImageHomeomorphCircle n hn_pos
  have boundaryClosedPathConnected := boundaryImage_closed_pathConnected n
  let h : C(B², Space n) := transportedQuotientMap n
  have hBoundary : Set.MapsTo h (StandardSphere.boundary 1)
      A := by
    -- The named sphere restriction supplies the boundary compatibility required by Theorem 72.1.
    exact transportedQuotientMap_mapsToBoundary n
  have hInterior : Set.BijOn h ClosedUnitDisk.interior
      Aᶜ := by
    -- Interior uniqueness and quotient surjectivity give the attachment bijection.
    exact transportedQuotientMap_bijOnInterior n
  let attachingMap : C(StandardSphere.boundary 1, A) :=
    ClosedUnitDisk.boundaryMap A h hBoundary
  let sourceBoundaryEquiv := diskBoundaryHomeomorphCircle
  let boundaryCoordinate : C(A, Circle) := boundaryEquiv
  let sourceBoundaryCoordinate : C(StandardSphere.boundary 1, Circle) :=
    sourceBoundaryEquiv
  -- The two circle coordinates identify the attaching map with `z ↦ z ^ n`.
  have coordinateMap :
      boundaryCoordinate.comp attachingMap =
        (CircleMap.zpower (n : ℤ)).comp sourceBoundaryCoordinate := by
    apply ContinuousMap.ext
    intro q
    have attachingMap_apply :
        attachingMap q =
          ⟨quotientMap n (boundary (sourceBoundaryEquiv q)),
            Set.mem_range_self (sourceBoundaryEquiv q)⟩ := by
      -- Compare the restricted attaching map on underlying points of `Space n`.
      apply Subtype.ext
      calc
        (attachingMap q : Space n) = h q :=
          ClosedUnitDisk.boundaryMap_coe A h hBoundary q
        _ = quotientMap n (closedUnitDiskHomeomorphComplexDisk (q : B²)) :=
          transportedQuotientMap_apply n q
        _ = quotientMap n (boundary (sourceBoundaryEquiv q)) :=
          congrArg (quotientMap n) (closedUnitDiskHomeomorphComplexDisk_boundary_apply q)
    dsimp only [ContinuousMap.comp_apply, boundaryCoordinate, sourceBoundaryCoordinate]
    rw [CircleMap.zpower_apply, zpow_natCast, attachingMap_apply]
    exact boundaryEquiv_apply (sourceBoundaryEquiv q)
  let p : StandardSphere.boundary 1 := sourceBoundaryEquiv.symm 1
  have hp : sourceBoundaryCoordinate p = 1 := by
    -- The chosen attaching basepoint is the inverse image of the standard circle basepoint.
    exact sourceBoundaryEquiv.apply_symm_apply 1
  have htarget : boundaryCoordinate (attachingMap p) = 1 := by
    -- Evaluate the coordinate identity at `p`; the degree map fixes `1`.
    have hpoint := congrArg
      (fun f : C(StandardSphere.boundary 1, Circle) ↦ f p) coordinateMap
    simpa only [ContinuousMap.comp_apply, hp, CircleMap.zpower_one] using hpoint
  have htargetComposite :
      (boundaryCoordinate.comp attachingMap) p = 1 := by
    -- This is the same target-basepoint equation in composite-map notation.
    exact htarget
  have hpowerComposite :
      ((CircleMap.zpower (n : ℤ)).comp sourceBoundaryCoordinate) p = 1 := by
    -- Both factors carry the chosen basepoint to `1`.
    rw [ContinuousMap.comp_apply, hp, CircleMap.zpower_one]
  -- Homeomorphisms induce bijections on the two boundary fundamental groups.
  have sourceMapBijective : Function.Bijective
      (FundamentalGroup.mapOfEq sourceBoundaryCoordinate hp) := by
    exact ContinuousMap.HomotopyEquiv.fundamentalGroupMapOfEq_bijective
      sourceBoundaryEquiv.toHomotopyEquiv p 1 hp
  have targetMapBijective : Function.Bijective
      (FundamentalGroup.mapOfEq boundaryCoordinate htarget) := by
    exact ContinuousMap.HomotopyEquiv.fundamentalGroupMapOfEq_bijective
      boundaryEquiv.toHomotopyEquiv (attachingMap p) 1 htarget
  let sourceFundamentalEquiv := MulEquiv.ofBijective
    (FundamentalGroup.mapOfEq sourceBoundaryCoordinate hp) sourceMapBijective
  let targetFundamentalEquiv := MulEquiv.ofBijective
    (FundamentalGroup.mapOfEq boundaryCoordinate htarget) targetMapBijective
  have inducedCoordinateMap :
      targetFundamentalEquiv.toMonoidHom.comp (FundamentalGroup.map attachingMap p) =
        (FundamentalGroup.mapOfEq (CircleMap.zpower (n : ℤ))
          (CircleMap.zpower_one (n : ℤ))).comp sourceFundamentalEquiv.toMonoidHom := by
    -- Functoriality transports the pointwise coordinate identity to fundamental groups.
    have inducedCoordinateMapRaw :
        (FundamentalGroup.mapOfEq boundaryCoordinate htarget).comp
            (FundamentalGroup.map attachingMap p) =
          (FundamentalGroup.mapOfEq (CircleMap.zpower (n : ℤ))
            (CircleMap.zpower_one (n : ℤ))).comp
              (FundamentalGroup.mapOfEq sourceBoundaryCoordinate hp) := by
      calc
        (FundamentalGroup.mapOfEq boundaryCoordinate htarget).comp
              (FundamentalGroup.map attachingMap p) =
            (FundamentalGroup.mapOfEq boundaryCoordinate htarget).comp
              (FundamentalGroup.mapOfEq attachingMap rfl) := by
                rw [fundamentalGroupMapOfEq_refl]
        _ = FundamentalGroup.mapOfEq
              (boundaryCoordinate.comp attachingMap) htargetComposite :=
          fundamentalGroupMapOfEq_comp attachingMap boundaryCoordinate
            rfl htarget htargetComposite
        _ = FundamentalGroup.mapOfEq
              ((CircleMap.zpower (n : ℤ)).comp sourceBoundaryCoordinate)
              hpowerComposite :=
          fundamentalGroupMapOfEq_congr _ _ coordinateMap
            htargetComposite hpowerComposite
        _ = (FundamentalGroup.mapOfEq (CircleMap.zpower (n : ℤ))
              (CircleMap.zpower_one (n : ℤ))).comp
                (FundamentalGroup.mapOfEq sourceBoundaryCoordinate hp) :=
          (fundamentalGroupMapOfEq_comp sourceBoundaryCoordinate
            (CircleMap.zpower (n : ℤ)) hp (CircleMap.zpower_one (n : ℤ))
            hpowerComposite).symm
    exact inducedCoordinateMapRaw
  let sourceCoordinates := sourceFundamentalEquiv.trans Circle.fundamentalGroupEquivInt
  let targetCoordinates := targetFundamentalEquiv.trans Circle.fundamentalGroupEquivInt
  have integerCoordinateMap :
      targetCoordinates.toMonoidHom.comp (FundamentalGroup.map attachingMap p) =
        (zpowGroupHom (n : ℤ)).comp sourceCoordinates.toMonoidHom := by
    -- Postcompose the induced square with the standard integer coordinate on `π₁(S¹)`.
    calc
      targetCoordinates.toMonoidHom.comp (FundamentalGroup.map attachingMap p) =
          Circle.fundamentalGroupEquivInt.toMonoidHom.comp
            (targetFundamentalEquiv.toMonoidHom.comp
              (FundamentalGroup.map attachingMap p)) := by rfl
      _ = Circle.fundamentalGroupEquivInt.toMonoidHom.comp
            ((FundamentalGroup.mapOfEq (CircleMap.zpower (n : ℤ))
              (CircleMap.zpower_one (n : ℤ))).comp
                sourceFundamentalEquiv.toMonoidHom) :=
        congrArg (fun map ↦ Circle.fundamentalGroupEquivInt.toMonoidHom.comp map)
          inducedCoordinateMap
      _ = (Circle.fundamentalGroupEquivInt.toMonoidHom.comp
            (FundamentalGroup.mapOfEq (CircleMap.zpower (n : ℤ))
              (CircleMap.zpower_one (n : ℤ)))).comp
                sourceFundamentalEquiv.toMonoidHom :=
        (MonoidHom.comp_assoc _ _ _).symm
      _ = ((zpowGroupHom (n : ℤ)).comp
            Circle.fundamentalGroupEquivInt.toMonoidHom).comp
              sourceFundamentalEquiv.toMonoidHom := by
        rw [CircleMap.induced_zpower]
      _ = (zpowGroupHom (n : ℤ)).comp
            (Circle.fundamentalGroupEquivInt.toMonoidHom.comp
              sourceFundamentalEquiv.toMonoidHom) :=
        MonoidHom.comp_assoc _ _ _
      _ = (zpowGroupHom (n : ℤ)).comp sourceCoordinates.toMonoidHom := by rfl
  have attachingRangeCoordinates :
      (FundamentalGroup.map attachingMap p).range.map targetCoordinates.toMonoidHom =
        AddSubgroup.toSubgroup (AddSubgroup.zmultiples (n : ℤ)) := by
    -- The algebraic range bridge turns degree `n` into the subgroup `nℤ`.
    exact map_range_eq_zmultiples_of_coordinateSquare
      (FundamentalGroup.map attachingMap p) sourceCoordinates targetCoordinates n
        integerCoordinateMap
  letI : CommGroup (FundamentalGroup A (attachingMap p)) :=
    targetCoordinates.toMonoidHom.commGroupOfInjective targetCoordinates.injective
  have inclusionSurjective : Function.Surjective
      (FundamentalGroup.mapOfSubtype A (attachingMap p)) := by
    -- Theorem 72.1 gives surjectivity after attaching the single two-cell.
    exact adjoinTwoCell_inclusion_surjective A boundaryClosedPathConnected.1
      boundaryClosedPathConnected.2 h hBoundary hInterior p
  have inclusionKernel :
      (FundamentalGroup.mapOfSubtype A (attachingMap p)).ker =
        (FundamentalGroup.map attachingMap p).range := by
    -- Theorem 72.1 identifies the kernel with the normal closure of the attaching range.
    calc
      (FundamentalGroup.mapOfSubtype A (attachingMap p)).ker =
          Subgroup.normalClosure
            (Set.range (FundamentalGroup.map attachingMap p)) :=
        adjoinTwoCell_inclusion_ker A boundaryClosedPathConnected.1
          boundaryClosedPathConnected.2 h hBoundary hInterior p
      _ = (FundamentalGroup.map attachingMap p).range :=
        normalClosure_range_eq_range_of_commGroup (FundamentalGroup.map attachingMap p)
  have inclusionKernelCoordinates :
      (FundamentalGroup.mapOfSubtype A (attachingMap p)).ker.map
          targetCoordinates.toMonoidHom =
        AddSubgroup.toSubgroup (AddSubgroup.zmultiples (n : ℤ)) := by
    -- Rewrite the kernel to the already-computed attaching range.
    rw [inclusionKernel]
    exact attachingRangeCoordinates
  let quotientCoordinates := quotientMulEquivZModOfMappedSubgroup targetCoordinates
    (FundamentalGroup.mapOfSubtype A (attachingMap p)).ker n inclusionKernelCoordinates
  let resultEquiv :
      FundamentalGroup (Space n) (attachingMap p : Space n) ≃*
        Multiplicative (ZMod n) :=
    (QuotientGroup.quotientKerEquivOfSurjective
      (FundamentalGroup.mapOfSubtype A (attachingMap p)) inclusionSurjective).symm.trans
        quotientCoordinates
  have ambientBasepoint :
      (attachingMap p : Space n) = quotientMap n (boundary (1 : Circle)) := by
    -- Unwind the boundary restriction and use that `p` has circle coordinate `1`.
    calc
      (attachingMap p : Space n) = h p :=
        ClosedUnitDisk.boundaryMap_coe A h hBoundary p
      _ = quotientMap n (closedUnitDiskHomeomorphComplexDisk (p : B²)) :=
        transportedQuotientMap_apply n p
      _ = quotientMap n (boundary (sourceBoundaryEquiv p)) :=
        congrArg (quotientMap n) (closedUnitDiskHomeomorphComplexDisk_boundary_apply p)
      _ = quotientMap n (boundary (1 : Circle)) := by
        rw [show sourceBoundaryEquiv p = 1 from hp]
  -- Transport the quotient equivalence to the theorem's canonical ambient basepoint.
  rw [ambientBasepoint] at resultEquiv
  exact ⟨resultEquiv⟩

/-- Helper for Theorem 73.4: the degenerate quotients with `n ≤ 1` have trivial
fundamental group. -/
private theorem fundamentalGroupSubsingletonOfNatLeOne (n : ℕ) (hn : n ≤ 1) :
    Subsingleton
      (FundamentalGroup (Space n) (quotientMap n (boundary (1 : Circle)))) := by
  -- Replace the quotient relation by equality, then transport disk contractibility.
  have identified_eq := identified_eq_bot_of_natLeOne n hn
  have quotientMap_injective : Function.Injective (quotientMap n) := by
    intro x y hxy
    rw [quotientMap_eq_iff, identified_eq] at hxy
    exact hxy
  have quotientMap_homeomorph : IsHomeomorph (quotientMap n) :=
    isHomeomorph_iff_isQuotientMap_injective.mpr
      ⟨quotientMap_isQuotientMap n, quotientMap_injective⟩
  let diskEquiv : Disk ≃ₜ Space n := quotientMap_homeomorph.homeomorph (quotientMap n)
  letI : ContractibleSpace Disk := Metric.contractibleSpace_closedBall (by positivity)
  letI : ContractibleSpace (Space n) := diskEquiv.symm.contractibleSpace
  letI : SimplyConnectedSpace (Space n) := SimplyConnectedSpace.ofContractible (Space n)
  infer_instance

/-- The fundamental group of the `n`-fold dunce cap, based at the image of
`1 : Circle`, is cyclic. -/
instance instIsCyclicFundamentalGroup (n : ℕ) :
    IsCyclic (FundamentalGroup (Space n) (quotientMap n (boundary (1 : Circle)))) := by
  -- Split the geometric computation from the two degenerate quotient cases.
  by_cases hn : 1 < n
  · obtain ⟨equiv⟩ := fundamentalGroupMulEquivZModOfOneLt n hn
    exact equiv.isCyclic.mpr inferInstance
  · have hn_le : n ≤ 1 := Nat.le_of_not_gt hn
    letI := fundamentalGroupSubsingletonOfNatLeOne n hn_le
    infer_instance

/-- The fundamental group of the `n`-fold dunce cap has order `n`. -/
theorem natCardFundamentalGroup (n : ℕ) (hn : 1 < n) :
    Nat.card (FundamentalGroup (Space n) (quotientMap n (boundary (1 : Circle)))) = n := by
  -- The comparison with `ZMod n` simultaneously records cyclicity and cardinality.
  exact
    (isCyclic_card_eq_iff_nonempty_equiv_zmod.mpr
      (fundamentalGroupMulEquivZModOfOneLt n hn)).2

/-- Theorem 73.4. The fundamental group of the `n`-fold dunce cap, based at the
image of `1 : Circle`, is cyclic of order `n`. -/
theorem fundamentalGroupIsCyclicOfOrder (n : ℕ) (hn : 1 < n) :
    IsCyclic (FundamentalGroup (Space n) (quotientMap n (boundary (1 : Circle)))) ∧
      Nat.card (FundamentalGroup (Space n) (quotientMap n (boundary (1 : Circle)))) = n :=
  ⟨inferInstance, natCardFundamentalGroup n hn⟩

/-- The fundamental group of the `n`-fold dunce cap is isomorphic to the
multiplicative group of integers modulo `n`. -/
theorem fundamentalGroupMulEquivZMod (n : ℕ) (hn : 1 < n) :
    Nonempty
      (FundamentalGroup (Space n) (quotientMap n (boundary (1 : Circle))) ≃*
        Multiplicative (ZMod n)) :=
  isCyclic_card_eq_iff_nonempty_equiv_zmod.mp (fundamentalGroupIsCyclicOfOrder n hn)

end DunceCap
