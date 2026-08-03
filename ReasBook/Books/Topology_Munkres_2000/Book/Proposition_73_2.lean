module

public import Topology_Munkres_2000.Book.Definition_73_1.DunceCap
public import Topology_Munkres_2000.Book.Exercise_60_2
public import Topology_Munkres_2000.Book.Exercise_60_2.Quotient
import all Topology_Munkres_2000.Book.Definition_21_3.ClosedUnitDisk
import all Topology_Munkres_2000.Book.Definition_73_1.DunceCap

public section

namespace DunceCap

/-- Helper for Proposition 73.2: rotation through the nontrivial angle for the
`2`-fold dunce cap is the antipodal map on `Circle`. -/
private lemma rotation_two_apply (z : Circle) : rotation 2 z = -z := by
  -- Unfold the left translation just far enough to expose its complex rotation factor.
  apply Circle.ext
  change ((Circle.exp (2 * Real.pi / 2) * z : Circle) : ℂ) = -(z : ℂ)
  have hangle : (2 : ℝ) * Real.pi / 2 = Real.pi := by
    ring
  -- In complex coordinates the remaining rotation factor is `exp (π * I) = -1`.
  rw [Circle.coe_mul, Circle.coe_exp, hangle, Complex.exp_pi_mul_I]
  exact neg_one_mul (z : ℂ)

/-- Helper for Proposition 73.2: the complex closed-disk relation identifying
antipodal boundary points is an equivalence relation. -/
private lemma complexDiskAntipodalRelEquivalence :
    Equivalence (fun x y : Disk ↦
      y = x ∨ (‖(x : ℂ)‖ = 1 ∧ y = -x)) := by
  -- Reflexivity uses the equality alternative.
  constructor
  · intro x
    exact Or.inl rfl
  · -- Symmetry preserves the boundary equation under negation.
    rintro x y (rfl | ⟨hx, rfl⟩)
    · exact Or.inl rfl
    · have hBoundaryNeg : ‖((-x : Disk) : ℂ)‖ = 1 := by
        change ‖-(x : ℂ)‖ = 1
        rw [norm_neg]
        exact hx
      have hDoubleNeg : x = -(-x : Disk) := by
        simp only [neg_neg]
      exact Or.inr ⟨hBoundaryNeg, hDoubleNeg⟩
  · -- Composing two antipodal steps returns to the original point.
    intro x y z hxy hyz
    rcases hxy with rfl | ⟨hx, rfl⟩
    · exact hyz
    · rcases hyz with rfl | ⟨hy, rfl⟩
      · exact Or.inr ⟨hx, rfl⟩
      · exact Or.inl (neg_neg x)

/-- Helper for Proposition 73.2: the explicit antipodal-boundary relation on the
complex closed disk, packaged as a setoid. -/
private def complexDiskAntipodalSetoid : Setoid Disk :=
  ⟨fun x y ↦ y = x ∨ (‖(x : ℂ)‖ = 1 ∧ y = -x),
    complexDiskAntipodalRelEquivalence⟩

/-- Helper for Proposition 73.2: the boundary inclusion commutes with negation. -/
private lemma boundary_neg (z : Circle) : boundary (-z) = -boundary z := by
  -- Coercion to `ℂ` turns both sides into the same complex number.
  apply Subtype.ext
  exact Circle.coe_neg z

/-- Helper for Proposition 73.2: `Identified 2` relates exactly equal disk points
and antipodal pairs on the boundary. -/
private lemma identified_two_iff_eq_or_boundary_neg (x y : Disk) :
    Identified 2 x y ↔ y = x ∨ (‖(x : ℂ)‖ = 1 ∧ y = -x) := by
  -- First bound the generated relation by the explicit antipodal setoid.
  have identified_le : Identified 2 ≤ complexDiskAntipodalSetoid := by
    refine (identified_le_iff_boundary_rotations 2 complexDiskAntipodalSetoid).2 ?_
    intro z k
    change boundary ((rotation 2 ^ (k : ℕ)) z) = boundary z ∨
      (‖((boundary z : Disk) : ℂ)‖ = 1 ∧
        boundary ((rotation 2 ^ (k : ℕ)) z) = -boundary z)
    have hk : (k : ℕ) = 0 ∨ (k : ℕ) = 1 := by
      omega
    rcases hk with hk | hk
    · have hkZero : k = 0 := Fin.ext hk
      subst k
      have hFixed : boundary ((rotation 2 ^ ((0 : Fin 2) : ℕ)) z) = boundary z := by
        simp only [Fin.val_zero, pow_zero, Homeomorph.one_apply]
      exact Or.inl hFixed
    · have hkOne : k = 1 := Fin.ext hk
      subst k
      refine Or.inr ⟨?_, ?_⟩
      · simpa only [coe_boundary] using Circle.norm_coe z
      · simp only [Fin.val_one, pow_one, rotation_two_apply, boundary_neg]
  constructor
  · -- Every generated identification is therefore equality or a boundary antipode.
    intro hxy
    exact identified_le hxy
  · -- Conversely, equality is reflexive and a boundary antipode is a direct generator.
    rintro (rfl | ⟨hx, rfl⟩)
    · exact (Identified 2).refl _
    · have hxCircle : (x : ℂ) ∈ Metric.sphere (0 : ℂ) 1 :=
        mem_sphere_zero_iff_norm.mpr hx
      let z : Circle := ⟨x, hxCircle⟩
      have hBoundary : boundary z = x := by
        apply Subtype.ext
        simp only [coe_boundary, z]
      have hAntipode :
          boundary ((rotation 2 ^ (((1 : Fin 2) : ℕ))) z) = -x := by
        simp only [Fin.val_one, pow_one, rotation_two_apply, boundary_neg, hBoundary]
      apply (quotientMap_eq_iff 2 x (-x)).1
      calc
        quotientMap 2 x = quotientMap 2 (boundary z) :=
          congrArg (quotientMap 2) hBoundary.symm
        _ = quotientMap 2 (boundary ((rotation 2 ^ (((1 : Fin 2) : ℕ))) z)) :=
          quotientMap_rotate 2 z 1
        _ = quotientMap 2 (-x) := congrArg (quotientMap 2) hAntipode

/-- Helper for Proposition 73.2: the canonical real-linear isometry carries the
Euclidean closed unit disk to the complex closed unit disk. -/
private lemma euclideanPlane_mem_closedBall_iff (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
      Complex.orthonormalBasisOneI.repr.symm x ∈ Metric.closedBall (0 : ℂ) 1 := by
  -- Both membership statements reduce to the norm inequality preserved by the isometry.
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact (Complex.orthonormalBasisOneI.repr.symm.norm_map x).symm ▸ Iff.rfl

/-- Helper for Proposition 73.2: complex coordinates give a homeomorphism between
the Euclidean and complex models of the closed unit disk. -/
private noncomputable def euclideanDiskHomeomorphComplexDisk : B² ≃ₜ Disk :=
  Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.subtype
    euclideanPlane_mem_closedBall_iff

/-- Helper for Proposition 73.2: the disk coordinate homeomorphism preserves norms. -/
private lemma euclideanDiskHomeomorphComplexDisk_norm (x : B²) :
    ‖((euclideanDiskHomeomorphComplexDisk x : Disk) : ℂ)‖ =
      ‖(x : EuclideanSpace ℝ (Fin 2))‖ := by
  -- This is the norm-preservation law of the underlying linear isometry.
  exact Complex.orthonormalBasisOneI.repr.symm.norm_map x.1

/-- Helper for Proposition 73.2: the disk coordinate homeomorphism commutes with
the antipodal involution. -/
private lemma euclideanDiskHomeomorphComplexDisk_neg (x : B²) :
    euclideanDiskHomeomorphComplexDisk (-x) =
      -euclideanDiskHomeomorphComplexDisk x := by
  -- Coercing to `ℂ` reduces the statement to linearity of the ambient isometry.
  apply Subtype.ext
  exact map_neg Complex.orthonormalBasisOneI.repr.symm x.1

/-- Helper for Proposition 73.2: complex disk coordinates transport the Euclidean
boundary-antipodal setoid to `Identified 2`. -/
private lemma euclideanDiskHomeomorphComplexDiskRelation (x y : B²) :
    DiskAntipodalQuotient.setoid x y ↔
      Identified 2 (euclideanDiskHomeomorphComplexDisk x)
        (euclideanDiskHomeomorphComplexDisk y) := by
  -- Expand both relations through their stable equality-or-antipode interfaces.
  rw [DiskAntipodalQuotient.setoid_rel_iff,
    identified_two_iff_eq_or_boundary_neg]
  constructor
  · rintro (hxy | ⟨hx, hxy⟩)
    · exact Or.inl (congrArg euclideanDiskHomeomorphComplexDisk hxy)
    · refine Or.inr ⟨?_, ?_⟩
      · calc
          ‖((euclideanDiskHomeomorphComplexDisk x : Disk) : ℂ)‖ =
              ‖(x : EuclideanSpace ℝ (Fin 2))‖ :=
            euclideanDiskHomeomorphComplexDisk_norm x
          _ = 1 := hx
      · calc
          euclideanDiskHomeomorphComplexDisk y =
              euclideanDiskHomeomorphComplexDisk (-x) :=
            congrArg euclideanDiskHomeomorphComplexDisk hxy
          _ = -euclideanDiskHomeomorphComplexDisk x :=
            euclideanDiskHomeomorphComplexDisk_neg x
  · rintro (hxy | ⟨hx, hxy⟩)
    · exact Or.inl (euclideanDiskHomeomorphComplexDisk.injective hxy)
    · refine Or.inr ⟨?_, ?_⟩
      · unfold ClosedUnitDisk.IsBoundary
        calc
          ‖(x : EuclideanSpace ℝ (Fin 2))‖ =
              ‖((euclideanDiskHomeomorphComplexDisk x : Disk) : ℂ)‖ :=
            (euclideanDiskHomeomorphComplexDisk_norm x).symm
          _ = 1 := hx
      · apply euclideanDiskHomeomorphComplexDisk.injective
        exact hxy.trans (euclideanDiskHomeomorphComplexDisk_neg x).symm

/-- Helper for Proposition 73.2: the `2`-fold dunce cap is homeomorphic to the
quotient of the closed Euclidean disk obtained by identifying antipodal boundary points. -/
theorem twoFoldHomeomorphicDiskAntipodalQuotient :
    Nonempty (Space 2 ≃ₜ DiskAntipodalQuotient.Space) := by
  -- Quotient congruence transports the explicit relation, and symmetry gives the desired order.
  exact ⟨(Homeomorph.Quotient.congr euclideanDiskHomeomorphComplexDisk
    euclideanDiskHomeomorphComplexDiskRelation).symm⟩

/-- Proposition 73.2: The `2`-fold dunce cap is homeomorphic to the real projective
plane `P²`. -/
theorem twoFoldHomeomorphicProjectivePlane :
    Nonempty (Space 2 ≃ₜ RealProjectivePlane) := by
  -- Compose the quotient-model comparison with the standard disk model of `P²`.
  exact Nonempty.map2 Homeomorph.trans twoFoldHomeomorphicDiskAntipodalQuotient
    diskAntipodalQuotientHomeomorphicProjectivePlane

end DunceCap
