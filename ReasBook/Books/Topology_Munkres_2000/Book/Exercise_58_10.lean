module

import all Topology_Munkres_2000.Book.Definition_55_2.Sphere

public import Topology_Munkres_2000.Book.Definition_35_1.Retraction
public import Topology_Munkres_2000.Book.Exercise_55_5.Inclusion
public import Topology_Munkres_2000.Book.Exercise_58_10.Degree
public import Topology_Munkres_2000.Book.Exercise_58_10.Homotopy
public import Topology_Munkres_2000.Book.Exercise_58_10.Reflection
public import Topology_Munkres_2000.Book.Exercise_58_10.VectorField
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Homotopy.Contractible

public section

open scoped SphereDegree

namespace StandardSphere

/-- Helper for Exercise 58.10: a sphere point belongs to the boundary of the closed unit ball. -/
theorem toBall_mem_boundary (n : ℕ) (x : StandardSphere n) :
    toBall n x ∈ boundary n := by
  -- Rewrite both sphere models to the common ambient norm equation.
  rw [boundary, Set.mem_setOf_eq]
  calc
    ‖(toBall n x : EuclideanSpace ℝ (Fin (n + 1)))‖ = ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ :=
      congrArg norm (toBall_apply n x)
    _ = 1 := mem_sphere_zero_iff_norm.mp x.property

/-- Helper for Exercise 58.10: the sphere-to-boundary inclusion is continuous. -/
theorem continuous_toBoundary (n : ℕ) :
    Continuous (fun x : StandardSphere n ↦
      (⟨toBall n x, toBall_mem_boundary n x⟩ : boundary n)) := by
  -- Continuity follows from the canonical sphere-to-ball inclusion.
  fun_prop

/-- Helper for Exercise 58.10: the canonical sphere inclusion lands in the ball boundary. -/
def toBoundary (n : ℕ) : C(StandardSphere n, boundary n) :=
  ⟨fun x ↦ ⟨toBall n x, toBall_mem_boundary n x⟩, continuous_toBoundary n⟩

/-- Helper for Exercise 58.10: `toBoundary` preserves the underlying ball point. -/
theorem toBoundary_apply (n : ℕ) (x : StandardSphere n) :
    (toBoundary n x : ClosedUnitBall n) = toBall n x := by
  -- The codomain restriction changes only the subtype certificate.
  rfl

/-- Helper for Exercise 58.10: a boundary point determines a point of the standard sphere. -/
theorem boundary_mem_sphere (n : ℕ) (x : boundary n) :
    (x : EuclideanSpace ℝ (Fin (n + 1))) ∈ StandardSphere n := by
  -- Rewrite the boundary norm equation as the defining distance equation of the sphere.
  exact mem_sphere_zero_iff_norm.mpr x.property

/-- Helper for Exercise 58.10: the boundary inclusion into the ambient space is continuous. -/
theorem continuous_boundaryToSphere (n : ℕ) :
    Continuous (fun x : boundary n ↦
      (⟨(x : EuclideanSpace ℝ (Fin (n + 1))), boundary_mem_sphere n x⟩ : StandardSphere n)) := by
  -- Continuity follows from the two nested subtype projections.
  fun_prop

/-- Helper for Exercise 58.10: identify the ball boundary with the standard sphere. -/
def boundaryToSphere (n : ℕ) : C(boundary n, StandardSphere n) :=
  ⟨fun x ↦ ⟨x, boundary_mem_sphere n x⟩, continuous_boundaryToSphere n⟩

/-- Helper for Exercise 58.10: converting a sphere point to the boundary and back
is the identity. -/
theorem boundaryToSphere_toBoundary (n : ℕ) (x : StandardSphere n) :
    boundaryToSphere n (toBoundary n x) = x := by
  -- Both sides have the same ambient Euclidean vector.
  apply Subtype.ext
  exact toBall_apply n x

end StandardSphere

namespace SphereDegree

/-- Helper for Exercise 58.10: the identity sphere map cannot be nullhomotopic when
degree exists. -/
theorem id_not_nullhomotopic {n : ℕ} (degree : SphereDegree n) :
    ¬ (ContinuousMap.id (StandardSphere n)).Nullhomotopic := by
  -- A nullhomotopy would equate the degree-one identity with a degree-zero constant map.
  rintro ⟨x, homotopic⟩
  have degree_eq := degree.homotopy homotopic
  rw [degree.id, degree.const] at degree_eq
  norm_num at degree_eq

end SphereDegree

/-- Exercise 58.10 (1). No continuous retraction exists from the closed unit ball
onto its boundary sphere. -/
theorem sphereNotRetractOfBall_of_degree (n : ℕ) (degree : SphereDegree n) :
    ¬ Set.IsRetract (StandardSphere.boundary n) := by
  -- A retraction would turn the contractible ball inclusion into a nullhomotopic sphere identity.
  intro h_retract
  rw [Set.isRetract_iff] at h_retract
  obtain ⟨retractionMap, leftInverse⟩ := h_retract
  let retraction := Set.Retraction.ofContinuousMap retractionMap leftInverse
  have unitRadius_nonneg : (0 : ℝ) ≤ 1 := by
    positivity
  letI : ContractibleSpace (ClosedUnitBall n) :=
    Metric.contractibleSpace_closedBall unitRadius_nonneg
  have inclusion_null : (StandardSphere.toBall n).Nullhomotopic :=
    (id_nullhomotopic (ClosedUnitBall n)).comp_left (StandardSphere.toBall n)
  have composite_null :
      ((StandardSphere.boundaryToSphere n).comp
        (retraction.toContinuousMap.comp (StandardSphere.toBall n))).Nullhomotopic :=
    (inclusion_null.comp_right retraction.toContinuousMap).comp_right
      (StandardSphere.boundaryToSphere n)
  have composite_eq :
      (StandardSphere.boundaryToSphere n).comp
          (retraction.toContinuousMap.comp (StandardSphere.toBall n)) =
        ContinuousMap.id (StandardSphere n) := by
    -- The retraction fixes boundary points, and the two sphere models are inverse on these points.
    apply ContinuousMap.ext
    intro x
    rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply]
    rw [← StandardSphere.toBoundary_apply n x]
    rw [← Set.Retraction.apply_eq, retraction.apply_coe]
    exact StandardSphere.boundaryToSphere_toBoundary n x
  rw [composite_eq] at composite_null
  exact degree.id_not_nullhomotopic composite_null

/-- Exercise 58.10 (2). A sphere self-map whose degree differs from that of the
antipodal map has a fixed point. -/
theorem exists_fixedPoint_of_degree_ne {n : ℕ} (degree : SphereDegree n)
    (h : C(StandardSphere n, StandardSphere n))
    (hne : deg[degree] h ≠ (-1 : ℤ) ^ (n + 1)) :
    ∃ x, h x = x := by
  -- Without a fixed point, the geometric homotopy identifies `h` with the antipodal map.
  by_contra no_fixedPoint
  have fixedPoint_free : ∀ x, h x ≠ x := by
    simpa only [not_exists] using no_fixedPoint
  have homotopic := StandardSphere.homotopic_antipodal_of_fixedPoint_free h fixedPoint_free
  apply hne
  calc
    deg[degree] h = deg[degree] (StandardSphere.antipodal n) := degree.homotopy homotopic
    _ = (-1 : ℤ) ^ (n + 1) := degree.antipodal_eq

/-- Exercise 58.10 (3). A sphere self-map of degree different from one maps some
point to its antipode. -/
theorem exists_mapsToAntipode_of_degree_ne {n : ℕ} (degree : SphereDegree n)
    (h : C(StandardSphere n, StandardSphere n)) (hne : deg[degree] h ≠ 1) :
    ∃ x, h x = -x := by
  -- If no point maps to its antipode, the geometric homotopy identifies `h` with the identity.
  by_contra avoids_antipodes
  have antipode_free : ∀ x, h x ≠ -x := by
    simpa only [not_exists] using avoids_antipodes
  have homotopic := StandardSphere.homotopic_id_of_avoids_antipodes h antipode_free
  apply hne
  calc
    deg[degree] h = deg[degree] (ContinuousMap.id (StandardSphere n)) := degree.homotopy homotopic
    _ = 1 := degree.id

/-- Exercise 58.10 (4). A standard sphere admitting a nonvanishing tangent vector
field has odd dimension. -/
theorem odd_of_nonvanishingTangentField {n : ℕ} (degree : SphereDegree n)
    (v : StandardSphere.VectorField n) (h_tangent : v.IsTangent)
    (h_nonvanishing : v.IsNonvanishing) : Odd n := by
  -- The vector-field homotopy forces the identity and antipodal maps to have equal degree.
  have homotopic := StandardSphere.homotopic_antipodal_of_nonvanishingTangentField
    v h_tangent h_nonvanishing
  have degree_eq : (1 : ℤ) = (-1 : ℤ) ^ (n + 1) := by
    calc
      (1 : ℤ) = deg[degree] (ContinuousMap.id (StandardSphere n)) := degree.id.symm
      _ = deg[degree] (StandardSphere.antipodal n) := degree.homotopy homotopic
      _ = (-1 : ℤ) ^ (n + 1) := degree.antipodal_eq
  -- If `n` were even, then `n + 1` would be odd and the right side would be `-1`.
  rw [← Nat.not_even_iff_odd]
  intro even_n
  have odd_succ : Odd (n + 1) := even_n.add_one
  rw [odd_succ.neg_one_pow] at degree_eq
  norm_num at degree_eq
