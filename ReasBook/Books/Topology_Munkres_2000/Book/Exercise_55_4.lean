module

public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Topology_Munkres_2000.Book.Definition_35_1.Retraction
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Topology.Homotopy.Contractible

public section

namespace StandardSphere

universe u

/-- Helper for Exercise 55.4: a point of the unit sphere lies in the closed unit ball. -/
private theorem spherePoint_mem_closedUnitBall (n : ℕ) (x : StandardSphere n) :
    (x : EuclideanSpace ℝ (Fin (n + 1))) ∈
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  -- The sphere equation gives the required weak norm bound.
  rw [Metric.mem_closedBall, dist_zero_right]
  have hx : ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  exact hx.le

/-- Helper for Exercise 55.4: the standard sphere includes continuously in its closed ball. -/
private def sphereInclusion (n : ℕ) : C(StandardSphere n, ClosedUnitBall n) :=
  ⟨fun x ↦ ⟨x, spherePoint_mem_closedUnitBall n x⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- Helper for Exercise 55.4: the sphere inclusion lands in the boundary of the closed ball. -/
private theorem sphereInclusion_mem_boundary (n : ℕ) (x : StandardSphere n) :
    sphereInclusion n x ∈ boundary n := by
  -- Both boundary and sphere membership express the same unit-norm equation.
  rw [mem_boundary_iff_norm_eq]
  unfold sphereInclusion
  change ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1
  simpa only [Metric.mem_sphere, dist_zero_right] using x.property

/-- Helper for Exercise 55.4: view a sphere point as a point of the ball boundary. -/
private def sphereToBoundary (n : ℕ) : C(StandardSphere n, boundary n) :=
  ⟨fun x ↦ ⟨sphereInclusion n x, sphereInclusion_mem_boundary n x⟩,
    (sphereInclusion n).continuous.subtype_mk _⟩

/-- Helper for Exercise 55.4: a boundary point determines its underlying sphere point. -/
private theorem boundaryPoint_mem_sphere (n : ℕ) (x : boundary n) :
    (x.1 : EuclideanSpace ℝ (Fin (n + 1))) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  -- Forgetting the nested subtype preserves the unit-norm boundary equation.
  rw [Metric.mem_sphere, dist_zero_right]
  exact (mem_boundary_iff_norm_eq n x.1).mp x.property

/-- Helper for Exercise 55.4: forget the nested boundary subtype to obtain a sphere point. -/
private def boundaryToSphere (n : ℕ) (x : boundary n) : StandardSphere n :=
  ⟨x.1, boundaryPoint_mem_sphere n x⟩

/-- Helper for Exercise 55.4: converting a boundary point to the sphere and back is the identity. -/
private theorem sphereToBoundary_boundaryToSphere (n : ℕ) (x : boundary n) :
    sphereToBoundary n (boundaryToSphere n x) = x := by
  -- Extensionality discards the two membership proofs and compares the ambient vectors.
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- Helper for Exercise 55.4: the sphere inclusion of a boundary point is its ball value. -/
private theorem sphereInclusion_boundaryToSphere (n : ℕ) (x : boundary n) :
    sphereInclusion n (boundaryToSphere n x) = x.1 := by
  -- The two closed-ball points have the same ambient vector.
  apply Subtype.ext
  rfl

/-- Helper for Exercise 55.4: the radial point represented by a cone coordinate. -/
private def sphereConePoint (n : ℕ) (p : unitInterval × StandardSphere n) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  (1 - (p.1 : ℝ)) • (p.2 : EuclideanSpace ℝ (Fin (n + 1)))

/-- Helper for Exercise 55.4: every radial cone point lies in the closed unit ball. -/
private theorem sphereConePoint_mem (n : ℕ) (p : unitInterval × StandardSphere n) :
    sphereConePoint n p ∈
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  -- The radial coefficient lies in `[0,1]` and the sphere vector has norm one.
  rw [Metric.mem_closedBall, dist_zero_right, sphereConePoint, norm_smul]
  have hnorm : ‖(p.2 : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.2.property
  rw [hnorm, mul_one, Real.norm_eq_abs, abs_of_nonneg]
  · linarith [unitInterval.nonneg p.1]
  · linarith [unitInterval.le_one p.1]

/-- Helper for Exercise 55.4: the radial cone point varies continuously. -/
private theorem continuous_sphereConePoint (n : ℕ) : Continuous (sphereConePoint n) := by
  -- Scalar multiplication is continuous in the radial and sphere coordinates.
  unfold sphereConePoint
  fun_prop

/-- Helper for Exercise 55.4: the cone on the unit sphere projects radially onto the ball. -/
private def sphereConeProjection (n : ℕ) :
    C(unitInterval × StandardSphere n, ClosedUnitBall n) :=
  ⟨fun p ↦ ⟨sphereConePoint n p, sphereConePoint_mem n p⟩,
    (continuous_sphereConePoint n).subtype_mk _⟩

/-- Helper for Exercise 55.4: the radial projection at time zero is the sphere inclusion. -/
private theorem sphereConeProjection_zero (n : ℕ) (x : StandardSphere n) :
    sphereConeProjection n (0, x) = sphereInclusion n x := by
  -- At time zero the radial coefficient is one.
  apply Subtype.ext
  change (1 - (0 : ℝ)) • (x : EuclideanSpace ℝ (Fin (n + 1))) = x
  simp

/-- Helper for Exercise 55.4: the radial cone projection is surjective. -/
private theorem sphereConeProjection_surjective (n : ℕ) :
    Function.Surjective (sphereConeProjection n) := by
  -- A nonzero ball point is its norm times its normalization; the origin uses a fixed unit vector.
  rintro ⟨x, hx⟩
  have hxnorm : ‖x‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  by_cases hxzero : x = 0
  · let v : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1
    have hvnorm : ‖v‖ = 1 := by
      simp [v]
    have hvsphere :
        v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hvnorm
    let q : StandardSphere n := ⟨v, hvsphere⟩
    refine ⟨(1, q), ?_⟩
    apply Subtype.ext
    simp [sphereConeProjection, sphereConePoint, hxzero]
  · have hnorm_nonneg : 0 ≤ ‖x‖ := norm_nonneg x
    have ht_le_one : 1 - ‖x‖ ≤ 1 := by
      linarith
    let t : unitInterval := ⟨1 - ‖x‖, sub_nonneg.mpr hxnorm, ht_le_one⟩
    have hnormalize : ‖NormedSpace.normalize x‖ = 1 :=
      NormedSpace.norm_normalize hxzero
    have hnormalize_sphere :
        NormedSpace.normalize x ∈
          Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hnormalize
    let q : StandardSphere n := ⟨NormedSpace.normalize x, hnormalize_sphere⟩
    refine ⟨(t, q), ?_⟩
    apply Subtype.ext
    simp only [sphereConeProjection, sphereConePoint, ContinuousMap.coe_mk, t, q]
    rw [sub_sub_cancel, NormedSpace.norm_smul_normalize]

/-- Helper for Exercise 55.4: equal radial images come from equal cone points or the apex. -/
private theorem sphereConeProjection_fiber (n : ℕ)
    (p q : unitInterval × StandardSphere n)
    (hpq : sphereConeProjection n p = sphereConeProjection n q) :
    p = q ∨ (p.1 = 1 ∧ q.1 = 1) := by
  -- Comparing ambient vectors and then their norms identifies the radial coordinate.
  have hvector : sphereConePoint n p = sphereConePoint n q :=
    congrArg (fun z : ClosedUnitBall n ↦
      (z : EuclideanSpace ℝ (Fin (n + 1)))) hpq
  have hp_norm : ‖(p.2 : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.2.property
  have hq_norm : ‖(q.2 : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using q.2.property
  have htime_val : (p.1 : ℝ) = q.1 := by
    have hnorm := congrArg norm hvector
    simp only [sphereConePoint, norm_smul, hp_norm, hq_norm, mul_one,
      Real.norm_eq_abs] at hnorm
    rw [abs_of_nonneg, abs_of_nonneg] at hnorm
    · linarith
    · linarith [unitInterval.le_one q.1]
    · linarith [unitInterval.le_one p.1]
  have htime : p.1 = q.1 := Subtype.ext htime_val
  by_cases hapex : p.1 = 1
  · exact Or.inr ⟨hapex, htime.symm.trans hapex⟩
  · left
    apply Prod.ext htime
    apply Subtype.ext
    have hscalar : (1 - (p.1 : ℝ)) ≠ 0 := by
      intro hzero
      apply hapex
      apply Subtype.ext
      exact (sub_eq_zero.mp hzero).symm
    apply smul_right_injective (EuclideanSpace ℝ (Fin (n + 1))) hscalar
    simpa only [sphereConePoint, htime] using hvector

/-- Helper for Exercise 55.4: the radial cone projection is a quotient map. -/
private theorem sphereConeProjection_isQuotientMap (n : ℕ) :
    Topology.IsQuotientMap (sphereConeProjection n) := by
  -- A continuous surjection from the compact cone to the Hausdorff ball is quotient.
  exact Topology.IsQuotientMap.of_surjective_continuous
    (sphereConeProjection_surjective n) (sphereConeProjection n).continuous

/-- Helper for Exercise 55.4: a nullhomotopy is constant on radial-projection fibers. -/
private theorem nullhomotopy_factors_sphereConeProjection
    {X : Type u} [TopologicalSpace X] {n : ℕ}
    {f : C(StandardSphere n, X)} {x : X}
    (H : f.Homotopy (ContinuousMap.const _ x)) :
    Function.FactorsThrough H.toContinuousMap (sphereConeProjection n) := by
  -- Equal non-apex representatives coincide, while all apex representatives map to the endpoint.
  intro p q hpq
  rcases sphereConeProjection_fiber n p q hpq with rfl | ⟨hp, hq⟩
  · rfl
  · have hp_pair : p = (1, p.2) := Prod.ext hp rfl
    have hq_pair : q = (1, q.2) := Prod.ext hq rfl
    rw [hp_pair, hq_pair]
    change H (1, p.2) = H (1, q.2)
    rw [H.apply_one, H.apply_one]
    rfl

/-- Helper for Exercise 55.4: descend a nullhomotopy from the sphere cone to the ball. -/
private noncomputable def sphereConeExtension
    {X : Type u} [TopologicalSpace X] {n : ℕ}
    {f : C(StandardSphere n, X)} {x : X}
    (H : f.Homotopy (ContinuousMap.const _ x)) : C(ClosedUnitBall n, X) :=
  (sphereConeProjection_isQuotientMap n).lift H.toContinuousMap
    (nullhomotopy_factors_sphereConeProjection H)

/-- Helper for Exercise 55.4: the descended cone map restricts to the original sphere map. -/
private theorem sphereConeExtension_comp_sphereInclusion
    {X : Type u} [TopologicalSpace X] {n : ℕ}
    {f : C(StandardSphere n, X)} {x : X}
    (H : f.Homotopy (ContinuousMap.const _ x)) :
    (sphereConeExtension H).comp (sphereInclusion n) = f := by
  -- Evaluate the quotient lift at each time-zero cone representative.
  apply ContinuousMap.ext
  intro q
  rw [ContinuousMap.comp_apply, ← sphereConeProjection_zero n q]
  have hlift := congrArg
    (fun g : C(unitInterval × StandardSphere n, X) ↦ g (0, q))
    ((sphereConeProjection_isQuotientMap n).lift_comp H.toContinuousMap
      (nullhomotopy_factors_sphereConeProjection H))
  exact hlift.trans (H.apply_zero q)

/-- Helper for Exercise 55.4: the retraction map induced by a nullhomotopy of the identity. -/
private noncomputable def boundaryRetractionMapOfIdHomotopy {n : ℕ} {p : StandardSphere n}
    (H : (ContinuousMap.id (StandardSphere n)).Homotopy
      (ContinuousMap.const _ p)) : C(ClosedUnitBall n, boundary n) :=
  (sphereToBoundary n).comp (sphereConeExtension H)

/-- Helper for Exercise 55.4: the induced boundary map is a left inverse to inclusion. -/
private theorem boundaryRetractionMapOfIdHomotopy_leftInverse {n : ℕ}
    {p : StandardSphere n}
    (H : (ContinuousMap.id (StandardSphere n)).Homotopy
      (ContinuousMap.const _ p)) :
    Function.LeftInverse (boundaryRetractionMapOfIdHomotopy H) Subtype.val := by
  -- Rewrite a boundary input through its sphere representative and use the extension equation.
  intro x
  let q : StandardSphere n := boundaryToSphere n x
  have hinput : sphereInclusion n q = x.1 := sphereInclusion_boundaryToSphere n x
  have hrestriction := congrArg
    (fun g : C(StandardSphere n, StandardSphere n) ↦ g q)
    (sphereConeExtension_comp_sphereInclusion H)
  calc
    boundaryRetractionMapOfIdHomotopy H x.1 =
        sphereToBoundary n (sphereConeExtension H (sphereInclusion n q)) := by
      rw [hinput]
      rfl
    _ = sphereToBoundary n ((ContinuousMap.id (StandardSphere n)) q) := by
      exact congrArg (sphereToBoundary n) hrestriction
    _ = x := sphereToBoundary_boundaryToSphere n x

/-- A nullhomotopy of the identity on the standard sphere induces a retraction of the
closed unit ball onto its boundary sphere. -/
theorem boundary_isRetract_of_id_nullhomotopic (n : ℕ)
    (h : (ContinuousMap.id (StandardSphere n)).Nullhomotopic) :
    Set.IsRetract (boundary n) := by
  -- Choose the constant endpoint and descend its homotopy to the ball boundary.
  obtain ⟨p, ⟨H⟩⟩ := h
  rw [Set.isRetract_iff]
  exact ⟨boundaryRetractionMapOfIdHomotopy H,
    boundaryRetractionMapOfIdHomotopy_leftInverse H⟩

end StandardSphere

/-- Exercise 55.4. Assuming the standard sphere is not a retract of the closed
unit ball, the identity map of the sphere is not nullhomotopic. -/
theorem sphere_id_not_nullhomotopic (n : ℕ)
    (h_noRetraction : ¬ Set.IsRetract (StandardSphere.boundary n)) :
    ¬ (ContinuousMap.id (StandardSphere n)).Nullhomotopic :=
  fun h ↦ h_noRetraction (StandardSphere.boundary_isRetract_of_id_nullhomotopic n h)
