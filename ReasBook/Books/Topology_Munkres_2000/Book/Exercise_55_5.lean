module

public import Topology_Munkres_2000.Book.Exercise_55_5.Inclusion
public import Topology_Munkres_2000.Book.Exercise_55_5.VectorField
public import Topology_Munkres_2000.Book.Definition_55_2.Nonvanishing
public import Topology_Munkres_2000.Book.Definition_35_1.Retraction
public import Topology_Munkres_2000.Book.Exercise_55_1.FixedPoint
public import Topology_Munkres_2000.Book.Exercise_55_4
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.Topology.Instances.Matrix

noncomputable section

public section

open scoped unitInterval

namespace StandardSphere

/-- Helper for Exercise 55.5: radial projection from punctured Euclidean space to the
unit sphere is continuous. -/
private theorem continuous_radialRetraction (n : ℕ) :
    Continuous (fun x : PuncturedEuclideanSpace n ↦
      ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin (n + 1)))) x).1) := by
  -- Polar coordinates provide continuity of the direction coordinate.
  fun_prop

/-- Helper for Exercise 55.5: radial projection sends every nonzero Euclidean vector to
its direction on the unit sphere. -/
private def radialRetraction (n : ℕ) :
    C(PuncturedEuclideanSpace n, StandardSphere n) :=
  ⟨fun x ↦ ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin (n + 1)))) x).1,
    continuous_radialRetraction n⟩

/-- Helper for Exercise 55.5: radial projection is ambient normalization by the norm. -/
private theorem radialRetraction_coe (n : ℕ) (x : PuncturedEuclideanSpace n) :
    (radialRetraction n x : EuclideanSpace ℝ (Fin (n + 1))) =
      ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖⁻¹ • x := by
  -- Read the direction-coordinate computation rule of polar coordinates.
  exact homeomorphUnitSphereProd_apply_fst_coe _ x

/-- Helper for Exercise 55.5: radial projection is a left inverse to the inclusion of the
unit sphere into punctured Euclidean space. -/
private theorem radialRetraction_comp_toPunctured (n : ℕ) :
    (radialRetraction n).comp (toPunctured n) = ContinuousMap.id (StandardSphere n) := by
  -- A unit vector is unchanged by normalization.
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rw [ContinuousMap.comp_apply, radialRetraction_coe, toPunctured_apply]
  simp only [mem_sphere_zero_iff_norm.mp x.property, inv_one, one_smul,
    ContinuousMap.id_apply]

/-- Helper for Exercise 55.5: the segment from one unit vector toward the negative of
another avoids zero unless the vectors agree. -/
private theorem unitSegmentToNeg_ne_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (x y : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hne : y ≠ x)
    (t : unitInterval) :
    (1 - (t : ℝ)) • y - (t : ℝ) • x ≠ 0 := by
  -- A zero on the segment forces equal coefficients, hence occurs only at its midpoint.
  intro hz
  have heq : (1 - (t : ℝ)) • y = (t : ℝ) • x := sub_eq_zero.mp hz
  have hnorm := congrArg norm heq
  rw [norm_smul, norm_smul, hx, hy, mul_one, mul_one, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr t.property.2),
    abs_of_nonneg t.property.1] at hnorm
  have ht : (t : ℝ) = 1 / 2 := by
    linarith
  rw [ht] at heq
  norm_num at heq
  exact hne heq

/-- Helper for Exercise 55.5: every value of the normalized fixed-point-free segment is
nonzero before normalization. -/
private theorem fixedPointSegment_ne_zero {n : ℕ}
    (h : C(StandardSphere n, StandardSphere n)) (hfree : ∀ x, h x ≠ x)
    (p : unitInterval × StandardSphere n) :
    (1 - (p.1 : ℝ)) • (h p.2 : EuclideanSpace ℝ (Fin (n + 1))) -
        (p.1 : ℝ) • (p.2 : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0 := by
  -- Apply the unit-vector segment criterion to the two sphere values.
  apply unitSegmentToNeg_ne_zero
  · exact mem_sphere_zero_iff_norm.mp p.2.property
  · exact mem_sphere_zero_iff_norm.mp (h p.2).property
  · exact fun heq ↦ hfree p.2 (Subtype.ext heq)

/-- Helper for Exercise 55.5: normalizing the fixed-point-free segment produces a point
of the standard sphere. -/
private theorem fixedPointHomotopyValue_mem {n : ℕ}
    (h : C(StandardSphere n, StandardSphere n)) (hfree : ∀ x, h x ≠ x)
    (p : unitInterval × StandardSphere n) :
    NormedSpace.normalize
      ((1 - (p.1 : ℝ)) • (h p.2 : EuclideanSpace ℝ (Fin (n + 1))) -
        (p.1 : ℝ) • (p.2 : EuclideanSpace ℝ (Fin (n + 1)))) ∈ StandardSphere n := by
  -- The norm of the normalization of a nonzero vector is one.
  rw [mem_sphere_zero_iff_norm]
  exact NormedSpace.norm_normalize (fixedPointSegment_ne_zero h hfree p)

/-- Helper for Exercise 55.5: a point on the normalized segment from a sphere map to
the antipodal map. -/
private def fixedPointHomotopyValue {n : ℕ}
    (h : C(StandardSphere n, StandardSphere n)) (hfree : ∀ x, h x ≠ x)
    (p : unitInterval × StandardSphere n) : StandardSphere n :=
  ⟨NormedSpace.normalize
    ((1 - (p.1 : ℝ)) • (h p.2 : EuclideanSpace ℝ (Fin (n + 1))) -
      (p.1 : ℝ) • (p.2 : EuclideanSpace ℝ (Fin (n + 1)))),
    fixedPointHomotopyValue_mem h hfree p⟩

/-- Helper for Exercise 55.5: the normalized fixed-point-free segment varies
continuously. -/
private theorem continuous_fixedPointHomotopyValue {n : ℕ}
    (h : C(StandardSphere n, StandardSphere n)) (hfree : ∀ x, h x ≠ x) :
    Continuous (fixedPointHomotopyValue h hfree) := by
  -- Normalize continuously away from the zero vector.
  apply Continuous.subtype_mk
  rw [continuous_iff_continuousAt]
  intro p
  unfold NormedSpace.normalize
  apply ContinuousAt.smul (M := ℝ)
  · apply ContinuousAt.inv₀
    · fun_prop
    · exact norm_ne_zero_iff.mpr (fixedPointSegment_ne_zero h hfree p)
  · fun_prop

/-- Helper for Exercise 55.5: the normalized fixed-point-free segment starts at the
given sphere map. -/
private theorem fixedPointHomotopyValue_zero {n : ℕ}
    (h : C(StandardSphere n, StandardSphere n)) (hfree : ∀ x, h x ≠ x)
    (x : StandardSphere n) : fixedPointHomotopyValue h hfree (0, x) = h x := by
  -- At time zero, normalization fixes the unit vector `h x`.
  apply Subtype.ext
  simp [fixedPointHomotopyValue, NormedSpace.normalize_eq_self_of_norm_eq_one,
    mem_sphere_zero_iff_norm.mp (h x).property]

/-- Helper for Exercise 55.5: the normalized fixed-point-free segment ends at the
antipode. -/
private theorem fixedPointHomotopyValue_one {n : ℕ}
    (h : C(StandardSphere n, StandardSphere n)) (hfree : ∀ x, h x ≠ x)
    (x : StandardSphere n) : fixedPointHomotopyValue h hfree (1, x) = -x := by
  -- At time one, normalization fixes the unit vector `-x`.
  apply Subtype.ext
  simp [fixedPointHomotopyValue, NormedSpace.normalize_eq_self_of_norm_eq_one,
    mem_sphere_zero_iff_norm.mp x.property]

/-- Helper for Exercise 55.5: pointwise negation is the antipodal self-map of the
standard sphere. -/
private def antipodalMap (n : ℕ) : C(StandardSphere n, StandardSphere n) :=
  ⟨fun x ↦ -x, continuous_neg⟩

/-- Helper for Exercise 55.5: a fixed-point-free sphere self-map is homotopic to the
antipodal map. -/
private theorem homotopic_antipodal_of_fixedPointFree {n : ℕ}
    (h : C(StandardSphere n, StandardSphere n)) (hfree : ∀ x, h x ≠ x) :
    h.Homotopic (antipodalMap n) := by
  -- Assemble the homotopy from the segment's continuity and endpoint formulas.
  exact ⟨{
    toFun := fixedPointHomotopyValue h hfree
    continuous_toFun := continuous_fixedPointHomotopyValue h hfree
    map_zero_left := fixedPointHomotopyValue_zero h hfree
    map_one_left := fixedPointHomotopyValue_one h hfree
  }⟩

/-- Helper for Exercise 55.5: a sphere self-map that avoids all antipodes is homotopic
to the identity. -/
private theorem homotopic_id_of_avoidsAntipodes {n : ℕ}
    (h : C(StandardSphere n, StandardSphere n)) (havoid : ∀ x, h x ≠ -x) :
    h.Homotopic (ContinuousMap.id (StandardSphere n)) := by
  -- Negating the map changes antipode avoidance into fixed-point freeness.
  let negH : C(StandardSphere n, StandardSphere n) := (antipodalMap n).comp h
  have negH_free : ∀ x, negH x ≠ x := by
    intro x hneg
    apply havoid x
    apply Subtype.ext
    have hcoe := congrArg Subtype.val hneg
    simpa [negH, antipodalMap] using congrArg Neg.neg hcoe
  have hneg := homotopic_antipodal_of_fixedPointFree negH negH_free
  -- Postcomposition with the antipodal involution identifies the two endpoints.
  have hcomposed :=
    ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl (antipodalMap n)) hneg
  have hleft : (antipodalMap n).comp negH = h := by
    ext x
    simp [negH, antipodalMap]
  have hright :
      (antipodalMap n).comp (antipodalMap n) = ContinuousMap.id (StandardSphere n) := by
    ext x
    simp [antipodalMap]
  rwa [hleft, hright] at hcomposed

end StandardSphere

/-- Helper for Exercise 55.5: nullhomotopy is preserved when the target map is replaced
by a homotopic map. -/
private theorem ContinuousMap.Nullhomotopic.trans_homotopic {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}
    (hf : f.Nullhomotopic) (hfg : f.Homotopic g) : g.Nullhomotopic := by
  -- Concatenate the reverse of the given homotopy with the nullhomotopy.
  obtain ⟨y, hfy⟩ := hf
  exact ⟨y, hfg.symm.trans hfy⟩

/-- Helper for Exercise 55.5: radial normalization of a nonvanishing vector field on the
closed unit ball is a sphere-valued continuous map. -/
private def normalizedBallVectorField {n : ℕ} (v : BallVectorField n)
    (h_nonvanishing : v.IsNonvanishing) : C(ClosedUnitBall n, StandardSphere n) :=
  (StandardSphere.radialRetraction n).comp (v.toNonzero h_nonvanishing)

/-- Helper for Exercise 55.5: the normalized ball vector field has ambient value
`‖v x‖⁻¹ • v x`. -/
private theorem normalizedBallVectorField_coe {n : ℕ} (v : BallVectorField n)
    (h_nonvanishing : v.IsNonvanishing) (x : ClosedUnitBall n) :
    (normalizedBallVectorField v h_nonvanishing x :
      EuclideanSpace ℝ (Fin (n + 1))) = ‖v x‖⁻¹ • v x := by
  -- Expand only the radial-projection computation rule.
  rw [normalizedBallVectorField, ContinuousMap.comp_apply,
    StandardSphere.radialRetraction_coe, ContinuousMap.toNonzero_apply]

/-- Helper for Exercise 55.5: negating a ball vector field preserves continuity. -/
private theorem continuous_negBallVectorField {n : ℕ} (v : BallVectorField n) :
    Continuous (fun x ↦ -v x) := by
  -- Negation is continuous in the ambient Euclidean space.
  fun_prop

/-- Helper for Exercise 55.5: pointwise negation of a ball vector field. -/
private def negBallVectorField {n : ℕ} (v : BallVectorField n) : BallVectorField n :=
  ⟨fun x ↦ -v x, continuous_negBallVectorField v⟩

/-- Helper for Exercise 55.5: pointwise negation preserves nonvanishing of a ball vector
field. -/
private theorem negBallVectorField_isNonvanishing {n : ℕ} (v : BallVectorField n)
    (h_nonvanishing : v.IsNonvanishing) : (negBallVectorField v).IsNonvanishing := by
  -- A negated vector is zero exactly when the original vector is zero.
  intro x hx
  apply h_nonvanishing x
  simpa [negBallVectorField] using congrArg Neg.neg hx

/-- Helper for Exercise 55.5: a nonvanishing vector field on the ball has an inward radial
value on the boundary whenever the sphere identity is not nullhomotopic. -/
private theorem exists_inwardPoint_of_nonvanishing (n : ℕ)
    (h_noRetraction : ¬ Set.IsRetract (StandardSphere.boundary n))
    (v : BallVectorField n) (h_nonvanishing : v.IsNonvanishing) :
    ∃ x : StandardSphere n, ∃ r : ℝ, 0 < r ∧
      v (StandardSphere.toBall n x) = -(r • x) := by
  -- Contractibility of the ball makes the normalized field nullhomotopic.
  letI : ContractibleSpace (ClosedUnitBall n) :=
    Metric.contractibleSpace_closedBall zero_le_one
  let w := normalizedBallVectorField v h_nonvanishing
  have w_null : w.Nullhomotopic := by
    have hid_null := id_nullhomotopic (ClosedUnitBall n)
    have hcomp := hid_null.comp_right w
    simpa [w] using hcomp
  let boundaryDirection := w.comp (StandardSphere.toBall n)
  have boundary_null : boundaryDirection.Nullhomotopic := by
    exact w_null.comp_left (StandardSphere.toBall n)
  -- If the boundary direction avoided every antipode, it would be homotopic to the identity.
  have exists_antipode : ∃ x : StandardSphere n, boundaryDirection x = -x := by
    by_contra hnone
    have havoid : ∀ x, boundaryDirection x ≠ -x := by
      simpa only [not_exists] using hnone
    have hid_null := boundary_null.trans_homotopic
      (StandardSphere.homotopic_id_of_avoidsAntipodes boundaryDirection havoid)
    exact sphere_id_not_nullhomotopic n h_noRetraction hid_null
  obtain ⟨x, hx⟩ := exists_antipode
  let r := ‖v (StandardSphere.toBall n x)‖
  have hr : 0 < r := by
    exact norm_pos_iff.mpr (h_nonvanishing (StandardSphere.toBall n x))
  refine ⟨x, r, hr, ?_⟩
  -- Rescale the equality of radial directions by the positive norm of the field value.
  have hxcoe := congrArg Subtype.val hx
  have hnormalized :
      ‖v (StandardSphere.toBall n x)‖⁻¹ • v (StandardSphere.toBall n x) =
        -(x : EuclideanSpace ℝ (Fin (n + 1))) := by
    simpa [boundaryDirection, w, normalizedBallVectorField_coe] using hxcoe
  have hscaled := congrArg
    (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ r • z) hnormalized
  simpa [r, smul_smul, hr.ne'] using hscaled

/-- Part (b) of Exercise 55.5. Assuming the standard sphere is not a retract of the
closed unit ball, its inclusion into punctured Euclidean space is not nullhomotopic. -/
theorem sphereInclusion_not_nullhomotopic (n : ℕ)
    (h_noRetraction : ¬ Set.IsRetract (StandardSphere.boundary n)) :
    ¬ (StandardSphere.toPunctured n).Nullhomotopic := by
  -- A nullhomotopy would remain null after radial projection and would become the identity.
  intro hinclusion
  have hid := hinclusion.comp_right (StandardSphere.radialRetraction n)
  apply sphere_id_not_nullhomotopic n h_noRetraction
  rwa [StandardSphere.radialRetraction_comp_toPunctured] at hid

/-- Outward-point companion for Exercise 55.5 (c). Every nonvanishing vector field
on the closed unit ball points directly outward at some point of the boundary sphere. -/
theorem nonvanishingBallVectorField_exists_outwardPoint (n : ℕ)
    (h_noRetraction : ¬ Set.IsRetract (StandardSphere.boundary n))
    (v : BallVectorField n) (h_nonvanishing : v.IsNonvanishing) :
    ∃ x : StandardSphere n, ∃ r : ℝ, 0 < r ∧
      v (StandardSphere.toBall n x) = r • x := by
  -- Apply the inward-point theorem to the negated vector field.
  obtain ⟨x, r, hr, hx⟩ := exists_inwardPoint_of_nonvanishing n h_noRetraction
    (negBallVectorField v) (negBallVectorField_isNonvanishing v h_nonvanishing)
  refine ⟨x, r, hr, ?_⟩
  have hneg := congrArg Neg.neg hx
  simpa [negBallVectorField] using hneg

/-- Inward-point companion for Exercise 55.5 (c). Every nonvanishing vector field
on the closed unit ball points directly inward at some point of the boundary sphere. -/
theorem nonvanishingBallVectorField_exists_inwardPoint (n : ℕ)
    (h_noRetraction : ¬ Set.IsRetract (StandardSphere.boundary n))
    (v : BallVectorField n) (h_nonvanishing : v.IsNonvanishing) :
    ∃ x : StandardSphere n, ∃ r : ℝ, 0 < r ∧
      v (StandardSphere.toBall n x) = -(r • x) := by
  -- Consume the normalized-boundary direction theorem directly.
  exact exists_inwardPoint_of_nonvanishing n h_noRetraction v h_nonvanishing

/-- Part (c) of Exercise 55.5. Every nonvanishing vector field on the closed unit ball
points directly outward somewhere on the boundary sphere and directly inward somewhere on it. -/
theorem nonvanishingBallVectorField_exists_outwardPoint_and_inwardPoint (n : ℕ)
    (h_noRetraction : ¬ Set.IsRetract (StandardSphere.boundary n))
    (v : BallVectorField n) (h_nonvanishing : v.IsNonvanishing) :
    (∃ x : StandardSphere n, ∃ r : ℝ, 0 < r ∧
      v (StandardSphere.toBall n x) = r • x) ∧
    ∃ x : StandardSphere n, ∃ r : ℝ, 0 < r ∧
      v (StandardSphere.toBall n x) = -(r • x) :=
  ⟨nonvanishingBallVectorField_exists_outwardPoint n h_noRetraction v h_nonvanishing,
    nonvanishingBallVectorField_exists_inwardPoint n h_noRetraction v h_nonvanishing⟩

/-- Helper for Exercise 55.5: the displacement `f x - x` of a continuous ball self-map
varies continuously in the ambient Euclidean space. -/
private theorem continuous_ballMapDisplacement {n : ℕ}
    (f : C(ClosedUnitBall n, ClosedUnitBall n)) :
    Continuous (fun x ↦
      (f x : EuclideanSpace ℝ (Fin (n + 1))) -
        (x : EuclideanSpace ℝ (Fin (n + 1)))) := by
  -- Both the self-map and the subtype inclusion are continuous.
  fun_prop

/-- Helper for Exercise 55.5: the ambient displacement vector field of a continuous
self-map of the closed unit ball. -/
private def ballMapDisplacement {n : ℕ}
    (f : C(ClosedUnitBall n, ClosedUnitBall n)) : BallVectorField n :=
  ⟨fun x ↦
    (f x : EuclideanSpace ℝ (Fin (n + 1))) -
      (x : EuclideanSpace ℝ (Fin (n + 1))),
    continuous_ballMapDisplacement f⟩

/-- Helper for Exercise 55.5: a fixed-point-free ball self-map has nonvanishing
displacement. -/
private theorem ballMapDisplacement_isNonvanishing {n : ℕ}
    (f : C(ClosedUnitBall n, ClosedUnitBall n))
    (hfree : ∀ x, f x ≠ x) : (ballMapDisplacement f).IsNonvanishing := by
  -- A zero displacement is precisely a fixed point after subtype extensionality.
  intro x hx
  apply hfree x
  apply Subtype.ext
  exact sub_eq_zero.mp hx

/-- Part (d) of Exercise 55.5. Every continuous self-map of the standard closed unit
ball has a fixed point. -/
theorem closedUnitBall_exists_fixedPoint (n : ℕ)
    (h_noRetraction : ¬ Set.IsRetract (StandardSphere.boundary n))
    (f : C(ClosedUnitBall n, ClosedUnitBall n)) :
    ∃ x, Function.IsFixedPt f x := by
  -- If there is no fixed point, the displacement field is nonvanishing.
  by_contra hnone
  have hfree : ∀ x, f x ≠ x := by
    simpa only [not_exists, Function.IsFixedPt] using hnone
  obtain ⟨x, r, hr, hx⟩ := nonvanishingBallVectorField_exists_outwardPoint n
    h_noRetraction (ballMapDisplacement f)
    (ballMapDisplacement_isNonvanishing f hfree)
  -- At an outward boundary point, the image has norm `1 + r`, outside the unit ball.
  have hambient :
      (f (StandardSphere.toBall n x) : EuclideanSpace ℝ (Fin (n + 1))) =
        (1 + r) • (x : EuclideanSpace ℝ (Fin (n + 1))) := by
    have hsum := sub_eq_iff_eq_add.mp hx
    simpa [ballMapDisplacement, StandardSphere.toBall_apply, add_smul, add_comm] using hsum
  have hnorm_le :
      ‖(f (StandardSphere.toBall n x) : EuclideanSpace ℝ (Fin (n + 1)))‖ ≤ 1 := by
    have hmem := (f (StandardSphere.toBall n x)).property
    rw [Metric.mem_closedBall] at hmem
    simpa only [dist_zero_right] using hmem
  have hxnorm : ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp x.property
  have hnorm_eq :
      ‖(f (StandardSphere.toBall n x) : EuclideanSpace ℝ (Fin (n + 1)))‖ =
        1 + r := by
    rw [hambient, norm_smul, hxnorm, mul_one, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  linarith

/-- Helper for Exercise 55.5: the ambient point selected as a nearest point of a nonempty
complete convex set. -/
private noncomputable def convexMetricProjectionPoint {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (s : Set E)
    (hne : s.Nonempty) (hcomplete : IsComplete s) (hconvex : Convex ℝ s)
    (x : E) : E :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex hne hcomplete hconvex x)

/-- Helper for Exercise 55.5: the selected nearest point belongs to its convex set. -/
private theorem convexMetricProjectionPoint_mem {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (s : Set E)
    (hne : s.Nonempty) (hcomplete : IsComplete s) (hconvex : Convex ℝ s)
    (x : E) : convexMetricProjectionPoint s hne hcomplete hconvex x ∈ s := by
  -- This is the membership component of the Hilbert projection theorem.
  exact (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex hne hcomplete hconvex x)).1

/-- Helper for Exercise 55.5: nearest-point projection onto a nonempty complete convex
set. -/
private noncomputable def convexMetricProjection {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (s : Set E)
    (hne : s.Nonempty) (hcomplete : IsComplete s) (hconvex : Convex ℝ s)
    (x : E) : s :=
  ⟨convexMetricProjectionPoint s hne hcomplete hconvex x,
    convexMetricProjectionPoint_mem s hne hcomplete hconvex x⟩

/-- Helper for Exercise 55.5: the selected projection realizes the infimal distance to
the convex set. -/
private theorem convexMetricProjection_spec {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (s : Set E)
    (hne : s.Nonempty) (hcomplete : IsComplete s) (hconvex : Convex ℝ s)
    (x : E) :
    ‖x - convexMetricProjection s hne hcomplete hconvex x‖ =
      ⨅ z : s, ‖x - z‖ := by
  -- This is the minimizing component of the Hilbert projection theorem.
  exact (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex hne hcomplete hconvex x)).2

/-- Helper for Exercise 55.5: metric projection onto a convex set does not increase
distances. -/
private theorem convexMetricProjection_dist_le {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (s : Set E)
    (hne : s.Nonempty) (hcomplete : IsComplete s) (hconvex : Convex ℝ s)
    (x y : E) :
    dist (convexMetricProjection s hne hcomplete hconvex x)
        (convexMetricProjection s hne hcomplete hconvex y) ≤ dist x y := by
  -- The variational inequalities at the two projected points give firm nonexpansiveness.
  let px : E := convexMetricProjection s hne hcomplete hconvex x
  let py : E := convexMetricProjection s hne hcomplete hconvex y
  have hxvar : ∀ z ∈ s, inner ℝ (x - px) (z - px) ≤ 0 := by
    exact (norm_eq_iInf_iff_real_inner_le_zero hconvex
      (convexMetricProjection s hne hcomplete hconvex x).property).mp
      (convexMetricProjection_spec s hne hcomplete hconvex x)
  have hyvar : ∀ z ∈ s, inner ℝ (y - py) (z - py) ≤ 0 := by
    exact (norm_eq_iInf_iff_real_inner_le_zero hconvex
      (convexMetricProjection s hne hcomplete hconvex y).property).mp
      (convexMetricProjection_spec s hne hcomplete hconvex y)
  have hx := hxvar py (convexMetricProjection s hne hcomplete hconvex y).property
  have hy := hyvar px (convexMetricProjection s hne hcomplete hconvex x).property
  have hxnonneg : 0 ≤ inner ℝ (x - px) (px - py) := by
    have hneg : py - px = -(px - py) := by abel
    rw [hneg, inner_neg_right] at hx
    linarith
  have hinnerIdentity :
      inner ℝ (x - px) (px - py) - inner ℝ (y - py) (px - py) =
        inner ℝ (x - y) (px - py) - inner ℝ (px - py) (px - py) := by
    rw [← inner_sub_left, ← inner_sub_left]
    congr 1
    abel
  have hsq : ‖px - py‖ ^ 2 ≤ inner ℝ (x - y) (px - py) := by
    rw [← real_inner_self_eq_norm_sq]
    have hdiff :
        0 ≤ inner ℝ (x - px) (px - py) - inner ℝ (y - py) (px - py) := by
      linarith
    rw [hinnerIdentity] at hdiff
    linarith
  have hinner := real_inner_le_norm (x - y) (px - py)
  have hnorm : ‖px - py‖ ≤ ‖x - y‖ := by
    by_cases hp : ‖px - py‖ = 0
    · rw [hp]
      exact norm_nonneg (x - y)
    · have hp_pos : 0 < ‖px - py‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hp)
      nlinarith
  simpa [px, py, Subtype.dist_eq, dist_eq_norm] using hnorm

/-- Helper for Exercise 55.5: metric projection onto a complete convex set is
continuous. -/
private theorem continuous_convexMetricProjection {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (s : Set E)
    (hne : s.Nonempty) (hcomplete : IsComplete s) (hconvex : Convex ℝ s) :
    Continuous (convexMetricProjection s hne hcomplete hconvex) := by
  -- The distance estimate is the Lipschitz condition with constant one.
  refine (LipschitzWith.of_dist_le_mul (K := 1) ?_).continuous
  intro x y
  simpa only [NNReal.coe_one, one_mul] using
    convexMetricProjection_dist_le s hne hcomplete hconvex x y

/-- Helper for Exercise 55.5: metric projection fixes every point already in the convex
set. -/
private theorem convexMetricProjection_leftInverse {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (s : Set E)
    (hne : s.Nonempty) (hcomplete : IsComplete s) (hconvex : Convex ℝ s) :
    Function.LeftInverse (convexMetricProjection s hne hcomplete hconvex) Subtype.val := by
  -- A point of the set has infimal distance zero, so its chosen nearest point is itself.
  intro x
  apply Subtype.ext
  have hinf : (⨅ z : s, ‖(x : E) - z‖) ≤ 0 := by
    have hbounded : BddBelow (Set.range (fun z : s ↦ ‖(x : E) - z‖)) := by
      exact ⟨0, Set.forall_mem_range.mpr (fun z ↦ norm_nonneg _)⟩
    simpa using ciInf_le hbounded x
  have hnorm :
      ‖(x : E) - convexMetricProjection s hne hcomplete hconvex x‖ = 0 := by
    have hspec := convexMetricProjection_spec s hne hcomplete hconvex (x : E)
    exact le_antisymm (hspec.trans_le hinf) (norm_nonneg _)
  have heq : (x : E) = convexMetricProjection s hne hcomplete hconvex x := by
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  exact heq.symm

/-- Helper for Exercise 55.5: the probability simplex inside Euclidean space consists of
nonnegative vectors whose coordinates sum to one. -/
private def euclideanProbabilitySimplex (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

/-- Helper for Exercise 55.5: the Euclidean probability simplex is nonempty. -/
private theorem euclideanProbabilitySimplex_nonempty (n : ℕ) :
    (euclideanProbabilitySimplex n).Nonempty := by
  -- The zeroth coordinate vector is a vertex of the simplex.
  classical
  refine ⟨WithLp.toLp 2 (Pi.single (0 : Fin (n + 1)) 1), ?_⟩
  constructor
  · intro i
    by_cases hi : i = 0
    · simp [hi]
    · simp [hi]
  · simp

/-- Helper for Exercise 55.5: the Euclidean probability simplex is closed. -/
private theorem isClosed_euclideanProbabilitySimplex (n : ℕ) :
    IsClosed (euclideanProbabilitySimplex n) := by
  -- Coordinate half-spaces and the coordinate-sum hyperplane are closed.
  have hnonneg : IsClosed
      {x : EuclideanSpace ℝ (Fin (n + 1)) | ∀ i, 0 ≤ x i} := by
    rw [show {x : EuclideanSpace ℝ (Fin (n + 1)) | ∀ i, 0 ≤ x i} =
        ⋂ i, {x | 0 ≤ x i} by ext x; simp]
    exact isClosed_iInter (fun i ↦
      isClosed_le continuous_const
        (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) ↦ ℝ) i))
  have hsum : IsClosed
      {x : EuclideanSpace ℝ (Fin (n + 1)) | ∑ i, x i = 1} := by
    exact isClosed_eq (by fun_prop) continuous_const
  simpa only [euclideanProbabilitySimplex, Set.setOf_and] using hnonneg.inter hsum

/-- Helper for Exercise 55.5: the Euclidean probability simplex is convex. -/
private theorem convex_euclideanProbabilitySimplex (n : ℕ) :
    Convex ℝ (euclideanProbabilitySimplex n) := by
  -- Convex combinations preserve coordinatewise nonnegativity and total mass one.
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, hx.2, hy.2, mul_one]
    exact hab

/-- Helper for Exercise 55.5: every Euclidean probability vector lies in the closed unit
ball. -/
private theorem euclideanProbabilitySimplex_subset_closedBall (n : ℕ) :
    euclideanProbabilitySimplex n ⊆
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  -- For coordinates in `[0,1]`, the sum of squares is at most the coordinate sum.
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  have hcoord_le (i : Fin (n + 1)) : x i ≤ 1 := by
    calc
      x i ≤ ∑ j, x j :=
        Finset.single_le_sum (fun j _ ↦ hx.1 j) (Finset.mem_univ i)
      _ = 1 := hx.2
  have hsquares : ∑ i, (x i) ^ 2 ≤ 1 := by
    calc
      ∑ i, (x i) ^ 2 ≤ ∑ i, x i := by
        exact Finset.sum_le_sum (fun i _ ↦ by
          nlinarith [hx.1 i, hcoord_le i])
      _ = 1 := hx.2
  have hnormsq := EuclideanSpace.real_norm_sq_eq x
  nlinarith [norm_nonneg x]

/-- Helper for Exercise 55.5: the Euclidean probability simplex is complete. -/
private theorem isComplete_euclideanProbabilitySimplex (n : ℕ) :
    IsComplete (euclideanProbabilitySimplex n) := by
  -- Closed subsets of the complete Euclidean space are complete.
  exact (isClosed_euclideanProbabilitySimplex n).isComplete

/-- Helper for Exercise 55.5: continuous nearest-point projection from Euclidean space
onto the probability simplex. -/
private noncomputable def probabilitySimplexProjection (n : ℕ) :
    C(EuclideanSpace ℝ (Fin (n + 1)), euclideanProbabilitySimplex n) :=
  ⟨convexMetricProjection (euclideanProbabilitySimplex n)
      (euclideanProbabilitySimplex_nonempty n)
      (isComplete_euclideanProbabilitySimplex n)
      (convex_euclideanProbabilitySimplex n),
    continuous_convexMetricProjection (euclideanProbabilitySimplex n)
      (euclideanProbabilitySimplex_nonempty n)
      (isComplete_euclideanProbabilitySimplex n)
      (convex_euclideanProbabilitySimplex n)⟩

/-- Helper for Exercise 55.5: probability-simplex projection fixes every probability
vector. -/
private theorem probabilitySimplexProjection_leftInverse (n : ℕ) :
    Function.LeftInverse (probabilitySimplexProjection n) Subtype.val := by
  -- Specialize the generic nearest-point projection's left-inverse property.
  exact convexMetricProjection_leftInverse (euclideanProbabilitySimplex n)
    (euclideanProbabilitySimplex_nonempty n)
    (isComplete_euclideanProbabilitySimplex n)
    (convex_euclideanProbabilitySimplex n)

/-- Helper for Exercise 55.5: inclusion of the probability simplex into the closed unit
ball. -/
private def probabilitySimplexToBall (n : ℕ) :
    C(euclideanProbabilitySimplex n, ClosedUnitBall n) :=
  ContinuousMap.inclusion (euclideanProbabilitySimplex_subset_closedBall n)

/-- Helper for Exercise 55.5: restricting probability-simplex projection to the closed
unit ball is continuous. -/
private theorem continuous_ballToProbabilitySimplex (n : ℕ) :
    Continuous (fun x : ClosedUnitBall n ↦ probabilitySimplexProjection n x) := by
  -- Compose the ambient projection with the ball's subtype inclusion.
  exact (probabilitySimplexProjection n).continuous.comp continuous_subtype_val

/-- Helper for Exercise 55.5: projection from the closed unit ball onto its probability
simplex. -/
private noncomputable def ballToProbabilitySimplex (n : ℕ) :
    C(ClosedUnitBall n, euclideanProbabilitySimplex n) :=
  ⟨fun x ↦ probabilitySimplexProjection n x,
    continuous_ballToProbabilitySimplex n⟩

/-- Helper for Exercise 55.5: projecting a probability vector after including it in the
ball returns that vector. -/
private theorem ballToProbabilitySimplex_leftInverse (n : ℕ)
    (x : euclideanProbabilitySimplex n) :
    ballToProbabilitySimplex n (probabilitySimplexToBall n x) = x := by
  -- Reduce to the ambient projection's left-inverse equation.
  exact probabilitySimplexProjection_leftInverse n x

/-- Helper for Exercise 55.5: extend a simplex self-map to the ball using nearest-point
projection. -/
private noncomputable def extendProbabilitySimplexMap (n : ℕ)
    (f : C(euclideanProbabilitySimplex n, euclideanProbabilitySimplex n)) :
    C(ClosedUnitBall n, ClosedUnitBall n) :=
  (probabilitySimplexToBall n).comp (f.comp (ballToProbabilitySimplex n))

/-- Helper for Exercise 55.5: every continuous self-map of the Euclidean probability
simplex has a fixed point. -/
private theorem euclideanProbabilitySimplex_exists_fixedPoint (n : ℕ)
    (h_noRetraction : ¬ Set.IsRetract (StandardSphere.boundary n))
    (f : C(euclideanProbabilitySimplex n, euclideanProbabilitySimplex n)) :
    ∃ x, Function.IsFixedPt f x := by
  -- Extend to the ball, take its Brouwer fixed point, and project the equation back.
  obtain ⟨y, hy⟩ := closedUnitBall_exists_fixedPoint n h_noRetraction
    (extendProbabilitySimplexMap n f)
  refine ⟨ballToProbabilitySimplex n y, ?_⟩
  have hprojected := congrArg (ballToProbabilitySimplex n) hy
  simpa [Function.IsFixedPt, extendProbabilitySimplexMap, ContinuousMap.comp_apply,
    ballToProbabilitySimplex_leftInverse] using hprojected

/-- Helper for Exercise 55.5: the total coordinate mass of the image of a probability
vector under a matrix. -/
private noncomputable def positiveMatrixScale {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (x : euclideanProbabilitySimplex n) : ℝ :=
  ∑ i, A.mulVec (fun j ↦ (x : EuclideanSpace ℝ (Fin (n + 1))) j) i

/-- Helper for Exercise 55.5: a strictly positive matrix has positive output in every
coordinate on the probability simplex. -/
private theorem positiveMatrix_mulVec_pos {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : ∀ i j, 0 < A i j)
    (x : euclideanProbabilitySimplex n) (i : Fin (n + 1)) :
    0 < A.mulVec (fun j ↦ (x : EuclideanSpace ℝ (Fin (n + 1))) j) i := by
  -- Some input coordinate is positive, and every matrix coefficient is positive.
  have hxsum : 0 < ∑ j, (x : EuclideanSpace ℝ (Fin (n + 1))) j := by
    rw [x.property.2]
    norm_num
  obtain ⟨j, hj_mem, hj⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun j _ ↦ x.property.1 j)).mp hxsum
  unfold Matrix.mulVec dotProduct
  exact (Finset.sum_pos_iff_of_nonneg
    (fun k _ ↦ mul_nonneg (hA i k).le (x.property.1 k))).mpr
    ⟨j, hj_mem, mul_pos (hA i j) hj⟩

/-- Helper for Exercise 55.5: the normalization scale of a positive matrix action on the
probability simplex is positive. -/
private theorem positiveMatrixScale_pos {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : ∀ i j, 0 < A i j)
    (x : euclideanProbabilitySimplex n) : 0 < positiveMatrixScale A x := by
  -- Sum the strictly positive output coordinates.
  unfold positiveMatrixScale
  exact Finset.sum_pos (fun i _ ↦ positiveMatrix_mulVec_pos A hA x i)
    Finset.univ_nonempty

/-- Helper for Exercise 55.5: the normalized value of a positive matrix on a probability
vector, represented in Euclidean space. -/
private noncomputable def normalizedPositiveMatrixValue {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (x : euclideanProbabilitySimplex n) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun i ↦
    A.mulVec (fun j ↦ (x : EuclideanSpace ℝ (Fin (n + 1))) j) i /
      positiveMatrixScale A x)

/-- Helper for Exercise 55.5: normalization sends the positive matrix image back to the
probability simplex. -/
private theorem normalizedPositiveMatrixValue_mem {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : ∀ i j, 0 < A i j)
    (x : euclideanProbabilitySimplex n) :
    normalizedPositiveMatrixValue A x ∈ euclideanProbabilitySimplex n := by
  -- Positivity gives nonnegative coordinates, while division by total mass gives sum one.
  constructor
  · intro i
    exact div_nonneg (positiveMatrix_mulVec_pos A hA x i).le
      (positiveMatrixScale_pos A hA x).le
  · simp only [normalizedPositiveMatrixValue, PiLp.toLp_apply]
    rw [← Finset.sum_div]
    exact div_self (positiveMatrixScale_pos A hA x).ne'

/-- Helper for Exercise 55.5: the positive-matrix normalization scale varies
continuously. -/
private theorem continuous_positiveMatrixScale {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Continuous (positiveMatrixScale A) := by
  -- Expand matrix multiplication into its two finite coordinate sums.
  unfold positiveMatrixScale Matrix.mulVec dotProduct
  apply continuous_finsetSum Finset.univ
  intro i _
  apply continuous_finsetSum Finset.univ
  intro j _
  exact continuous_const.mul
    ((PiLp.continuous_apply 2 (fun _ : Fin (n + 1) ↦ ℝ) j).comp
      continuous_subtype_val)

/-- Helper for Exercise 55.5: normalized positive-matrix values vary continuously on the
probability simplex. -/
private theorem continuous_normalizedPositiveMatrixValue {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : ∀ i j, 0 < A i j) :
    Continuous (normalizedPositiveMatrixValue A) := by
  -- Each coordinate is a continuous quotient with a positive denominator.
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) ↦ ℝ)).comp
  apply continuous_pi
  intro i
  have hnumerator : Continuous (fun x : euclideanProbabilitySimplex n ↦
      A.mulVec (fun j ↦ (x : EuclideanSpace ℝ (Fin (n + 1))) j) i) := by
    unfold Matrix.mulVec dotProduct
    apply continuous_finsetSum Finset.univ
    intro j _
    exact continuous_const.mul
      ((PiLp.continuous_apply 2 (fun _ : Fin (n + 1) ↦ ℝ) j).comp
        continuous_subtype_val)
  exact hnumerator.div (continuous_positiveMatrixScale A)
    (fun x ↦ (positiveMatrixScale_pos A hA x).ne')

/-- Helper for Exercise 55.5: the normalized action of a positive matrix on the
probability simplex. -/
private noncomputable def normalizedPositiveMatrixAction {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : ∀ i j, 0 < A i j) :
    C(euclideanProbabilitySimplex n, euclideanProbabilitySimplex n) :=
  ⟨fun x ↦ ⟨normalizedPositiveMatrixValue A x,
      normalizedPositiveMatrixValue_mem A hA x⟩,
    (continuous_normalizedPositiveMatrixValue A hA).subtype_mk _⟩

/-- Part (e) of Exercise 55.5. Every `(n + 1) × (n + 1)` real matrix with strictly
positive entries has a strictly positive real eigenvalue. -/
theorem Matrix.exists_pos_eigenvalue_of_pos_of_noRetraction (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : ∀ i j, 0 < A i j)
    (h_noRetraction : ¬ Set.IsRetract (StandardSphere.boundary n)) :
    ∃ μ : ℝ, 0 < μ ∧ Module.End.HasEigenvalue (Matrix.toLin' A) μ := by
  -- Brouwer supplies a fixed probability vector for the normalized positive action.
  obtain ⟨x, hx⟩ := euclideanProbabilitySimplex_exists_fixedPoint n h_noRetraction
    (normalizedPositiveMatrixAction A hA)
  let v : Fin (n + 1) → ℝ :=
    fun i ↦ (x : EuclideanSpace ℝ (Fin (n + 1))) i
  let μ := positiveMatrixScale A x
  have hμ : 0 < μ := positiveMatrixScale_pos A hA x
  have hcoord (i : Fin (n + 1)) : A.mulVec v i = μ * v i := by
    have hi := congrArg
      (fun y : euclideanProbabilitySimplex n ↦
        (y : EuclideanSpace ℝ (Fin (n + 1))) i) hx
    change A.mulVec v i / μ = v i at hi
    simpa [mul_comm] using (div_eq_iff hμ.ne').mp hi
  have hv_ne : v ≠ 0 := by
    -- A zero probability vector cannot have coordinate sum one.
    intro hv
    have hsum : ∑ i, v i = 1 := by
      simpa [v] using x.property.2
    rw [hv] at hsum
    simp at hsum
  refine ⟨μ, hμ, ?_⟩
  -- Assemble the fixed-point coordinate equations into a nonzero eigenvector.
  have heigen_eq : Matrix.toLin' A v = μ • v := by
    rw [Matrix.toLin'_apply]
    funext i
    simpa [Pi.smul_apply, smul_eq_mul] using hcoord i
  have hmem : v ∈ Module.End.eigenspace (Matrix.toLin' A) μ :=
    Module.End.mem_eigenspace_iff.mpr heigen_eq
  have heigenvector : Module.End.HasEigenvector (Matrix.toLin' A) μ v := by
    rw [Module.End.hasEigenvector_iff]
    constructor
    · exact hmem
    · exact hv_ne
  exact Module.End.hasEigenvalue_of_hasEigenvector heigenvector

/-- Fixed-point companion for Exercise 55.5 (f). Every nullhomotopic self-map of
the standard sphere has a fixed point. -/
theorem nullhomotopicSphereMap_exists_fixedPoint (n : ℕ)
    (h_noRetraction : ¬ Set.IsRetract (StandardSphere.boundary n))
    (h : C(StandardSphere n, StandardSphere n)) (h_null : h.Nullhomotopic) :
    ∃ x, Function.IsFixedPt h x := by
  -- Without a fixed point, the normalized straight-line homotopy reaches the antipodal map.
  by_contra hnone
  have hfree : ∀ x, h x ≠ x := by
    simpa only [not_exists, Function.IsFixedPt] using hnone
  have hantipodal_null := h_null.trans_homotopic
    (StandardSphere.homotopic_antipodal_of_fixedPointFree h hfree)
  -- Composing that nullhomotopy with the antipodal involution nullhomotopes the identity.
  have hid_null := hantipodal_null.comp_right (StandardSphere.antipodalMap n)
  apply sphere_id_not_nullhomotopic n h_noRetraction
  have hcomp :
      (StandardSphere.antipodalMap n).comp (StandardSphere.antipodalMap n) =
        ContinuousMap.id (StandardSphere n) := by
    apply ContinuousMap.ext
    intro x
    simp [StandardSphere.antipodalMap]
  rwa [hcomp] at hid_null

/-- Antipodal-point companion for Exercise 55.5 (f). Every nullhomotopic self-map
of the standard sphere maps some point to its antipode. -/
theorem nullhomotopicSphereMap_exists_mapsToAntipode (n : ℕ)
    (h_noRetraction : ¬ Set.IsRetract (StandardSphere.boundary n))
    (h : C(StandardSphere n, StandardSphere n)) (h_null : h.Nullhomotopic) :
    ∃ x, h x = -x := by
  -- If every antipode were avoided, the normalized segment would join `h` to the identity.
  by_contra hnone
  have havoid : ∀ x, h x ≠ -x := by
    simpa only [not_exists] using hnone
  have hid_null := h_null.trans_homotopic
    (StandardSphere.homotopic_id_of_avoidsAntipodes h havoid)
  -- This contradicts the identity obstruction supplied by non-retractability.
  exact sphere_id_not_nullhomotopic n h_noRetraction hid_null

/-- Part (f) of Exercise 55.5. Every nullhomotopic self-map of the standard sphere has a
fixed point and maps some point to its antipode. -/
theorem nullhomotopicSphereMap_exists_fixedPoint_and_mapsToAntipode (n : ℕ)
    (h_noRetraction : ¬ Set.IsRetract (StandardSphere.boundary n))
    (h : C(StandardSphere n, StandardSphere n)) (h_null : h.Nullhomotopic) :
    (∃ x, Function.IsFixedPt h x) ∧ ∃ x, h x = -x :=
  ⟨nullhomotopicSphereMap_exists_fixedPoint n h_noRetraction h h_null,
    nullhomotopicSphereMap_exists_mapsToAntipode n h_noRetraction h h_null⟩

/-- Exercise 55.5 theorem family: non-retractability yields the sphere-inclusion,
vector-field, fixed-point, positive-eigenvalue, and nullhomotopic-map conclusions. -/
theorem «Exercise 55.5 theorem family» (n : ℕ)
    (h_noRetraction : ¬ Set.IsRetract (StandardSphere.boundary n)) :
    ¬ (StandardSphere.toPunctured n).Nullhomotopic ∧
    (∀ (v : BallVectorField n), v.IsNonvanishing →
      ((∃ x : StandardSphere n, ∃ r : ℝ, 0 < r ∧
        v (StandardSphere.toBall n x) = r • x) ∧
      ∃ x : StandardSphere n, ∃ r : ℝ, 0 < r ∧
        v (StandardSphere.toBall n x) = -(r • x))) ∧
    (∀ f : C(ClosedUnitBall n, ClosedUnitBall n),
      ∃ x, Function.IsFixedPt f x) ∧
    (∀ (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ),
      (∀ i j, 0 < A i j) →
      ∃ μ : ℝ, 0 < μ ∧ Module.End.HasEigenvalue (Matrix.toLin' A) μ) ∧
    ∀ (h : C(StandardSphere n, StandardSphere n)), h.Nullhomotopic →
      (∃ x, Function.IsFixedPt h x) ∧ ∃ x, h x = -x := by
  -- Assemble the five established parts into the planner's source-facing family.
  refine ⟨sphereInclusion_not_nullhomotopic n h_noRetraction, ?_, ?_, ?_, ?_⟩
  · intro v h_nonvanishing
    exact nonvanishingBallVectorField_exists_outwardPoint_and_inwardPoint n
      h_noRetraction v h_nonvanishing
  · intro f
    exact closedUnitBall_exists_fixedPoint n h_noRetraction f
  · intro A hA
    exact Matrix.exists_pos_eigenvalue_of_pos_of_noRetraction n A hA h_noRetraction
  · intro h h_null
    exact nullhomotopicSphereMap_exists_fixedPoint_and_mapsToAntipode n
      h_noRetraction h h_null
