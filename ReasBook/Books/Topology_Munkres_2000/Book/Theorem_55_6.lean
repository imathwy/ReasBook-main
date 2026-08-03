module

public import Topology_Munkres_2000.Book.Definition_21_3.ClosedUnitDisk
import all Topology_Munkres_2000.Book.Definition_21_3.ClosedUnitDisk
import Topology_Munkres_2000.Book.Theorem_55_5

public section

/-- Helper for Theorem 55.6: the displacement of a continuous disk self-map is continuous. -/
private lemma continuous_closedUnitDiskDisplacement (f : C(B², B²)) :
    Continuous (fun x : B² ↦ (f x : EuclideanPlane) - (x : EuclideanPlane)) := by
  -- Compose with the ambient inclusions, then use continuity of subtraction.
  exact (continuous_subtype_val.comp f.continuous).sub continuous_subtype_val

/-- Helper for Theorem 55.6: the displacement vector field associated to a disk self-map. -/
private def closedUnitDiskDisplacement (f : C(B², B²)) : DiskVectorField :=
  ⟨fun x ↦ (f x : EuclideanPlane) - (x : EuclideanPlane),
    continuous_closedUnitDiskDisplacement f⟩

/-- Helper for Theorem 55.6: the displacement field evaluates to ambient subtraction. -/
private lemma closedUnitDiskDisplacement_apply (f : C(B², B²)) (x : B²) :
    closedUnitDiskDisplacement f x =
      (f x : EuclideanPlane) - (x : EuclideanPlane) := by
  -- Expose the sole computation rule needed from the bundled vector field.
  rfl

/-- Helper for Theorem 55.6: a fixed-point-free map has nonvanishing displacement. -/
private lemma closedUnitDiskDisplacement_isNonvanishing (f : C(B², B²))
    (hfree : ∀ x, ¬ Function.IsFixedPt f x) :
    (closedUnitDiskDisplacement f).IsNonvanishing := by
  intro x hzero
  -- A zero ambient displacement makes the two subtype values equal.
  have hvalue : (f x : EuclideanPlane) - (x : EuclideanPlane) = 0 := by
    simpa only [closedUnitDiskDisplacement_apply] using hzero
  apply hfree x
  apply Subtype.ext
  exact sub_eq_zero.mp hvalue

/-- Helper for Theorem 55.6: positive radial displacement from the unit sphere leaves the ball. -/
private lemma normExceedsOneOfPositiveRadialDisplacement
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : E} {r : ℝ} (hx : ‖x‖ = 1) (hr : 0 < r)
    (hdisplacement : y - x = r • x) : 1 < ‖y‖ := by
  -- Rewrite the endpoint as a positive scalar multiple of the unit vector.
  have hy : y = (r + 1) • x := by
    calc
      y = r • x + x := sub_eq_iff_eq_add.mp hdisplacement
      _ = (r + 1) • x := by rw [add_smul, one_smul]
  have hscalar : 0 < r + 1 := by
    linarith
  -- Homogeneity of the norm reduces the claim to the positivity of `r`.
  rw [hy, norm_smul, Real.norm_eq_abs, abs_of_pos hscalar, hx, mul_one]
  linarith

/-- Theorem 55.6 (Brouwer fixed-point theorem for the disc): Every continuous
self-map of the closed unit disk has a fixed point. -/
theorem closedUnitDisk_exists_fixedPoint
    (f : B² → B²) (hf : Continuous f) :
    ∃ x, Function.IsFixedPt f x := by
  classical
  let F : C(B², B²) := ⟨f, hf⟩
  by_contra hfixed
  simp only [not_exists] at hfixed
  have hfree : ∀ x, ¬ Function.IsFixedPt F x := by
    intro x hx
    exact hfixed x hx
  -- Theorem 55.5 supplies an outward-pointing boundary displacement.
  obtain ⟨x, hxboundary, r, hr, hout⟩ :=
    (closedUnitDiskDisplacement F).exists_pointingOutwardOnBoundary
      (closedUnitDiskDisplacement_isNonvanishing F hfree)
  have hxnorm : ‖(x : EuclideanPlane)‖ = 1 := by
    simpa only [ClosedUnitDisk.IsBoundary] using hxboundary
  have hdisplacement :
      (F x : EuclideanPlane) - (x : EuclideanPlane) = r • (x : EuclideanPlane) := by
    simpa only [closedUnitDiskDisplacement_apply] using hout
  have houtside : 1 < ‖(F x : EuclideanPlane)‖ :=
    normExceedsOneOfPositiveRadialDisplacement hxnorm hr hdisplacement
  -- Membership of `F x` in the closed disk gives the contradictory upper bound.
  have hinside : ‖(F x : EuclideanPlane)‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (F x).property
  linarith

namespace ClosedUnitDisk

/-- Every bundled continuous self-map of the closed unit disk has a fixed point. -/
theorem exists_fixedPoint (f : C(B², B²)) :
    ∃ x, Function.IsFixedPt f x :=
  closedUnitDisk_exists_fixedPoint f f.continuous

end ClosedUnitDisk
