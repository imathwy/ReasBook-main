module

public import Topology_Munkres_2000.Book.Example_22_4.BoundaryCollapse
import all Topology_Munkres_2000.Book.Definition_21_3.ClosedUnitDisk
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Homeomorph.Quotient

public section

namespace DiskBoundaryQuotient

open ClosedUnitDisk

/-- Helper for Example 22.4: coordinates for the disk map to the two-sphere. -/
private noncomputable def sphereCoordinates (x : ClosedUnitDisk) :
    EuclideanSpace ℝ (Fin 3) :=
  !₂[2 * √(1 - ‖(x : EuclideanSpace ℝ (Fin 2))‖ ^ 2) * x.1 0,
    2 * √(1 - ‖(x : EuclideanSpace ℝ (Fin 2))‖ ^ 2) * x.1 1,
    2 * ‖(x : EuclideanSpace ℝ (Fin 2))‖ ^ 2 - 1]

/-- Helper for Example 22.4: the disk coordinates lie on the unit two-sphere. -/
private lemma sphereCoordinates_mem_sphere (x : ClosedUnitDisk) :
    sphereCoordinates x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  -- The disk bound makes the radicand nonnegative.
  have hxnorm : ‖(x : EuclideanSpace ℝ (Fin 2))‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
  have hrad : 0 ≤ 1 - ‖(x : EuclideanSpace ℝ (Fin 2))‖ ^ 2 := by
    nlinarith [norm_nonneg (x : EuclideanSpace ℝ (Fin 2))]
  have hxy : (x.1 0) ^ 2 + (x.1 1) ^ 2 =
      ‖(x : EuclideanSpace ℝ (Fin 2))‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  -- Expanding the three coordinates reduces the sphere equation to the square-root identity.
  rw [EuclideanSpace.sphere_zero_eq 1 zero_le_one]
  simp only [Set.mem_setOf_eq, sphereCoordinates, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Fin.succ_zero_eq_one]
  ring_nf
  nlinarith [Real.sq_sqrt hrad]

/-- Helper for Example 22.4: the coordinate vector packaged as a point of the sphere. -/
private noncomputable def spherePoint (x : ClosedUnitDisk) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨sphereCoordinates x, sphereCoordinates_mem_sphere x⟩

/-- Helper for Example 22.4: the explicit disk-to-sphere map is continuous. -/
private lemma continuous_spherePoint : Continuous spherePoint := by
  -- Continuity is checked coordinatewise after forgetting the sphere subtype.
  apply continuous_induced_rng.mpr
  unfold spherePoint sphereCoordinates
  fun_prop

/-- Helper for Example 22.4: the bundled continuous disk-to-sphere map. -/
private noncomputable def sphereMap :
    C(ClosedUnitDisk, Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  ⟨spherePoint, continuous_spherePoint⟩

/-- Helper for Example 22.4: equality of sphere images is exactly the boundary-collapse
relation. -/
private lemma spherePoint_eq_iff (x y : ClosedUnitDisk) :
    spherePoint x = spherePoint y ↔ setoid x y := by
  constructor
  · intro h
    -- The height coordinate first recovers equality of the squared radii.
    have hcoords : sphereCoordinates x = sphereCoordinates y := congrArg Subtype.val h
    have hradius : ‖(x : EuclideanSpace ℝ (Fin 2))‖ ^ 2 =
        ‖(y : EuclideanSpace ℝ (Fin 2))‖ ^ 2 := by
      have hlast := congrArg (fun z : EuclideanSpace ℝ (Fin 3) ↦ z 2) hcoords
      simp only [sphereCoordinates, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
        Function.comp_apply, Fin.succ_zero_eq_one, Matrix.cons_val_one,
        Matrix.cons_val_zero] at hlast
      linarith
    have hnormEq : ‖(x : EuclideanSpace ℝ (Fin 2))‖ =
        ‖(y : EuclideanSpace ℝ (Fin 2))‖ :=
      (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hradius
    rw [setoid_rel_iff]
    by_cases hx : ‖(x : EuclideanSpace ℝ (Fin 2))‖ = 1
    · right
      constructor
      · exact hx
      · exact hnormEq.symm.trans hx
    · left
      have hxnorm : ‖(x : EuclideanSpace ℝ (Fin 2))‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
      have hxlt : ‖(x : EuclideanSpace ℝ (Fin 2))‖ < 1 := lt_of_le_of_ne hxnorm hx
      have hrad : 0 < 1 - ‖(x : EuclideanSpace ℝ (Fin 2))‖ ^ 2 := by
        nlinarith [norm_nonneg (x : EuclideanSpace ℝ (Fin 2))]
      have hscale : 2 * √(1 - ‖(x : EuclideanSpace ℝ (Fin 2))‖ ^ 2) ≠ 0 := by
        exact mul_ne_zero (by norm_num) (ne_of_gt (Real.sqrt_pos.2 hrad))
      -- The nonzero radial scale then recovers both planar coordinates.
      apply Subtype.ext
      ext i
      fin_cases i
      · have hzero : 2 * √(1 - ‖(x : EuclideanSpace ℝ (Fin 2))‖ ^ 2) * x.1 0 =
            2 * √(1 - ‖(y : EuclideanSpace ℝ (Fin 2))‖ ^ 2) * y.1 0 := by
          simpa only [sphereCoordinates, Matrix.cons_val_zero] using
            congrArg (fun z : EuclideanSpace ℝ (Fin 3) ↦ z 0) hcoords
        rw [← hradius] at hzero
        exact mul_left_cancel₀ hscale hzero
      · have hone : 2 * √(1 - ‖(x : EuclideanSpace ℝ (Fin 2))‖ ^ 2) * x.1 1 =
            2 * √(1 - ‖(y : EuclideanSpace ℝ (Fin 2))‖ ^ 2) * y.1 1 := by
          simpa only [sphereCoordinates, Matrix.cons_val_one, Matrix.cons_val_zero] using
            congrArg (fun z : EuclideanSpace ℝ (Fin 3) ↦ z 1) hcoords
        rw [← hradius] at hone
        exact mul_left_cancel₀ hscale hone
  · intro h
    -- Equal points map equally; two boundary points both map to the north pole.
    rw [setoid_rel_iff] at h
    rcases h with rfl | ⟨hx, hy⟩
    · rfl
    · change ‖(x : EuclideanSpace ℝ (Fin 2))‖ = 1 at hx
      change ‖(y : EuclideanSpace ℝ (Fin 2))‖ = 1 at hy
      apply Subtype.ext
      ext i
      fin_cases i <;> simp [spherePoint, sphereCoordinates, hx, hy]

/-- Helper for Example 22.4: raw disk coordinates chosen above a sphere point. -/
private noncomputable def spherePreimageCoordinates
    (q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 2) :=
  if q.1 2 = 1 then !₂[1, 0]
  else !₂[q.1 0 / √(2 * (1 - q.1 2)), q.1 1 / √(2 * (1 - q.1 2))]

/-- Helper for Example 22.4: the chosen preimage lies in the disk and has the prescribed
squared radius. -/
private lemma spherePreimageCoordinates_spec
    (q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    spherePreimageCoordinates q ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
      ‖spherePreimageCoordinates q‖ ^ 2 = (q.1 2 + 1) / 2 := by
  -- The sphere equation controls both the last coordinate and the planar numerator.
  have hsphere : q.1 0 ^ 2 + q.1 1 ^ 2 + q.1 2 ^ 2 = 1 := by
    have hmem : q.1 ∈ {x : EuclideanSpace ℝ (Fin 3) | ∑ i, x i ^ 2 = 1 ^ 2} :=
      (Set.ext_iff.mp (EuclideanSpace.sphere_zero_eq 1 zero_le_one) q.1).mp q.property
    simpa only [Set.mem_setOf_eq, Fin.sum_univ_three, one_pow] using hmem
  have hzle : q.1 2 ≤ 1 := by
    nlinarith [sq_nonneg (q.1 0), sq_nonneg (q.1 1), sq_nonneg (q.1 2)]
  by_cases hz : q.1 2 = 1
  · constructor
    · rw [Metric.mem_closedBall, dist_zero_right]
      have hone : ‖(!₂[1, 0] : EuclideanSpace ℝ (Fin 2))‖ ^ 2 = 1 := by
        rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
        norm_num
      simp only [spherePreimageCoordinates, if_pos hz]
      nlinarith [norm_nonneg (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))]
    · simp only [spherePreimageCoordinates, EuclideanSpace.real_norm_sq_eq,
        Fin.sum_univ_two, hz]
      norm_num
  · have hzlt : q.1 2 < 1 := lt_of_le_of_ne hzle hz
    have hrad : 0 < 2 * (1 - q.1 2) := by positivity
    have hsqrt : √(2 * (1 - q.1 2)) ^ 2 = 2 * (1 - q.1 2) :=
      Real.sq_sqrt hrad.le
    have hsqrtne : √(2 * (1 - q.1 2)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hrad)
    have hnorm : ‖spherePreimageCoordinates q‖ ^ 2 = (q.1 2 + 1) / 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [spherePreimageCoordinates, if_neg hz, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      field_simp
      nlinarith
    constructor
    · rw [Metric.mem_closedBall, dist_zero_right]
      nlinarith [norm_nonneg (spherePreimageCoordinates q)]
    · exact hnorm

/-- Helper for Example 22.4: the chosen raw coordinates packaged as a disk point. -/
private noncomputable def spherePreimage
    (q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : ClosedUnitDisk :=
  ⟨spherePreimageCoordinates q, (spherePreimageCoordinates_spec q).1⟩

/-- Helper for Example 22.4: applying the sphere map to the chosen disk preimage returns the
original sphere point. -/
private lemma spherePoint_spherePreimage
    (q : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    spherePoint (spherePreimage q) = q := by
  -- Recover the sphere equation and the prescribed squared radius once for all coordinates.
  have hsphere : q.1 0 ^ 2 + q.1 1 ^ 2 + q.1 2 ^ 2 = 1 := by
    have hmem : q.1 ∈ {x : EuclideanSpace ℝ (Fin 3) | ∑ i, x i ^ 2 = 1 ^ 2} :=
      (Set.ext_iff.mp (EuclideanSpace.sphere_zero_eq 1 zero_le_one) q.1).mp q.property
    simpa only [Set.mem_setOf_eq, Fin.sum_univ_three, one_pow] using hmem
  have hnorm : ‖spherePreimageCoordinates q‖ ^ 2 = (q.1 2 + 1) / 2 :=
    (spherePreimageCoordinates_spec q).2
  have hheight : 2 * ‖spherePreimageCoordinates q‖ ^ 2 - 1 = q.1 2 := by
    linarith
  by_cases hz : q.1 2 = 1
  · have hzero : q.1 0 = 0 := by
      nlinarith [sq_nonneg (q.1 0), sq_nonneg (q.1 1)]
    have hone : q.1 1 = 0 := by
      nlinarith [sq_nonneg (q.1 0), sq_nonneg (q.1 1)]
    have hnormOne : ‖spherePreimageCoordinates q‖ ^ 2 = 1 := by
      rw [hnorm, hz]
      norm_num
    have hscaleZero : √(1 - ‖spherePreimageCoordinates q‖ ^ 2) = 0 := by
      rw [hnormOne]
      norm_num
    -- At the north pole the chosen boundary point has vanishing planar image.
    apply Subtype.ext
    change sphereCoordinates (spherePreimage q) = q.1
    ext i
    fin_cases i
    · change 2 * √(1 - ‖spherePreimageCoordinates q‖ ^ 2) *
          spherePreimageCoordinates q 0 = q.1 0
      rw [hscaleZero]
      simp [spherePreimageCoordinates, hz, hzero]
    · change 2 * √(1 - ‖spherePreimageCoordinates q‖ ^ 2) *
          spherePreimageCoordinates q 1 = q.1 1
      rw [hscaleZero]
      simp [spherePreimageCoordinates, hz, hone]
    · change 2 * ‖spherePreimageCoordinates q‖ ^ 2 - 1 = q.1 2
      exact hheight
  · have hzle : q.1 2 ≤ 1 := by
      nlinarith [sq_nonneg (q.1 0), sq_nonneg (q.1 1), sq_nonneg (q.1 2)]
    have hzlt : q.1 2 < 1 := lt_of_le_of_ne hzle hz
    have hdenrad : 0 < 2 * (1 - q.1 2) := by positivity
    have hdenne : √(2 * (1 - q.1 2)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hdenrad)
    have hpreRad : 0 ≤ 1 - ‖spherePreimageCoordinates q‖ ^ 2 := by
      rw [hnorm]
      linarith
    have hscale : 2 * √(1 - ‖spherePreimageCoordinates q‖ ^ 2) =
        √(2 * (1 - q.1 2)) := by
      nlinarith [Real.sq_sqrt hpreRad, Real.sq_sqrt hdenrad.le,
        Real.sqrt_nonneg (1 - ‖spherePreimageCoordinates q‖ ^ 2),
        Real.sqrt_nonneg (2 * (1 - q.1 2))]
    -- Away from the north pole the positive radial scale cancels the inverse denominator.
    apply Subtype.ext
    change sphereCoordinates (spherePreimage q) = q.1
    ext i
    fin_cases i
    · change 2 * √(1 - ‖spherePreimageCoordinates q‖ ^ 2) *
          spherePreimageCoordinates q 0 = q.1 0
      rw [hscale]
      simpa only [spherePreimageCoordinates, if_neg hz, Matrix.cons_val_zero] using
        mul_div_cancel₀ (q.1 0) hdenne
    · change 2 * √(1 - ‖spherePreimageCoordinates q‖ ^ 2) *
          spherePreimageCoordinates q 1 = q.1 1
      rw [hscale]
      simpa only [spherePreimageCoordinates, if_neg hz, Matrix.cons_val_one,
        Matrix.cons_val_zero] using
        mul_div_cancel₀ (q.1 1) hdenne
    · change 2 * ‖spherePreimageCoordinates q‖ ^ 2 - 1 = q.1 2
      exact hheight

/-- Example 22.4: The quotient of the closed unit disk obtained by collapsing its boundary
circle to one point is homeomorphic to the unit two-sphere. -/
theorem homeomorphicTwoSphere :
    Nonempty (Space ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  -- The explicit preimage proves that the continuous disk map is onto the sphere.
  have hsurjective : Function.Surjective sphereMap := by
    intro q
    exact ⟨spherePreimage q, spherePoint_spherePreimage q⟩
  have hquotient : Topology.IsQuotientMap sphereMap :=
    Topology.IsQuotientMap.of_surjective_continuous hsurjective continuous_spherePoint
  -- Its kernel is the boundary-collapse relation, so the two canonical quotient
  -- homeomorphisms compose to the required presentation.
  have hkernel : ∀ x y : ClosedUnitDisk,
      setoid x y ↔ Setoid.ker sphereMap x y := by
    intro x y
    change setoid x y ↔ spherePoint x = spherePoint y
    exact (spherePoint_eq_iff x y).symm
  exact ⟨(Homeomorph.Quotient.congrRight hkernel).trans hquotient.homeomorph⟩

end DiskBoundaryQuotient

end
