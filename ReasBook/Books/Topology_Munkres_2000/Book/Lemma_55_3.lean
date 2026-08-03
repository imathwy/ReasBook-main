module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Category.TopCat.Sphere
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Homotopy.Contractible

public section

open TopCat

universe u

/-- Helper for Lemma 55.3: the Euclidean plane used by the canonical disk model. -/
private abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Helper for Lemma 55.3: the radial coordinate of a point in the cone on
`∂𝔻 2`. -/
private def diskConePoint (p : unitInterval × ∂𝔻 2) : Plane :=
  (1 - (p.1 : ℝ)) • (p.2.down : Plane)

/-- Helper for Lemma 55.3: every radial cone coordinate lies in the closed
unit disk. -/
private theorem diskConePoint_mem (p : unitInterval × ∂𝔻 2) :
    diskConePoint p ∈ Metric.closedBall (0 : Plane) 1 := by
  -- The radial coefficient lies in `[0,1]`, while the boundary vector has norm one.
  rw [Metric.mem_closedBall, dist_zero_right, diskConePoint, norm_smul]
  have hnorm : ‖(p.2.down : Plane)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.2.down.property
  rw [hnorm, mul_one, Real.norm_eq_abs, abs_of_nonneg]
  · linarith [unitInterval.nonneg p.1]
  · linarith [unitInterval.le_one p.1]

/-- Helper for Lemma 55.3: the radial cone coordinate varies continuously. -/
private theorem continuous_diskConePoint : Continuous diskConePoint := by
  -- Scalar multiplication is continuous in both the time and boundary coordinates.
  unfold diskConePoint
  fun_prop

/-- Helper for Lemma 55.3: the cone on `∂𝔻 2` maps radially onto `𝔻 2`. -/
private def diskConeProjection : C(unitInterval × ∂𝔻 2, 𝔻 2) :=
  ⟨fun p ↦ ULift.up ⟨diskConePoint p, diskConePoint_mem p⟩,
    continuous_uliftUp.comp (continuous_diskConePoint.subtype_mk _)⟩

/-- Helper for Lemma 55.3: the radial cone projection at time zero is the
boundary inclusion. -/
private theorem diskConeProjection_zero (x : ∂𝔻 2) :
    diskConeProjection (0, x) = (diskBoundaryInclusion 2).hom x := by
  -- At time zero the radial coefficient is one, so the underlying vector is unchanged.
  apply ULift.ext
  apply Subtype.ext
  change (1 - (0 : ℝ)) • (x.down : Plane) = (x.down : Plane)
  simp

/-- Helper for Lemma 55.3: the radial cone projection is onto the closed disk. -/
private theorem diskConeProjection_surjective : Function.Surjective diskConeProjection := by
  -- A nonzero disk point is its norm times its normalization; the origin uses a fixed unit vector.
  rintro ⟨⟨x, hx⟩⟩
  have hxnorm : ‖x‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  by_cases hxzero : x = 0
  · let v : Plane := EuclideanSpace.single 0 1
    have hvnorm : ‖v‖ = 1 := by
      simp [v]
    have hvsphere : v ∈ Metric.sphere (0 : Plane) 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hvnorm
    let q : ∂𝔻 2 := ULift.up ⟨v, hvsphere⟩
    refine ⟨(1, q), ?_⟩
    apply ULift.ext
    apply Subtype.ext
    simp [diskConeProjection, diskConePoint, hxzero]
  · have hnorm_nonneg : 0 ≤ ‖x‖ := norm_nonneg x
    have ht_le_one : 1 - ‖x‖ ≤ 1 := by linarith
    let t : unitInterval := ⟨1 - ‖x‖, sub_nonneg.mpr hxnorm, ht_le_one⟩
    have hnormalize : ‖NormedSpace.normalize x‖ = 1 :=
      NormedSpace.norm_normalize hxzero
    have hnormalize_sphere :
        NormedSpace.normalize x ∈ Metric.sphere (0 : Plane) 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hnormalize
    let q : ∂𝔻 2 := ULift.up ⟨NormedSpace.normalize x, hnormalize_sphere⟩
    refine ⟨(t, q), ?_⟩
    apply ULift.ext
    apply Subtype.ext
    simp only [diskConeProjection, diskConePoint, ContinuousMap.coe_mk, t, q,
      ULift.down_up]
    rw [sub_sub_cancel, NormedSpace.norm_smul_normalize]

/-- Helper for Lemma 55.3: two cone points have the same radial image only
when they coincide or both lie at the collapsed apex. -/
private theorem diskConeProjection_fiber
    (p q : unitInterval × ∂𝔻 2)
    (hpq : diskConeProjection p = diskConeProjection q) :
    p = q ∨ (p.1 = 1 ∧ q.1 = 1) := by
  -- Comparing norms first identifies the two time coordinates.
  have hvector : diskConePoint p = diskConePoint q := by
    exact congrArg (fun z : 𝔻 2 ↦ (z.down.val : Plane)) hpq
  have hp_norm : ‖(p.2.down : Plane)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.2.down.property
  have hq_norm : ‖(q.2.down : Plane)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using q.2.down.property
  have htime_val : (p.1 : ℝ) = q.1 := by
    have hnorm := congrArg norm hvector
    simp only [diskConePoint, norm_smul, hp_norm, hq_norm, mul_one,
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
    apply ULift.ext
    apply Subtype.ext
    have hscalar : (1 - (p.1 : ℝ)) ≠ 0 := by
      intro hzero
      apply hapex
      apply Subtype.ext
      exact (sub_eq_zero.mp hzero).symm
    apply smul_right_injective Plane hscalar
    simpa only [diskConePoint, htime] using hvector

/-- Helper for Lemma 55.3: the radial cone projection is a quotient map. -/
private theorem diskConeProjection_isQuotientMap :
    Topology.IsQuotientMap diskConeProjection := by
  -- A continuous surjection from the compact cone to the Hausdorff disk is quotient.
  letI : T2Space (𝔻 2) := by
    change T2Space (ULift (Metric.closedBall (0 : Plane) 1))
    infer_instance
  exact Topology.IsQuotientMap.of_surjective_continuous
    diskConeProjection_surjective diskConeProjection.continuous

/-- Helper for Lemma 55.3: a nullhomotopy is constant on every fiber of the
radial cone projection. -/
private theorem nullhomotopy_factors_diskConeProjection {X : Type u}
    [TopologicalSpace X] {h : C(∂𝔻 2, X)} {x : X}
    (H : h.Homotopy (ContinuousMap.const _ x)) :
    Function.FactorsThrough H.toContinuousMap diskConeProjection := by
  -- Equal non-apex points are identical; all apex points are sent to the constant endpoint.
  intro p q hpq
  rcases diskConeProjection_fiber p q hpq with rfl | ⟨hp, hq⟩
  · rfl
  · have hp_pair : p = (1, p.2) := Prod.ext hp rfl
    have hq_pair : q = (1, q.2) := Prod.ext hq rfl
    rw [hp_pair, hq_pair]
    change H (1, p.2) = H (1, q.2)
    rw [H.apply_one, H.apply_one]
    rfl

/-- Helper for Lemma 55.3: descending a nullhomotopy along the radial quotient
gives a map on the closed disk. -/
private noncomputable def diskConeExtension {X : Type u} [TopologicalSpace X]
    {h : C(∂𝔻 2, X)} {x : X}
    (H : h.Homotopy (ContinuousMap.const _ x)) : C(𝔻 2, X) :=
  diskConeProjection_isQuotientMap.lift H.toContinuousMap
    (nullhomotopy_factors_diskConeProjection H)

/-- Helper for Lemma 55.3: the descended cone map restricts to the original
boundary map. -/
private theorem diskConeExtension_comp_boundary {X : Type u} [TopologicalSpace X]
    {h : C(∂𝔻 2, X)} {x : X}
    (H : h.Homotopy (ContinuousMap.const _ x)) :
    (diskConeExtension H).comp (diskBoundaryInclusion 2).hom = h := by
  -- Evaluate the quotient lift on the time-zero representative of each boundary point.
  apply ContinuousMap.ext
  intro q
  rw [ContinuousMap.comp_apply, ← diskConeProjection_zero q]
  have hlift := congrArg (fun f : C(unitInterval × ∂𝔻 2, X) ↦ f (0, q))
    (diskConeProjection_isQuotientMap.lift_comp H.toContinuousMap
      (nullhomotopy_factors_diskConeProjection H))
  exact hlift.trans (H.apply_zero q)

/-- Helper for Lemma 55.3: the canonical two-dimensional disk is contractible. -/
private theorem diskTwoContractibleSpace : ContractibleSpace (𝔻 2) := by
  -- Transport convex contractibility of the closed Euclidean ball across `ULift`.
  letI : ContractibleSpace (Metric.closedBall (0 : Plane) 1) :=
    Metric.contractibleSpace_closedBall (by positivity)
  change ContractibleSpace (ULift (Metric.closedBall (0 : Plane) 1))
  exact Homeomorph.ulift.contractibleSpace

/-- Helper for Lemma 55.3: the standard real-linear isometry identifies the
Euclidean plane with the complex plane. -/
private noncomputable def planeComplexIsometry : Plane ≃ᵢ ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

/-- Helper for Lemma 55.3: the plane-complex isometry carries the real unit
sphere onto the complex unit circle. -/
private theorem planeComplexIsometry_image_unitSphere :
    planeComplexIsometry '' (Metric.sphere 0 1 : Set Plane) =
      (Submonoid.unitSphere ℂ : Set ℂ) := by
  -- Isometries preserve spheres and the chosen linear isometry fixes the origin.
  rw [planeComplexIsometry.image_sphere]
  simp [Submonoid.unitSphere, planeComplexIsometry]

/-- Helper for Lemma 55.3: the canonical disk boundary is homeomorphic to the
complex unit circle. -/
private noncomputable def diskBoundaryHomeomorphCircle : ∂𝔻 2 ≃ₜ Circle :=
  Homeomorph.ulift.trans
    ((planeComplexIsometry.toHomeomorph.isEmbedding.homeomorphImage
      (Metric.sphere 0 1)).trans
        (Homeomorph.setCongr planeComplexIsometry_image_unitSphere))

/-- Helper for Lemma 55.3: the standard once-around loop based at `b₀` in
the disk boundary. -/
private noncomputable def diskBoundaryLoopValue (b₀ : ∂𝔻 2)
    (t : unitInterval) : ∂𝔻 2 :=
  diskBoundaryHomeomorphCircle.symm
    (Circle.exp ((t : ℝ) * (2 * Real.pi)) * diskBoundaryHomeomorphCircle b₀)

/-- Helper for Lemma 55.3: the standard boundary loop is continuous. -/
private theorem continuous_diskBoundaryLoopValue (b₀ : ∂𝔻 2) :
    Continuous (diskBoundaryLoopValue b₀) := by
  -- Compose the exponential parametrization, multiplication, and the inverse homeomorphism.
  unfold diskBoundaryLoopValue
  fun_prop

/-- Helper for Lemma 55.3: the standard boundary loop starts at its prescribed
basepoint. -/
private theorem diskBoundaryLoopValue_zero (b₀ : ∂𝔻 2) :
    diskBoundaryLoopValue b₀ 0 = b₀ := by
  -- The exponential at angle zero is the identity of the circle.
  simp [diskBoundaryLoopValue]

/-- Helper for Lemma 55.3: the standard boundary loop ends at its prescribed
basepoint. -/
private theorem diskBoundaryLoopValue_one (b₀ : ∂𝔻 2) :
    diskBoundaryLoopValue b₀ 1 = b₀ := by
  -- The exponential at angle `2 * π` is again the identity of the circle.
  simp [diskBoundaryLoopValue]

/-- Helper for Lemma 55.3: the standard once-around parametrization is a loop
in the disk boundary. -/
private noncomputable def diskBoundaryLoop (b₀ : ∂𝔻 2) : Path b₀ b₀ :=
  ⟨⟨diskBoundaryLoopValue b₀, continuous_diskBoundaryLoopValue b₀⟩,
    diskBoundaryLoopValue_zero b₀, diskBoundaryLoopValue_one b₀⟩

/-- Helper for Lemma 55.3: evaluation of the standard boundary loop uses its
explicit exponential parametrization. -/
private theorem diskBoundaryLoop_apply (b₀ : ∂𝔻 2) (t : unitInterval) :
    diskBoundaryLoop b₀ t = diskBoundaryLoopValue b₀ t := by
  -- This is the evaluation rule for the bundled path.
  rfl

/-- Helper for Lemma 55.3: circle coordinates of the standard boundary loop
are the rotated exponential coordinates. -/
private theorem diskBoundaryLoop_circle_apply (b₀ : ∂𝔻 2) (t : unitInterval) :
    diskBoundaryHomeomorphCircle (diskBoundaryLoop b₀ t) =
      Circle.exp ((t : ℝ) * (2 * Real.pi)) * diskBoundaryHomeomorphCircle b₀ := by
  -- Cancel the inverse homeomorphism in the definition of the loop.
  rw [diskBoundaryLoop_apply]
  exact diskBoundaryHomeomorphCircle.apply_symm_apply _

/-- Helper for Lemma 55.3: the standard boundary loop covers every point of
the disk boundary. -/
private theorem diskBoundaryLoop_surjective (b₀ : ∂𝔻 2) :
    Function.Surjective (diskBoundaryLoop b₀) := by
  -- Periodicity puts an exponential preimage in `[0, 2 * π]`, which rescales to `I`.
  intro q
  let z : Circle := diskBoundaryHomeomorphCircle q /
    diskBoundaryHomeomorphCircle b₀
  have hz_range : z ∈ Set.range Circle.exp := by
    rw [Circle.exp_surjective.range_eq]
    exact Set.mem_univ z
  have himage : Circle.exp '' Set.Icc (0 : ℝ) (2 * Real.pi) =
      Set.range Circle.exp := by
    simpa only [zero_add] using Circle.periodic_exp.image_Icc Real.two_pi_pos 0
  rw [← himage] at hz_range
  obtain ⟨x, hx, hxexp⟩ := hz_range
  obtain ⟨hx_zero, hx_period⟩ := hx
  have hperiod_pos : 0 < 2 * Real.pi := Real.two_pi_pos
  have hperiod_ne : 2 * Real.pi ≠ 0 := hperiod_pos.ne'
  let t : unitInterval :=
    ⟨x / (2 * Real.pi), div_nonneg hx_zero hperiod_pos.le,
      (div_le_one hperiod_pos).mpr hx_period⟩
  refine ⟨t, ?_⟩
  apply diskBoundaryHomeomorphCircle.injective
  rw [diskBoundaryLoop_circle_apply]
  change Circle.exp ((x / (2 * Real.pi)) * (2 * Real.pi)) *
      diskBoundaryHomeomorphCircle b₀ = diskBoundaryHomeomorphCircle q
  rw [div_mul_cancel₀ x hperiod_ne, hxexp]
  simp [z, div_eq_mul_inv]

/-- Helper for Lemma 55.3: the only repeated values of the standard boundary
loop are its two endpoints. -/
private theorem diskBoundaryLoop_fiber (b₀ : ∂𝔻 2) (s t : unitInterval)
    (hst : diskBoundaryLoop b₀ s = diskBoundaryLoop b₀ t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  -- Cancel the basepoint rotation and classify exponential fibers in one period.
  have hcircle := congrArg diskBoundaryHomeomorphCircle hst
  have hexp : Circle.exp ((s : ℝ) * (2 * Real.pi)) =
      Circle.exp ((t : ℝ) * (2 * Real.pi)) := by
    have hmul : Circle.exp ((s : ℝ) * (2 * Real.pi)) *
        diskBoundaryHomeomorphCircle b₀ =
        Circle.exp ((t : ℝ) * (2 * Real.pi)) *
          diskBoundaryHomeomorphCircle b₀ := by
      simpa only [diskBoundaryLoop_circle_apply] using hcircle
    exact mul_right_cancel hmul
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hexp
  have hperiod_pos : 0 < 2 * Real.pi := Real.two_pi_pos
  have hm_value : (s : ℝ) = t + (m : ℝ) := by
    nlinarith
  have hm_lower_real : (-1 : ℝ) ≤ (m : ℝ) := by
    linarith [unitInterval.nonneg s, unitInterval.le_one t]
  have hm_upper_real : (m : ℝ) ≤ 1 := by
    linarith [unitInterval.le_one s, unitInterval.nonneg t]
  have hm_lower : (-1 : ℤ) ≤ m := by exact_mod_cast hm_lower_real
  have hm_upper : m ≤ (1 : ℤ) := by exact_mod_cast hm_upper_real
  have hm_cases : m = -1 ∨ m = 0 ∨ m = 1 := by omega
  have hs_nonneg : 0 ≤ (s : ℝ) := s.property.1
  have hs_le_one : (s : ℝ) ≤ 1 := s.property.2
  have ht_nonneg : 0 ≤ (t : ℝ) := t.property.1
  have ht_le_one : (t : ℝ) ≤ 1 := t.property.2
  rcases hm_cases with hm_neg | hm_zero | hm_pos
  · right
    left
    subst m
    norm_num at hm_value
    constructor
    · have hs_value : (s : ℝ) = 0 := by linarith
      exact Subtype.ext hs_value
    · have ht_value : (t : ℝ) = 1 := by linarith
      exact Subtype.ext ht_value
  · left
    subst m
    norm_num at hm_value
    exact Subtype.ext hm_value
  · right
    right
    subst m
    norm_num at hm_value
    constructor
    · have hs_value : (s : ℝ) = 1 := by linarith
      exact Subtype.ext hs_value
    · have ht_value : (t : ℝ) = 0 := by linarith
      exact Subtype.ext ht_value

/-- Helper for Lemma 55.3: the product of the identity interval map with the
standard boundary loop presents `I × ∂𝔻 2` as a quotient of the square. -/
private noncomputable def loopSquareProjection (b₀ : ∂𝔻 2) :
    C(unitInterval × unitInterval, unitInterval × ∂𝔻 2) :=
  (ContinuousMap.id unitInterval).prodMap (diskBoundaryLoop b₀).toContinuousMap

/-- Helper for Lemma 55.3: the loop-square projection is surjective. -/
private theorem loopSquareProjection_surjective (b₀ : ∂𝔻 2) :
    Function.Surjective (loopSquareProjection b₀) := by
  -- Lift the boundary coordinate through the surjective loop and retain the time coordinate.
  rintro ⟨t, q⟩
  obtain ⟨s, hs⟩ := diskBoundaryLoop_surjective b₀ q
  refine ⟨(t, s), ?_⟩
  apply Prod.ext
  · rfl
  · exact hs

/-- Helper for Lemma 55.3: the loop-square projection is a quotient map. -/
private theorem loopSquareProjection_isQuotientMap (b₀ : ∂𝔻 2) :
    Topology.IsQuotientMap (loopSquareProjection b₀) := by
  -- The square is compact and the product of the interval with the boundary is Hausdorff.
  letI : T2Space (∂𝔻 2) := by
    change T2Space (ULift (Metric.sphere (0 : Plane) 1))
    infer_instance
  exact Topology.IsQuotientMap.of_surjective_continuous
    (loopSquareProjection_surjective b₀) (loopSquareProjection b₀).continuous

/-- Helper for Lemma 55.3: a relative homotopy of the standard loop is
constant on the fibers of the loop-square projection. -/
private theorem pathHomotopy_factors_loopSquare {X : Type u} [TopologicalSpace X]
    (h : C(∂𝔻 2, X)) (b₀ : ∂𝔻 2)
    (F : ((diskBoundaryLoop b₀).map h.continuous).Homotopy (Path.refl (h b₀))) :
    Function.FactorsThrough F.toContinuousMap (loopSquareProjection b₀) := by
  -- Equal loop parameters either agree or are opposite endpoints, where relativity applies.
  intro p q hpq
  change (p.1, diskBoundaryLoop b₀ p.2) =
    (q.1, diskBoundaryLoop b₀ q.2) at hpq
  have htime : p.1 = q.1 :=
    congrArg (fun z : unitInterval × ∂𝔻 2 ↦ z.1) hpq
  have hloop : diskBoundaryLoop b₀ p.2 = diskBoundaryLoop b₀ q.2 :=
    congrArg (fun z : unitInterval × ∂𝔻 2 ↦ z.2) hpq
  rcases diskBoundaryLoop_fiber b₀ p.2 q.2 hloop with
    hparam | ⟨hp_zero, hq_one⟩ | ⟨hp_one, hq_zero⟩
  · exact congrArg F.toContinuousMap (Prod.ext htime hparam)
  · have hp_pair : p = (p.1, 0) := Prod.ext rfl hp_zero
    have hq_pair : q = (q.1, 1) := Prod.ext rfl hq_one
    rw [hp_pair, hq_pair]
    change F (p.1, 0) = F (q.1, 1)
    rw [Path.Homotopy.source, Path.Homotopy.target]
  · have hp_pair : p = (p.1, 1) := Prod.ext rfl hp_one
    have hq_pair : q = (q.1, 0) := Prod.ext rfl hq_zero
    rw [hp_pair, hq_pair]
    change F (p.1, 1) = F (q.1, 0)
    rw [Path.Homotopy.target, Path.Homotopy.source]

/-- Helper for Lemma 55.3: descending a relative loop homotopy gives a
homotopy on the whole disk boundary. -/
private noncomputable def loopSquareHomotopyLift {X : Type u} [TopologicalSpace X]
    (h : C(∂𝔻 2, X)) (b₀ : ∂𝔻 2)
    (F : ((diskBoundaryLoop b₀).map h.continuous).Homotopy (Path.refl (h b₀))) :
    C(unitInterval × ∂𝔻 2, X) :=
  (loopSquareProjection_isQuotientMap b₀).lift F.toContinuousMap
    (pathHomotopy_factors_loopSquare h b₀ F)

/-- Helper for Lemma 55.3: at time zero the descended loop homotopy is the
original boundary map. -/
private theorem loopSquareHomotopyLift_zero {X : Type u} [TopologicalSpace X]
    (h : C(∂𝔻 2, X)) (b₀ : ∂𝔻 2)
    (F : ((diskBoundaryLoop b₀).map h.continuous).Homotopy (Path.refl (h b₀)))
    (q : ∂𝔻 2) : loopSquareHomotopyLift h b₀ F (0, q) = h q := by
  -- Choose a loop parameter for `q` and evaluate the quotient-lift triangle at time zero.
  obtain ⟨s, rfl⟩ := diskBoundaryLoop_surjective b₀ q
  have hlift := congrArg
    (fun f : C(unitInterval × unitInterval, X) ↦ f (0, s))
    ((loopSquareProjection_isQuotientMap b₀).lift_comp F.toContinuousMap
      (pathHomotopy_factors_loopSquare h b₀ F))
  change loopSquareHomotopyLift h b₀ F (0, diskBoundaryLoop b₀ s) = F (0, s)
    at hlift
  calc
    loopSquareHomotopyLift h b₀ F (0, diskBoundaryLoop b₀ s) = F (0, s) := hlift
    _ = (diskBoundaryLoop b₀).map h.continuous s := F.apply_zero s
    _ = h (diskBoundaryLoop b₀ s) := rfl

/-- Helper for Lemma 55.3: at time one the descended loop homotopy is constant
at the image of the basepoint. -/
private theorem loopSquareHomotopyLift_one {X : Type u} [TopologicalSpace X]
    (h : C(∂𝔻 2, X)) (b₀ : ∂𝔻 2)
    (F : ((diskBoundaryLoop b₀).map h.continuous).Homotopy (Path.refl (h b₀)))
    (q : ∂𝔻 2) : loopSquareHomotopyLift h b₀ F (1, q) = h b₀ := by
  -- Choose a loop parameter for `q` and use the constant endpoint of the path homotopy.
  obtain ⟨s, rfl⟩ := diskBoundaryLoop_surjective b₀ q
  have hlift := congrArg
    (fun f : C(unitInterval × unitInterval, X) ↦ f (1, s))
    ((loopSquareProjection_isQuotientMap b₀).lift_comp F.toContinuousMap
      (pathHomotopy_factors_loopSquare h b₀ F))
  change loopSquareHomotopyLift h b₀ F (1, diskBoundaryLoop b₀ s) = F (1, s)
    at hlift
  calc
    loopSquareHomotopyLift h b₀ F (1, diskBoundaryLoop b₀ s) = F (1, s) := hlift
    _ = Path.refl (h b₀) s := F.apply_one s
    _ = h b₀ := rfl

/-- Helper for Lemma 55.3: the descended square supplies an unbased
nullhomotopy of the boundary map. -/
private noncomputable def diskBoundaryNullhomotopy {X : Type u} [TopologicalSpace X]
    (h : C(∂𝔻 2, X)) (b₀ : ∂𝔻 2)
    (F : ((diskBoundaryLoop b₀).map h.continuous).Homotopy (Path.refl (h b₀))) :
    h.Homotopy (ContinuousMap.const _ (h b₀)) :=
  ⟨loopSquareHomotopyLift h b₀ F, loopSquareHomotopyLift_zero h b₀ F,
    loopSquareHomotopyLift_one h b₀ F⟩

/-- Helper for Lemma 55.3: a null path homotopy of the standard boundary loop
forces the entire boundary map to be nullhomotopic. -/
private theorem nullhomotopic_of_diskBoundaryLoop_homotopic_refl
    {X : Type u} [TopologicalSpace X] (h : C(∂𝔻 2, X)) (b₀ : ∂𝔻 2)
    (hloop : ((diskBoundaryLoop b₀).map h.continuous).Homotopic
      (Path.refl (h b₀))) : h.Nullhomotopic := by
  -- Choose the relative path homotopy and descend it through the loop quotient.
  obtain ⟨F⟩ := hloop
  exact ⟨h b₀, ⟨diskBoundaryNullhomotopy h b₀ F⟩⟩

/-- Helper for Lemma 55.3: an extension across the disk induces the trivial
homomorphism on fundamental groups. -/
private theorem fundamentalGroupMap_eq_one_of_extends_disk
    {X : Type u} [TopologicalSpace X] (h : C(∂𝔻 2, X)) (b₀ : ∂𝔻 2)
    (k : C(𝔻 2, X)) (hk : k.comp (diskBoundaryInclusion 2).hom = h) :
    FundamentalGroup.map h b₀ = 1 := by
  -- Factor the induced map through the subsingleton fundamental group of the disk.
  letI : ContractibleSpace (𝔻 2) := diskTwoContractibleSpace
  have hinclusion : FundamentalGroup.map (diskBoundaryInclusion 2).hom b₀ = 1 := by
    ext p
    exact Subsingleton.elim _ _
  rw [← hk]
  ext p
  rw [FundamentalGroup.map_apply, MonoidHom.one_apply, FundamentalGroup.one_def,
    Path.Homotopic.Quotient.map_comp]
  have hp_disk : Path.Homotopic.Quotient.map p (diskBoundaryInclusion 2).hom =
      Path.Homotopic.Quotient.refl ((diskBoundaryInclusion 2).hom b₀) := by
    have hp := congrArg (fun f : FundamentalGroup (∂𝔻 2) b₀ →*
      FundamentalGroup (𝔻 2) ((diskBoundaryInclusion 2).hom b₀) ↦ f p) hinclusion
    rw [FundamentalGroup.map_apply, MonoidHom.one_apply,
      FundamentalGroup.one_def] at hp
    change Path.Homotopic.Quotient.map p (diskBoundaryInclusion 2).hom =
      Path.Homotopic.Quotient.refl ((diskBoundaryInclusion 2).hom b₀) at hp
    exact hp
  rw [hp_disk]
  rfl

/-- Lemma 55.3, equivalence of (1) and (2). A continuous map from `∂𝔻 2` is
nullhomotopic if and only if it extends continuously over `𝔻 2`. -/
theorem nullhomotopic_iff_extends_disk {X : Type u} [TopologicalSpace X]
    (h : C(∂𝔻 2, X)) :
    h.Nullhomotopic ↔
      ∃ k : C(𝔻 2, X), k.comp (diskBoundaryInclusion 2).hom = h := by
  -- Route correction: the fundamental-group argument proves a later companion;
  -- this equivalence follows directly from cone descent and disk contractibility.
  constructor
  · -- Descend the given contraction through the radial quotient of the boundary cone.
    rintro ⟨x, ⟨H⟩⟩
    exact ⟨diskConeExtension H, diskConeExtension_comp_boundary H⟩
  · -- Restrict a contraction of the disk and postcompose it with the extension.
    rintro ⟨k, hk⟩
    letI : ContractibleSpace (𝔻 2) := diskTwoContractibleSpace
    have hinclusion : ((diskBoundaryInclusion 2).hom).Nullhomotopic :=
      (id_nullhomotopic (𝔻 2)).comp_left (diskBoundaryInclusion 2).hom
    have hcomposite := hinclusion.comp_right k
    rwa [hk] at hcomposite

/-- Companion to Lemma 55.3, equivalence of (1) and (3). A continuous map from `∂𝔻 2` is
nullhomotopic if and only if its induced fundamental-group homomorphism is trivial. -/
theorem nullhomotopic_iff_fundamentalGroupMap_eq_one {X : Type u} [TopologicalSpace X]
    (h : C(∂𝔻 2, X)) (b₀ : ∂𝔻 2) :
    h.Nullhomotopic ↔ FundamentalGroup.map h b₀ = 1 := by
  constructor
  · -- Extend a nullhomotopic map across the disk, whose fundamental group is trivial.
    intro hnull
    obtain ⟨k, hk⟩ := (nullhomotopic_iff_extends_disk h).mp hnull
    exact fundamentalGroupMap_eq_one_of_extends_disk h b₀ k hk
  · -- Evaluate the trivial induced map on the once-around loop and descend its path homotopy.
    intro hmap
    have hclass := congrArg
      (fun f : FundamentalGroup (∂𝔻 2) b₀ →* FundamentalGroup X (h b₀) ↦
        f (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (diskBoundaryLoop b₀)))) hmap
    have hquotient :
        Path.Homotopic.Quotient.mk ((diskBoundaryLoop b₀).map h.continuous) =
          Path.Homotopic.Quotient.mk (Path.refl (h b₀)) := by
      rw [FundamentalGroup.map_apply, MonoidHom.one_apply,
        FundamentalGroup.one_def] at hclass
      rw [Path.Homotopic.Quotient.mk_map, Path.Homotopic.Quotient.mk_refl]
      exact hclass
    exact nullhomotopic_of_diskBoundaryLoop_homotopic_refl h b₀
      (Path.Homotopic.Quotient.eq.mp hquotient)

/-- Companion to Lemma 55.3, equivalence of (2) and (3). A continuous map from `∂𝔻 2` extends
continuously over `𝔻 2` if and only if its induced fundamental-group homomorphism is trivial. -/
theorem extends_disk_iff_fundamentalGroupMap_eq_one {X : Type u} [TopologicalSpace X]
    (h : C(∂𝔻 2, X)) (b₀ : ∂𝔻 2) :
    (∃ k : C(𝔻 2, X), k.comp (diskBoundaryInclusion 2).hom = h) ↔
      FundamentalGroup.map h b₀ = 1 :=
  (nullhomotopic_iff_extends_disk h).symm.trans
    (nullhomotopic_iff_fundamentalGroupMap_eq_one h b₀)
