import Mathlib
import DifferentialForms_Cartan_1970.cartan.II.section05.«0026_Definition_II_1_extra_16»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped unitInterval
open Metric

noncomputable section

open Topology

/-- The positive real basepoint of the radius-`r` closed disc. -/
def closedDiscBoundaryBasepoint (r : NNReal) : closedBall (0 : ℂ) (r : ℝ) :=
  ⟨(r : ℂ), by
    have hr : (r : ℂ) = circleMap 0 (r : ℝ) 0 := by
      simp [circleMap_zero]
    rw [hr]
    exact circleMap_mem_closedBall 0 r.2 (0 : ℝ)⟩

/-- The positively oriented boundary loop of the radius-`r` closed disc, viewed in the closed
disc itself. -/
def closedDiscBoundary (r : NNReal) :
    Path (closedDiscBoundaryBasepoint r) (closedDiscBoundaryBasepoint r) :=
  Path.mk
    ⟨fun t ↦
        (⟨circleMap 0 (r : ℝ) (2 * Real.pi * (t : ℝ)),
          circleMap_mem_closedBall 0 r.2 (2 * Real.pi * (t : ℝ))⟩ :
          closedBall (0 : ℂ) (r : ℝ)),
      Continuous.subtype_mk (by fun_prop) _⟩
    (by
      apply Subtype.ext
      simp [closedDiscBoundaryBasepoint, circleMap_zero])
    (by
      apply Subtype.ext
      simp [closedDiscBoundaryBasepoint, circleMap_zero, Complex.exp_two_pi_mul_I])

/-- Evaluating `closedDiscBoundary r` gives the standard positive counterclockwise circle
parameterization inside the closed disc. -/
@[simp] theorem closedDiscBoundary_apply (r : NNReal) (t : I) :
    closedDiscBoundary r t =
      (⟨circleMap 0 (r : ℝ) (2 * Real.pi * (t : ℝ)),
        circleMap_mem_closedBall 0 r.2 (2 * Real.pi * (t : ℝ))⟩ :
        closedBall (0 : ℂ) (r : ℝ)) := rfl

/-- The closed boundary loop obtained by restricting a continuous map on the closed disc to the
circle `|z| = r`. -/
def closedDiscBoundaryPath (r : NNReal) (f : C(closedBall (0 : ℂ) (r : ℝ), ℂ)) :
    Path (f (closedDiscBoundaryBasepoint r)) (f (closedDiscBoundaryBasepoint r)) :=
  (closedDiscBoundary r).map f.continuous

/-- Evaluating the boundary loop amounts to evaluating `f` on the standard positive
counterclockwise circle parameterization. -/
-- Proof sketch: `closedDiscBoundaryPath r f` is `closedDiscBoundary r` mapped by `f`, so
-- evaluation is just `f` applied to the standard boundary point.
@[simp] theorem closedDiscBoundaryPath_apply (r : NNReal)
    (f : C(closedBall (0 : ℂ) (r : ℝ), ℂ)) (t : I) :
    closedDiscBoundaryPath r f t =
      f ⟨circleMap 0 (r : ℝ) (2 * Real.pi * (t : ℝ)),
        circleMap_mem_closedBall 0 r.2 (2 * Real.pi * (t : ℝ))⟩ := rfl

/-- The positively oriented standard circle of radius `r` in `ℂ`. -/
def standardCirclePath (r : NNReal) : Path (r : ℂ) (r : ℂ) :=
  closedDiscBoundaryPath r ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
theorem standardCirclePath_apply (r : NNReal) (t : I) :
    standardCirclePath r t = circleMap 0 (r : ℝ) (2 * Real.pi * (t : ℝ)) := rfl

/-- A point outside the closed disc bounded by the standard circle is outside its image. -/
theorem standardCirclePath_not_mem_range_of_not_mem_closedBall
    (r : NNReal) {a : ℂ} (ha : a ∉ closedBall (0 : ℂ) (r : ℝ)) :
    a ∉ Set.range (standardCirclePath r) := by
  rintro ⟨t, rfl⟩
  exact ha <| by
    rw [standardCirclePath_apply]
    exact circleMap_mem_closedBall 0 r.2 (2 * Real.pi * (t : ℝ))

/-- A point inside the open disc bounded by the standard circle is outside its image. -/
theorem standardCirclePath_not_mem_range_of_mem_ball
    (r : NNReal) {a : ℂ} (ha : a ∈ ball (0 : ℂ) (r : ℝ)) :
    a ∉ Set.range (standardCirclePath r) := by
  rintro ⟨t, rfl⟩
  rw [standardCirclePath_apply] at ha
  exact circleMap_notMem_ball 0 (r : ℝ) (2 * Real.pi * (t : ℝ)) ha

/-- Helper for Proposition 8.1: the center lies in the closed disc of radius `r`. -/
theorem zero_mem_closedDisc (r : NNReal) : (0 : ℂ) ∈ closedBall (0 : ℂ) (r : ℝ) := by
  -- The closed disc radius is nonnegative by definition.
  simp [Metric.mem_closedBall]

/-- Helper for Proposition 8.1: the center of the closed disc as a subtype point. -/
def closedDiscCenter (r : NNReal) : closedBall (0 : ℂ) (r : ℝ) :=
  ⟨0, zero_mem_closedDisc r⟩

/-- Helper for Proposition 8.1: the radial point at radius `s r` and angle `2πt` lies in the
closed disc of radius `r`. -/
theorem radial_boundary_point_mem_closedDisc (r : NNReal) (p : I × I) :
    circleMap 0 ((p.1 : ℝ) * (r : ℝ)) (2 * Real.pi * (p.2 : ℝ)) ∈
      closedBall (0 : ℂ) (r : ℝ) := by
  -- The radius of the intermediate circle is bounded by `r` because `0 ≤ s ≤ 1`.
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_circleMap_zero]
  have hp_nonneg : 0 ≤ (p.1 : ℝ) := p.1.2.1
  have hmul_nonneg : 0 ≤ (p.1 : ℝ) * (r : ℝ) := mul_nonneg hp_nonneg r.2
  rw [abs_of_nonneg hmul_nonneg]
  nlinarith [p.1.2.2, r.2]

/-- Helper for Proposition 8.1: the radial point in the closed disc used to contract the boundary
loop. -/
def radial_boundary_point (r : NNReal) (p : I × I) : closedBall (0 : ℂ) (r : ℝ) :=
  ⟨circleMap 0 ((p.1 : ℝ) * (r : ℝ)) (2 * Real.pi * (p.2 : ℝ)),
    radial_boundary_point_mem_closedDisc r p⟩

/-- Helper for Proposition 8.1: the radial-point map is continuous on the square. -/
theorem continuous_radial_boundary_point (r : NNReal) :
    Continuous (radial_boundary_point r) := by
  -- Continuity is inherited from the explicit circle-map formula.
  apply Continuous.subtype_mk
  fun_prop

/-- Helper for Proposition 8.1: restricting `f` to concentric circles gives the radial homotopy
from the boundary loop to the center value. -/
def radial_boundary_homotopy (r : NNReal) (f : C(closedBall (0 : ℂ) (r : ℝ), ℂ)) :
    C(I × I, ℂ) :=
  ⟨fun p ↦ f (radial_boundary_point r p), by
    exact f.continuous.comp (continuous_radial_boundary_point r)⟩

/-- Helper for Proposition 8.1: at the top edge of the square, the radial homotopy is the boundary
loop of `f`. -/
@[simp] theorem radial_boundary_homotopy_apply_top (r : NNReal)
    (f : C(closedBall (0 : ℂ) (r : ℝ), ℂ)) (t : I) :
    radial_boundary_homotopy r f (1, t) = closedDiscBoundaryPath r f t := by
  -- Setting the radial parameter to `1` recovers the original boundary circle.
  simp [radial_boundary_homotopy, radial_boundary_point, closedDiscBoundaryPath_apply]

/-- Helper for Proposition 8.1: at the bottom edge of the square, the radial homotopy is constant
with value `f(0)`. -/
@[simp] theorem radial_boundary_homotopy_apply_bottom (r : NNReal)
    (f : C(closedBall (0 : ℂ) (r : ℝ), ℂ)) (t : I) :
    radial_boundary_homotopy r f (0, t) = f (closedDiscCenter r) := by
  -- Radius `0` collapses every angle to the center of the disc.
  simp [radial_boundary_homotopy, radial_boundary_point, closedDiscCenter, circleMap_zero]

/-- Helper for Proposition 8.1: the left and right edges of the radial square agree because the
circle parameterization is `2π`-periodic. -/
theorem radial_boundary_homotopy_apply_left_eq_right (r : NNReal)
    (f : C(closedBall (0 : ℂ) (r : ℝ), ℂ)) (s : I) :
    radial_boundary_homotopy r f (s, 0) = radial_boundary_homotopy r f (s, 1) := by
  -- The angles `0` and `2π` determine the same point on every intermediate circle.
  change f (radial_boundary_point r (s, 0)) = f (radial_boundary_point r (s, 1))
  congr 1
  apply Subtype.ext
  simpa [radial_boundary_point] using (periodic_circleMap 0 ((s : ℝ) * (r : ℝ)) 0).symm

/-- Helper for Proposition 8.1: if `f` avoids `a` on the open disc, then the whole radial square
also avoids `a`. -/
theorem radial_boundary_homotopy_avoids_center (r : NNReal)
    (f : C(closedBall (0 : ℂ) (r : ℝ), ℂ)) (a : ℂ) {n : ℤ}
    (hindex : (closedDiscBoundaryPath r f).HasIndexAt a n)
    (hno : ∀ z : ball (0 : ℂ) (r : ℝ), f ⟨z, ball_subset_closedBall z.property⟩ ≠ a) :
    ∀ p : I × I, radial_boundary_homotopy r f p ≠ a := by
  intro p
  rcases lt_or_eq_of_le p.1.2.2 with hp_lt | hp_eq
  · -- On the interior circles, the point lies in the open disc and the contradiction hypothesis
    -- excludes the value `a`.
    by_cases hr_zero : (r : ℝ) = 0
    · -- When `r = 0`, the whole square collapses to the center, which is also the boundary value.
      have hcenter_ne : f (closedDiscCenter r) ≠ a := by
        have hboundary_zero : closedDiscBoundaryPath r f 0 = f (closedDiscCenter r) := by
          change
            f ⟨circleMap 0 (r : ℝ) (2 * Real.pi * (0 : ℝ)),
              circleMap_mem_closedBall 0 r.2 (2 * Real.pi * (0 : ℝ))⟩ =
              f (closedDiscCenter r)
          congr 1
          apply Subtype.ext
          simp [closedDiscCenter, hr_zero, circleMap_zero]
        simpa [hboundary_zero] using hindex.ne_center 0
      simpa [radial_boundary_homotopy, radial_boundary_point, hr_zero, circleMap_zero,
        closedDiscCenter] using hcenter_ne
    · have hr_pos : 0 < (r : ℝ) := lt_of_le_of_ne r.2 fun h ↦ hr_zero h.symm
      let z : ball (0 : ℂ) (r : ℝ) :=
        ⟨circleMap 0 ((p.1 : ℝ) * (r : ℝ)) (2 * Real.pi * (p.2 : ℝ)), by
          rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_circleMap_zero]
          have hp_nonneg : 0 ≤ (p.1 : ℝ) := p.1.2.1
          have hmul_nonneg : 0 ≤ (p.1 : ℝ) * (r : ℝ) := mul_nonneg hp_nonneg r.2
          rw [abs_of_nonneg hmul_nonneg]
          nlinarith⟩
      -- The radial point is exactly the interior witness supplied to `hno`.
      simpa [radial_boundary_homotopy, radial_boundary_point, z]
        using hno z
  · -- On the top edge, the square is exactly the boundary loop, so `hindex` already shows it
    -- avoids `a`.
    have hp_top : p.1 = (1 : I) := Subtype.ext hp_eq
    have hp_pair : p = (1, p.2) := Prod.ext hp_top rfl
    rw [hp_pair]
    simpa using hindex.ne_center p.2

-- Proof sketch: argue by contradiction. If `f` avoids `a` on the whole closed disc, then the
-- radial contraction of the disc to the center induces a homotopy in `ℂ \ {a}` from the boundary
-- loop `closedDiscBoundaryPath r f` to a constant loop, forcing winding index `0`, contrary to
-- `hn`.
/-- Proposition 8.1: if the boundary loop of a continuous map on the closed disc has nonzero
winding index about `a`, then `f` takes the value `a` at some point of the open disc. -/
theorem exists_preimage_in_openBall_of_closedDiscBoundaryPath_hasIndexAt_ne_zero
    (r : NNReal) (f : C(closedBall (0 : ℂ) (r : ℝ), ℂ)) (a : ℂ) {n : ℤ}
    (hindex : (closedDiscBoundaryPath r f).HasIndexAt a n) (hn : n ≠ 0) :
    ∃ z : ball (0 : ℂ) (r : ℝ), f ⟨z, ball_subset_closedBall z.property⟩ = a := by
  by_contra hno_exists
  push Not at hno_exists
  let H := radial_boundary_homotopy r f
  have hH_ne : ∀ p : I × I, H p ≠ a :=
    radial_boundary_homotopy_avoids_center r f a hindex hno_exists
  have hcenter_ne : f (closedDiscCenter r) - a ≠ 0 := by
    -- The center is either an interior point of the disc or, in the degenerate radius-zero case,
    -- the same point as the boundary basepoint.
    by_cases hr_zero : (r : ℝ) = 0
    · have hfa : f (closedDiscCenter r) ≠ a := by
        have hboundary_zero : closedDiscBoundaryPath r f 0 = f (closedDiscCenter r) := by
          change
            f ⟨circleMap 0 (r : ℝ) (2 * Real.pi * (0 : ℝ)),
              circleMap_mem_closedBall 0 r.2 (2 * Real.pi * (0 : ℝ))⟩ =
              f (closedDiscCenter r)
          congr 1
          apply Subtype.ext
          simp [closedDiscCenter, hr_zero, circleMap_zero]
        simpa [hboundary_zero] using hindex.ne_center 0
      exact sub_ne_zero.mpr hfa
    · have hr_pos : 0 < (r : ℝ) := lt_of_le_of_ne r.2 fun h ↦ hr_zero h.symm
      have hcenter_mem : (0 : ℂ) ∈ ball (0 : ℂ) (r : ℝ) := by
        simpa using hr_pos
      have hfa : f (closedDiscCenter r) ≠ a := by
        simpa [closedDiscCenter] using
          hno_exists ⟨0, hcenter_mem⟩
      exact sub_ne_zero.mpr hfa
  let G : C(I × I, {z : ℂ // z ≠ 0}) :=
    ⟨fun p ↦ ⟨H p - a, sub_ne_zero.mpr (hH_ne p)⟩, by
      apply Continuous.subtype_mk
      fun_prop⟩
  let bottomLift : C(I, ℂ) := ContinuousMap.const I (Complex.log (f (closedDiscCenter r) - a))
  have hbottom_lifts : ∀ t : I, G (0, t) = ⟨Complex.exp (bottomLift t), Complex.exp_ne_zero _⟩ := by
    intro t
    apply Subtype.ext
    -- The chosen bottom lift is the logarithm of the constant bottom edge.
    change H (0, t) - a = Complex.exp (bottomLift t)
    rw [radial_boundary_homotopy_apply_bottom]
    symm
    simpa [bottomLift] using Complex.exp_log hcenter_ne
  let W : C(I × I, ℂ) := Complex.isCoveringMap_exp.liftHomotopy G bottomLift hbottom_lifts
  have hW_lifts :
      (fun z : ℂ ↦ (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ∘ W = G :=
    Complex.isCoveringMap_exp.liftHomotopy_lifts G bottomLift hbottom_lifts
  have hW_zero : ∀ t : I, W (0, t) = bottomLift t :=
    Complex.isCoveringMap_exp.liftHomotopy_zero G bottomLift hbottom_lifts
  have hbottom_const : W (0, 0) = W (0, 1) := by
    -- The homotopy lift was anchored along the entire bottom edge by a constant logarithm.
    rw [hW_zero 0, hW_zero 1]
    simp [bottomLift]
  let leftLift : C(I, ℂ) :=
    ⟨fun s ↦ W (s, 0), by
      fun_prop⟩
  let rightLift : C(I, ℂ) :=
    ⟨fun s ↦ W (s, 1), by
      fun_prop⟩
  have hvertical_eq_fun : ⇑leftLift = ⇑rightLift := by
    -- The left and right edges have the same projection under `exp`, and the bottom-edge
    -- computation gives them the same starting value.
    refine Complex.isCoveringMap_exp.eq_of_comp_eq leftLift.continuous rightLift.continuous ?_ 0 ?_
    · ext s
      change Complex.exp (leftLift s) = Complex.exp (rightLift s)
      have hs_left : Complex.exp (leftLift s) = H (s, 0) - a := by
        simpa [leftLift, G] using congrArg Subtype.val (congr_fun hW_lifts (s, 0))
      have hs_right : Complex.exp (rightLift s) = H (s, 1) - a := by
        simpa [rightLift, G] using congrArg Subtype.val (congr_fun hW_lifts (s, 1))
      calc
        Complex.exp (leftLift s) = H (s, 0) - a := hs_left
        _ = H (s, 1) - a := by rw [radial_boundary_homotopy_apply_left_eq_right]
        _ = Complex.exp (rightLift s) := hs_right.symm
    · simpa [leftLift, rightLift] using hbottom_const
  have hvertical_eq : leftLift = rightLift := by
    ext s
    exact congr_fun hvertical_eq_fun s
  have htop_endpoints : W (1, 1) = W (1, 0) := by
    -- Evaluating the equality of the vertical edge lifts at `s = 1` gives the needed top-edge
    -- endpoint agreement.
    symm
    simpa [leftLift, rightLift] using congrArg (fun F : C(I, ℂ) ↦ F 1) hvertical_eq
  let topLift : C(I, ℂ) :=
    ⟨fun t ↦ W (1, t), by
      fun_prop⟩
  have htop_exp : ∀ t : I, Complex.exp (topLift t) = closedDiscBoundaryPath r f t - a := by
    intro t
    -- Restrict the lifted square to the top edge to obtain a logarithm of the boundary loop.
    simpa [topLift, G, H, radial_boundary_homotopy_apply_top] using
      congrArg Subtype.val (congr_fun hW_lifts (1, t))
  have htop_jump :
      topLift 1 = topLift 0 + ((2 * Real.pi : ℂ) * (((0 : ℤ) : ℂ))) * Complex.I := by
    -- The top-edge lift has equal endpoints, so its index jump is zero.
    simpa [topLift] using htop_endpoints
  have hzero : (closedDiscBoundaryPath r f).HasIndexAt a 0 := by
    refine ⟨topLift, htop_exp, htop_jump⟩
  have hn_zero : n = 0 := hindex.eq hzero
  exact hn hn_zero
